#!/usr/bin/env python3
"""Prepare a source-first v11 contract map without issuing semantic receipts.

This mechanical preparer is deliberately narrow.  It binds a curated list of
canonical paper claim Specs to existing byte-pinned source inventory items; it
does not judge their meanings, invent claim atoms, or make an older receipt
current.  The resulting map is therefore an auditable *pending* v11 surface:
every selected Spec has one source route, while any retained source claim with
no selected semantic target remains visible for the subsequent review.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
_SOURCE_LOCATOR_RE = re.compile(r"^(?P<path>[^:]+):(?P<start>[1-9][0-9]*)(?:-(?P<end>[1-9][0-9]*))?$")
_SOURCE_LOCATOR_IN_TEXT_RE = re.compile(
    r"(?P<path>[^\s;:,]+):(?P<start>[1-9][0-9]*)(?:-(?P<end>[1-9][0-9]*))?"
)


class PreparationError(ValueError):
    """Raised when a proposed source-to-Spec route is ambiguous or invalid."""


def load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise PreparationError(f"could not read {label}: {error}") from error
    if not isinstance(payload, dict):
        raise PreparationError(f"{label} must be a JSON object")
    return payload


def as_string_list(value: object, *, label: str) -> list[str]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise PreparationError(f"{label} must be a list of nonempty strings")
    result = [item.strip() for item in value]
    if len(result) != len(set(result)):
        raise PreparationError(f"{label} must not contain duplicates")
    return result


def full_name(namespace: str, module: str, short: str) -> str:
    return f"{namespace}.{module}.{short}"


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _corrected_target_digest(target: Mapping[str, Any]) -> str:
    payload = dict(target)
    payload.pop("corrected_target_sha256", None)
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _source_quote(folder: Path, locator: str) -> tuple[str, str]:
    match = _SOURCE_LOCATOR_RE.fullmatch(locator.strip())
    if match is None:
        raise PreparationError(
            "corrected-target archival_source_locator must be one relative file:line or file:start-end anchor"
        )
    path = folder / match.group("path")
    try:
        relative = path.resolve().relative_to(folder.resolve())
    except ValueError as error:
        raise PreparationError("corrected-target source anchor leaves its paper folder") from error
    if not path.is_file() or str(relative).startswith("../"):
        raise PreparationError(f"corrected-target source anchor `{locator}` is not a readable paper-local file")
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    start = int(match.group("start"))
    end = int(match.group("end") or start)
    if start > end or end > len(lines):
        raise PreparationError(f"corrected-target source anchor `{locator}` is out of range")
    quote = "\n".join(lines[start - 1 : end])
    return quote, hashlib.sha256(quote.encode("utf-8")).hexdigest()


def _apply_corrected_targets(
    items: dict[str, dict[str, Any]],
    config: Mapping[str, Any],
    *,
    folder: Path | None,
) -> None:
    """Apply explicit approved-target records without deciding their semantics.

    This prepares the deterministic pins an independent reviewer needs.  It
    intentionally accepts neither an inferred correction nor a replacement of
    the archival statement: every target, defect id, source anchor, and
    approval reference must be supplied in the configuration.
    """

    raw_targets = config.get("corrected_targets", {})
    if raw_targets in ({}, None):
        return
    if folder is None:
        raise PreparationError("corrected_targets require the paper folder")
    if not isinstance(raw_targets, Mapping):
        raise PreparationError("corrected_targets must be an object keyed by source-map item")
    for raw_key, raw_target in raw_targets.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_target, Mapping):
            raise PreparationError("each corrected_targets entry needs an existing source-map item and object")
        statement = str(raw_target.get("statement") or "").strip()
        archival_statement = str(raw_target.get("archival_statement") or "").strip()
        locator = str(raw_target.get("archival_source_locator") or "").strip()
        source_note = str(raw_target.get("source_note") or "").strip()
        governing = raw_target.get("governing_defect_ids")
        approval_raw = raw_target.get("approval")
        if not statement or not archival_statement or not locator or not source_note:
            raise PreparationError(
                f"{key}: corrected target needs statement, archival_statement, archival_source_locator, and source_note"
            )
        if re.sub(r"\s+", " ", statement) == re.sub(r"\s+", " ", archival_statement):
            raise PreparationError(f"{key}: corrected target must differ from its preserved archival_statement")
        if (
            not isinstance(governing, list)
            or not governing
            or any(not isinstance(value, str) or not value.strip() for value in governing)
            or len({value.strip() for value in governing}) != len(governing)
        ):
            raise PreparationError(f"{key}: governing_defect_ids must be a nonempty unique string list")
        if not isinstance(approval_raw, Mapping):
            raise PreparationError(f"{key}: corrected target needs an approval object")
        kind = str(approval_raw.get("kind") or "").strip()
        recorded_at = str(approval_raw.get("recorded_at") or "").strip()
        reference = str(approval_raw.get("reference") or "").strip()
        artifact_rel = str(approval_raw.get("artifact_path") or "").strip()
        artifact = folder / artifact_rel
        try:
            artifact.resolve().relative_to(folder.resolve())
        except ValueError as error:
            raise PreparationError(f"{key}: approval artifact must remain paper-local") from error
        if not kind or not recorded_at or not reference or not artifact_rel or not artifact.is_file():
            raise PreparationError(f"{key}: approval needs kind, recorded_at, reference, and a readable paper-local artifact_path")
        _quote, quote_digest = _source_quote(folder, locator)
        approval = {
            "kind": kind,
            "recorded_at": recorded_at,
            "reference": reference,
            "target_statement_sha256": hashlib.sha256(
                re.sub(r"\s+", " ", statement).strip().encode("utf-8")
            ).hexdigest(),
            "artifact_path": artifact_rel,
            "artifact_sha256": _sha256_file(artifact),
        }
        target: dict[str, Any] = {
            "schema": 1,
            "statement": statement,
            "governing_defect_ids": [value.strip() for value in governing],
            "archival_equivalence_claimed": False,
            "archival_source_locator": locator,
            "archival_source_quote_sha256": quote_digest,
            "approval": approval,
        }
        target["corrected_target_sha256"] = _corrected_target_digest(target)
        item = items[key]
        item["coverage_status"] = "corrected_source_statement"
        item["source_status"] = "corrected"
        item["inventory_role"] = "corrected_source_target"
        item["statement"] = archival_statement
        item["source_note"] = source_note
        item["corrected_target"] = target


def _atomize_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Split an explicitly compound source presentation into claim-level rows.

    A v11 source-to-Spec contract is deliberately one-to-one.  Some earlier
    inventories used one source item for multiple separately stated branches
    of a displayed definition.  This helper preserves the same byte-pinned
    source anchor but requires the migration configuration to supply each
    branch's statement, source note, and direct Lean route.  It does not infer
    a semantic split from declaration names.
    """

    raw_atomizations = config.get("atomize_source_items", {})
    if raw_atomizations in ({}, None):
        return
    if not isinstance(raw_atomizations, Mapping):
        raise PreparationError("atomize_source_items must be an object")
    for raw_parent, raw_plan in raw_atomizations.items():
        parent = str(raw_parent).strip()
        if not parent or parent not in items or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each atomize_source_items entry needs an existing source item and object"
            )
        reason = str(raw_plan.get("reason") or "").strip()
        raw_atoms = raw_plan.get("items")
        if not reason or not isinstance(raw_atoms, Mapping) or not raw_atoms:
            raise PreparationError(
                f"{parent}: atomization needs a reason and nonempty items object"
            )
        atom_names = [str(raw_name).strip() for raw_name in raw_atoms]
        if (
            any(not name for name in atom_names)
            or len(atom_names) != len(set(atom_names))
            or any(name in items and name != parent for name in atom_names)
        ):
            raise PreparationError(
                f"{parent}: atomized item names must be new, nonempty, and unique"
            )
        original = items.pop(parent)
        for raw_name, raw_atom in raw_atoms.items():
            name = str(raw_name).strip()
            if not isinstance(raw_atom, Mapping):
                raise PreparationError(f"{parent}/{name}: atom must be an object")
            statement = str(raw_atom.get("statement") or "").strip()
            source_note = str(raw_atom.get("source_note") or "").strip()
            declarations = raw_atom.get("lean_declarations")
            if (
                not statement
                or not source_note
                or not isinstance(declarations, list)
                or not declarations
                or any(not isinstance(value, str) or not value.strip() for value in declarations)
                or len({value.strip() for value in declarations}) != len(declarations)
            ):
                raise PreparationError(
                    f"{parent}/{name}: atom needs statement, source_note, and unique lean_declarations"
                )
            item = dict(original)
            item["statement"] = statement
            item["source_note"] = source_note
            item["lean_declarations"] = [value.strip() for value in declarations]
            item["aliases"] = [value.rsplit(".", maxsplit=1)[-1] for value in declarations]
            # The old reconciliation spoke about the compound presentation;
            # fresh v11 source-to-Spec review is responsible for the new
            # claim-level semantic comparison.
            item.pop("source_prose_definition_reconciliation", None)
            item["source_atomization"] = {
                "schema": 1,
                "parent_source_item": parent,
                "basis": reason,
                "validator": "v11 source-first review-surface preparation",
                "validated_at": "2026-08-18T00:00:00Z",
            }
            items[name] = item


def _deduplicated_values(values: list[object]) -> list[object]:
    """Preserve order while deduplicating JSON-shaped source metadata."""

    seen: set[str] = set()
    result: list[object] = []
    for value in values:
        token = json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
        if token not in seen:
            seen.add(token)
            result.append(value)
    return result


def _canonical_anchor_evidence(folder: Path, source_location: str) -> list[dict[str, Any]]:
    """Construct byte-pinned exact source excerpts for a declared locator bundle."""

    anchors: list[dict[str, Any]] = []
    for match in _SOURCE_LOCATOR_IN_TEXT_RE.finditer(source_location):
        raw_path = match.group("path")
        path = folder / raw_path
        try:
            relative = path.resolve().relative_to(folder.resolve())
        except ValueError as error:
            raise PreparationError("consolidated source anchor leaves its paper folder") from error
        if not path.is_file() or str(relative).startswith("../"):
            raise PreparationError(
                f"consolidated source anchor `{raw_path}` is not a readable paper-local file"
            )
        try:
            text = path.read_bytes().decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        except UnicodeDecodeError as error:
            raise PreparationError(
                f"consolidated source anchor `{raw_path}` is not UTF-8 text"
            ) from error
        lines = text.split("\n")
        if text.endswith("\n"):
            lines.pop()
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if start > end or end > len(lines):
            raise PreparationError(
                f"consolidated source anchor `{raw_path}:{start}-{end}` is out of range"
            )
        quote = "\n".join(lines[start - 1 : end])
        anchors.append(
            {
                "path": raw_path,
                "line_start": start,
                "line_end": end,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
            }
        )
    if not anchors:
        raise PreparationError(
            "consolidated source item needs source_location with at least one file:line anchor"
        )
    return anchors


def _consolidate_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Replace a prior implementation-level split by one paper-source claim.

    This is the inverse of atomization for the distinct case where the paper
    itself has one numbered/defined claim but the initial interface split its
    semantic content into several Specs.  The configuration must spell out the
    one source presentation, exact semantic target, and one atom; this helper
    only performs deterministic inventory surgery and exact source pinning.
    """

    raw_consolidations = config.get("consolidate_source_items", {})
    if raw_consolidations in ({}, None):
        return
    if folder is None:
        raise PreparationError("consolidate_source_items require the paper folder")
    if not isinstance(raw_consolidations, Mapping):
        raise PreparationError("consolidate_source_items must be an object")
    for raw_name, raw_plan in raw_consolidations.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_plan, Mapping):
            raise PreparationError("each consolidated source item needs a name and object")
        raw_sources = raw_plan.get("source_items")
        if not isinstance(raw_sources, list) or len(raw_sources) < 2:
            raise PreparationError(f"{name}: source_items must name at least two prior source items")
        sources = [str(value).strip() for value in raw_sources]
        if any(not value for value in sources) or len(sources) != len(set(sources)):
            raise PreparationError(f"{name}: source_items must be nonempty and unique")
        target_already_exists = name in items
        if target_already_exists and any(source in items for source in sources):
            raise PreparationError(f"{name}: target already exists while prior source items remain")
        missing = [source for source in sources if source not in items]
        if missing and not target_already_exists:
            raise PreparationError(f"{name}: source item(s) absent: {', '.join(missing)}")
        statement = str(raw_plan.get("statement") or "").strip()
        source_note = str(raw_plan.get("source_note") or "").strip()
        source_kind = str(raw_plan.get("source_kind") or "").strip()
        source_location = str(raw_plan.get("source_location") or "").strip()
        declarations = raw_plan.get("lean_declarations")
        raw_atom = raw_plan.get("source_claim_atom")
        if (
            not statement
            or not source_note
            or not source_kind
            or not source_location
            or not isinstance(declarations, list)
            or len(declarations) != 1
            or not isinstance(declarations[0], str)
            or not declarations[0].strip()
            or not isinstance(raw_atom, Mapping)
        ):
            raise PreparationError(
                f"{name}: needs statement, source_note, source_kind, source_location, "
                "one lean declaration, and source_claim_atom"
            )
        atom_id = str(raw_atom.get("id") or "").strip()
        atom_locator = str(raw_atom.get("source_locator") or "").strip()
        atom_claim = str(raw_atom.get("semantic_claim") or "").strip()
        if not atom_id or not atom_locator or not atom_claim:
            raise PreparationError(
                f"{name}: source_claim_atom needs id, source_locator, and semantic_claim"
            )
        atom_anchors = _canonical_anchor_evidence(folder, atom_locator)
        if len(atom_anchors) != 1:
            raise PreparationError(
                f"{name}: source_claim_atom.source_locator must be one exact source anchor"
            )
        source_items = [items.pop(name)] if target_already_exists else [items.pop(source) for source in sources]
        result = dict(source_items[0])
        result["statement"] = statement
        result["source_note"] = source_note
        result["source_kind"] = source_kind
        result["source_location"] = source_location
        result["source_anchor_evidence"] = _canonical_anchor_evidence(folder, source_location)
        result["lean_declarations"] = [declarations[0].strip()]
        result["aliases"] = [declarations[0].strip().rsplit(".", maxsplit=1)[-1]]
        result["claim_bearing"] = True
        result["source_claim_atoms"] = [
            {
                "id": atom_id,
                "source_locator": atom_locator,
                "source_quote_sha256": atom_anchors[0]["quoted_text_sha256"],
                "semantic_claim": atom_claim,
                "reviewed_lean_route": declarations[0].strip() + "Spec",
            }
        ]
        raw_reconciliation = raw_plan.get("prose_definition_reconciliation")
        if raw_reconciliation is not None:
            if not isinstance(raw_reconciliation, Mapping) or source_kind != "definition":
                raise PreparationError(
                    f"{name}: prose_definition_reconciliation is allowed only for a definition object"
                )
            presentation_sha = str(raw_reconciliation.get("presentation_sha256") or "").strip()
            semantic_basis = str(raw_reconciliation.get("semantic_basis") or "").strip()
            validator = str(raw_reconciliation.get("validator") or "").strip()
            validator_type = str(raw_reconciliation.get("validator_type") or "").strip()
            validated_at = str(raw_reconciliation.get("validated_at") or "").strip()
            if (
                not re.fullmatch(r"[0-9a-fA-F]{64}", presentation_sha)
                or len(semantic_basis) < 20
                or not validator
                or validator_type not in {"agent", "human", "model"}
                or not validated_at
            ):
                raise PreparationError(
                    f"{name}: prose_definition_reconciliation needs a presentation SHA-256, "
                    "substantive basis, validator, validator type, and timestamp"
                )
            statement_digest = hashlib.sha256(
                " ".join(statement.replace("\r\n", "\n").replace("\r", "\n").split()).encode("utf-8")
            ).hexdigest()
            result["source_prose_definition_reconciliation"] = {
                "schema": 2,
                "relation": "source_item_represents_prose_definition",
                "presentation_sha256": presentation_sha.lower(),
                "source_item_statement_sha256": statement_digest,
                "judgment": "semantically_equivalent",
                "semantic_basis": semantic_basis,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
            }
        raw_contexts = raw_plan.get("semantic_context_requirements")
        clear_contexts = raw_plan.get("clear_semantic_context_requirements")
        if clear_contexts is True:
            if raw_contexts is not None:
                raise PreparationError(
                    f"{name}: cannot supply and clear semantic_context_requirements"
                )
            contexts = []
        elif clear_contexts not in {None, False}:
            raise PreparationError(
                f"{name}: clear_semantic_context_requirements must be boolean"
            )
        elif raw_contexts is None:
            contexts = _deduplicated_values(
                [
                    context
                    for source in source_items
                    for context in source.get("semantic_context_requirements", [])
                    if isinstance(context, Mapping)
                ]
            )
        else:
            if not isinstance(raw_contexts, list) or not raw_contexts:
                raise PreparationError(
                    f"{name}: semantic_context_requirements must be a nonempty list when supplied"
                )
            contexts = []
            for index, raw_context in enumerate(raw_contexts):
                if not isinstance(raw_context, Mapping):
                    raise PreparationError(
                        f"{name}: semantic_context_requirements[{index}] must be an object"
                    )
                semantic_role = str(raw_context.get("semantic_role") or "").strip()
                context_location = str(raw_context.get("source_location") or "").strip()
                if semantic_role not in {
                    "definition",
                    "model",
                    "model_construction",
                    "scope",
                    "prior_result",
                    "stated_antecedent",
                } or not context_location:
                    raise PreparationError(
                        f"{name}: semantic context needs a bounded semantic_role and source_location"
                    )
                context: dict[str, Any] = {
                    "semantic_role": semantic_role,
                    "source_anchor_evidence": _canonical_anchor_evidence(
                        folder, context_location
                    ),
                }
                contexts.append(context)
            contexts = _deduplicated_values(contexts)
        if contexts:
            result["semantic_context_requirements"] = contexts
        else:
            result.pop("semantic_context_requirements", None)
        conventions = _deduplicated_values(
            [
                convention
                for source in source_items
                for convention in source.get("model_convention_ids", [])
                if isinstance(convention, str) and convention.strip()
            ]
        )
        if conventions:
            result["model_convention_ids"] = conventions
        else:
            result.pop("model_convention_ids", None)
        raw_presentation_core = raw_plan.get("source_presentation_reconciliation")
        if raw_presentation_core is not None:
            if not isinstance(raw_presentation_core, Mapping):
                raise PreparationError(
                    f"{name}: source_presentation_reconciliation must be an object"
                )
            presentation_kind = str(raw_presentation_core.get("presentation_kind") or "").strip()
            presentation_label = str(raw_presentation_core.get("presentation_label") or "").strip()
            core_locator = str(raw_presentation_core.get("core_anchor_locator") or "").strip()
            boundary_reason = str(raw_presentation_core.get("boundary_reason") or "").strip()
            semantic_basis = str(raw_presentation_core.get("semantic_basis") or "").strip()
            validator = str(raw_presentation_core.get("validator") or "").strip()
            validated_at = str(raw_presentation_core.get("validated_at") or "").strip()
            core_anchors = _canonical_anchor_evidence(folder, core_locator) if core_locator else []
            if (
                not presentation_kind
                or not presentation_label
                or len(core_anchors) != 1
                or boundary_reason != "completed_statement_then_explanation"
                or not semantic_basis
                or not validator
                or not validated_at
            ):
                raise PreparationError(
                    f"{name}: source_presentation_reconciliation needs source kind/label, one core "
                    "anchor, completed-statement boundary reason, basis, validator, and timestamp"
                )
            result["source_presentation_reconciliation"] = {
                "schema": 1,
                "relation": "conservative_text_span_core",
                "presentation_kind": presentation_kind,
                "presentation_label": presentation_label,
                "core_anchor": core_anchors[0],
                "boundary_reason": boundary_reason,
                "semantic_basis": semantic_basis,
                "validator": validator,
                "validated_at": validated_at,
            }
        for stale in (
            "source_atomization",
            "source_presentation_alias",
            "semantic_contract",
            "proof_lean_declarations",
            "support_lean_declarations",
            "source_spec_correspondence",
        ):
            result.pop(stale, None)
        items[name] = result


def _consolidate_presentation_aliases(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Collapse redundant aliases of one repeated source presentation."""

    raw_consolidations = config.get("consolidate_presentation_aliases", {})
    if raw_consolidations in ({}, None):
        return
    if folder is None:
        raise PreparationError("consolidate_presentation_aliases require the paper folder")
    if not isinstance(raw_consolidations, Mapping):
        raise PreparationError("consolidate_presentation_aliases must be an object")
    for raw_name, raw_plan in raw_consolidations.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_plan, Mapping):
            raise PreparationError("each consolidated presentation alias needs a name and object")
        raw_sources = raw_plan.get("source_items")
        if not isinstance(raw_sources, list) or len(raw_sources) < 2:
            raise PreparationError(f"{name}: source_items must name at least two prior aliases")
        sources = [str(value).strip() for value in raw_sources]
        if any(not value for value in sources) or len(sources) != len(set(sources)):
            raise PreparationError(f"{name}: source_items must be nonempty and unique")
        if name in items:
            if any(source in items for source in sources):
                raise PreparationError(f"{name}: target already exists while prior aliases remain")
            continue
        missing = [source for source in sources if source not in items]
        if missing:
            raise PreparationError(f"{name}: source alias(es) absent: {', '.join(missing)}")
        statement = str(raw_plan.get("statement") or "").strip()
        source_note = str(raw_plan.get("source_note") or "").strip()
        source_kind = str(raw_plan.get("source_kind") or "").strip()
        source_location = str(raw_plan.get("source_location") or "").strip()
        if not statement or not source_note or not source_kind or not source_location:
            raise PreparationError(
                f"{name}: needs statement, source_note, source_kind, and source_location"
            )
        prior_items = [items.pop(source) for source in sources]
        result = dict(prior_items[0])
        result["statement"] = statement
        result["source_note"] = source_note
        result["source_kind"] = source_kind
        result["source_location"] = source_location
        result["source_anchor_evidence"] = _canonical_anchor_evidence(folder, source_location)
        result["claim_bearing"] = False
        result["inventory_role"] = "source_presentation_alias"
        for stale in (
            "aliases",
            "lean_declarations",
            "proof_lean_declarations",
            "support_lean_declarations",
            "source_claim_atoms",
            "source_atomization",
            "source_spec_correspondence",
            "semantic_contract",
        ):
            result.pop(stale, None)
        items[name] = result


def prepare(
    source_map: dict[str, Any], config: Mapping[str, Any], *, folder: Path | None = None
) -> dict[str, Any]:
    paper = str(config.get("paper") or "").strip()
    if paper != str(source_map.get("paper") or "").strip():
        raise PreparationError("config paper must match paper_statement_map.json")
    namespace = str(config.get("namespace") or "").strip()
    if not namespace:
        raise PreparationError("config needs namespace")
    specs = as_string_list(config.get("include_specs"), label="include_specs")
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise PreparationError("paper_statement_map.json has no items object")
    items = {str(key): dict(value) for key, value in raw_items.items() if isinstance(value, Mapping)}
    if len(items) != len(raw_items):
        raise PreparationError("every existing source-map item must be an object")
    _atomize_source_items(items, config)
    _consolidate_source_items(items, config, folder=folder)
    _consolidate_presentation_aliases(items, config, folder=folder)

    overrides_raw = config.get("source_item_for_spec", {})
    if not isinstance(overrides_raw, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in overrides_raw.items()
    ):
        raise PreparationError("source_item_for_spec must be a string-to-string object")
    overrides = {str(key).strip(): str(value).strip() for key, value in overrides_raw.items()}
    unknown_overrides = sorted(set(overrides) - set(specs))
    if unknown_overrides:
        raise PreparationError(
            "source_item_for_spec names not selected by include_specs: "
            + ", ".join(unknown_overrides)
        )

    raw_evidence_names = config.get("evidence_declaration_for_spec", {})
    if not isinstance(raw_evidence_names, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str) and value.strip()
        for key, value in raw_evidence_names.items()
    ):
        raise PreparationError(
            "evidence_declaration_for_spec must be a string-to-nonempty-string object"
        )
    evidence_names = {
        str(key).strip(): str(value).strip()
        for key, value in raw_evidence_names.items()
    }
    unknown_evidence_names = sorted(set(evidence_names) - set(specs))
    if unknown_evidence_names:
        raise PreparationError(
            "evidence_declaration_for_spec names not selected by include_specs: "
            + ", ".join(unknown_evidence_names)
        )

    raw_evidence_modes = config.get("evidence_mode_for_spec", {})
    if not isinstance(raw_evidence_modes, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str) and value.strip()
        for key, value in raw_evidence_modes.items()
    ):
        raise PreparationError("evidence_mode_for_spec must be a string-to-nonempty-string object")
    evidence_modes = {
        str(key).strip(): str(value).strip()
        for key, value in raw_evidence_modes.items()
    }
    unknown_evidence_modes = sorted(set(evidence_modes) - set(specs))
    if unknown_evidence_modes:
        raise PreparationError(
            "evidence_mode_for_spec names not selected by include_specs: "
            + ", ".join(unknown_evidence_modes)
        )
    invalid_evidence_modes = sorted(
        spec for spec, mode in evidence_modes.items()
        if mode not in {"proves", "definitionally_realizes"}
    )
    if invalid_evidence_modes:
        raise PreparationError(
            "evidence_mode_for_spec values must be `proves` or `definitionally_realizes`: "
            + ", ".join(invalid_evidence_modes)
        )

    merge_raw = config.get("merge_source_items", {})
    if not isinstance(merge_raw, Mapping) or not all(
        isinstance(key, str) and isinstance(value, list)
        and all(isinstance(item, str) for item in value)
        for key, value in merge_raw.items()
    ):
        raise PreparationError("merge_source_items must map a source item to a string list")
    for raw_canonical, raw_aliases in merge_raw.items():
        canonical = str(raw_canonical).strip()
        aliases = [str(item).strip() for item in raw_aliases]
        if canonical not in items:
            raise PreparationError(f"merge canonical source item `{canonical}` is absent")
        if not aliases or len(aliases) != len(set(aliases)):
            raise PreparationError(f"{canonical}: merged source items must be a nonempty unique list")
        canonical_item = items[canonical]
        canonical_anchors = list(canonical_item.get("source_anchor_evidence") or [])
        locations = [str(canonical_item.get("source_location") or "").strip()]
        for alias in aliases:
            if alias == canonical:
                raise PreparationError(f"{canonical}: cannot merge a source item into itself")
            if alias not in items:
                # A previous preparation may already have folded this exact
                # context presentation into its canonical raw bundle. The
                # command remains idempotent; current anchor hashes still
                # decide whether that bundled evidence is usable.
                continue
            alias_item = items.pop(alias)
            canonical_anchors.extend(alias_item.get("source_anchor_evidence") or [])
            locations.append(str(alias_item.get("source_location") or "").strip())
        canonical_item["source_anchor_evidence"] = canonical_anchors
        canonical_item["source_location"] = "; ".join(
            location for location in locations if location
        )
        canonical_item["source_note"] = (
            str(canonical_item.get("source_note") or "").strip()
            + " The raw source bundle also includes the explicitly merged source presentation(s) "
            "needed to interpret this one canonical claim."
        ).strip()

    aliases_raw = config.get("presentation_aliases", {})
    if not isinstance(aliases_raw, Mapping):
        raise PreparationError("presentation_aliases must be an object")
    presentation_aliases: dict[str, dict[str, str]] = {}
    for raw_alias, raw_value in aliases_raw.items():
        alias = str(raw_alias).strip()
        if not isinstance(raw_value, Mapping):
            raise PreparationError(f"presentation alias `{alias}` must be an object")
        canonical = str(raw_value.get("canonical_source_item") or "").strip()
        basis = str(raw_value.get("semantic_basis") or "").strip()
        if not alias or alias not in items or not canonical or canonical not in items or not basis:
            raise PreparationError(
                f"presentation alias `{alias}` needs an existing canonical source item and semantic_basis"
            )
        presentation_aliases[alias] = {
            "canonical_source_item": canonical,
            "semantic_basis": basis,
        }

    source_items_for_spec: dict[str, str] = {}
    for spec in specs:
        configured = overrides.get(spec)
        if configured:
            if configured not in items:
                raise PreparationError(f"{spec}: configured source item `{configured}` is absent")
            source_items_for_spec[spec] = configured
            continue
        routes = [
            key
            for key, item in items.items()
            if spec in {
                declaration.rsplit(".", maxsplit=1)[-1]
                for declaration in item.get("lean_declarations", [])
                if isinstance(declaration, str)
            }
        ]
        if len(routes) != 1:
            rendered = ", ".join(routes) if routes else "none"
            raise PreparationError(
                f"{spec}: needs one explicit source_item_for_spec route; found {rendered}"
            )
        source_items_for_spec[spec] = routes[0]

    reused_items: dict[str, list[str]] = {}
    for spec, key in source_items_for_spec.items():
        reused_items.setdefault(key, []).append(spec)
    ambiguous_items = {key: values for key, values in reused_items.items() if len(values) > 1}
    if ambiguous_items:
        details = "; ".join(
            f"{key}: {', '.join(values)}" for key, values in sorted(ambiguous_items.items())
        )
        raise PreparationError(
            "one source-map item cannot silently represent multiple canonical Specs; "
            "atomize the source presentation first (" + details + ")"
        )

    selected_by_item = {key: spec for spec, key in source_items_for_spec.items()}
    raw_dispositions = config.get("unselected_item_dispositions", {})
    if not isinstance(raw_dispositions, Mapping):
        raise PreparationError("unselected_item_dispositions must be an object")
    unselected_dispositions: dict[str, dict[str, str]] = {}
    for raw_key, raw_value in raw_dispositions.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_value, Mapping):
            raise PreparationError(
                "each unselected_item_dispositions entry needs an existing source-map item and object"
            )
        role = str(raw_value.get("inventory_role") or "").strip()
        disposition = str(raw_value.get("scope_disposition") or "").strip()
        reason = str(raw_value.get("reason") or "").strip()
        if not role or not disposition or not reason:
            raise PreparationError(
                f"{key}: unselected disposition needs inventory_role, scope_disposition, and reason"
            )
        if key in selected_by_item:
            raise PreparationError(
                f"{key}: selected source item cannot also receive an unselected disposition"
            )
        unselected_dispositions[key] = {
            "inventory_role": role,
            "scope_disposition": disposition,
            "reason": reason,
        }

    for key, item in items.items():
        selected = selected_by_item.get(key)
        item.pop("semantic_contract", None)
        if key in presentation_aliases:
            alias = presentation_aliases[key]
            item["source_presentation_alias"] = {
                "schema": 1,
                "canonical_source_item": alias["canonical_source_item"],
                "relation": "repeated_source_presentation",
                "semantic_basis": alias["semantic_basis"],
                "validator": "v11 source-first review-surface preparation",
                "validated_at": "2026-08-18T00:00:00Z",
            }
            # A repeated source presentation remains claim-bearing, but its
            # canonical source item alone owns the source-to-Spec route.
            # Retained old direct routes would turn the alias into a hidden
            # second semantic claim.
            item.pop("lean_declarations", None)
            item.pop("proof_lean_declarations", None)
            item.pop("support_lean_declarations", None)
        else:
            item.pop("source_presentation_alias", None)
        if selected is None:
            # The source inventory stays intact. A later audit must either add
            # a semantic target or give this genuine source claim an explicit,
            # source-grounded disposition; it cannot disappear during a
            # mechanical interface migration.
            if key in presentation_aliases:
                # A repeated byte-pinned presentation is retained for source
                # traceability but is not a second paper claim or denominator
                # row. Its canonical source item alone owns the semantic route.
                item["claim_bearing"] = False
                item["inventory_role"] = "source_presentation_alias"
                continue
            configured = unselected_dispositions.get(key)
            if configured is not None:
                item["claim_bearing"] = False
                item["inventory_role"] = configured["inventory_role"]
                item["scope_disposition"] = configured["scope_disposition"]
                item["scope_disposition_note"] = configured["reason"]
                continue
            current_role = str(item.get("inventory_role") or "").strip()
            if current_role in {"proof_support", "source_premise_declaration"}:
                item["claim_bearing"] = False
                continue
            if bool(item.get("claim_bearing")) or current_role == "direct_source_target":
                raise PreparationError(
                    f"{key}: unselected source claim needs an explicit unselected_item_dispositions entry"
                )
            item["claim_bearing"] = False
            continue
        item["claim_bearing"] = True
        spec_name = full_name(namespace, "PaperInterface", selected + "Spec")
        endpoint_name = full_name(
            namespace,
            "PaperInterface",
            evidence_names.get(selected, selected),
        )
        item["semantic_contract"] = {
            "spec_declaration": spec_name,
            "evidence_declaration": endpoint_name,
            "evidence_mode": evidence_modes.get(selected, "proves"),
            "semantic_shape": "plain",
        }
        item["lean_declarations"] = [endpoint_name]
        item["support_lean_declarations"] = [spec_name]
        item.pop("proof_lean_declarations", None)

    _apply_corrected_targets(items, config, folder=folder)

    result = dict(source_map)
    result["items"] = items
    result["semantic_contract_schema"] = 1
    result["source_spec_correspondence_schema"] = 1
    source_version = str(config.get("source_version") or "").strip()
    if source_version:
        result["source_version"] = source_version
    policy = str(result.get("source_inventory_policy") or "").strip()
    v11_policy = (
        "Canonical v11 review binds one transparent PaperInterface Spec to each "
        "selected source claim; retained source claims without a current Spec route "
        "remain explicit audit work rather than disappearing from the inventory."
    )
    policy_without_v11 = policy.replace(v11_policy, " ")
    policy_without_v11 = " ".join(policy_without_v11.split())
    result["source_inventory_policy"] = (
        policy_without_v11 + " " + v11_policy
    ).strip()
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = ROOT / "papers" / args.paper
    try:
        source_map = load_object(paper_dir / "audit" / "paper_statement_map.json", label="source map")
        config = load_object(args.config, label="preparation config")
        prepared = prepare(source_map, config, folder=paper_dir)
    except PreparationError as error:
        print(f"v11 source-map preparation refused: {error}", file=sys.stderr)
        return 1
    selected = len(as_string_list(config.get("include_specs"), label="include_specs"))
    if not args.write:
        print(f"{args.paper}: prepared {selected} canonical v11 source-to-Spec route(s); rerun with --write")
        return 0
    path = paper_dir / "audit" / "paper_statement_map.json"
    path.write_text(json.dumps(prepared, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} with {selected} canonical v11 source-to-Spec route(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
