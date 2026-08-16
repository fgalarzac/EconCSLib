#!/usr/bin/env python3
"""Generate and validate a portable immutable legacy-v10 trust ledger.

The ledger credits name-independent semantic material identities and a separate
content-addressed saved-status reuse receipt. Paper folders, source-map keys,
and Lean declaration names are locators rather than material lookup keys.
Folder names supplied to the generator only select an explicit candidate tree
and provide human navigation labels. Runtime validation reads current tracked
worktree files and Git index metadata, but no historical Git objects, so the
same ledger is portable to the public clone.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence

try:
    from formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
        IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
        IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
        formalization_material_protocol_digest,
        validate_formalization_protocol,
    )
    from theorem_realization_transition import (
        CLOSEOUT_STATUSES,
        MATERIAL_ARTIFACT_PATHS,
        current_material_closeout_identity_record,
    )
    from saved_status_reuse import (
        WorktreeImportClosureProvider,
        current_saved_status_reuse_receipt,
        validated_saved_status_reuse_receipt,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style imports.
    from scripts.formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
        IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
        IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
        formalization_material_protocol_digest,
        validate_formalization_protocol,
    )
    from scripts.theorem_realization_transition import (
        CLOSEOUT_STATUSES,
        MATERIAL_ARTIFACT_PATHS,
        current_material_closeout_identity_record,
    )
    from scripts.saved_status_reuse import (
        WorktreeImportClosureProvider,
        current_saved_status_reuse_receipt,
        validated_saved_status_reuse_receipt,
    )


MANIFEST_ID = "legacy-v10-semantic-material-identities"
ENTRY_SCHEMA = 3
EVIDENCE_SCHEMA = 1
SAVED_STATUS_REUSE_EVIDENCE = "saved-status-reuse"
DIRECT_SOURCE_ROW_REVIEW_EVIDENCE = "direct-source-row-review"
ENGINE_SOURCE_PATHS = (
    "scripts/formalization_protocol.py",
    "scripts/source_coverage_scope.py",
    "scripts/source_archive_surface.py",
    "scripts/theorem_realization_transition.py",
    "scripts/lean_import_closure.py",
    "scripts/lean_import_graph_helper.lean",
    "scripts/saved_status_reuse.py",
    "scripts/final_closure_receipt.py",
    "scripts/tomllib_compat.py",
    "scripts/review_dashboard.py",
    "scripts/legacy_v10_trust_ledger.py",
)
GENERATED_AGGREGATE_EXCLUSIONS = (
    "papers/status.json",
    "papers/human_status.json",
    "docs/PAPER_STATUS.md",
    "site/index.html",
)
MATERIAL_COMPONENT_KEYS = frozenset(
    {
        "selected_source_item_semantic_sha256s",
        "statement_semantic_identities",
        "source_record_semantic_identity",
        "formalization_scope_semantic_identity",
        "governing_correction_semantic_sha256s",
        "lean_owned_dependency_and_artifact_context",
        "audit_authority_identity",
    }
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class LegacyV10TrustLedgerError(ValueError):
    """The configured trust ledger is absent, malformed, stale, or ambiguous."""


@dataclass(frozen=True)
class TrustLedgerEvaluation:
    required: bool
    reason: str
    current_material_identity_sha256: str = ""
    baseline_material_identity_sha256: str = ""


@dataclass(frozen=True)
class SavedStatusReuseEvaluation:
    required: bool
    reason: str
    current_material_identity_sha256: str = ""
    baseline_material_identity_sha256: str = ""
    current_receipt_sha256: str = ""
    baseline_receipt_sha256: str = ""
    statement_counts: Mapping[str, int] | None = None
    coverage_counts: Mapping[str, int] | None = None
    coverage_source_bindings: tuple[Mapping[str, str], ...] = ()
    canonical_source_state: str = ""


def _stable_digest(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if len(text) != 64 or any(
        character not in "0123456789abcdef" for character in text
    ):
        raise LegacyV10TrustLedgerError(f"{field} must be a lowercase SHA-256")
    return text


def _validated_saved_status_reuse_receipt(
    value: object,
    field: str,
) -> dict[str, object]:
    try:
        return validated_saved_status_reuse_receipt(value)
    except ValueError as exc:
        raise LegacyV10TrustLedgerError(f"{field} is invalid: {exc}") from exc


def _validated_direct_source_row_review_receipt(
    value: object, field: str
) -> dict[str, object]:
    """Validate the portable portion of a canonical direct-review receipt.

    The configured manifest authenticates this historical evidence. Runtime
    acceptance separately validates the current paper-local receipt against
    source/map/interface/ledger bytes, so this structural check deliberately
    does not try to reconstruct the source-row semantic judgment from prose.
    """

    if not isinstance(value, Mapping):
        raise LegacyV10TrustLedgerError(f"{field} must be an object")
    expected = {
        "schema",
        "paper",
        "closure_status",
        "evidence_lane",
        "source_artifact",
        "statement_map",
        "paper_interface_closure",
        "review_ledger",
        "focused_build",
        "protocol",
        "closed_at",
    }
    if set(value) != expected:
        raise LegacyV10TrustLedgerError(f"{field} fields are malformed")
    if value.get("schema") != 2:
        raise LegacyV10TrustLedgerError(f"{field}.schema is unsupported")
    if (
        not isinstance(value.get("paper"), str)
        or not str(value.get("paper") or "").strip()
        or value.get("closure_status") != "current"
        or value.get("evidence_lane") != DIRECT_SOURCE_ROW_REVIEW_EVIDENCE
        or not isinstance(value.get("closed_at"), str)
        or not str(value.get("closed_at") or "").strip()
    ):
        raise LegacyV10TrustLedgerError(f"{field} direct-review identity is malformed")

    def file_pin(name: str, *, allow_boundary: bool = False) -> dict[str, str]:
        raw = value.get(name)
        if not isinstance(raw, Mapping):
            raise LegacyV10TrustLedgerError(f"{field}.{name} is malformed")
        allowed = {"path", "sha256"}
        if allow_boundary:
            allowed.add("content_start")
        if set(raw) - allowed or not {"path", "sha256"} <= set(raw):
            raise LegacyV10TrustLedgerError(f"{field}.{name} fields are malformed")
        path = str(raw.get("path") or "").strip()
        if not path or PurePosixPath(path).is_absolute() or ".." in PurePosixPath(path).parts:
            raise LegacyV10TrustLedgerError(f"{field}.{name}.path is unsafe")
        if allow_boundary and "content_start" in raw and (
            not isinstance(raw.get("content_start"), str)
            or not str(raw.get("content_start") or "").strip()
        ):
            raise LegacyV10TrustLedgerError(f"{field}.{name}.content_start is malformed")
        result = {"path": path, "sha256": _sha256(raw.get("sha256"), f"{field}.{name}.sha256")}
        if allow_boundary and "content_start" in raw:
            result["content_start"] = str(raw["content_start"]).strip()
        return result

    source = file_pin("source_artifact")
    statement_map = file_pin("statement_map")
    ledger = file_pin("review_ledger", allow_boundary=True)
    closure = value.get("paper_interface_closure")
    if not isinstance(closure, Mapping) or set(closure) != {"root", "sha256"}:
        raise LegacyV10TrustLedgerError(f"{field}.paper_interface_closure is malformed")
    if str(closure.get("root") or "").strip() != "PaperInterface.lean":
        raise LegacyV10TrustLedgerError(f"{field}.paper_interface_closure root is malformed")
    focused = value.get("focused_build")
    if not isinstance(focused, Mapping) or set(focused) != {"command", "target", "result", "commit"}:
        raise LegacyV10TrustLedgerError(f"{field}.focused_build is malformed")
    if (
        not str(focused.get("command") or "").strip()
        or not str(focused.get("target") or "").strip()
        or focused.get("result") != "passed"
        or not re.fullmatch(r"[0-9a-f]{40}", str(focused.get("commit") or "").strip().lower())
    ):
        raise LegacyV10TrustLedgerError(f"{field}.focused_build identity is malformed")
    protocol = value.get("protocol")
    if not isinstance(protocol, Mapping) or set(protocol) != {"formalization_review_protocol_sha256"}:
        raise LegacyV10TrustLedgerError(f"{field}.protocol is malformed")
    return {
        "schema": 2,
        "paper": str(value["paper"]).strip(),
        "closure_status": "current",
        "evidence_lane": DIRECT_SOURCE_ROW_REVIEW_EVIDENCE,
        "source_artifact": source,
        "statement_map": statement_map,
        "paper_interface_closure": {
            "root": "PaperInterface.lean",
            "sha256": _sha256(closure.get("sha256"), f"{field}.paper_interface_closure.sha256"),
        },
        "review_ledger": ledger,
        "focused_build": {
            "command": str(focused["command"]).strip(),
            "target": str(focused["target"]).strip(),
            "result": "passed",
            "commit": str(focused["commit"]).strip().lower(),
        },
        "protocol": {
            "formalization_review_protocol_sha256": _sha256(
                protocol.get("formalization_review_protocol_sha256"),
                f"{field}.protocol.formalization_review_protocol_sha256",
            )
        },
        "closed_at": str(value["closed_at"]).strip(),
    }


def _current_direct_source_row_review_receipt(
    root: Path, paper: str
) -> tuple[dict[str, object] | None, str]:
    """Read one explicitly selected direct closeout; absence is not an error."""

    try:
        try:
            from final_closure_receipt import (
                DIRECT_SOURCE_ROW_REVIEW_LANE,
                final_closure_receipt_path,
                validate_final_closure_receipt,
            )
        except ModuleNotFoundError:  # pragma: no cover - module-style imports.
            from scripts.final_closure_receipt import (
                DIRECT_SOURCE_ROW_REVIEW_LANE,
                final_closure_receipt_path,
                validate_final_closure_receipt,
            )
        if not final_closure_receipt_path(root, paper).is_file():
            return None, ""
        receipt = validate_final_closure_receipt(
            root, paper, required_lane=DIRECT_SOURCE_ROW_REVIEW_LANE
        )
        return _validated_direct_source_row_review_receipt(
            receipt.payload, "current direct-source-row-review receipt"
        ), ""
    except (OSError, ValueError) as exc:
        return None, str(exc)


def _protocol_for_root(
    root: Path, protocol: Mapping[str, Any] | None
) -> dict[str, Any]:
    if isinstance(protocol, Mapping):
        return validate_formalization_protocol(dict(protocol))
    path = root / "config" / "formalization_audit_protocol.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LegacyV10TrustLedgerError(
            f"could not load candidate protocol {path}: {exc}"
        ) from exc
    return validate_formalization_protocol(payload)


def trust_ledger_engine_sha256(root: Path) -> str:
    """Hash every source file that defines the credited semantic projection."""

    sources: list[dict[str, str]] = []
    for relative in ENGINE_SOURCE_PATHS:
        try:
            raw = (root / relative).read_bytes()
        except OSError as exc:
            raise LegacyV10TrustLedgerError(
                f"trust-ledger engine source is unavailable: {relative}: {exc}"
            ) from exc
        sources.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest()})
    return _stable_digest(
        {
            "engine_id": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
            "engine_schema": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
            "sources": sources,
        }
    )


def _lookup_identity_from_components(components: Mapping[str, str]) -> str:
    return _stable_digest(
        {
            "schema": 1,
            "selected_source_items_component_sha256": components[
                "selected_source_item_semantic_sha256s"
            ],
        }
    )


def _material_identity_from_components(components: Mapping[str, str]) -> str:
    return _stable_digest(
        {
            "schema": IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
            "component_sha256s": dict(components),
        }
    )


def _entry_credit(
    *,
    lookup_identity_sha256: str,
    material_identity_sha256: str,
    component_sha256s: Mapping[str, str],
    closeout_evidence: Mapping[str, object],
) -> dict[str, object]:
    return {
        "schema": ENTRY_SCHEMA,
        "lookup_identity_sha256": lookup_identity_sha256,
        "material_identity_sha256": material_identity_sha256,
        "component_sha256s": dict(component_sha256s),
        "closeout_evidence": dict(closeout_evidence),
    }


def _entry_identity(credit: Mapping[str, object]) -> str:
    return _stable_digest({"entry_credit": credit})


def _credited_entries_sha256(entries: Sequence[Mapping[str, object]]) -> str:
    credits = [
        {
            key: entry[key]
            for key in (
                "schema",
                "lookup_identity_sha256",
                "material_identity_sha256",
                "component_sha256s",
                "closeout_evidence",
                "entry_identity_sha256",
            )
        }
        for entry in entries
    ]
    return _stable_digest(
        {
            "schema": IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
            "credited_entries": sorted(
                credits, key=lambda value: str(value["entry_identity_sha256"])
            ),
        }
    )


def _paper_folder(root: Path, navigation_label: str) -> Path:
    label = navigation_label.strip()
    path = PurePosixPath(label)
    if (
        not label
        or path.is_absolute()
        or len(path.parts) != 1
        or path.parts[0] in {".", ".."}
        or "\\" in label
    ):
        raise LegacyV10TrustLedgerError(
            "selected paper folders must be direct names under papers/"
        )
    folder = (root / "papers" / label).resolve()
    try:
        folder.relative_to((root / "papers").resolve())
    except ValueError as exc:
        raise LegacyV10TrustLedgerError(
            f"selected paper folder escapes the candidate tree: {label}"
        ) from exc
    return folder


def generate_trust_ledger_payload(
    *,
    root: Path,
    selected_paper_folders: Sequence[str],
    protocol: Mapping[str, Any] | None = None,
    closure_provider: WorktreeImportClosureProvider | None = None,
) -> dict[str, object]:
    """Generate a deterministic ledger from one explicit candidate tree/list."""

    root = root.resolve()
    labels = [str(value).strip() for value in selected_paper_folders]
    if not labels or any(not value for value in labels):
        raise LegacyV10TrustLedgerError(
            "generator requires an explicit nonempty completed-paper list"
        )
    if len(labels) != len(set(labels)):
        raise LegacyV10TrustLedgerError(
            "generator completed-paper list contains duplicate navigation labels"
        )
    protocol_payload = _protocol_for_root(root, protocol)
    protocol_sha256 = formalization_material_protocol_digest(protocol_payload)
    entries: list[dict[str, object]] = []
    if closure_provider is None:
        closure_provider = WorktreeImportClosureProvider(root)
    for label in labels:
        folder = _paper_folder(root, label)
        try:
            status = json.loads((folder / "status.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise LegacyV10TrustLedgerError(
                f"selected paper has no valid status.json: {label}: {exc}"
            ) from exc
        if not isinstance(status, Mapping):
            raise LegacyV10TrustLedgerError(
                f"selected paper status is not an object: {label}"
            )
        status_value = str(status.get("status") or "").strip().lower()
        if status_value not in CLOSEOUT_STATUSES:
            raise LegacyV10TrustLedgerError(
                f"selected paper is not a completed closeout: {label}"
            )
        record, error = current_material_closeout_identity_record(
            folder,
            schema=IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
            protocol=protocol_payload,
        )
        if record is None:
            raise LegacyV10TrustLedgerError(
                f"selected paper material identity is unavailable: {label}: {error}"
            )
        direct_receipt, direct_problem = _current_direct_source_row_review_receipt(
            root, label
        )
        if direct_receipt is not None:
            closeout_evidence: dict[str, object] = {
                "schema": EVIDENCE_SCHEMA,
                "kind": DIRECT_SOURCE_ROW_REVIEW_EVIDENCE,
                "receipt": direct_receipt,
            }
        elif direct_problem:
            raise LegacyV10TrustLedgerError(
                f"selected paper direct closeout receipt is invalid: {label}: "
                + direct_problem
            )
        else:
            reuse_receipt, reuse_problem = current_saved_status_reuse_receipt(
                root,
                folder,
                closure_provider=closure_provider,
            )
            if reuse_receipt is None:
                detail = (
                    reuse_problem.format()
                    if reuse_problem is not None
                    else "unknown saved-status receipt failure"
                )
                raise LegacyV10TrustLedgerError(
                    f"selected paper has neither a current direct closeout nor a "
                    f"saved-status reuse receipt: {label}: {detail}"
                )
            closeout_evidence = {
                "schema": EVIDENCE_SCHEMA,
                "kind": SAVED_STATUS_REUSE_EVIDENCE,
                "receipt": reuse_receipt.as_dict(),
            }
        credit = _entry_credit(
            lookup_identity_sha256=record.lookup_identity_sha256,
            material_identity_sha256=record.material_identity_sha256,
            component_sha256s=record.component_sha256s,
            closeout_evidence=closeout_evidence,
        )
        entries.append(
            {
                **credit,
                "entry_identity_sha256": _entry_identity(credit),
                "navigation": {
                    "folder": f"papers/{label}",
                    "paper_id": str(status.get("id") or label),
                    "title": str(status.get("title") or ""),
                },
            }
        )
    entries.sort(key=lambda value: str(value["entry_identity_sha256"]))
    _validate_entry_uniqueness(entries)
    finalization_problems = closure_provider.finalization_problems()
    if finalization_problems:
        details = "; ".join(
            problem.format() for problem in finalization_problems[:3]
        )
        raise LegacyV10TrustLedgerError(
            "Lean import-closure inputs changed during trust-ledger issuance: "
            + details
        )
    credited_digest = _credited_entries_sha256(entries)
    return {
        "schema": IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
        "manifest_id": MANIFEST_ID,
        "engine": {
            "id": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
            "schema": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
            "sha256": trust_ledger_engine_sha256(root),
            "source_paths": list(ENGINE_SOURCE_PATHS),
        },
        "material_identity_schema": IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        "formalization_material_protocol_sha256": protocol_sha256,
        "identity_input_paths": list(MATERIAL_ARTIFACT_PATHS),
        "identity_excludes_configured_manifest": True,
        "generated_aggregate_exclusions": list(GENERATED_AGGREGATE_EXCLUSIONS),
        "selected_entry_count": len(entries),
        "credited_entries_sha256": credited_digest,
        "entries": entries,
    }


def encode_trust_ledger(payload: Mapping[str, object]) -> bytes:
    """Return the deterministic on-disk representation whose raw digest is pinned."""

    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _validate_entry_uniqueness(entries: Sequence[Mapping[str, object]]) -> None:
    for field in (
        "entry_identity_sha256",
        "lookup_identity_sha256",
        "material_identity_sha256",
    ):
        values = [str(entry.get(field) or "") for entry in entries]
        if len(values) != len(set(values)):
            raise LegacyV10TrustLedgerError(
                f"trust ledger contains duplicate or ambiguous {field} entries"
            )


def validate_trust_ledger_payload(
    payload: object,
    *,
    root: Path,
    protocol: Mapping[str, Any],
) -> dict[str, object]:
    """Validate every credited field and runtime engine/protocol identity."""

    if not isinstance(payload, dict):
        raise LegacyV10TrustLedgerError("trust ledger must be a JSON object")
    expected_top_level = {
        "schema",
        "manifest_id",
        "engine",
        "material_identity_schema",
        "formalization_material_protocol_sha256",
        "identity_input_paths",
        "identity_excludes_configured_manifest",
        "generated_aggregate_exclusions",
        "selected_entry_count",
        "credited_entries_sha256",
        "entries",
    }
    if set(payload) != expected_top_level:
        raise LegacyV10TrustLedgerError(
            "trust ledger has missing or unexpected top-level fields"
        )
    if payload.get("schema") != IMMUTABLE_V10_TRUST_LEDGER_SCHEMA:
        raise LegacyV10TrustLedgerError("trust ledger schema is unsupported")
    if payload.get("manifest_id") != MANIFEST_ID:
        raise LegacyV10TrustLedgerError("trust ledger id is unsupported")
    if (
        payload.get("material_identity_schema")
        != IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA
    ):
        raise LegacyV10TrustLedgerError(
            "trust ledger material-identity schema is unsupported"
        )
    if payload.get("identity_input_paths") != list(MATERIAL_ARTIFACT_PATHS):
        raise LegacyV10TrustLedgerError("trust ledger identity input paths changed")
    if payload.get("identity_excludes_configured_manifest") is not True:
        raise LegacyV10TrustLedgerError(
            "trust ledger must exclude its configured manifest from material identity"
        )
    if payload.get("generated_aggregate_exclusions") != list(
        GENERATED_AGGREGATE_EXCLUSIONS
    ):
        raise LegacyV10TrustLedgerError(
            "trust ledger generated-aggregate exclusions changed"
        )
    engine = payload.get("engine")
    if not isinstance(engine, Mapping):
        raise LegacyV10TrustLedgerError("trust ledger engine record is malformed")
    if set(engine) != {"id", "schema", "sha256", "source_paths"}:
        raise LegacyV10TrustLedgerError("trust ledger engine fields are malformed")
    if engine.get("id") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID:
        raise LegacyV10TrustLedgerError("trust ledger engine id is stale")
    if engine.get("schema") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA:
        raise LegacyV10TrustLedgerError("trust ledger engine schema is stale")
    if engine.get("source_paths") != list(ENGINE_SOURCE_PATHS):
        raise LegacyV10TrustLedgerError("trust ledger engine source set changed")
    if _sha256(engine.get("sha256"), "engine.sha256") != trust_ledger_engine_sha256(
        root
    ):
        raise LegacyV10TrustLedgerError("trust ledger engine identity is stale")
    expected_protocol = formalization_material_protocol_digest(protocol)
    if (
        _sha256(
            payload.get("formalization_material_protocol_sha256"),
            "formalization_material_protocol_sha256",
        )
        != expected_protocol
    ):
        raise LegacyV10TrustLedgerError("trust ledger protocol identity is stale")
    raw_entries = payload.get("entries")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise LegacyV10TrustLedgerError("trust ledger entries must be nonempty")
    entries: list[dict[str, object]] = []
    for index, raw_entry in enumerate(raw_entries):
        if not isinstance(raw_entry, dict):
            raise LegacyV10TrustLedgerError(f"trust ledger entry {index} is malformed")
        expected_fields = {
            "schema",
            "lookup_identity_sha256",
            "material_identity_sha256",
            "component_sha256s",
            "closeout_evidence",
            "entry_identity_sha256",
            "navigation",
        }
        if set(raw_entry) != expected_fields or raw_entry.get("schema") != ENTRY_SCHEMA:
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} fields/schema are malformed"
            )
        components = raw_entry.get("component_sha256s")
        if (
            not isinstance(components, dict)
            or set(components) != MATERIAL_COMPONENT_KEYS
        ):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} material components are incomplete"
            )
        validated_components = {
            str(key): _sha256(value, f"entries[{index}].component_sha256s.{key}")
            for key, value in components.items()
        }
        lookup = _sha256(
            raw_entry.get("lookup_identity_sha256"),
            f"entries[{index}].lookup_identity_sha256",
        )
        material = _sha256(
            raw_entry.get("material_identity_sha256"),
            f"entries[{index}].material_identity_sha256",
        )
        evidence = raw_entry.get("closeout_evidence")
        if (
            not isinstance(evidence, Mapping)
            or set(evidence) != {"schema", "kind", "receipt"}
            or evidence.get("schema") != EVIDENCE_SCHEMA
        ):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} closeout evidence is malformed"
            )
        evidence_kind = str(evidence.get("kind") or "").strip()
        if evidence_kind == SAVED_STATUS_REUSE_EVIDENCE:
            validated_evidence_receipt = _validated_saved_status_reuse_receipt(
                evidence.get("receipt"),
                f"entries[{index}].closeout_evidence.receipt",
            )
        elif evidence_kind == DIRECT_SOURCE_ROW_REVIEW_EVIDENCE:
            validated_evidence_receipt = _validated_direct_source_row_review_receipt(
                evidence.get("receipt"),
                f"entries[{index}].closeout_evidence.receipt",
            )
        else:
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} closeout evidence kind is unsupported"
            )
        if lookup != _lookup_identity_from_components(validated_components):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} lookup/component association is invalid"
            )
        if material != _material_identity_from_components(validated_components):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} material/component association is invalid"
            )
        credit = _entry_credit(
            lookup_identity_sha256=lookup,
            material_identity_sha256=material,
            component_sha256s=validated_components,
            closeout_evidence={
                "schema": EVIDENCE_SCHEMA,
                "kind": evidence_kind,
                "receipt": validated_evidence_receipt,
            },
        )
        if _sha256(
            raw_entry.get("entry_identity_sha256"),
            f"entries[{index}].entry_identity_sha256",
        ) != _entry_identity(credit):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} identity is invalid"
            )
        navigation = raw_entry.get("navigation")
        if not isinstance(navigation, Mapping) or set(navigation) != {
            "folder",
            "paper_id",
            "title",
        }:
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} navigation labels are malformed"
            )
        if any(not isinstance(value, str) for value in navigation.values()):
            raise LegacyV10TrustLedgerError(
                f"trust ledger entry {index} navigation labels must be strings"
            )
        entries.append(dict(raw_entry))
    _validate_entry_uniqueness(entries)
    if payload.get("selected_entry_count") != len(entries):
        raise LegacyV10TrustLedgerError("trust ledger entry count is stale")
    if _sha256(
        payload.get("credited_entries_sha256"), "credited_entries_sha256"
    ) != _credited_entries_sha256(entries):
        raise LegacyV10TrustLedgerError("trust ledger credited-entry digest is stale")
    return json.loads(json.dumps(payload))


def load_configured_trust_ledger(
    *,
    root: Path,
    baseline: Mapping[str, Any],
    protocol: Mapping[str, Any],
) -> dict[str, object]:
    if baseline.get("authority") != IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY:
        raise LegacyV10TrustLedgerError("configured authority is not a trust ledger")
    if baseline.get("manifest_schema") != IMMUTABLE_V10_TRUST_LEDGER_SCHEMA:
        raise LegacyV10TrustLedgerError("configured trust-ledger schema is unsupported")
    if baseline.get("engine_id") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID:
        raise LegacyV10TrustLedgerError(
            "configured trust-ledger engine id is unsupported"
        )
    if baseline.get("engine_schema") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA:
        raise LegacyV10TrustLedgerError(
            "configured trust-ledger engine schema is unsupported"
        )
    raw_path = str(baseline.get("manifest_path") or "").strip()
    path = PurePosixPath(raw_path)
    if (
        path.is_absolute()
        or "\\" in raw_path
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise LegacyV10TrustLedgerError("configured trust-ledger path is unsafe")
    manifest_path = (root / raw_path).resolve()
    try:
        manifest_path.relative_to(root.resolve())
    except ValueError as exc:
        raise LegacyV10TrustLedgerError(
            "configured trust-ledger path escapes the repository"
        ) from exc
    try:
        raw = manifest_path.read_bytes()
    except OSError as exc:
        raise LegacyV10TrustLedgerError(
            f"configured trust ledger is unavailable: {exc}"
        ) from exc
    expected_digest = _sha256(
        baseline.get("manifest_sha256"), "configured manifest_sha256"
    )
    if hashlib.sha256(raw).hexdigest() != expected_digest:
        raise LegacyV10TrustLedgerError("configured trust-ledger raw digest mismatches")
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LegacyV10TrustLedgerError(
            f"configured trust ledger is invalid JSON: {exc}"
        ) from exc
    return validate_trust_ledger_payload(payload, root=root, protocol=protocol)


def evaluate_trust_ledger_entry(
    *,
    root: Path,
    folder: Path,
    baseline: Mapping[str, Any],
    protocol: Mapping[str, Any] | None,
) -> TrustLedgerEvaluation:
    """Compare one current semantic record with its unique immutable entry."""

    try:
        protocol_payload = _protocol_for_root(root, protocol)
        manifest = load_configured_trust_ledger(
            root=root, baseline=baseline, protocol=protocol_payload
        )
    except (OSError, ValueError) as exc:
        return TrustLedgerEvaluation(
            True, f"immutable legacy-v10 trust ledger is unavailable: {exc}"
        )
    record, error = current_material_closeout_identity_record(
        folder,
        schema=IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        protocol=protocol_payload,
    )
    if record is None:
        return TrustLedgerEvaluation(
            True, "current material closeout identity is unavailable: " + error
        )
    entries = manifest["entries"]
    matches = [
        entry
        for entry in entries
        if entry["lookup_identity_sha256"] == record.lookup_identity_sha256
    ]
    if not matches:
        return TrustLedgerEvaluation(
            True,
            "paper has no semantic source identity in the immutable legacy-v10 trust ledger",
            current_material_identity_sha256=record.material_identity_sha256,
        )
    if len(matches) != 1:
        return TrustLedgerEvaluation(
            True,
            "paper has an ambiguous semantic source identity in the immutable "
            "legacy-v10 trust ledger",
            current_material_identity_sha256=record.material_identity_sha256,
        )
    entry = matches[0]
    baseline_identity = str(entry["material_identity_sha256"])
    if baseline_identity != record.material_identity_sha256 or entry[
        "component_sha256s"
    ] != dict(record.component_sha256s):
        return TrustLedgerEvaluation(
            True,
            "source/model/target, Lean-owned dependency, correction/scope, or "
            "validator/protocol semantics changed since the immutable legacy-v10 closeout",
            current_material_identity_sha256=record.material_identity_sha256,
            baseline_material_identity_sha256=baseline_identity,
        )
    return TrustLedgerEvaluation(
        False,
        "unchanged immutable legacy-v10 semantic material identity",
        current_material_identity_sha256=record.material_identity_sha256,
        baseline_material_identity_sha256=baseline_identity,
    )


def evaluate_saved_status_reuse(
    *,
    root: Path,
    folder: Path,
    baseline: Mapping[str, Any],
    protocol: Mapping[str, Any] | None,
    closure_provider: WorktreeImportClosureProvider | None = None,
) -> SavedStatusReuseEvaluation:
    """Compare current Lean/audit dispositions with one immutable reuse receipt."""

    try:
        protocol_payload = _protocol_for_root(root, protocol)
        manifest = load_configured_trust_ledger(
            root=root,
            baseline=baseline,
            protocol=protocol_payload,
        )
    except (OSError, ValueError) as exc:
        return SavedStatusReuseEvaluation(
            True, f"immutable legacy-v10 trust ledger is unavailable: {exc}"
        )
    record, error = current_material_closeout_identity_record(
        folder,
        schema=IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        protocol=protocol_payload,
    )
    if record is None:
        return SavedStatusReuseEvaluation(
            True, "current material closeout identity is unavailable: " + error
        )
    matches = [
        entry
        for entry in manifest["entries"]
        if entry["lookup_identity_sha256"] == record.lookup_identity_sha256
    ]
    if len(matches) != 1:
        qualifier = "no" if not matches else "an ambiguous"
        return SavedStatusReuseEvaluation(
            True,
            f"paper has {qualifier} semantic source identity in the immutable "
            "legacy-v10 trust ledger",
            current_material_identity_sha256=record.material_identity_sha256,
        )
    entry = matches[0]
    if entry["material_identity_sha256"] != record.material_identity_sha256 or entry[
        "component_sha256s"
    ] != dict(record.component_sha256s):
        return SavedStatusReuseEvaluation(
            True,
            "paper material identity changed before saved-status reuse",
            current_material_identity_sha256=record.material_identity_sha256,
            baseline_material_identity_sha256=str(entry["material_identity_sha256"]),
        )
    closeout_evidence = entry["closeout_evidence"]
    if closeout_evidence["kind"] != SAVED_STATUS_REUSE_EVIDENCE:
        return SavedStatusReuseEvaluation(
            True,
            "immutable legacy-v10 closeout uses direct-source-row-review evidence; "
            "it is not a saved-status sidecar reuse receipt",
            current_material_identity_sha256=record.material_identity_sha256,
            baseline_material_identity_sha256=str(entry["material_identity_sha256"]),
        )
    baseline_receipt = closeout_evidence["receipt"]
    current, problem = current_saved_status_reuse_receipt(
        root,
        folder,
        closure_provider=closure_provider,
        baseline_lean_closure=baseline_receipt["lean_candidate_closure"],
        baseline_coverage_source_bindings=baseline_receipt["coverage_source_bindings"],
        baseline_canonical_source_attestation=baseline_receipt[
            "canonical_source_attestation"
        ],
    )
    baseline_sha256 = _stable_digest({"saved_status_reuse_receipt": baseline_receipt})
    if current is None:
        detail = problem.format() if problem is not None else "unknown receipt failure"
        return SavedStatusReuseEvaluation(
            True,
            "current saved-status reuse receipt is unavailable: " + detail,
            current_material_identity_sha256=record.material_identity_sha256,
            baseline_material_identity_sha256=str(entry["material_identity_sha256"]),
            baseline_receipt_sha256=baseline_sha256,
        )
    if current.as_dict() != baseline_receipt:
        return SavedStatusReuseEvaluation(
            True,
            "Lean import closure, statement disposition, or coverage disposition "
            "changed since the immutable legacy-v10 review",
            current_material_identity_sha256=record.material_identity_sha256,
            baseline_material_identity_sha256=str(entry["material_identity_sha256"]),
            current_receipt_sha256=current.sha256,
            baseline_receipt_sha256=baseline_sha256,
        )
    return SavedStatusReuseEvaluation(
        False,
        "unchanged immutable legacy-v10 saved-status reuse receipt",
        current_material_identity_sha256=record.material_identity_sha256,
        baseline_material_identity_sha256=str(entry["material_identity_sha256"]),
        current_receipt_sha256=current.sha256,
        baseline_receipt_sha256=baseline_sha256,
        statement_counts=current.statement_counts,
        coverage_counts=current.coverage_counts,
        coverage_source_bindings=tuple(
            dict(binding) for binding in current.coverage_source_bindings
        ),
        canonical_source_state=current.canonical_source_state,
    )


def material_association_comparison_errors(
    previous: object,
    candidate: object,
) -> list[str]:
    """Compare old/new material credits while ignoring the new reuse receipt."""

    def index(
        payload: object, label: str
    ) -> tuple[dict[str, Mapping[str, object]], list[str]]:
        if not isinstance(payload, Mapping) or not isinstance(
            payload.get("entries"), list
        ):
            return {}, [f"{label} manifest has no entries list"]
        indexed: dict[str, Mapping[str, object]] = {}
        errors: list[str] = []
        for offset, raw_entry in enumerate(payload["entries"]):
            if not isinstance(raw_entry, Mapping):
                errors.append(f"{label} entry {offset} is malformed")
                continue
            lookup = str(raw_entry.get("lookup_identity_sha256") or "").strip()
            if not SHA256_RE.fullmatch(lookup):
                errors.append(f"{label} entry {offset} has no lookup identity")
            elif lookup in indexed:
                errors.append(
                    f"{label} manifest has duplicate lookup identity {lookup}"
                )
            else:
                indexed[lookup] = raw_entry
        return indexed, errors

    old, errors = index(previous, "previous")
    new, new_errors = index(candidate, "candidate")
    errors.extend(new_errors)
    if errors:
        return errors
    if set(old) != set(new):
        errors.append("previous/candidate credited source-identity sets differ")
    for lookup in sorted(set(old) & set(new)):
        for field in ("material_identity_sha256", "component_sha256s"):
            if old[lookup].get(field) != new[lookup].get(field):
                errors.append(
                    f"credited material association changed for {lookup}: {field}"
                )
    return errors


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        required=True,
        help="explicit candidate repository root",
    )
    parser.add_argument(
        "--paper",
        action="append",
        required=True,
        help="exact direct paper-folder name; repeat for every selected closeout",
    )
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="manifest output path (the generator never edits protocol config)",
    )
    parser.add_argument(
        "--compare-material-associations",
        type=Path,
        help=(
            "old manifest to compare against; generation fails if any existing "
            "source/material/component association changes"
        ),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    payload = generate_trust_ledger_payload(
        root=args.repo,
        selected_paper_folders=args.paper,
    )
    if args.compare_material_associations is not None:
        try:
            previous = json.loads(
                args.compare_material_associations.read_text(encoding="utf-8")
            )
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            raise LegacyV10TrustLedgerError(
                f"could not read comparison manifest: {exc}"
            ) from exc
        comparison_errors = material_association_comparison_errors(
            previous,
            payload,
        )
        if comparison_errors:
            for error in comparison_errors:
                print("ERROR: " + error)
            return 1
        print("material associations: unchanged")
    raw = encode_trust_ledger(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
