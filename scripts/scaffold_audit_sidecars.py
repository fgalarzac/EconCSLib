#!/usr/bin/env python3
"""Create blank current-schema audit sidecars for an existing paper.

This is an intake helper, not an audit.  It requires a current frozen review
cache and a canonical source map.  Before it writes anything, it also runs the
current source-record helper with its Lean check enabled and validates the
resulting v10 payload.  By default it writes the dashboard intake sidecars plus
the fresh machine-generated source-record audit and a blank source-record
judgment sidecar pinned to that audit digest.  ``--source-record-only`` writes
only the latter two artifacts, so a current statement/coverage review can be
preserved before the source-record surface is regenerated.

The dashboard and judgment files contain no translations, semantic judgments,
source routes, coverage verdicts, validators, timestamps, or source/Lean
statement evidence.  They record only opaque input fingerprints and a
machine-readable ``needs_review`` marker; dashboard loaders reject that marker
until a reviewer removes it after performing the actual audit.

``--force`` is deliberately narrow: it may replace only a recognized blank
scaffold or a zero-judgment machine-generated source-record artifact, whether
its source identity is current or stale. Replacing an invalid, unknown, or
populated semantic artifact requires both ``--force`` and
``--destroy-semantic-evidence``. The command refuses to shadow a legacy
root-level sidecar with a new canonical ``audit/`` sidecar.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

try:
    from scripts import new_paper
    from scripts import review_dashboard
except ModuleNotFoundError:  # Direct `python scripts/scaffold_audit_sidecars.py` execution.
    import new_paper
    import review_dashboard


ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"
PAPER_NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9]*$")
NON_EVIDENCE_SCAFFOLD_KIND = "frozen_cache_source_map_blank_sidecar"
DASHBOARD_SIDECARS = (
    "lean_to_tex_llm.json",
    "statement_match_llm.json",
    "paper_coverage_llm.json",
    "review_surface_llm.json",
)
SOURCE_RECORD_AUDIT_SIDECAR = "source_record_audit.json"
SOURCE_RECORD_MATCH_SIDECAR = "source_record_match_llm.json"
SOURCE_RECORD_SIDECARS = (
    SOURCE_RECORD_AUDIT_SIDECAR,
    SOURCE_RECORD_MATCH_SIDECAR,
)
SOURCE_RECORD_MATCH_SCAFFOLD_KIND = "fresh_source_record_blank_judgment_sidecar"
SOURCE_RECORD_HELPER_RELATIVE_PATH = (
    Path("skills") / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
CANONICAL_SIDECARS = DASHBOARD_SIDECARS + (
    *SOURCE_RECORD_SIDECARS,
)
SOURCE_RECORD_AUDIT_TOP_LEVEL_KEYS = frozenset(
    {
        "paper",
        "paper_dir",
        "import_module",
        "review_interface_source",
        "review_assumption_source",
        "configured_review_rows",
        "prompt_version",
        "source_record_policy_version",
        "source_record_audit_sha256",
        "source_record_judgment_file",
        "current_source_record_judgment_count",
        "resolved_structure_aliases",
        "expected_input_judgment_keys",
        "statement_ledger_covered_boundary_input_keys",
        "expected_field_judgment_keys",
        "expected_semantic_model_judgment_keys",
        "conclusion_dependency_count",
        "conclusion_dependency_items",
        "type_valued_certificate_result_count",
        "type_valued_certificate_result_items",
        "resolved_conclusion_dependency_count",
        "resolved_conclusion_dependency_items",
        "unresolved_conclusion_dependency_count",
        "unresolved_conclusion_dependency_items",
        "review_row_count",
        "configured_review_rows_count",
        "configured_review_row_count",
        "missing_configured_review_rows",
        "quarantined_auxiliary_review_rows",
        "unconfigured_review_surface_rows",
        "unconfigured_paper_interface_rows",
        "unconfigured_assumption_support_rows",
        "boundary_input_count",
        "boundary_input_items",
        "rows_with_record_premises",
        "rows_with_semantic_inputs",
        "row_visible_inputs",
        "row_conclusion_inputs",
        "recursive_field_count",
        "recursive_field_items",
        "semantic_model_item_count",
        "semantic_model_items",
        "source_premise_consistency_item_count",
        "source_premise_consistency_items",
        "source_premise_consistency_scanned_record_roots",
        "source_premise_consistency_error",
        "source_premise_consistency_schema",
        "available_local_lean_declarations",
        "semantic_model_review_configuration_errors",
        "recursion_failure_count",
        "recursion_failures",
        "source_proof_fidelity",
        "formalization_scope",
        "fresh_source_elaboration",
        "llm_judge_prompt",
        "lean_check",
    }
)


class AuditScaffoldError(ValueError):
    """Raised when an existing paper is not safe to scaffold mechanically."""


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _paper_folder(paper: str) -> Path:
    name = str(paper or "").strip()
    if not PAPER_NAME_RE.fullmatch(name):
        raise AuditScaffoldError("--paper must be an existing paper-folder name")
    folder = (PAPERS_DIR / name).resolve()
    try:
        folder.relative_to(PAPERS_DIR.resolve())
    except ValueError as exc:
        raise AuditScaffoldError("--paper escapes the papers directory") from exc
    if not folder.is_dir():
        raise AuditScaffoldError(f"paper folder does not exist: {name}")
    return folder


def _load_json_object(path: Path, label: str) -> dict[str, Any]:
    if not path.is_file():
        raise AuditScaffoldError(f"missing {label}: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AuditScaffoldError(f"invalid JSON in {label}: {path}") from exc
    if not isinstance(payload, dict):
        raise AuditScaffoldError(f"{label} must contain a JSON object: {path}")
    return payload


def _static_review_declaration_index(
    folder: Path,
) -> tuple[set[str], dict[str, set[str]], str]:
    """Return syntactic review-source identities without elaborating Lean.

    The scaffold preflight only checks whether source-map endpoints are exposed
    to the configured human-review surface.  It deliberately does not decide
    whether those endpoints prove anything.  Parsing the canonical
    ``PaperInterface.lean`` is enough to disambiguate a short name such as
    ``claim`` from fully-qualified declarations with the same suffix.
    """

    try:
        source_path = review_dashboard.review_source_file(folder)
    except (OSError, ValueError) as exc:
        return set(), {}, str(exc)
    parsed = review_dashboard.parse_review_source_declarations(source_path)
    if not parsed:
        return set(), {}, f"no declarations could be read from {source_path.name}"
    full_names: set[str] = set()
    short_to_full: dict[str, set[str]] = {}
    for _kind, short_name, full_name, *_rest in parsed:
        full_names.add(full_name)
        short_to_full.setdefault(short_name, set()).add(full_name)
    return full_names, short_to_full, ""


def _canonical_static_review_name(
    name: str,
    *,
    full_names: set[str],
    short_to_full: dict[str, set[str]],
) -> tuple[str | None, str]:
    """Resolve a configured route without suffix guessing.

    A qualified route must identify the exact syntactic declaration.  An
    unqualified route is accepted only when its short spelling names exactly
    one declaration on the review source.  This avoids turning a name match
    into accidental coverage when two namespaces export the same suffix.
    """

    candidate = str(name or "").strip()
    if not candidate:
        return None, "is empty"
    if candidate in full_names:
        return candidate, ""
    if "." in candidate:
        return (
            None,
            "is not an exact namespace-qualified declaration on PaperInterface.lean",
        )
    matches = short_to_full.get(candidate, set())
    if not matches:
        return None, "does not name a declaration on PaperInterface.lean"
    if len(matches) != 1:
        return (
            None,
            "is ambiguous on PaperInterface.lean; use an exact namespace-qualified name",
        )
    return next(iter(matches)), ""


def _configured_route_name_lists(
    review_surface: dict[str, Any],
    field: str,
) -> tuple[list[str], list[str]]:
    """Read one route-list field, retaining malformed entries as diagnostics."""

    raw = review_surface.get(field, [])
    if raw is None:
        return [], []
    if not isinstance(raw, list):
        return [], [f"review_surface.{field} must be a string list"]
    names: list[str] = []
    errors: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            errors.append(f"review_surface.{field}[{index}] must be a nonempty string")
            continue
        names.append(value.strip())
    return names, errors


def _source_map_direct_route_requests(
    source_items: dict[str, Any],
) -> tuple[list[tuple[str, str, str]], list[str]]:
    """Collect direct review endpoints without assigning mathematical credit."""

    requests: list[tuple[str, str, str]] = []
    errors: list[str] = []
    for raw_source_key, raw_item in source_items.items():
        source_key = str(raw_source_key)
        if not isinstance(raw_item, dict):
            continue
        if raw_item.get("claim_bearing") is True and "lean_declarations" in raw_item:
            raw_declarations = raw_item.get("lean_declarations")
            # A claim can be routed exclusively through a semantic contract;
            # legacy source maps commonly spell that as JSON ``null`` here.
            # Only a present direct route belongs to this configuration check.
            if raw_declarations is None:
                pass
            elif not isinstance(raw_declarations, list):
                errors.append(
                    f"{source_key}.lean_declarations must be a string list for a claim-bearing route"
                )
            else:
                for index, raw_name in enumerate(raw_declarations, start=1):
                    if not isinstance(raw_name, str) or not raw_name.strip():
                        errors.append(
                            f"{source_key}.lean_declarations[{index}] must be a nonempty string"
                        )
                        continue
                    requests.append(
                        (source_key, "lean_declarations", raw_name.strip())
                    )

        raw_contract = raw_item.get("semantic_contract")
        if raw_contract is None:
            continue
        if not isinstance(raw_contract, dict):
            errors.append(f"{source_key}.semantic_contract must be an object")
            continue
        for field in ("spec_declaration", "evidence_declaration"):
            raw_name = raw_contract.get(field)
            if not isinstance(raw_name, str) or not raw_name.strip():
                errors.append(
                    f"{source_key}.semantic_contract.{field} must be a nonempty string"
                )
                continue
            requests.append(
                (source_key, f"semantic_contract.{field}", raw_name.strip())
            )
    return requests, errors


def _route_name_might_target(
    configured_name: str,
    *,
    route_name: str,
    canonical_route_name: str,
) -> bool:
    """Whether an unresolved configured spelling could be this route."""

    return configured_name in {
        route_name,
        canonical_route_name,
        canonical_route_name.rsplit(".", 1)[-1],
    }


def _source_map_direct_route_configuration_errors(
    folder: Path,
    source_map: dict[str, Any],
) -> list[str]:
    """Check that direct source-map endpoints are on the review configuration.

    This is intentionally a cheap, syntactic routing preflight.  It does not
    run Lean Meta, inspect proofs, or treat a configured endpoint as evidence
    that a source statement was formalized.  Its sole purpose is to prevent a
    source map from routing a claim through a hidden helper before blank audit
    sidecars are created.
    """

    source_items = source_map.get("items")
    if not isinstance(source_items, dict):
        return ["source map items must be an object"]
    requests, errors = _source_map_direct_route_requests(source_items)
    if not requests:
        return errors

    status_path = folder / "status.json"
    try:
        status = _load_json_object(status_path, "paper status")
    except AuditScaffoldError as exc:
        return [str(exc)]
    review_surface = status.get("review_surface")
    if not isinstance(review_surface, dict):
        return errors + ["status.json has no review_surface object"]

    include_names, include_list_errors = _configured_route_name_lists(
        review_surface, "include_names"
    )
    auxiliary_names, auxiliary_list_errors = _configured_route_name_lists(
        review_surface, "auxiliary_names"
    )
    quarantined_names, quarantined_list_errors = _configured_route_name_lists(
        review_surface, "quarantined_auxiliary_names"
    )
    full_names, short_to_full, index_error = _static_review_declaration_index(folder)
    if index_error:
        return errors + [index_error]

    def resolve_configured(
        names: list[str],
    ) -> tuple[dict[str, set[str]], list[tuple[str, str]]]:
        resolved: dict[str, set[str]] = {}
        unresolved: list[tuple[str, str]] = []
        for name in names:
            canonical, resolution_error = _canonical_static_review_name(
                name, full_names=full_names, short_to_full=short_to_full
            )
            if canonical is None:
                unresolved.append((name, resolution_error))
                continue
            resolved.setdefault(canonical, set()).add(name)
        return resolved, unresolved

    included, unresolved_includes = resolve_configured(include_names)
    auxiliary, unresolved_auxiliary = resolve_configured(auxiliary_names)
    quarantined, unresolved_quarantined = resolve_configured(quarantined_names)
    list_errors = {
        "include_names": include_list_errors,
        "auxiliary_names": auxiliary_list_errors,
        "quarantined_auxiliary_names": quarantined_list_errors,
    }

    for source_key, field, route_name in requests:
        canonical, resolution_error = _canonical_static_review_name(
            route_name, full_names=full_names, short_to_full=short_to_full
        )
        route_label = f"{source_key}.{field} `{route_name}`"
        if canonical is None:
            errors.append(f"{route_label} {resolution_error}")
            continue

        for list_name, problems in list_errors.items():
            if problems:
                errors.extend(
                    f"{route_label} cannot validate {problem}" for problem in problems
                )
        for list_name, unresolved in (
            ("include_names", unresolved_includes),
            ("auxiliary_names", unresolved_auxiliary),
            ("quarantined_auxiliary_names", unresolved_quarantined),
        ):
            for configured_name, configured_error in unresolved:
                if _route_name_might_target(
                    configured_name,
                    route_name=route_name,
                    canonical_route_name=canonical,
                ):
                    errors.append(
                        f"{route_label} has ambiguous or unresolved "
                        f"review_surface.{list_name} route `{configured_name}`: "
                        f"{configured_error}"
                    )

        if canonical in quarantined:
            errors.append(
                f"{route_label} is configured as a quarantined auxiliary declaration"
            )
            continue
        if canonical in auxiliary:
            if canonical in included:
                errors.append(
                    f"{route_label} is also configured as auxiliary; direct source routes "
                    "cannot use auxiliary declarations"
                )
            else:
                errors.append(
                    f"{route_label} is configured only as auxiliary, not in "
                    "review_surface.include_names"
                )
            continue
        if canonical not in included:
            errors.append(
                f"{route_label} is not configured in review_surface.include_names"
            )
    return errors


def _frozen_input_snapshot(folder: Path) -> dict[str, Any]:
    """Validate current cache/map inputs and return non-semantic fingerprints.

    The cached row names, statements, manifests, source keys, and source text
    deliberately never enter the generated review files.  Their cache/map byte
    identities only make it clear which deterministic intake snapshot must be
    audited next.
    """

    cache_path = folder / ".review_traces" / review_dashboard.DEFAULT_PAPER_INTERFACE_CACHE_FILE
    cache = _load_json_object(cache_path, "frozen review cache")
    if cache.get("schema") != review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA:
        raise AuditScaffoldError(
            "frozen review cache has an unsupported schema; refresh it before scaffolding"
        )
    if cache.get("paper") != folder.name:
        raise AuditScaffoldError("frozen review cache paper does not match --paper")
    rows = cache.get("rows")
    if not isinstance(rows, list) or not rows:
        raise AuditScaffoldError("frozen review cache has no review rows")
    if not isinstance(cache.get("signature_contexts"), dict) or not cache["signature_contexts"]:
        raise AuditScaffoldError(
            "frozen review cache has no signature context; run review_dashboard.py --refresh-cache"
        )
    recorded_hashes = cache.get("hashes")
    if not isinstance(recorded_hashes, dict):
        raise AuditScaffoldError("frozen review cache has no source-hash object")
    try:
        current_hashes = review_dashboard._cache_source_hashes(folder)
    except (OSError, ValueError) as exc:
        raise AuditScaffoldError(
            "could not validate the frozen review cache against the current review surface"
        ) from exc
    stale_hashes = sorted(
        key
        for key, expected in current_hashes.items()
        if str(recorded_hashes.get(key) or "") != str(expected or "")
    )
    if stale_hashes:
        raise AuditScaffoldError(
            "frozen review cache is stale for " + ", ".join(stale_hashes)
            + "; run review_dashboard.py --refresh-cache"
        )

    source_map_path = folder / review_dashboard.PAPER_STATEMENT_MAP_FILE
    source_map = _load_json_object(source_map_path, "canonical source map")
    if source_map.get("paper") not in {None, folder.name}:
        raise AuditScaffoldError("canonical source map paper does not match --paper")
    source_items = source_map.get("items")
    if not isinstance(source_items, dict) or not source_items:
        raise AuditScaffoldError("canonical source map has no source items")
    direct_route_errors = _source_map_direct_route_configuration_errors(
        folder, source_map
    )
    if direct_route_errors:
        raise AuditScaffoldError(
            "canonical source map has direct routes outside the configured review surface: "
            + "; ".join(direct_route_errors[:8])
            + ("; ..." if len(direct_route_errors) > 8 else "")
        )

    return {
        "schema": 1,
        "review_cache_path": ".review_traces/" + review_dashboard.DEFAULT_PAPER_INTERFACE_CACHE_FILE,
        "review_cache_sha256": _sha256_file(cache_path),
        "review_cache_schema": cache["schema"],
        "review_row_count": len(rows),
        "source_map_path": review_dashboard.PAPER_STATEMENT_MAP_FILE,
        "source_map_sha256": _sha256_file(source_map_path),
        "source_map_schema": source_map.get("schema"),
        "source_item_count": len(source_items),
    }


def _raw_dashboard_template_payloads(paper: str) -> dict[str, dict[str, Any]]:
    """Return the unmodified new-paper dashboard templates.

    Exact template equality is one of the two allow-listed forms that
    ``--force`` may safely replace.  This lets a paper created by the normal
    new-paper workflow enter the stricter intake workflow without treating its
    known empty templates as semantic evidence.
    """

    raw_templates = {
        "lean_to_tex_llm.json": new_paper.lean_to_tex_llm_text(paper),
        "statement_match_llm.json": new_paper.statement_match_llm_text(paper),
        "paper_coverage_llm.json": new_paper.paper_coverage_llm_text(paper),
        "review_surface_llm.json": new_paper.review_surface_llm_text(paper),
    }
    return {name: json.loads(raw) for name, raw in raw_templates.items()}


def _fresh_source_record_digest(payload: dict[str, Any]) -> str:
    digest = str(payload.get("source_record_audit_sha256") or "").strip()
    if not SHA256_RE.fullmatch(digest):
        raise AuditScaffoldError(
            "fresh source-record audit has no valid source_record_audit_sha256"
        )
    return digest


def _validate_fresh_source_record_payload(
    folder: Path, payload: dict[str, Any]
) -> None:
    """Reject anything short of a current isolated Lean-checked v10 payload."""

    if payload.get("paper") != folder.name:
        raise AuditScaffoldError(
            "fresh source-record audit paper does not match --paper"
        )
    if payload.get("prompt_version") != new_paper.SOURCE_RECORD_PROMPT_VERSION:
        raise AuditScaffoldError(
            "fresh source-record audit is not a current v10 payload"
        )
    if (
        payload.get("source_record_policy_version")
        != new_paper.SOURCE_RECORD_PROMPT_VERSION
    ):
        raise AuditScaffoldError(
            "fresh source-record audit does not expose the current source-record policy"
        )
    _fresh_source_record_digest(payload)
    if payload.get("source_record_judgment_file") != (
        "audit/" + SOURCE_RECORD_MATCH_SIDECAR
    ):
        raise AuditScaffoldError(
            "fresh source-record audit does not target the canonical judgment sidecar"
        )

    lean_check = payload.get("lean_check")
    if not isinstance(lean_check, dict) or lean_check.get("returncode") != 0:
        raise AuditScaffoldError(
            "fresh source-record audit lacks a successful Lean check"
        )
    fresh = payload.get("fresh_source_elaboration")
    if not isinstance(fresh, dict):
        fresh = lean_check.get("fresh_source_elaboration")
    if (
        not isinstance(fresh, dict)
        or fresh.get("mode") != "isolated_temp_overlay"
        or fresh.get("returncode") != 0
    ):
        raise AuditScaffoldError(
            "fresh source-record audit lacks a successful isolated current-source elaboration"
        )
    source_file = str(fresh.get("source_file") or "").strip()
    source_sha256 = str(fresh.get("source_sha256") or "").strip()
    if not source_file or not SHA256_RE.fullmatch(source_sha256):
        raise AuditScaffoldError(
            "fresh source-record audit omits the elaborated source identity"
        )
    source_path = Path(source_file)
    if not source_path.is_absolute():
        source_path = ROOT / source_path
    try:
        source_path = source_path.resolve()
        source_path.relative_to(folder.resolve())
    except ValueError as exc:
        raise AuditScaffoldError(
            "fresh source-record audit elaborated a source outside the requested paper"
        ) from exc
    if not source_path.is_file() or _sha256_file(source_path) != source_sha256:
        raise AuditScaffoldError(
            "fresh source-record audit source identity is stale or unreadable"
        )


def _is_zero_judgment_machine_source_record_audit(
    folder: Path, payload: dict[str, Any]
) -> bool:
    """Recognize a v10 machine artifact without treating its age as evidence.

    A stale source hash makes an artifact unusable for closeout, but it does
    not make its zero-judgment machine output human semantic evidence. This
    narrow recognizer permits ``--force`` to replace that stale intake while
    retaining the strict protection for any populated judgment sidecar.
    """

    if not set(payload).issubset(SOURCE_RECORD_AUDIT_TOP_LEVEL_KEYS):
        return False
    if payload.get("paper") != folder.name:
        return False
    if payload.get("prompt_version") != new_paper.SOURCE_RECORD_PROMPT_VERSION:
        return False
    if (
        payload.get("source_record_policy_version")
        != new_paper.SOURCE_RECORD_PROMPT_VERSION
    ):
        return False
    if payload.get("source_record_judgment_file") != (
        "audit/" + SOURCE_RECORD_MATCH_SIDECAR
    ):
        return False
    if not (
        isinstance(payload.get("current_source_record_judgment_count"), int)
        and not isinstance(payload.get("current_source_record_judgment_count"), bool)
        and payload.get("current_source_record_judgment_count") == 0
    ):
        return False
    try:
        _fresh_source_record_digest(payload)
    except AuditScaffoldError:
        return False
    lean_check = payload.get("lean_check")
    if not isinstance(lean_check, dict) or lean_check.get("returncode") != 0:
        return False
    fresh = payload.get("fresh_source_elaboration")
    if not isinstance(fresh, dict):
        fresh = lean_check.get("fresh_source_elaboration")
    if (
        not isinstance(fresh, dict)
        or fresh.get("mode") != "isolated_temp_overlay"
        or fresh.get("returncode") != 0
    ):
        return False
    source_file = str(fresh.get("source_file") or "").strip()
    source_sha256 = str(fresh.get("source_sha256") or "").strip()
    if not source_file or not SHA256_RE.fullmatch(source_sha256):
        return False
    source_path = Path(source_file)
    if not source_path.is_absolute():
        source_path = ROOT / source_path
    try:
        source_path = source_path.resolve()
        source_path.relative_to(folder.resolve())
    except ValueError:
        return False
    return source_path.is_file()


def _generate_fresh_source_record_audit(folder: Path) -> dict[str, Any]:
    """Run the v10 helper in a temporary file and return its checked payload.

    This is intentionally a subprocess boundary: the helper is the authority
    for the recursive Lean-backed source-record surface, while this command is
    responsible only for safely staging its result with blank human-review
    sidecars.
    """

    helper = ROOT / SOURCE_RECORD_HELPER_RELATIVE_PATH
    if not helper.is_file():
        raise AuditScaffoldError(f"missing source-record audit helper: {helper}")
    with tempfile.TemporaryDirectory(prefix="audit-sidecar-source-record-") as tmpdir:
        output = Path(tmpdir) / SOURCE_RECORD_AUDIT_SIDECAR
        environment = os.environ.copy()
        # The helper performs an isolated current-source Lean elaboration.  Use
        # the repository's conservative default unless the caller deliberately
        # configured a different value.
        environment.setdefault("LEAN_NUM_THREADS", "1")
        completed = subprocess.run(
            [
                sys.executable,
                str(helper),
                "--root",
                str(ROOT),
                "--paper",
                folder.name,
                "--out",
                str(output),
                "--ignore-current-judgments",
            ],
            cwd=ROOT,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if completed.returncode != 0:
            detail = completed.stdout.strip()
            if len(detail) > 4000:
                detail = detail[-4000:]
            suffix = f"\n{detail}" if detail else ""
            raise AuditScaffoldError(
                "fresh Lean-checked source-record audit failed "
                f"(exit {completed.returncode}){suffix}"
            )
        payload = _load_json_object(output, "fresh source-record audit")
    _validate_fresh_source_record_payload(folder, payload)
    return payload


def _source_record_match_payload(
    paper: str, source_record_audit: dict[str, Any]
) -> dict[str, Any]:
    """Return a blank v10 judgment scaffold tied to one exact audit digest."""

    digest = _fresh_source_record_digest(source_record_audit)
    payload = json.loads(new_paper.source_record_match_llm_text(paper))
    payload["source_record_audit_sha256"] = digest
    payload["non_evidence_scaffold"] = {
        "schema": review_dashboard.NON_EVIDENCE_SCAFFOLD_SCHEMA,
        "kind": SOURCE_RECORD_MATCH_SCAFFOLD_KIND,
        "status": review_dashboard.NON_EVIDENCE_SCAFFOLD_STATUS,
        "source_record_audit_sha256": digest,
        "reason": (
            "Mechanical intake only: this blank judgment sidecar is pinned to a fresh "
            "Lean-checked source-record surface and supplies no semantic evidence."
        ),
    }
    payload["comment"] = (
        "NON-EVIDENCE SCAFFOLD. Status: needs_review. This file supplies no source-record "
        "judgments; remove non_evidence_scaffold only after independent semantic review."
    )
    return payload


def _template_payloads(
    paper: str,
    snapshot: dict[str, Any],
    source_record_audit: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    """Return canonical blank templates carrying only non-evidence metadata."""

    raw_templates = _raw_dashboard_template_payloads(paper)
    marker = {
        "schema": review_dashboard.NON_EVIDENCE_SCAFFOLD_SCHEMA,
        "kind": NON_EVIDENCE_SCAFFOLD_KIND,
        "status": review_dashboard.NON_EVIDENCE_SCAFFOLD_STATUS,
        "reason": (
            "Mechanical intake only: the frozen cache/map snapshot has not received "
            "a context-free translation, semantic statement judgment, source coverage "
            "judgment, or review-surface judgment."
        ),
        "input_snapshot": snapshot,
    }
    out: dict[str, dict[str, Any]] = {}
    for filename, raw in raw_templates.items():
        payload = raw
        payload["items"] = {}
        payload["non_evidence_scaffold"] = marker
        payload["comment"] = (
            "NON-EVIDENCE SCAFFOLD. Status: needs_review. This file supplies no audit "
            "evidence; remove non_evidence_scaffold only after independent review."
        )
        out[filename] = payload

    coverage = out["paper_coverage_llm.json"]
    # These values make the existing coverage validator fail closed even if a
    # later edit populates rows before clearing the scaffold marker.
    coverage["audit_kind"] = "dashboard_seeded_preliminary"
    coverage["source_grounded"] = False
    coverage["seed_scaffold"] = True
    coverage["paper_statement_inventory_sha256"] = ""
    coverage["review_surface_sha256"] = ""

    surface = out["review_surface_llm.json"]
    surface["judgment"] = ""
    surface["reason"] = ""
    surface["review_rows"] = 0
    surface["review_surface_sha256"] = ""
    out[SOURCE_RECORD_AUDIT_SIDECAR] = source_record_audit
    out[SOURCE_RECORD_MATCH_SIDECAR] = _source_record_match_payload(
        paper, source_record_audit
    )
    return out


def _dashboard_scaffold_payload_without_marker(
    paper: str, filename: str
) -> dict[str, Any]:
    """Return the deterministic dashboard scaffold apart from its input snapshot."""

    payload = _raw_dashboard_template_payloads(paper)[filename]
    payload["items"] = {}
    payload["comment"] = (
        "NON-EVIDENCE SCAFFOLD. Status: needs_review. This file supplies no audit "
        "evidence; remove non_evidence_scaffold only after independent review."
    )
    if filename == "paper_coverage_llm.json":
        payload["audit_kind"] = "dashboard_seeded_preliminary"
        payload["source_grounded"] = False
        payload["seed_scaffold"] = True
        payload["paper_statement_inventory_sha256"] = ""
        payload["review_surface_sha256"] = ""
    return payload


def _is_known_dashboard_blank(
    paper: str, filename: str, payload: dict[str, Any]
) -> bool:
    """Recognize only an exact new-paper template or our blank scaffold."""

    raw = _raw_dashboard_template_payloads(paper)[filename]
    if payload == raw:
        return True
    marker = payload.get("non_evidence_scaffold")
    if not isinstance(marker, dict):
        return False
    required_marker_keys = {
        "schema",
        "kind",
        "status",
        "reason",
        "input_snapshot",
    }
    snapshot_keys = {
        "schema",
        "review_cache_path",
        "review_cache_sha256",
        "review_cache_schema",
        "review_row_count",
        "source_map_path",
        "source_map_sha256",
        "source_map_schema",
        "source_item_count",
    }
    snapshot = marker.get("input_snapshot")
    if (
        set(marker) != required_marker_keys
        or marker.get("schema") != review_dashboard.NON_EVIDENCE_SCAFFOLD_SCHEMA
        or marker.get("kind") != NON_EVIDENCE_SCAFFOLD_KIND
        or marker.get("status") != review_dashboard.NON_EVIDENCE_SCAFFOLD_STATUS
        or not isinstance(marker.get("reason"), str)
        or not isinstance(snapshot, dict)
        or set(snapshot) != snapshot_keys
    ):
        return False
    candidate = dict(payload)
    candidate.pop("non_evidence_scaffold", None)
    return candidate == _dashboard_scaffold_payload_without_marker(paper, filename)


def _is_known_blank_source_record_match(
    paper: str, payload: dict[str, Any]
) -> bool:
    """Recognize a raw template or a digest-pinned blank judgment scaffold."""

    raw = json.loads(new_paper.source_record_match_llm_text(paper))
    if payload == raw:
        return True
    marker = payload.get("non_evidence_scaffold")
    digest = str(payload.get("source_record_audit_sha256") or "").strip()
    if (
        not isinstance(marker, dict)
        or set(marker)
        != {
            "schema",
            "kind",
            "status",
            "source_record_audit_sha256",
            "reason",
        }
        or marker.get("schema") != review_dashboard.NON_EVIDENCE_SCAFFOLD_SCHEMA
        or marker.get("kind") != SOURCE_RECORD_MATCH_SCAFFOLD_KIND
        or marker.get("status") != review_dashboard.NON_EVIDENCE_SCAFFOLD_STATUS
        or marker.get("source_record_audit_sha256") != digest
        or not SHA256_RE.fullmatch(digest)
        or not isinstance(marker.get("reason"), str)
    ):
        return False
    expected = _source_record_match_payload(
        paper, {"source_record_audit_sha256": digest}
    )
    return payload == expected


def _is_known_mechanical_source_record_audit(
    folder: Path, payload: dict[str, Any]
) -> bool:
    """Allow only a current source helper output with no carried judgments."""

    if not _is_zero_judgment_machine_source_record_audit(folder, payload):
        return False
    try:
        _validate_fresh_source_record_payload(folder, payload)
    except AuditScaffoldError:
        return False
    return True


def _is_known_stale_mechanical_source_record_audit(
    folder: Path, payload: dict[str, Any]
) -> bool:
    """Allow safe replacement of stale zero-judgment machine intake only."""

    if not _is_zero_judgment_machine_source_record_audit(folder, payload):
        return False
    try:
        _validate_fresh_source_record_payload(folder, payload)
    except AuditScaffoldError:
        return True
    return False


def _replaceability_of_existing_target(
    folder: Path, filename: str, target: Path
) -> str:
    """Classify an existing target without ever inferring evidence from names."""

    if not target.is_file():
        return "invalid-or-unknown"
    try:
        payload = json.loads(target.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid-or-unknown"
    if not isinstance(payload, dict):
        return "invalid-or-unknown"
    if filename in DASHBOARD_SIDECARS:
        return (
            "known-blank"
            if _is_known_dashboard_blank(folder.name, filename, payload)
            else "invalid-or-populated"
        )
    if filename == SOURCE_RECORD_MATCH_SIDECAR:
        return (
            "known-blank"
            if _is_known_blank_source_record_match(folder.name, payload)
            else "invalid-or-populated"
        )
    if filename == SOURCE_RECORD_AUDIT_SIDECAR:
        if _is_known_mechanical_source_record_audit(folder, payload):
            return "known-mechanical"
        if _is_known_stale_mechanical_source_record_audit(folder, payload):
            return "known-stale-mechanical"
        return "invalid-or-populated"
    return "invalid-or-unknown"


def _preflight_targets(
    folder: Path,
    *,
    filenames: tuple[str, ...],
    force: bool,
    destroy_semantic_evidence: bool,
) -> dict[str, Path]:
    """Validate only the canonical sidecars this operation will replace."""

    if destroy_semantic_evidence and not force:
        raise AuditScaffoldError(
            "--destroy-semantic-evidence requires --force"
        )
    audit_dir = folder / "audit"
    targets = {name: audit_dir / name for name in filenames}
    legacy_conflicts = [
        folder / name
        for name, target in targets.items()
        if (folder / name).exists() and not target.exists()
    ]
    if legacy_conflicts:
        labels = ", ".join(str(path.relative_to(folder)) for path in legacy_conflicts)
        raise AuditScaffoldError(
            "refusing to shadow legacy root-level sidecar(s): " + labels
        )
    duplicate_conflicts = [
        folder / name
        for name, target in targets.items()
        if (folder / name).exists() and target.exists()
    ]
    if duplicate_conflicts:
        labels = ", ".join(str(path.relative_to(folder)) for path in duplicate_conflicts)
        raise AuditScaffoldError(
            "refusing to operate with duplicate legacy/canonical sidecar(s): " + labels
        )
    existing = [target for target in targets.values() if target.exists()]
    if existing and not force:
        labels = ", ".join(str(path.relative_to(folder)) for path in existing)
        raise AuditScaffoldError(
            "canonical sidecars already exist; pass --force only for known blank/mechanical "
            "scaffolds, or --force --destroy-semantic-evidence for intentional evidence "
            "destruction: "
            + labels
        )
    if force:
        protected = [
            target
            for name, target in targets.items()
            if target.exists()
            and _replaceability_of_existing_target(folder, name, target)
            not in {"known-blank", "known-mechanical", "known-stale-mechanical"}
        ]
        if protected and not destroy_semantic_evidence:
            labels = ", ".join(
                str(path.relative_to(folder)) for path in protected
            )
            raise AuditScaffoldError(
                "refusing to overwrite invalid, unknown, or populated semantic sidecar(s) "
                "with --force: "
                + labels
                + "; use --force --destroy-semantic-evidence only after preserving any "
                "needed review evidence"
            )
    return targets


def _write_sidecar_payloads(
    folder: Path,
    targets: dict[str, Path],
    payloads: dict[str, dict[str, Any]],
) -> None:
    """Atomically replace exactly ``targets`` after all payloads are ready."""

    serialized = {
        name: json.dumps(payloads[name], ensure_ascii=False, indent=2, sort_keys=True)
        + "\n"
        for name in targets
    }
    audit_dir = folder / "audit"
    audit_dir.mkdir(parents=True, exist_ok=True)
    temporaries: dict[str, Path] = {}
    try:
        for name, target in targets.items():
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=f".{target.name}.", suffix=".tmp", dir=audit_dir
            )
            os.close(descriptor)
            temporary = Path(temporary_name)
            temporaries[name] = temporary
            temporary.write_text(serialized[name], encoding="utf-8")
        for name, target in targets.items():
            os.replace(temporaries[name], target)
    finally:
        for temporary in temporaries.values():
            if temporary.exists():
                temporary.unlink()


def _fresh_source_record_payloads(
    paper: str, source_record_audit: dict[str, Any]
) -> dict[str, dict[str, Any]]:
    return {
        SOURCE_RECORD_AUDIT_SIDECAR: source_record_audit,
        SOURCE_RECORD_MATCH_SIDECAR: _source_record_match_payload(
            paper, source_record_audit
        ),
    }


def scaffold_current_audit_sidecars(
    paper: str,
    *,
    force: bool = False,
    destroy_semantic_evidence: bool = False,
    dry_run: bool = False,
) -> list[Path]:
    """Write guarded blank sidecars plus a fresh Lean-backed source-record audit."""

    folder = _paper_folder(paper)
    snapshot = _frozen_input_snapshot(folder)
    targets = _preflight_targets(
        folder,
        filenames=CANONICAL_SIDECARS,
        force=force,
        destroy_semantic_evidence=destroy_semantic_evidence,
    )
    source_record_audit = _generate_fresh_source_record_audit(folder)
    # The production generator performs this validation itself.  Repeat it at
    # the boundary so a test double or future implementation cannot bypass the
    # contract before this command writes a canonical artifact.
    _validate_fresh_source_record_payload(folder, source_record_audit)
    payloads = _template_payloads(folder.name, snapshot, source_record_audit)
    if dry_run:
        return [targets[name] for name in CANONICAL_SIDECARS]
    _write_sidecar_payloads(folder, targets, payloads)
    return [targets[name] for name in CANONICAL_SIDECARS]


def scaffold_source_record_sidecars(
    paper: str,
    *,
    force: bool = False,
    destroy_semantic_evidence: bool = False,
    dry_run: bool = False,
) -> list[Path]:
    """Refresh only the v10 source-record intake artifacts.

    This intentionally leaves all dashboard sidecars untouched.  It is the
    correct follow-up after a current statement ledger has been completed:
    the fresh source-record helper can then recognize its direct reviewed rows
    without erasing the review evidence that supplies that credit.
    """

    folder = _paper_folder(paper)
    # Keep the same frozen-input preflight as the full scaffold, even though
    # this mode writes no dashboard sidecar.  A stale cache or source map must
    # not be paired with a newly generated source-record surface.
    _frozen_input_snapshot(folder)
    targets = _preflight_targets(
        folder,
        filenames=SOURCE_RECORD_SIDECARS,
        force=force,
        destroy_semantic_evidence=destroy_semantic_evidence,
    )
    source_record_audit = _generate_fresh_source_record_audit(folder)
    _validate_fresh_source_record_payload(folder, source_record_audit)
    payloads = _fresh_source_record_payloads(folder.name, source_record_audit)
    if dry_run:
        return [targets[name] for name in SOURCE_RECORD_SIDECARS]
    _write_sidecar_payloads(folder, targets, payloads)
    return [targets[name] for name in SOURCE_RECORD_SIDECARS]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="existing paper folder name")
    parser.add_argument(
        "--force",
        action="store_true",
        help="replace only recognized blank/mechanical canonical sidecars after preflight",
    )
    parser.add_argument(
        "--destroy-semantic-evidence",
        action="store_true",
        help=(
            "with --force, intentionally replace invalid, unknown, or populated semantic "
            "sidecars after preflight"
        ),
    )
    parser.add_argument(
        "--source-record-only",
        action="store_true",
        help=(
            "refresh only source_record_audit.json and its blank pinned judgment "
            "sidecar; preserve every dashboard review artifact"
        ),
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="validate the frozen inputs and print target paths without writing",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        scaffold = (
            scaffold_source_record_sidecars
            if args.source_record_only
            else scaffold_current_audit_sidecars
        )
        targets = scaffold(
            args.paper,
            force=args.force,
            destroy_semantic_evidence=args.destroy_semantic_evidence,
            dry_run=args.dry_run,
        )
    except AuditScaffoldError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    action = "would write" if args.dry_run else "wrote"
    for target in targets:
        try:
            label = target.relative_to(ROOT)
        except ValueError:
            label = target
        print(f"{action} {label}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
