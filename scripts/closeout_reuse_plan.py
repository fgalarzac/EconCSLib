#!/usr/bin/env python3
"""Plan paper-closeout reuse without granting acceptance.

The planner is an advisory scheduling tool. It validates the current persisted
dashboard cache against exact source/build-control, source-evidence, selection,
and sidecar inputs. Its ignored compiled-input cache retains exact byte hashes;
stable filesystem guards avoid reads, and a changed guard rehashes only the
affected repository artifact (or exact external aggregate). It then applies the
same fail-closed item-level semantic pins used by ``semantic_audit_reuse.py``.

A positive result can avoid redundant *intermediate* builds or human reviews.
It is never a closeout receipt: final acceptance still requires the targeted
strict repository closeout and its fresh batched Lean attestation.
"""

from __future__ import annotations

import argparse
import fcntl
from functools import lru_cache
import hashlib
import inspect
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from uuid import uuid4
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

try:
    from scripts import lean_signature_manifest as lean_manifest
    from scripts import review_dashboard
    from scripts.lean_import_closure import (
        lake_routing_projection,
        lean_loaded_module_closure,
        validated_lean_import_closure_payload,
    )
    from scripts.semantic_audit_reuse import (
        _current_anchor_errors,
        _statement_validator,
        canonical_coverage_inventory_projection,
        inventory_from_source_map,
        migrate_sidecars,
        review_validator_identities,
        row_snapshots_from_dashboard,
    )
    from scripts.closeout_execution_state import (
        atomic_write_json,
        closeout_worker_state_path as canonical_closeout_worker_state_path,
        default_closeout_execution_path,
        effective_closeout_execution_state,
        resolve_paper_folder,
        running_execution_summary,
        utc_now,
    )
    from scripts.closeout_wave_engine import (
        CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH as WAVE_RAW_REISSUE_LOCK_RELATIVE_PATH,
        CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA as WAVE_RAW_REISSUE_LOCK_STATUS_SCHEMA,
        RAW_REISSUE_OPERATION_TRACE_FILENAME as WAVE_RAW_REISSUE_OPERATION_TRACE_FILENAME,
        RAW_REISSUE_OPERATION_TRACE_SCHEMA as WAVE_RAW_REISSUE_OPERATION_TRACE_SCHEMA,
        RAW_REISSUE_TRACE_DIRECTORY as WAVE_RAW_REISSUE_TRACE_DIRECTORY,
        closeout_raw_reissue_operation_receipt_state,
        closeout_raw_reissue_wrapper_lease_observation,
        closeout_raw_reissue_operation_receipt_path,
        closeout_wave_engine_snapshot_state,
        ensure_closeout_wave_engine_snapshot,
        reset_closeout_wave_engine_snapshot,
    )
    from scripts.closeout_legacy_adoption import (
        adopt_or_validate_legacy_completion,
        known_success_legacy_completion,
        legacy_adoption_path,
    )
    from scripts.closeout_plan_receipt import (
        CloseoutPlanReceiptError,
        OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        build_lean_closure_operational_projection,
        build_closeout_plan_receipt,
        closeout_plan_receipt_path,
        compiled_input_snapshot,
        content_input_snapshot,
        strict_closeout_protocol_projection,
        target_audit_config_projection,
        validate_lean_closure_operational_projection,
        validated_closeout_plan_receipt,
        validate_content_input_snapshot,
    )
    from scripts.python_import_closure import repository_python_import_closure
    from scripts.check_formalization_engine_revision import (
        is_engine_source_path,
        runtime_engine_registration_error,
    )
    from scripts.source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        source_coverage_mode_from_map,
    )
    from scripts.final_validation_report_status import report_status_alignment_errors
    from scripts.closeout_document_gates import (
        AGENT_SOURCE_AUDIT_RELATIVE_PATH,
        closeout_document_hard_errors,
    )
    from scripts.theorem_realization_transition import MATERIAL_ARTIFACT_PATHS
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    import lean_signature_manifest as lean_manifest
    import review_dashboard
    from lean_import_closure import (
        lake_routing_projection,
        lean_loaded_module_closure,
        validated_lean_import_closure_payload,
    )
    from semantic_audit_reuse import (
        _current_anchor_errors,
        _statement_validator,
        canonical_coverage_inventory_projection,
        inventory_from_source_map,
        migrate_sidecars,
        review_validator_identities,
        row_snapshots_from_dashboard,
    )
    from closeout_execution_state import (
        atomic_write_json,
        closeout_worker_state_path as canonical_closeout_worker_state_path,
        default_closeout_execution_path,
        effective_closeout_execution_state,
        resolve_paper_folder,
        running_execution_summary,
        utc_now,
    )
    from closeout_wave_engine import (
        CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH as WAVE_RAW_REISSUE_LOCK_RELATIVE_PATH,
        CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA as WAVE_RAW_REISSUE_LOCK_STATUS_SCHEMA,
        RAW_REISSUE_OPERATION_TRACE_FILENAME as WAVE_RAW_REISSUE_OPERATION_TRACE_FILENAME,
        RAW_REISSUE_OPERATION_TRACE_SCHEMA as WAVE_RAW_REISSUE_OPERATION_TRACE_SCHEMA,
        RAW_REISSUE_TRACE_DIRECTORY as WAVE_RAW_REISSUE_TRACE_DIRECTORY,
        closeout_raw_reissue_operation_receipt_state,
        closeout_raw_reissue_wrapper_lease_observation,
        closeout_raw_reissue_operation_receipt_path,
        closeout_wave_engine_snapshot_state,
        ensure_closeout_wave_engine_snapshot,
        reset_closeout_wave_engine_snapshot,
    )
    from closeout_legacy_adoption import (
        adopt_or_validate_legacy_completion,
        known_success_legacy_completion,
        legacy_adoption_path,
    )
    from closeout_plan_receipt import (
        CloseoutPlanReceiptError,
        OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        build_lean_closure_operational_projection,
        build_closeout_plan_receipt,
        closeout_plan_receipt_path,
        compiled_input_snapshot,
        content_input_snapshot,
        strict_closeout_protocol_projection,
        target_audit_config_projection,
        validate_lean_closure_operational_projection,
        validated_closeout_plan_receipt,
        validate_content_input_snapshot,
    )
    from python_import_closure import repository_python_import_closure
    from check_formalization_engine_revision import (
        is_engine_source_path,
        runtime_engine_registration_error,
    )
    from source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        source_coverage_mode_from_map,
    )
    from final_validation_report_status import report_status_alignment_errors
    from closeout_document_gates import (
        AGENT_SOURCE_AUDIT_RELATIVE_PATH,
        closeout_document_hard_errors,
    )
    from theorem_realization_transition import MATERIAL_ARTIFACT_PATHS


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
INTAKE_SOURCE_IDENTITY = "source-location+normalized-statement-sha256-v1"
ADVISORY_PLAN_CACHE_SCHEMA = 3
ADVISORY_PLAN_DECISION_CONTRACT = "item-semantic-reuse-v3"
ADVISORY_PLAN_CACHE_FILE = "closeout_reuse_advisory.json"
COMPILED_INPUT_CACHE_SCHEMA = 1
COMPILED_INPUT_CACHE_FILE = "closeout_compiled_inputs.json"
DECLARED_EXTERNAL_TOOL_GUARD_SCHEMA = 1
FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS = 45
FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE = Path(
    "skills/econcs-formalizer/scripts/source_record_audit.py"
)
SOURCE_RECORD_LOCK_STATUS_TIMEOUT_SECONDS = 10
SOURCE_RECORD_LOCK_STATUS_SCHEMA = 1
CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH = WAVE_RAW_REISSUE_LOCK_RELATIVE_PATH
CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA = WAVE_RAW_REISSUE_LOCK_STATUS_SCHEMA
RAW_REISSUE_TRACE_SCHEMA = 1
RAW_REISSUE_TRACE_DIRECTORY = WAVE_RAW_REISSUE_TRACE_DIRECTORY
RAW_REISSUE_OPERATION_TRACE_SCHEMA = WAVE_RAW_REISSUE_OPERATION_TRACE_SCHEMA
RAW_REISSUE_OPERATION_TRACE_FILENAME = WAVE_RAW_REISSUE_OPERATION_TRACE_FILENAME
PLAN_RECEIPT_PUBLICATION_DISPOSITIONS = frozenset(
    {"published", "source_race", "compiled_race", "deterministic_input", "publication_io"}
)
# Keep this exact set aligned with audit_evidence_integrity.FULL_CLOSEOUT_STATUSES.
# A planner must not schedule a strict acceptance route for an unrecognized
# status that merely happens to begin with a favorable word.
CLOSEOUT_PLANNER_ELIGIBLE_STATUSES = frozenset(
    {"formalized", "formalized with caveat"}
)
INTAKE_FREEZE_LEGACY_BASELINE_COMMIT = "2b500d8689a74616210a675192d14d83ac192c9f"
LEAN_BUILD_CONTROL_PATHS = (
    "lean-toolchain",
    "lake-manifest.json",
)
ADVISORY_DECISION_ENTRYPOINTS = (
    "scripts/closeout_reuse_plan.py",
    "scripts/formalization_protocol.py",
    "scripts/lean_signature_manifest.py",
    "scripts/review_dashboard.py",
    "scripts/semantic_audit_reuse.py",
    "scripts/source_coverage_scope.py",
)


def closeout_worker_state_path(paper: str) -> Path:
    return canonical_closeout_worker_state_path(ROOT, paper)


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    ).hexdigest()


def _valid_fingerprint(value: object) -> tuple[str, int] | None:
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        return None
    digest = str(value[0] or "").strip().lower()
    size = value[1]
    if not SHA256_RE.fullmatch(digest) or not isinstance(size, int) or size < 0:
        return None
    return digest, size


def _direct_expression_review_required(folder: Path) -> bool:
    policy = getattr(
        review_dashboard,
        "llm_direct_expression_semantics_review_required",
        None,
    )
    return bool(policy(folder)) if callable(policy) else False


def _validate_statement_for_plan(
    entry: dict[str, Any],
    row: Any,
    inventory: Mapping[str, Mapping[str, Any]],
    *,
    include_direct_expressions: bool,
    supports_direct_expression_parameter: bool | None = None,
) -> str:
    supports_direct_expression_parameter = (
        "include_direct_expressions"
        in inspect.signature(_statement_validator).parameters
        if supports_direct_expression_parameter is None
        else supports_direct_expression_parameter
    )
    if supports_direct_expression_parameter:
        return _statement_validator(
            entry,
            row,
            inventory,
            include_direct_expressions=include_direct_expressions,
        )
    return _statement_validator(entry, row, inventory)


def _signature_context_snapshot(
    root: Path, contexts: Mapping[str, Any]
) -> tuple[str, list[str]]:
    """Validate and hash exact current artifacts for all cached Lean contexts."""

    errors: list[str] = []
    snapshots: list[dict[str, Any]] = []
    current_hash_tool_identity: dict[str, str] | None = None
    hash_tool_identity_loaded = False
    helper_fingerprint: tuple[str, int] | None = None
    helper_fingerprint_loaded = False
    module_fingerprints: dict[str, tuple[str, int] | None] = {}
    if not contexts:
        return "", ["dashboard cache has no signature contexts"]
    for source_key, raw_context in sorted(contexts.items()):
        label = str(source_key).strip() or "<unnamed-source>"
        if not isinstance(raw_context, Mapping) or raw_context.get("schema") not in {
            2,
            3,
        }:
            errors.append(f"{label}: signature context schema is missing or stale")
            continue
        context_schema = int(raw_context["schema"])
        hash_tool_identity: dict[str, str] | None = None
        canonical_representation = ""
        if context_schema == 3:
            canonical_representation = str(
                raw_context.get("canonical_representation") or ""
            ).strip()
            if canonical_representation != "lean_compact_canonical_v2":
                errors.append(
                    f"{label}: signature context canonical representation is missing or stale"
                )
                continue
            if not hash_tool_identity_loaded:
                current_hash_tool_identity = (
                    lean_manifest._semantic_contract_closure_hash_tool_identity()  # noqa: SLF001
                )
                hash_tool_identity_loaded = True
            raw_hash_tool_identity = raw_context.get("semantic_hash_tool_identity")
            if (
                current_hash_tool_identity is None
                or not isinstance(raw_hash_tool_identity, Mapping)
                or dict(raw_hash_tool_identity) != current_hash_tool_identity
            ):
                errors.append(
                    f"{label}: signature context SHA-256 tool identity changed"
                )
                continue
            hash_tool_identity = dict(current_hash_tool_identity)
        import_module = str(raw_context.get("import_module") or "").strip()
        audit_modules_raw = raw_context.get("audit_modules")
        if (
            not import_module
            or not isinstance(audit_modules_raw, list)
            or not audit_modules_raw
            or not all(
                isinstance(module, str) and module for module in audit_modules_raw
            )
        ):
            errors.append(f"{label}: signature context module scope is malformed")
            continue
        audit_modules = tuple(sorted(audit_modules_raw))
        if (
            len(set(audit_modules)) != len(audit_modules)
            or import_module not in audit_modules
        ):
            errors.append(
                f"{label}: signature context module scope is incomplete or ambiguous"
            )
            continue

        expected_helper = _valid_fingerprint(raw_context.get("helper_fingerprint"))
        if not helper_fingerprint_loaded:
            helper_fingerprint = lean_manifest._file_content_fingerprint(  # noqa: SLF001
                lean_manifest.HELPER_PATH
            )
            helper_fingerprint_loaded = True
        actual_helper = helper_fingerprint
        if expected_helper is None or actual_helper != expected_helper:
            errors.append(f"{label}: Lean manifest helper identity changed")
            continue

        expected_main = _valid_fingerprint(raw_context.get("olean_fingerprint"))
        expected_modules_raw = raw_context.get("semantic_module_fingerprints")
        if expected_main is None or not isinstance(expected_modules_raw, list):
            errors.append(f"{label}: compiled artifact identities are malformed")
            continue
        expected_modules: dict[str, tuple[str, int]] = {}
        malformed = False
        for raw_entry in expected_modules_raw:
            if not isinstance(raw_entry, list) or len(raw_entry) != 2:
                malformed = True
                break
            module = str(raw_entry[0] or "").strip()
            fingerprint = _valid_fingerprint(raw_entry[1])
            if not module or fingerprint is None or module in expected_modules:
                malformed = True
                break
            expected_modules[module] = fingerprint
        if malformed or set(expected_modules) != set(audit_modules):
            errors.append(
                f"{label}: compiled import-closure identity is incomplete or ambiguous"
            )
            continue
        if expected_modules.get(import_module) != expected_main:
            errors.append(
                f"{label}: target artifact identity conflicts with its import closure"
            )
            continue

        actual_modules: dict[str, tuple[str, int]] = {}
        for module in audit_modules:
            if module not in module_fingerprints:
                module_fingerprints[module] = lean_manifest._built_olean_fingerprint(
                    root, module
                )  # noqa: SLF001
            actual = module_fingerprints[module]
            if actual != expected_modules[module]:
                errors.append(f"{label}: compiled artifact changed for {module}")
                malformed = True
                break
            actual_modules[module] = actual
        if malformed:
            continue
        expected_scope = lean_manifest._audit_scope_fingerprint(  # noqa: SLF001
            import_module,
            expected_main,
            audit_modules,
        )
        if str(raw_context.get("audit_scope_fingerprint") or "") != expected_scope:
            errors.append(f"{label}: Lean audit-scope identity is stale")
            continue
        snapshots.append(
            {
                "schema": context_schema,
                "source": label,
                "import_module": import_module,
                "helper": list(actual_helper),
                "modules": [
                    [module, list(actual_modules[module])] for module in audit_modules
                ],
                "audit_scope_fingerprint": expected_scope,
                **(
                    {
                        "canonical_representation": canonical_representation,
                        "semantic_hash_tool_identity": hash_tool_identity,
                    }
                    if context_schema == 3
                    else {}
                ),
            }
        )
    return (_digest(snapshots), []) if not errors else ("", errors)


def _signature_context_metadata_snapshot(
    root: Path, contexts: Mapping[str, Any]
) -> tuple[str, list[str]]:
    """Cheaply validate cached context structure, artifact presence, and size.

    This is scheduling evidence only. The strict closeout still validates exact
    artifact bytes before granting any acceptance result.
    """

    errors: list[str] = []
    snapshots: list[dict[str, Any]] = []
    if not contexts:
        return "", ["dashboard cache has no signature contexts"]
    helper_stat: os.stat_result | None
    try:
        helper_stat = lean_manifest.HELPER_PATH.stat()
    except OSError:
        helper_stat = None
    module_sizes: dict[str, int | None] = {}
    for source_key, raw_context in sorted(contexts.items()):
        label = str(source_key).strip() or "<unnamed-source>"
        if not isinstance(raw_context, Mapping) or raw_context.get("schema") not in {
            2,
            3,
        }:
            errors.append(f"{label}: signature context schema is missing or stale")
            continue
        context_schema = int(raw_context["schema"])
        if (
            context_schema == 3
            and str(raw_context.get("canonical_representation") or "").strip()
            != "lean_compact_canonical_v2"
        ):
            errors.append(
                f"{label}: signature context canonical representation is stale"
            )
            continue
        import_module = str(raw_context.get("import_module") or "").strip()
        raw_modules = raw_context.get("audit_modules")
        if (
            not import_module
            or not isinstance(raw_modules, list)
            or not raw_modules
            or not all(isinstance(module, str) and module for module in raw_modules)
        ):
            errors.append(f"{label}: signature context module scope is malformed")
            continue
        audit_modules = tuple(sorted(raw_modules))
        if (
            len(set(audit_modules)) != len(audit_modules)
            or import_module not in audit_modules
        ):
            errors.append(
                f"{label}: signature context module scope is incomplete or ambiguous"
            )
            continue
        expected_helper = _valid_fingerprint(raw_context.get("helper_fingerprint"))
        if (
            expected_helper is None
            or helper_stat is None
            or helper_stat.st_size != expected_helper[1]
        ):
            errors.append(
                f"{label}: Lean manifest helper is missing or has a different size"
            )
            continue
        expected_main = _valid_fingerprint(raw_context.get("olean_fingerprint"))
        raw_expected_modules = raw_context.get("semantic_module_fingerprints")
        if expected_main is None or not isinstance(raw_expected_modules, list):
            errors.append(f"{label}: compiled artifact identities are malformed")
            continue
        expected_modules: dict[str, tuple[str, int]] = {}
        malformed = False
        for raw_entry in raw_expected_modules:
            if not isinstance(raw_entry, list) or len(raw_entry) != 2:
                malformed = True
                break
            module = str(raw_entry[0] or "").strip()
            fingerprint = _valid_fingerprint(raw_entry[1])
            if not module or fingerprint is None or module in expected_modules:
                malformed = True
                break
            expected_modules[module] = fingerprint
        if malformed or set(expected_modules) != set(audit_modules):
            errors.append(f"{label}: compiled import-closure identity is incomplete")
            continue
        if expected_modules.get(import_module) != expected_main:
            errors.append(
                f"{label}: target artifact identity conflicts with its import closure"
            )
            continue
        expected_scope = lean_manifest._audit_scope_fingerprint(  # noqa: SLF001
            import_module,
            expected_main,
            audit_modules,
        )
        if str(raw_context.get("audit_scope_fingerprint") or "") != expected_scope:
            errors.append(f"{label}: Lean audit-scope identity is stale")
            continue
        for module in audit_modules:
            if module not in module_sizes:
                relative = Path(*module.split(".")).with_suffix(".olean")
                try:
                    module_sizes[module] = (
                        (root / ".lake" / "build" / "lib" / "lean" / relative)
                        .stat()
                        .st_size
                    )
                except OSError:
                    module_sizes[module] = None
            if module_sizes[module] != expected_modules[module][1]:
                errors.append(
                    f"{label}: compiled artifact is missing or resized for {module}"
                )
                malformed = True
                break
        if malformed:
            continue
        snapshots.append(
            {
                "schema": context_schema,
                "source": label,
                "import_module": import_module,
                "helper": list(expected_helper),
                "modules": [
                    [module, list(expected_modules[module])] for module in audit_modules
                ],
                "audit_scope_fingerprint": expected_scope,
                **(
                    {
                        "canonical_representation": "lean_compact_canonical_v2",
                        "semantic_hash_tool_identity": raw_context.get(
                            "semantic_hash_tool_identity"
                        ),
                    }
                    if context_schema == 3
                    else {}
                ),
            }
        )
    return (_digest(snapshots), errors)


def _artifact_mutation_snapshot(
    root: Path, contexts: Mapping[str, Any]
) -> dict[str, tuple[int, int, int, int, int] | None]:
    """Capture cheap identities after exact artifact content validation.

    This is only a within-planner mutation guard.  It never substitutes for
    the exact content hashes checked by ``_signature_context_snapshot`` or for
    the authoritative strict closeout.
    """

    paths = {lean_manifest.HELPER_PATH.resolve()}
    for raw_context in contexts.values():
        if not isinstance(raw_context, Mapping):
            continue
        raw_modules = raw_context.get("audit_modules")
        if isinstance(raw_modules, list):
            for raw_module in raw_modules:
                if not isinstance(raw_module, str) or not raw_module:
                    continue
                relative = Path(*raw_module.split(".")).with_suffix(".olean")
                paths.add(
                    (root / ".lake" / "build" / "lib" / "lean" / relative).resolve()
                )
        raw_tool = raw_context.get("semantic_hash_tool_identity")
        if isinstance(raw_tool, Mapping):
            resolved_tool = str(raw_tool.get("resolved_path") or "").strip()
            if resolved_tool:
                paths.add(Path(resolved_tool).resolve())

    snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    for path in sorted(paths, key=str):
        try:
            stat = path.stat()
        except OSError:
            snapshot[str(path)] = None
        else:
            snapshot[str(path)] = (
                stat.st_dev,
                stat.st_ino,
                stat.st_size,
                stat.st_mtime_ns,
                stat.st_ctime_ns,
            )
    return snapshot


def _declared_semantic_hash_tool_paths(
    contexts: Mapping[str, Any],
) -> set[Path]:
    """Return only exact schema-3 hash-tool paths declared by Lean contexts.

    The executable is an environment input, not a repository compiled artifact.
    It remains in the advisory mutation guard and is revalidated by the strict
    source-record/Lean paths, but must never be fed to the repository-only
    operational receipt.
    """

    paths: set[Path] = set()
    for context in contexts.values():
        if not isinstance(context, Mapping) or context.get("schema") != 3:
            continue
        raw_tool = context.get("semantic_hash_tool_identity")
        if not isinstance(raw_tool, Mapping):
            continue
        raw_path = str(raw_tool.get("resolved_path") or "").strip()
        if not raw_path:
            continue
        try:
            paths.add(Path(raw_path).resolve(strict=True))
        except OSError:
            continue
    return paths


def _declared_semantic_hash_tool_projection(
    contexts: Mapping[str, Any],
) -> dict[str, object]:
    """Persist the small external-tool subset of a large dashboard context."""

    paths = sorted(str(path) for path in _declared_semantic_hash_tool_paths(contexts))
    return {
        "schema": DECLARED_EXTERNAL_TOOL_GUARD_SCHEMA,
        "paths": paths,
        "sha256": _digest(paths),
    }


def _declared_semantic_hash_tool_paths_from_projection(
    value: object,
) -> set[Path] | None:
    """Validate a cache-owned projection without rereading the dashboard body."""

    if not isinstance(value, Mapping):
        return None
    raw_paths = value.get("paths")
    if (
        value.get("schema") != DECLARED_EXTERNAL_TOOL_GUARD_SCHEMA
        or not isinstance(raw_paths, list)
        or not all(isinstance(path, str) and path for path in raw_paths)
        or value.get("sha256") != _digest(raw_paths)
    ):
        return None
    paths: set[Path] = set()
    for raw_path in raw_paths:
        candidate = Path(raw_path)
        if not candidate.is_absolute():
            return None
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            return None
        if str(resolved) != raw_path or resolved in paths:
            return None
        paths.add(resolved)
    return paths


def _compiled_ledger_has_external_path(
    root: Path, snapshot: Mapping[str, object]
) -> tuple[bool, str]:
    """Classify normalized compiled-ledger keys before loading large contexts."""

    try:
        resolved_root = root.resolve()
    except OSError as exc:
        return False, f"could not resolve repository root: {exc}"
    for raw_path in snapshot:
        try:
            path = Path(str(raw_path)).resolve(strict=False)
        except OSError as exc:
            return False, f"could not resolve compiled artifact guard {raw_path}: {exc}"
        if str(path) != str(raw_path):
            return False, "compiled artifact mutation ledger has a noncanonical path key"
        try:
            path.relative_to(resolved_root)
        except ValueError:
            return True, ""
    return False, ""


def _partition_operational_compiled_ledger(
    root: Path,
    snapshot: Mapping[str, object],
    *,
    signature_contexts: Mapping[str, Any] | None = None,
    declared_tool_paths: set[Path] | None = None,
) -> tuple[
    dict[str, tuple[int, int, int, int, int] | None],
    dict[str, tuple[int, int, int, int, int] | None],
    str,
]:
    """Separate repository artifacts from declared external tool guards.

    Only a current schema-3 Lean context may identify an external executable.
    Any other external path is a malformed advisory ledger and fails closed.
    The returned external half stays in the advisory cache; callers must pass
    only the repository half to ``closeout_plan_receipt``.
    """

    try:
        resolved_root = root.resolve()
    except OSError as exc:
        return {}, {}, f"could not resolve repository root: {exc}"
    if declared_tool_paths is None:
        declared_tools = _declared_semantic_hash_tool_paths(signature_contexts or {})
    else:
        declared_tools = set()
        for raw_path in declared_tool_paths:
            try:
                declared_tools.add(raw_path.resolve(strict=True))
            except OSError:
                return {}, {}, f"declared external hash tool is unavailable: {raw_path}"
    repository: dict[str, tuple[int, int, int, int, int] | None] = {}
    external_tools: dict[str, tuple[int, int, int, int, int] | None] = {}
    for raw_path, raw_value in snapshot.items():
        if raw_value is not None and (
            not isinstance(raw_value, (tuple, list))
            or len(raw_value) != 5
            or any(
                not isinstance(value, int) or isinstance(value, bool)
                for value in raw_value
            )
        ):
            return {}, {}, "compiled artifact mutation ledger is malformed"
        try:
            path = Path(str(raw_path)).resolve(strict=False)
        except OSError as exc:
            return {}, {}, f"could not resolve compiled artifact guard {raw_path}: {exc}"
        if str(path) != str(raw_path):
            return (
                {},
                {},
                "compiled artifact mutation ledger has a noncanonical path key",
            )
        identity = (
            tuple(int(value) for value in raw_value)
            if raw_value is not None
            else None
        )
        try:
            path.relative_to(resolved_root)
        except ValueError:
            if path not in declared_tools:
                return (
                    {},
                    {},
                    "compiled artifact mutation ledger contains an undeclared "
                    f"external path: {path}",
                )
            external_tools[str(path)] = identity
        else:
            repository[str(path)] = identity
    return repository, external_tools, ""


def _dashboard_signature_contexts(folder: Path) -> Mapping[str, Any] | None:
    """Read the exact context declarations from the current dashboard cache."""

    try:
        payload = json.loads(
            review_dashboard.paper_interface_cache_file(folder.name).read_text(
                encoding="utf-8"
            )
        )
    except (OSError, ValueError, json.JSONDecodeError):
        return None
    contexts = payload.get("signature_contexts") if isinstance(payload, Mapping) else None
    return contexts if isinstance(contexts, Mapping) else None


def _source_artifact_mutation_snapshot(
    root: Path, contexts: Mapping[str, Any]
) -> dict[str, tuple[int, int, int, int, int] | None]:
    """Capture the Lean-graph-selected repository sources and build controls."""

    paths = {(root / relative).resolve() for relative in LEAN_BUILD_CONTROL_PATHS}
    for raw_context in contexts.values():
        if not isinstance(raw_context, Mapping):
            continue
        raw_modules = raw_context.get("audit_modules")
        if not isinstance(raw_modules, list):
            continue
        for raw_module in raw_modules:
            if not isinstance(raw_module, str) or not raw_module:
                continue
            path = lean_manifest._repository_module_source_path(  # noqa: SLF001
                root, raw_module
            )
            if path is not None:
                paths.add(path.resolve())
    snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    for path in sorted(paths, key=str):
        try:
            snapshot[str(path)] = _stat_identity(path.stat())
        except OSError:
            snapshot[str(path)] = None
    return snapshot


def _advisory_lean_graph_loader(
    root: Path, entry_module: str, timeout_seconds: int
) -> tuple[tuple[str, ...] | None, str]:
    """Read a loaded-module graph without silently compiling an advisory plan.

    The planner treats graph-only failure as a cache miss and schedules its
    explicit paper build.  Strict closeout keeps the default build-backed
    graph provider, so this non-authoritative shortcut cannot certify a
    successful closeout.
    """

    return lean_loaded_module_closure(
        root,
        entry_module,
        timeout_seconds,
        build_entry_module=False,
    )


def _root_import_closure_mutation_snapshots(
    root: Path,
    folder: Path,
    provider: lean_manifest.RepositoryBuildInputSnapshotProvider,
) -> tuple[
    dict[str, tuple[int, int, int, int, int] | None],
    dict[str, tuple[int, int, int, int, int] | None],
    list[str],
    dict[str, object] | None,
]:
    """Capture the exact Lean-selected paper-root source/compiled closure."""

    source_records = provider.repository_source_snapshot(folder.name)
    if not source_records:
        return (
            {},
            {},
            [
                "Lean could not provide the exact paper-root import closure; "
                "run the planner's focused build action before replanning"
            ],
            None,
        )
    closure_receipt = provider.lean_import_closure_receipt(folder.name)
    if closure_receipt is None:
        return (
            {},
            {},
            ["Lean did not retain a validated paper-root loaded-module receipt"],
            None,
        )
    source_snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    compiled_snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    errors: list[str] = []
    for module, path, _content, _digest_value in source_records:
        try:
            source_snapshot[str(path.resolve())] = _stat_identity(path.stat())
        except OSError as exc:
            source_snapshot[str(path.resolve())] = None
            errors.append(f"paper-root Lean source is unavailable: {path}: {exc}")
        artifact = (
            root / ".lake" / "build" / "lib" / "lean" / Path(*module.split("."))
        ).with_suffix(".olean")
        try:
            compiled_snapshot[str(artifact.resolve())] = _stat_identity(artifact.stat())
        except OSError as exc:
            compiled_snapshot[str(artifact.resolve())] = None
            errors.append(
                f"paper-root compiled Lean artifact is unavailable: {artifact}: {exc}"
            )
    return source_snapshot, compiled_snapshot, errors, closure_receipt


@dataclass(frozen=True)
class CachedReviewSnapshot:
    rows: list[Any]
    source_material_sha256: str
    compiled_material_sha256: str
    compiled_artifacts_ready: bool
    compiled_validation_mode: str
    compiled_invalidation_reasons: tuple[str, ...]
    source_hashes: dict[str, str]
    signature_contexts: dict[str, Any]
    source_artifact_mutation_snapshot: dict[str, tuple[int, int, int, int, int] | None]
    compiled_artifact_mutation_snapshot: dict[
        str, tuple[int, int, int, int, int] | None
    ]
    lean_import_closure_projection: dict[str, Any]
    cache_path: Path
    cache_mutation_snapshot: tuple[int, int, int, int, int]
    cache_sha256: str


def cached_review_snapshot(
    folder: Path,
    *,
    verify_compiled_content: bool = False,
) -> tuple[CachedReviewSnapshot | None, list[str]]:
    """Load the initial exact read-only cache snapshot for a guarded plan."""

    try:
        cache_path = review_dashboard.paper_interface_cache_file(folder.name)
        with cache_path.open("rb") as stream:
            cache_stat_before = _stat_identity(os.fstat(stream.fileno()))
            cache_bytes_before = stream.read()
            cache_stat_after = _stat_identity(os.fstat(stream.fileno()))
        payload = json.loads(cache_bytes_before)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        return None, [f"dashboard cache is unavailable: {error}"]
    if cache_stat_after != cache_stat_before:
        return None, ["dashboard cache changed while it was being read"]
    if not isinstance(payload, dict):
        return None, ["dashboard cache payload is not an object"]
    contexts = payload.get("signature_contexts")
    if not isinstance(contexts, Mapping):
        return None, ["dashboard cache has no exact Lean signature contexts"]

    source_artifacts_before = _source_artifact_mutation_snapshot(ROOT, contexts)
    # Advisory planning must never hide compilation behind a cache probe.  If
    # the required artifacts are absent, the graph-only provider fails closed
    # and the existing schedule exposes one explicit paper build instead.
    build_input_provider = lean_manifest.RepositoryBuildInputSnapshotProvider(
        ROOT,
        module_graph_loader=_advisory_lean_graph_loader,
    )
    source_before = review_dashboard._cache_source_hashes(  # noqa: SLF001
        folder,
        build_input_provider=build_input_provider,
    )
    root_sources, root_artifacts, root_closure_errors, root_closure_receipt = (
        _root_import_closure_mutation_snapshots(ROOT, folder, build_input_provider)
    )
    if root_closure_errors:
        return None, root_closure_errors
    context_sources_after = _source_artifact_mutation_snapshot(ROOT, contexts)
    if context_sources_after != source_artifacts_before:
        return None, ["Lean source material changed while it was being validated"]
    source_artifacts_after = dict(context_sources_after)
    source_artifacts_after.update(root_sources)
    load_parameters = inspect.signature(
        review_dashboard.load_cached_review_rows
    ).parameters
    load_kwargs: dict[str, Any] = {
        "signature_contexts": dict(contexts),
        "source_hashes": source_before,
        "persist_rebind": False,
    }
    if "cache_payload" in load_parameters:
        # Newer dashboards can deserialize the bytes captured above directly,
        # eliminating an ABA reread. Older v10 engines remain supported; the
        # planner's final cache digest still detects ordinary concurrent edits.
        load_kwargs["cache_payload"] = payload
    rows = review_dashboard.load_cached_review_rows(folder, **load_kwargs)
    if rows is None:
        return None, [
            "dashboard cache does not match the current review/source material"
        ]

    # Validate large compiled artifacts only after the cheap source/cache gate.
    # A stale source snapshot should never pay to hash an import closure that
    # cannot be reused. Shared modules are memoized by the validator above.
    artifacts_before = _artifact_mutation_snapshot(ROOT, contexts)
    artifacts_before.update(root_artifacts)
    compiled_validation_mode = (
        "exact_content" if verify_compiled_content else "metadata_preflight"
    )
    compiled_before, compiled_errors = (
        _signature_context_snapshot(ROOT, contexts)
        if verify_compiled_content
        else _signature_context_metadata_snapshot(ROOT, contexts)
    )
    artifacts_after = _artifact_mutation_snapshot(ROOT, contexts)
    for raw_path in root_artifacts:
        try:
            artifacts_after[raw_path] = _stat_identity(Path(raw_path).stat())
        except OSError:
            artifacts_after[raw_path] = None
    if artifacts_after != artifacts_before:
        return None, ["compiled Lean material changed while it was being validated"]
    if not build_input_provider.finalize_unchanged():
        return None, ["Lean import-closure inputs changed during planning"]
    assert root_closure_receipt is not None
    try:
        root_closure_projection = build_lean_closure_operational_projection(
            ROOT, root_closure_receipt
        )
    except CloseoutPlanReceiptError as exc:
        return None, [str(exc)]

    return (
        CachedReviewSnapshot(
            rows=rows,
            source_material_sha256=_digest(source_before),
            compiled_material_sha256=compiled_before or _digest(contexts),
            compiled_artifacts_ready=not compiled_errors,
            compiled_validation_mode=compiled_validation_mode,
            compiled_invalidation_reasons=tuple(compiled_errors),
            source_hashes=source_before,
            signature_contexts=dict(contexts),
            source_artifact_mutation_snapshot=source_artifacts_after,
            compiled_artifact_mutation_snapshot=artifacts_after,
            lean_import_closure_projection=root_closure_projection,
            cache_path=cache_path,
            cache_mutation_snapshot=cache_stat_after,
            cache_sha256=hashlib.sha256(cache_bytes_before).hexdigest(),
        ),
        [],
    )


def cached_snapshot_invalidation_reasons(
    folder: Path, snapshot: CachedReviewSnapshot
) -> list[str]:
    """Check cheap mutable paths after planning.

    Exact source-closure acquisition happened before row reuse. The planner's
    direct-input guard covers paper/source material after this function, while
    strict closeout repeats the authoritative closure validation. Reacquiring
    the full Lean closure here would duplicate the dominant planning cost.
    """

    errors: list[str] = []
    sources_after = _restat_mutation_snapshot(
        snapshot.source_artifact_mutation_snapshot
    )
    artifacts_after = _restat_mutation_snapshot(
        snapshot.compiled_artifact_mutation_snapshot
    )
    try:
        cache_stat_after = _stat_identity(snapshot.cache_path.stat())
    except OSError as error:
        errors.append(f"dashboard cache disappeared during planning: {error}")
        cache_stat_after = None
    if sources_after != snapshot.source_artifact_mutation_snapshot:
        errors.append("Lean source material changed during planning")
    if artifacts_after != snapshot.compiled_artifact_mutation_snapshot:
        errors.append("compiled Lean material changed during planning")
    # The cache is often the largest planner input. Its captured stat tuple
    # guards an unchanged file without rereading it; when the guard changes,
    # retain the previous exact-content comparison so harmless metadata churn
    # is still accepted and an actual cache edit fails closed.
    if (
        cache_stat_after is not None
        and cache_stat_after != snapshot.cache_mutation_snapshot
    ):
        try:
            cache_after = hashlib.sha256(snapshot.cache_path.read_bytes()).hexdigest()
        except OSError as error:
            errors.append(f"dashboard cache disappeared during planning: {error}")
            cache_after = ""
        if cache_after != snapshot.cache_sha256:
            errors.append("dashboard cache changed during planning")
    return errors


def _stat_identity(stat: os.stat_result) -> tuple[int, int, int, int, int]:
    return (
        stat.st_dev,
        stat.st_ino,
        stat.st_size,
        stat.st_mtime_ns,
        stat.st_ctime_ns,
    )


def _restat_mutation_snapshot(
    snapshot: Mapping[str, object],
) -> dict[str, tuple[int, int, int, int, int] | None]:
    current: dict[str, tuple[int, int, int, int, int] | None] = {}
    for raw_path in snapshot:
        path = str(raw_path)
        try:
            current[path] = _stat_identity(Path(path).stat())
        except OSError:
            current[path] = None
    return current


def _changed_stats_covered_by_content_snapshot(
    expected: Mapping[str, object],
    current: Mapping[str, object],
    content_snapshot: Mapping[str, object],
) -> bool:
    """Accept stat churn only where exact current content was revalidated."""

    for raw_path in set(expected) | set(current):
        path = str(raw_path)
        if expected.get(path) == current.get(path):
            continue
        candidate = Path(path)
        if not candidate.is_absolute():
            candidate = ROOT / candidate
        try:
            relative = candidate.relative_to(ROOT.resolve()).as_posix()
        except ValueError:
            return False
        if relative not in content_snapshot:
            return False
    return True


def _mutation_snapshot_is_current(snapshot: Mapping[str, object]) -> bool:
    expected: dict[str, tuple[int, int, int, int, int] | None] = {}
    for raw_path, raw_value in snapshot.items():
        path = str(raw_path)
        if raw_value is None:
            expected[path] = None
        elif isinstance(raw_value, (list, tuple)) and len(raw_value) == 5:
            expected[path] = tuple(int(value) for value in raw_value)
        else:
            return False
    return _restat_mutation_snapshot(snapshot) == expected


def _file_material_snapshot(paths: list[Path]) -> dict[str, dict[str, Any]]:
    """Capture content and filesystem identity, including explicit absence."""

    snapshot: dict[str, dict[str, Any]] = {}
    for path in paths:
        try:
            with path.open("rb") as stream:
                before = os.fstat(stream.fileno())
                content = stream.read()
                after = os.fstat(stream.fileno())
        except FileNotFoundError:
            snapshot[str(path)] = {"state": "missing", "sha256": None}
            continue
        except OSError as exc:
            snapshot[str(path)] = {"state": "unreadable", "error": str(exc)}
            continue
        stat_fields = _stat_identity(after)
        snapshot[str(path)] = {
            "state": (
                "present"
                if _stat_identity(before) == stat_fields
                else "changed_during_read"
            ),
            "sha256": hashlib.sha256(content).hexdigest(),
            "stat": list(stat_fields),
        }
    return snapshot


def _material_content_projection(
    snapshot: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Drop mutation-only metadata from a stable operational plan identity."""

    return {
        path: {
            "state": item.get("state"),
            "sha256": item.get("sha256"),
        }
        for path, item in snapshot.items()
    }


def _material_mutation_snapshot(
    *snapshots: Mapping[str, Mapping[str, Any]],
) -> dict[str, tuple[int, int, int, int, int] | None]:
    """Extract mutation-only stat guards without adding them to stable identity."""

    ledger: dict[str, tuple[int, int, int, int, int] | None] = {}
    for snapshot in snapshots:
        for path, item in snapshot.items():
            raw_stat = item.get("stat")
            ledger[path] = (
                tuple(int(value) for value in raw_stat)
                if isinstance(raw_stat, (list, tuple)) and len(raw_stat) == 5
                else None
            )
    return ledger


def _serialized_mutation_snapshot(
    value: object,
) -> dict[str, list[int] | None] | None:
    """Normalize one internal stat ledger before persisting advisory guards."""

    if not isinstance(value, Mapping):
        return None
    serialized: dict[str, list[int] | None] = {}
    for raw_path, raw_identity in value.items():
        path = str(raw_path)
        if raw_identity is None:
            serialized[path] = None
            continue
        if not isinstance(raw_identity, (list, tuple)) or len(raw_identity) != 5:
            return None
        try:
            serialized[path] = [int(item) for item in raw_identity]
        except (TypeError, ValueError):
            return None
    return serialized


def _reusable_dashboard_material_snapshot(
    folder: Path, cache_path: Path
) -> dict[str, dict[str, Any]] | None:
    """Reuse a large cache digest only while its exact filesystem guard matches."""

    try:
        payload = json.loads(
            _advisory_plan_cache_path(folder).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, Mapping)
        or payload.get("schema") != ADVISORY_PLAN_CACHE_SCHEMA
        or payload.get("decision_contract") != ADVISORY_PLAN_DECISION_CONTRACT
    ):
        return None
    input_material = payload.get("input_material")
    mutation_snapshot = payload.get("input_mutation_snapshot")
    if not isinstance(input_material, Mapping) or not isinstance(
        mutation_snapshot, Mapping
    ):
        return None
    raw_dashboard = input_material.get("dashboard_cache")
    path_key = str(cache_path)
    recorded_item = (
        raw_dashboard.get(path_key) if isinstance(raw_dashboard, Mapping) else None
    )
    recorded_stat = mutation_snapshot.get(path_key)
    if not isinstance(recorded_item, Mapping) or not isinstance(
        recorded_stat, (list, tuple)
    ):
        return None
    try:
        current_stat = _stat_identity(cache_path.stat())
    except OSError:
        return None
    if tuple(int(value) for value in recorded_stat) != current_stat:
        return None
    return {
        path_key: {
            "state": recorded_item.get("state"),
            "sha256": recorded_item.get("sha256"),
            "stat": list(current_stat),
        }
    }


def _captured_json_payloads(
    paths: list[Path],
) -> tuple[dict[Path, dict[str, Any]], dict[str, dict[str, Any]], list[str]]:
    """Parse each planner JSON input from the same bytes used for its identity."""

    payloads: dict[Path, dict[str, Any]] = {}
    snapshot: dict[str, dict[str, Any]] = {}
    errors: list[str] = []
    for path in paths:
        try:
            with path.open("rb") as stream:
                before = os.fstat(stream.fileno())
                content = stream.read()
                after = os.fstat(stream.fileno())
        except FileNotFoundError:
            snapshot[str(path)] = {"state": "missing", "sha256": None}
            payloads[path] = {}
            continue
        except OSError as exc:
            snapshot[str(path)] = {"state": "unreadable", "error": str(exc)}
            payloads[path] = {}
            errors.append(f"could not read {path.relative_to(ROOT)}: {exc}")
            continue
        state = (
            "present"
            if _stat_identity(before) == _stat_identity(after)
            else "changed_during_read"
        )
        snapshot[str(path)] = {
            "state": state,
            "sha256": hashlib.sha256(content).hexdigest(),
            "stat": list(_stat_identity(after)),
        }
        if state != "present":
            errors.append(f"{path.relative_to(ROOT)} changed while it was read")
        try:
            payload = json.loads(content)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            payload = {}
            errors.append(f"could not parse {path.relative_to(ROOT)}: {exc}")
        if not isinstance(payload, dict):
            payload = {}
            errors.append(f"{path.relative_to(ROOT)} is not a JSON object")
        payloads[path] = payload
    return payloads, snapshot, errors


def _advisory_plan_cache_path(folder: Path) -> Path:
    return folder / ".review_traces" / ADVISORY_PLAN_CACHE_FILE


def _compiled_input_cache_path(folder: Path) -> Path:
    return folder / ".review_traces" / COMPILED_INPUT_CACHE_FILE


def _compiled_content_projection(value: object) -> dict[str, dict[str, Any]] | None:
    if not isinstance(value, Mapping):
        return None
    projection: dict[str, dict[str, Any]] = {}
    for raw_path, raw_identity in value.items():
        if not isinstance(raw_identity, Mapping):
            return None
        identity = {
            str(key): item
            for key, item in raw_identity.items()
            if key != "stat_guard"
        }
        if identity.get("state") not in {"present", "missing"}:
            return None
        projection[str(raw_path)] = identity
    return projection


def _load_compiled_input_cache(folder: Path) -> dict[str, dict[str, Any]] | None:
    try:
        payload = json.loads(
            _compiled_input_cache_path(folder).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, Mapping)
        or payload.get("schema") != COMPILED_INPUT_CACHE_SCHEMA
        or payload.get("acceptance_credential") is not False
        or payload.get("operational_scheduling_only") is not True
        or payload.get("paper") != folder.name
        or not isinstance(payload.get("compiled_inputs"), Mapping)
    ):
        return None
    inputs = {
        str(path): dict(identity) if isinstance(identity, Mapping) else identity
        for path, identity in payload["compiled_inputs"].items()
    }
    if (
        _compiled_content_projection(inputs) is None
        or payload.get("compiled_inputs_sha256") != _digest(inputs)
    ):
        return None
    return inputs


def _write_compiled_input_cache(
    folder: Path, compiled_inputs: Mapping[str, object]
) -> None:
    inputs = {
        str(path): dict(identity) if isinstance(identity, Mapping) else identity
        for path, identity in compiled_inputs.items()
    }
    if _compiled_content_projection(inputs) is None:
        return
    atomic_write_json(
        _compiled_input_cache_path(folder),
        {
            "schema": COMPILED_INPUT_CACHE_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": folder.name,
            "compiled_inputs": inputs,
            "compiled_inputs_sha256": _digest(inputs),
        },
    )


def _semantic_direct_input_paths(
    folder: Path, source_map: Mapping[str, Any]
) -> list[Path]:
    """Return cheap direct inputs that must match an advisory reuse decision."""

    paths = {
        folder / "PaperInterface.lean",
        folder / "Assumptions.lean",
        folder / "status.json",
    }
    artifact_texts = [str(source_map.get("source_artifact_path") or "").strip()]
    raw_items = source_map.get("items")
    if isinstance(raw_items, Mapping):
        for raw_item in raw_items.values():
            if not isinstance(raw_item, Mapping):
                continue
            artifact_texts.extend(
                [
                    str(raw_item.get("source_artifact_path") or "").strip(),
                    str(raw_item.get("source_text_file") or "").strip(),
                ]
            )
    for text in artifact_texts:
        if not text:
            continue
        candidate = Path(text)
        if not candidate.is_absolute():
            candidate = (
                ROOT / candidate
                if candidate.parts[:1] == ("papers",)
                else folder / candidate
            )
        try:
            candidate.resolve().relative_to(ROOT.resolve())
        except ValueError:
            continue
        paths.add(candidate.resolve())
    return sorted(paths, key=str)


def _exact_raw_producer_paths(audit_payload: object) -> set[Path]:
    """Resolve exact producer identities that may never be optimized away."""

    if not isinstance(audit_payload, Mapping):
        return set()
    fingerprint = audit_payload.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping):
        return set()
    raw_identities = fingerprint.get("raw_producer_code_identities")
    if not isinstance(raw_identities, list):
        return set()
    paths: set[Path] = set()
    for raw in raw_identities:
        if not isinstance(raw, Mapping):
            continue
        text = str(raw.get("path") or "").split("#", 1)[0].strip()
        candidate = Path(text)
        if not text or candidate.is_absolute():
            continue
        try:
            resolved = (ROOT / candidate).resolve()
            resolved.relative_to(ROOT.resolve())
        except (OSError, RuntimeError, ValueError):
            continue
        paths.add(resolved)
    return paths


def _strict_transaction_content_snapshot(
    folder: Path,
) -> tuple[dict[str, dict[str, Any]] | None, str]:
    """Acquire the strict gate's own selected evidence-input set once.

    This uses the consolidated closeout builder only when semantic reuse is
    ready to advance toward a strict route.  Subsequent plans revalidate the
    persisted logical-path content snapshot and avoid repeating the builder's
    source-record preparation.
    """

    try:
        try:
            from scripts.audit_evidence_integrity import (
                _fingerprint_identity_watch_paths,
                _source_record_identity_declared_watch_paths,
                build_evidence_run_context,
            )
        except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
            from audit_evidence_integrity import (
                _fingerprint_identity_watch_paths,
                _source_record_identity_declared_watch_paths,
                build_evidence_run_context,
            )

        context = build_evidence_run_context(folder)
        projected_controls = {
            (ROOT / "papers" / "audit_config.json").resolve(),
            (ROOT / "lakefile.toml").resolve(),
            (
                ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
            ).resolve(),
        }
        paths = {
            snapshot.path
            for snapshot in context.input_snapshots
            if isinstance(getattr(snapshot, "path", None), Path)
            and snapshot.path.resolve() not in projected_controls
        }
        fingerprint_paths, _fingerprint_markers = _fingerprint_identity_watch_paths(
            context.audit_payload
        )
        declared_paths, _declared_markers = (
            _source_record_identity_declared_watch_paths(folder)
        )
        exact_raw_producers = _exact_raw_producer_paths(context.audit_payload)
        for path in fingerprint_paths | declared_paths:
            resolved = path.resolve()
            try:
                relative = resolved.relative_to(ROOT.resolve())
            except ValueError:
                continue
            implementation_only = (
                is_engine_source_path(relative.as_posix())
                and resolved not in exact_raw_producers
            )
            if resolved not in projected_controls and not implementation_only:
                paths.add(path)
        return content_input_snapshot(ROOT, paths), ""
    except (CloseoutPlanReceiptError, OSError, RuntimeError, ValueError) as exc:
        return None, f"could not acquire strict closeout input inventory: {exc}"


def _advisory_plan_input_identity(
    folder: Path,
    *,
    source_map: Mapping[str, Any],
    audit_material: Mapping[str, Mapping[str, Any]],
    current_mode: str,
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_coverage_inventory: Mapping[str, Mapping[str, Any]],
) -> tuple[str, dict[str, Any]]:
    """Bind ignored planner reuse to exact direct bytes and dashboard cache."""

    cache_path = review_dashboard.paper_interface_cache_file(folder.name)
    decision_paths = repository_python_import_closure(
        ROOT,
        [ROOT / relative for relative in ADVISORY_DECISION_ENTRYPOINTS],
    )
    routing_projection, routing_error = lake_routing_projection(ROOT, folder.name)
    if routing_projection is None:
        raise RuntimeError(
            routing_error or "target Lake routing projection is unavailable"
        )
    direct_snapshot = _file_material_snapshot(
        _semantic_direct_input_paths(folder, source_map)
    )
    decision_snapshot = _file_material_snapshot(list(decision_paths))
    cache_snapshot = _reusable_dashboard_material_snapshot(
        folder, cache_path
    ) or _file_material_snapshot([cache_path])
    material = {
        "schema": ADVISORY_PLAN_CACHE_SCHEMA,
        "decision_contract": ADVISORY_PLAN_DECISION_CONTRACT,
        "paper": folder.name,
        "decision_implementation": _material_content_projection(decision_snapshot),
        "audit_material": _material_content_projection(audit_material),
        "direct_material": _material_content_projection(direct_snapshot),
        "dashboard_cache": _material_content_projection(cache_snapshot),
        "target_lake_routing": routing_projection,
        "formalization_review_protocol": strict_closeout_protocol_projection(ROOT),
        "source_coverage_mode": current_mode,
        "source_inventory_sha256": _digest(current_inventory),
        "coverage_inventory_sha256": _digest(current_coverage_inventory),
    }
    identity = _digest(material)
    material["_mutation_snapshot"] = _material_mutation_snapshot(
        decision_snapshot,
        audit_material,
        direct_snapshot,
        cache_snapshot,
    )
    return identity, material


def _advisory_input_material_is_current(material: Mapping[str, Any]) -> bool:
    raw_snapshot = material.get("_mutation_snapshot")
    return isinstance(raw_snapshot, Mapping) and _mutation_snapshot_is_current(
        raw_snapshot
    )


def _semantic_plan_structure_error(plan: Mapping[str, Any]) -> str:
    """Return a fail-closed error for an advisory semantic-plan payload.

    The advisory cache is an optimization, not a trusted representation of an
    empty review worklist.  In particular, absent counters must not be treated
    as zero and permit a cached plan to reach a strict worker.  The checks use
    the plan's structural item data and counters, never declaration names.
    """

    summary = plan.get("summary")
    validator_errors = plan.get("validator_identity_errors")
    if not isinstance(summary, Mapping):
        return "advisory semantic plan has no summary object"
    if not isinstance(validator_errors, Mapping):
        return "advisory semantic plan has no validator-identity error object"

    required_counters = (
        ("statement", "statement_requires_review"),
        ("coverage", "coverage_requires_review"),
    )
    for lane, counter_name in required_counters:
        items = plan.get(lane)
        if not isinstance(items, Mapping):
            return f"advisory semantic plan has no {lane} item object"
        counter = summary.get(counter_name)
        if not isinstance(counter, int) or isinstance(counter, bool) or counter < 0:
            return f"advisory semantic plan has invalid {counter_name}"
        invalid_items = 0
        for item in items.values():
            if not isinstance(item, Mapping) or not isinstance(item.get("reusable"), bool):
                return f"advisory semantic plan has malformed {lane} item"
            invalid_items += item.get("reusable") is False
        if counter != invalid_items:
            return (
                f"advisory semantic plan's {counter_name} does not match its "
                f"{lane} items"
            )
        lane_errors = validator_errors.get(lane)
        if not isinstance(lane_errors, list):
            return f"advisory semantic plan has malformed {lane} validator errors"
    if "global_error" in plan and not isinstance(plan["global_error"], str):
        return "advisory semantic plan has malformed global error"
    return ""


def _read_advisory_plan_cache(
    folder: Path,
    expected_input_sha256: str,
    *,
    current_input_mutation_snapshot: object | None = None,
) -> dict[str, Any] | None:
    path = _advisory_plan_cache_path(folder)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, dict)
        or payload.get("schema") != ADVISORY_PLAN_CACHE_SCHEMA
        or payload.get("acceptance_credential") is not False
        or payload.get("decision_contract") != ADVISORY_PLAN_DECISION_CONTRACT
        or payload.get("input_identity_sha256") != expected_input_sha256
        or not isinstance(payload.get("semantic_plan"), dict)
    ):
        return None
    plan = dict(payload["semantic_plan"])
    if (
        plan.get("acceptance_credential") is not False
        or plan.get("requires_fresh_strict_closeout") is not True
    ):
        return None
    if _semantic_plan_structure_error(plan):
        return None
    # A cached worklist that still has unresolved semantic items cannot reach a
    # strict transaction.  Do not deserialize/revalidate its strict-input
    # snapshot merely to return the same manual-repair action.  The caller
    # still validates its current direct-input mutation guard before publishing
    # that action, and a repair changes the advisory identity before any strict
    # route can be considered.
    plan["cache_reusable"] = True
    if _semantic_plan_requires_manual_repair(plan):
        plan["advisory_plan_cache"] = {
            "hit": True,
            "path": str(path.relative_to(ROOT)),
            "acceptance_credential": False,
            "strict_input_validation_deferred_for_semantic_repair": True,
        }
        return plan
    # Advisory caches written before the compiled-artifact stop was introduced
    # can describe a semantic-ready plan without a usable compiled closure.
    # That plan must rebuild and replan before it can enter the strict route;
    # validating an old strict-input snapshot here would be needless work and
    # could make a pre-build cache look operationally fresher than it is.
    if plan.get("compiled_artifacts_ready") is not True:
        plan["advisory_plan_cache"] = {
            "hit": True,
            "path": str(path.relative_to(ROOT)),
            "acceptance_credential": False,
            "strict_input_validation_deferred_for_compiled_rebuild": True,
        }
        return plan
    recorded_strict_snapshot = payload.get("strict_transaction_content_snapshot")
    strict_snapshot, strict_snapshot_error = validate_content_input_snapshot(
        ROOT, recorded_strict_snapshot
    )
    if strict_snapshot is None or strict_snapshot_error:
        return None
    try:
        lean_closure_projection = validate_lean_closure_operational_projection(
            ROOT, payload.get("lean_import_closure_projection")
        )
    except CloseoutPlanReceiptError:
        return None
    if lean_closure_projection.get("state") != "present":
        return None
    raw_sources = payload.get("source_artifact_mutation_snapshot")
    raw_compiled = payload.get("compiled_artifact_mutation_snapshot")
    if not isinstance(raw_sources, Mapping) or not isinstance(raw_compiled, Mapping):
        return None
    current_sources = _restat_mutation_snapshot(raw_sources)
    expected_sources = {
        str(path): tuple(int(item) for item in value) if value is not None else None
        for path, value in raw_sources.items()
        if value is None or isinstance(value, (list, tuple)) and len(value) == 5
    }
    if len(expected_sources) != len(raw_sources):
        return None
    if current_sources != expected_sources and not _changed_stats_covered_by_content_snapshot(
        expected_sources, current_sources, strict_snapshot
    ):
        return None

    # A dashboard cache can be hundreds of megabytes. Read it only once for a
    # legacy advisory cache that actually contains an external guard; current
    # advisory caches retain a small, input-bound tool projection instead.
    has_external_guard, compiled_ledger_shape_error = (
        _compiled_ledger_has_external_path(ROOT, raw_compiled)
    )
    if compiled_ledger_shape_error:
        return None
    declared_tool_paths: set[Path] = set()
    external_tool_projection: dict[str, object] | None = None
    persist_external_tool_projection = False
    if has_external_guard:
        external_tool_projection = payload.get("declared_external_tool_projection")
        projected_paths = _declared_semantic_hash_tool_paths_from_projection(
            external_tool_projection
        )
        if projected_paths is None:
            signature_contexts = _dashboard_signature_contexts(folder)
            if signature_contexts is None:
                return None
            projected_paths = _declared_semantic_hash_tool_paths(signature_contexts)
            external_tool_projection = _declared_semantic_hash_tool_projection(
                signature_contexts
            )
            persist_external_tool_projection = True
        declared_tool_paths = projected_paths
    repository_compiled, external_tool_guards, partition_error = (
        _partition_operational_compiled_ledger(
            ROOT,
            raw_compiled,
            declared_tool_paths=declared_tool_paths,
        )
    )
    if partition_error:
        return None
    current_compiled = _restat_mutation_snapshot(raw_compiled)
    expected_compiled = {
        str(path): tuple(int(item) for item in value) if value is not None else None
        for path, value in raw_compiled.items()
        if value is None or isinstance(value, (list, tuple)) and len(value) == 5
    }
    if len(expected_compiled) != len(raw_compiled):
        return None
    expected_external_tools = {
        path: expected_compiled[path] for path in external_tool_guards
    }
    current_external_tools = {
        path: current_compiled[path] for path in external_tool_guards
    }
    if current_external_tools != expected_external_tools:
        # A fresh cache path will revalidate the declared executable's exact
        # Lean-owned identity before it can be used for any schedule.
        return None
    if current_compiled != expected_compiled:
        prior_compiled_inputs = _load_compiled_input_cache(folder)
        if prior_compiled_inputs is None:
            return None
        try:
            refreshed_compiled_inputs = compiled_input_snapshot(
                ROOT,
                (Path(str(path)) for path in repository_compiled),
                reusable=prior_compiled_inputs,
            )
        except CloseoutPlanReceiptError:
            return None
        if _compiled_content_projection(
            refreshed_compiled_inputs
        ) != _compiled_content_projection(prior_compiled_inputs):
            return None
        _write_compiled_input_cache(folder, refreshed_compiled_inputs)
        current_compiled = _restat_mutation_snapshot(raw_compiled)

    plan["_execution_source_artifact_mutation_snapshot"] = dict(current_sources)
    plan["_execution_compiled_artifact_mutation_snapshot"] = {
        path: current_compiled[path] for path in repository_compiled
    }
    plan["_execution_strict_transaction_content_snapshot"] = strict_snapshot
    plan["_execution_lean_import_closure_projection"] = lean_closure_projection
    plan["advisory_plan_cache"] = {
        "hit": True,
        "path": str(path.relative_to(ROOT)),
        "acceptance_credential": False,
        "strict_closeout_revalidates_all_semantic_and_compiled_inputs": True,
    }
    current_input_guards = None
    if current_input_mutation_snapshot is not None:
        current_input_guards = _serialized_mutation_snapshot(
            current_input_mutation_snapshot
        )
        if current_input_guards is None or not _mutation_snapshot_is_current(
            current_input_mutation_snapshot
        ):
            return None
    if (
        strict_snapshot != recorded_strict_snapshot
        or current_sources != expected_sources
        or current_compiled != expected_compiled
        or lean_closure_projection != payload.get("lean_import_closure_projection")
        or (
            current_input_guards is not None
            and current_input_guards != payload.get("input_mutation_snapshot")
        )
    ):
        refreshed_payload = dict(payload)
        refreshed_payload["strict_transaction_content_snapshot"] = strict_snapshot
        refreshed_payload["source_artifact_mutation_snapshot"] = {
            path: list(value) if value is not None else None
            for path, value in current_sources.items()
        }
        refreshed_payload["compiled_artifact_mutation_snapshot"] = {
            path: list(value) if value is not None else None
            for path, value in current_compiled.items()
        }
        refreshed_payload["lean_import_closure_projection"] = (
            lean_closure_projection
        )
        if current_input_guards is not None:
            refreshed_payload["input_mutation_snapshot"] = current_input_guards
        if external_tool_projection is not None:
            refreshed_payload["declared_external_tool_projection"] = (
                external_tool_projection
            )
        atomic_write_json(path, refreshed_payload)
    elif persist_external_tool_projection and external_tool_projection is not None:
        refreshed_payload = dict(payload)
        refreshed_payload["declared_external_tool_projection"] = (
            external_tool_projection
        )
        atomic_write_json(path, refreshed_payload)
    return plan


def _write_advisory_plan_cache(
    folder: Path,
    *,
    input_identity_sha256: str,
    input_material: Mapping[str, Any],
    semantic_plan: Mapping[str, Any],
    source_artifact_mutation_snapshot: Mapping[
        str, tuple[int, int, int, int, int] | None
    ],
    compiled_artifact_mutation_snapshot: Mapping[
        str, tuple[int, int, int, int, int] | None
    ],
    strict_transaction_content_snapshot: Mapping[str, Mapping[str, Any]],
    lean_import_closure_projection: Mapping[str, Any],
    declared_external_tool_projection: Mapping[str, object] | None = None,
) -> None:
    raw_mutation_snapshot = input_material.get("_mutation_snapshot")
    input_mutation_snapshot = (
        {
            str(path): list(value) if value is not None else None
            for path, value in raw_mutation_snapshot.items()
        }
        if isinstance(raw_mutation_snapshot, Mapping)
        else {}
    )
    payload: dict[str, Any] = {
            "schema": ADVISORY_PLAN_CACHE_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "decision_contract": ADVISORY_PLAN_DECISION_CONTRACT,
            "input_identity_sha256": input_identity_sha256,
            "input_material": {
                str(key): value
                for key, value in input_material.items()
                if not str(key).startswith("_")
            },
            "input_mutation_snapshot": input_mutation_snapshot,
            "source_artifact_mutation_snapshot": {
                path: list(value) if value is not None else None
                for path, value in source_artifact_mutation_snapshot.items()
            },
            "compiled_artifact_mutation_snapshot": {
                path: list(value) if value is not None else None
                for path, value in compiled_artifact_mutation_snapshot.items()
            },
            "strict_transaction_content_snapshot": {
                str(path): dict(value)
                for path, value in strict_transaction_content_snapshot.items()
            },
            "lean_import_closure_projection": dict(lean_import_closure_projection),
            "semantic_plan": dict(semantic_plan),
    }
    if declared_external_tool_projection is not None:
        payload["declared_external_tool_projection"] = dict(
            declared_external_tool_projection
        )
    atomic_write_json(_advisory_plan_cache_path(folder), payload)


def _lean_code_lines(text: str) -> list[tuple[int, str]]:
    """Strip nested block and line comments for a cheap placeholder preflight."""

    code_lines: list[tuple[int, str]] = []
    block_depth = 0
    for line_number, line in enumerate(text.splitlines(), start=1):
        out: list[str] = []
        index = 0
        while index < len(line):
            if line.startswith("/-", index):
                block_depth += 1
                index += 2
            elif block_depth > 0 and line.startswith("-/", index):
                block_depth -= 1
                index += 2
            elif block_depth > 0:
                index += 1
            else:
                out.append(line[index])
                index += 1
        code_lines.append((line_number, "".join(out).split("--", 1)[0]))
    return code_lines


@lru_cache(maxsize=None)
def _paper_predates_intake_freeze_baseline(root: str, paper: str) -> bool:
    """Use one immutable rollout tree, never a mutable status marker, as legacy authority."""

    try:
        result = subprocess.run(
            [
                "git",
                "cat-file",
                "-e",
                f"{INTAKE_FREEZE_LEGACY_BASELINE_COMMIT}:papers/{paper}/status.json",
            ],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except OSError:
        return False
    return result.returncode == 0


def _git_blob_at_rollout(root: Path, relative: str) -> tuple[bytes | None, str]:
    try:
        result = subprocess.run(
            [
                "git",
                "show",
                f"{INTAKE_FREEZE_LEGACY_BASELINE_COMMIT}:{relative}",
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as exc:
        return None, f"could not read trusted rollout tree: {exc}"
    if result.returncode == 0:
        return result.stdout, ""
    return None, ""


def _git_mode_at_rollout(root: Path, relative: str) -> tuple[str | None, str]:
    try:
        result = subprocess.run(
            [
                "git",
                "ls-tree",
                INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
                "--",
                relative,
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    except OSError as exc:
        return None, f"could not inspect trusted rollout tree: {exc}"
    if result.returncode != 0:
        return None, (
            "could not inspect trusted rollout tree: " + result.stderr.strip()
        )
    rows = [line for line in result.stdout.splitlines() if line.strip()]
    if not rows:
        return None, ""
    if len(rows) != 1 or "\t" not in rows[0]:
        return None, f"trusted rollout tree has an ambiguous path: {relative}"
    header, recorded_path = rows[0].split("\t", 1)
    fields = header.split()
    if recorded_path != relative or len(fields) != 3:
        return None, f"trusted rollout tree has a malformed path: {relative}"
    return fields[0], ""


def _rollout_content_input_error(
    root: Path, relative: str, identity: object
) -> str:
    """Compare one selected current content input with its rollout-tree value."""

    if not isinstance(identity, Mapping):
        return f"current content input is malformed: {relative}"
    mode, mode_error = _git_mode_at_rollout(root, relative)
    if mode_error:
        return mode_error
    state = identity.get("state")
    path_projection = identity.get("path")
    if state == "missing":
        return "" if mode is None else f"content input was present at rollout: {relative}"
    if state != "present" or not isinstance(path_projection, Mapping):
        return f"current content input is malformed: {relative}"
    logical_state = path_projection.get("logical_state")
    resolved_path = str(path_projection.get("resolved_path") or "")
    if logical_state == "regular":
        if mode not in {"100644", "100755"} or resolved_path != relative:
            return f"content input path identity differs from rollout: {relative}"
    elif logical_state == "symlink":
        link_target = path_projection.get("link_target")
        link_blob, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return blob_error
        if (
            mode != "120000"
            or not isinstance(link_target, str)
            or link_blob != os.fsencode(link_target)
        ):
            return f"content input symlink differs from rollout: {relative}"
    else:
        return f"content input has unsupported path identity: {relative}"
    baseline, blob_error = _git_blob_at_rollout(root, resolved_path)
    if blob_error:
        return blob_error
    if (
        baseline is None
        or len(baseline) != identity.get("byte_length")
        or hashlib.sha256(baseline).hexdigest() != identity.get("sha256")
    ):
        return f"content input differs from rollout: {relative}"
    return ""


def _rollout_graph_errors(
    root: Path, paper: str, current_closure: object
) -> list[str]:
    """Compare current ownership with Lean's recorded rollout review graph."""

    baseline_blob, blob_error = _git_blob_at_rollout(
        root, f"papers/{paper}/audit/source_record_audit.json"
    )
    if blob_error:
        return [blob_error]
    if baseline_blob is None:
        return ["trusted rollout has no Lean-authored source-record graph"]
    try:
        baseline_payload = json.loads(baseline_blob)
        baseline = validated_lean_import_closure_payload(
            baseline_payload.get("lean_import_closure")
        )
        current = validated_lean_import_closure_payload(current_closure)
    except (AttributeError, json.JSONDecodeError, UnicodeDecodeError, ValueError) as exc:
        return [f"trusted rollout Lean graph is unavailable: {exc}"]

    current_sources = {
        str(raw["module"]): str(raw["path"])
        for raw in current["sources"]
        if isinstance(raw, Mapping)
    }
    baseline_sources = {
        str(raw["module"]): str(raw["path"])
        for raw in baseline["sources"]
        if isinstance(raw, Mapping)
    }
    expected_sources = dict(baseline_sources)
    current_entry_module = str(current["entry_module"])
    current_entrypoint = str(current["entrypoint"])
    expected_entrypoint = f"papers/{paper}.lean"
    if current_entry_module != paper or current_entrypoint != expected_entrypoint:
        errors = ["current Lean graph is not rooted at the selected paper target"]
    else:
        errors = []
    if (
        current_entry_module == paper
        and current_entrypoint == expected_entrypoint
        and current_entry_module not in expected_sources
    ):
        # The closeout receipt is rooted at papers/<Paper>.lean, while the
        # rollout source-record graph is commonly rooted at PaperInterface.
        # Permit exactly that current root wrapper, not arbitrary new imports.
        expected_sources[current_entry_module] = current_entrypoint
    current_external = {str(module) for module in current["external_import_modules"]}
    baseline_external = {
        str(module) for module in baseline["external_import_modules"]
    }
    for module in sorted(set(expected_sources) | set(current_sources)):
        if current_sources.get(module) != expected_sources.get(module):
            errors.append(
                f"Lean source ownership differs from rollout graph: {module}"
            )
    for module in sorted(baseline_external ^ current_external):
        errors.append(
            f"external Lean ownership differs from rollout graph: {module}"
        )
    expected_loaded = set(expected_sources) | baseline_external
    if expected_loaded != set(current["lean_loaded_modules"]):
        for module in sorted(
            expected_loaded ^ set(str(value) for value in current["lean_loaded_modules"])
        ):
            errors.append(
                f"Lean loaded-module membership differs from rollout graph: {module}"
            )
    return errors


def _legacy_rollout_material_readiness(
    folder: Path, receipt: Mapping[str, Any]
) -> dict[str, Any]:
    """Prove first legacy adoption still matches the trusted rollout tree.

    This guard is deterministic and tracked. The ignored adoption record may be
    deleted without allowing a paper edited after rollout to acquire a new
    baseline. Administrative workflow code is deliberately outside the check.
    """

    root = ROOT.resolve()
    paper = folder.name
    errors: list[str] = []
    raw_content_inputs = receipt.get("content_inputs")
    if not isinstance(raw_content_inputs, Mapping):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no exact content-input projection"],
        }
    paper_prefix = f"papers/{paper}/"
    paper_root = f"papers/{paper}.lean"
    for raw_relative, identity in raw_content_inputs.items():
        relative = str(raw_relative)
        if relative != paper_root and not relative.startswith(paper_prefix):
            continue
        error = _rollout_content_input_error(root, relative, identity)
        if error:
            errors.append(error)

    try:
        inventory_result = subprocess.run(
            [
                "git",
                "ls-tree",
                "-r",
                "--name-only",
                INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
                "--",
                f"papers/{paper}",
                f"papers/{paper}.lean",
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    except OSError as exc:
        return {
            "ready": False,
            "state": "error",
            "errors": [f"could not inventory trusted rollout tree: {exc}"],
        }
    if inventory_result.returncode != 0:
        return {
            "ready": False,
            "state": "error",
            "errors": [
                "could not inventory target paper in the trusted rollout tree: "
                + inventory_result.stderr.strip()
            ],
        }
    baseline_lean_inventory = sorted(
        line.strip()
        for line in inventory_result.stdout.splitlines()
        if line.strip().endswith(".lean")
    )
    current_lean_inventory = receipt.get("target_lean_file_inventory")
    if current_lean_inventory != baseline_lean_inventory:
        errors.append("target paper Lean-file inventory differs from the rollout tree")

    raw_projection = receipt.get("lean_import_closure_projection")
    raw_closure = (
        raw_projection.get("lean_import_closure")
        if isinstance(raw_projection, Mapping)
        else None
    )
    raw_sources = (
        raw_closure.get("sources") if isinstance(raw_closure, Mapping) else None
    )
    if not isinstance(raw_sources, list):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no Lean-authored source closure"],
        }
    errors.extend(_rollout_graph_errors(root, paper, raw_closure))
    for raw in raw_sources:
        if not isinstance(raw, Mapping):
            return {
                "ready": False,
                "state": "error",
                "errors": ["current Lean source closure is malformed"],
            }
        relative = str(raw.get("path") or "")
        baseline, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return {"ready": False, "state": "error", "errors": [blob_error]}
        if baseline is None or hashlib.sha256(baseline).hexdigest() != raw.get(
            "sha256"
        ):
            errors.append(f"Lean source differs from rollout: {relative}")

    raw_controls = (
        raw_closure.get("build_controls") if isinstance(raw_closure, Mapping) else None
    )
    if not isinstance(raw_controls, list):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no Lean build-control closure"],
        }
    for raw in raw_controls:
        if not isinstance(raw, Mapping):
            return {
                "ready": False,
                "state": "error",
                "errors": ["current Lean build-control closure is malformed"],
            }
        relative = str(raw.get("path") or "")
        baseline, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return {"ready": False, "state": "error", "errors": [blob_error]}
        if baseline is None or hashlib.sha256(baseline).hexdigest() != raw.get(
            "sha256"
        ):
            errors.append(f"Lean build control differs from rollout: {relative}")

    audit_config, audit_error = _git_blob_at_rollout(root, "papers/audit_config.json")
    protocol, protocol_error = _git_blob_at_rollout(
        root, "config/formalization_audit_protocol.json"
    )
    if audit_error or protocol_error or audit_config is None or protocol is None:
        return {
            "ready": False,
            "state": "error",
            "errors": [
                audit_error
                or protocol_error
                or "trusted rollout configuration is unavailable"
            ],
        }
    with tempfile.TemporaryDirectory() as temp_dir:
        baseline_root = Path(temp_dir)
        (baseline_root / "papers").mkdir()
        (baseline_root / "config").mkdir()
        (baseline_root / "papers" / "audit_config.json").write_bytes(audit_config)
        (baseline_root / "config" / "formalization_audit_protocol.json").write_bytes(
            protocol
        )
        try:
            baseline_target_config = target_audit_config_projection(
                baseline_root, paper
            )
            baseline_protocol = strict_closeout_protocol_projection(baseline_root)
        except CloseoutPlanReceiptError as exc:
            return {"ready": False, "state": "error", "errors": [str(exc)]}
        for lakefile in ("lakefile.toml", "lakefile.lean"):
            content, blob_error = _git_blob_at_rollout(root, lakefile)
            if blob_error:
                return {"ready": False, "state": "error", "errors": [blob_error]}
            if content is not None:
                (baseline_root / lakefile).write_bytes(content)
        baseline_routing, routing_error = lake_routing_projection(baseline_root, paper)
    if baseline_target_config != receipt.get("target_audit_config_projection"):
        errors.append("target audit configuration differs from rollout")
    if baseline_protocol != receipt.get("strict_closeout_protocol_projection"):
        errors.append("semantic review protocol differs from rollout")
    if baseline_routing is None:
        return {
            "ready": False,
            "state": "error",
            "errors": [routing_error or "trusted rollout Lake routing is unavailable"],
        }
    if _digest(baseline_routing) != receipt.get("lake_routing_projection_sha256"):
        errors.append("target Lake routing differs from rollout")

    return {
        "ready": not errors,
        "state": "current" if not errors else "material_changed",
        "errors": errors,
        "baseline_commit": INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
        "acceptance_credential": False,
    }


def intake_freeze_readiness(
    folder: Path, *, repository_root: Path | None = None
) -> dict[str, Any]:
    """Validate the prospective intake seal when a new paper opted into it."""

    root = (repository_root or ROOT).resolve()

    status_path = folder / "status.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [f"cannot read status marker: {exc}"],
        }
    if not isinstance(status, Mapping):
        return {
            "ready": False,
            "state": "invalid",
            "errors": ["status.json must be a JSON object"],
        }
    if "intake_freeze_required" not in status:
        if not _paper_predates_intake_freeze_baseline(str(root), folder.name):
            return {
                "ready": False,
                "state": "prospective_marker_missing",
                "errors": [
                    "paper is outside the trusted intake-rollout cohort but its "
                    "intake_freeze_required marker is missing"
                ],
            }
        return {
            "ready": True,
            "state": "legacy_not_configured",
            "reason": "existing status predates the prospective intake seal",
            "errors": [],
        }
    if status.get("intake_freeze_required") is not True:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [
                "tracked intake_freeze_required marker must be exactly true when present"
            ],
        }

    path = folder / "audit" / "intake_freeze.json"
    if not path.is_file():
        return {
            "ready": False,
            "state": "missing",
            "errors": ["required prospective intake freeze is missing"],
        }
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {"ready": False, "state": "invalid", "errors": [str(exc)]}
    errors: list[str] = []
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        errors.append("intake freeze must be a schema-1 JSON object")
        payload = {}
    if payload.get("paper") != folder.name:
        errors.append("intake freeze paper does not match its folder")
    if (
        payload.get("state") != "sealed"
        or payload.get("inventory_complete") is not True
    ):
        errors.append(
            "intake freeze is not sealed with a complete named-theory inventory"
        )
    if payload.get("source_item_identity") != INTAKE_SOURCE_IDENTITY:
        errors.append(
            "intake freeze does not declare the normalized semantic identity scheme"
        )

    source_map_path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read canonical source map: {exc}")
        source_map = {}
    if not isinstance(source_map, Mapping):
        errors.append("canonical source map must be a JSON object")
        source_map = {}

    artifact_text = str(payload.get("source_artifact_path") or "").strip()
    artifact_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    map_artifact_text = str(source_map.get("source_artifact_path") or "").strip()
    map_artifact_digest = (
        str(source_map.get("source_artifact_sha256") or "").strip().lower()
    )
    if artifact_text != map_artifact_text or artifact_digest != map_artifact_digest:
        errors.append(
            "intake freeze source artifact identity does not equal the canonical source-map identity"
        )

    def paper_local_path(raw_path: str) -> Path | None:
        if not raw_path:
            return None
        unresolved = Path(raw_path)
        candidate = (
            unresolved.resolve()
            if unresolved.is_absolute()
            else (
                (root / unresolved).resolve()
                if unresolved.parts[:1] == ("papers",)
                else (folder / unresolved).resolve()
            )
        )
        try:
            candidate.relative_to(folder.resolve())
        except ValueError:
            return None
        return candidate

    artifact = paper_local_path(map_artifact_text)
    artifact_bytes: bytes | None = None
    if (
        artifact is None
        or not SHA256_RE.fullmatch(map_artifact_digest)
        or not artifact.is_file()
    ):
        errors.append(
            "canonical source map has no readable paper-local byte-pinned artifact"
        )
    else:
        try:
            artifact_bytes = artifact.read_bytes()
        except OSError as exc:
            errors.append(f"cannot read canonical source artifact: {exc}")
        else:
            if hashlib.sha256(artifact_bytes).hexdigest() != map_artifact_digest:
                errors.append("canonical source-map artifact SHA-256 is stale")

    atom_artifact_bytes = artifact_bytes
    if artifact is not None and artifact.suffix.lower() == ".pdf":
        receipt = payload.get("source_text_artifact")
        if not isinstance(receipt, Mapping) or receipt.get("schema") != 1:
            errors.append(
                "PDF intake freeze requires a schema-1 normalized source-text artifact receipt"
            )
            atom_artifact_bytes = None
        else:
            text_path_text = str(receipt.get("path") or "").strip()
            text_digest = str(receipt.get("sha256") or "").strip().lower()
            text_path = paper_local_path(text_path_text)
            extraction = receipt.get("extraction")
            if (
                receipt.get("normalization") != "utf8-lf-v1"
                or text_path is None
                or text_path.suffix.lower() == ".pdf"
                or not SHA256_RE.fullmatch(text_digest)
                or not text_path.is_file()
            ):
                errors.append(
                    "PDF source-text receipt has no readable normalized paper-local text artifact"
                )
                atom_artifact_bytes = None
            else:
                try:
                    text_bytes = text_path.read_bytes()
                    text_bytes.decode("utf-8")
                except (OSError, UnicodeDecodeError) as exc:
                    errors.append(
                        f"cannot read normalized PDF source text as UTF-8: {exc}"
                    )
                    atom_artifact_bytes = None
                else:
                    if b"\r" in text_bytes:
                        errors.append("PDF source text is not LF-normalized")
                        atom_artifact_bytes = None
                    elif hashlib.sha256(text_bytes).hexdigest() != text_digest:
                        errors.append("PDF source-text artifact SHA-256 is stale")
                        atom_artifact_bytes = None
                    else:
                        atom_artifact_bytes = text_bytes
            if not isinstance(extraction, Mapping) or extraction.get("schema") != 1:
                errors.append("PDF source-text artifact lacks an extraction receipt")
                atom_artifact_bytes = None
            else:
                extraction_path = str(
                    extraction.get("source_artifact_path") or ""
                ).strip()
                extraction_digest = (
                    str(extraction.get("source_artifact_sha256") or "").strip().lower()
                )
                options = extraction.get("options")
                if (
                    extraction_path != map_artifact_text
                    or extraction_digest != map_artifact_digest
                    or extraction.get("tool") != "pdftotext"
                    or not isinstance(options, list)
                    or not all(isinstance(option, str) for option in options)
                ):
                    errors.append(
                        "PDF extraction receipt is not bound to the canonical source-map artifact"
                    )
                    atom_artifact_bytes = None

    source_items_by_identity: dict[
        tuple[str, str], list[tuple[str, Mapping[str, Any]]]
    ] = {}
    if isinstance(source_map, Mapping):
        for key, source_item in inventory_from_source_map(folder, source_map).items():
            location = str(source_item.get("source_location") or "").strip()
            statement_sha = (
                str(source_item.get("statement_sha256") or "").strip().lower()
            )
            if location and SHA256_RE.fullmatch(statement_sha):
                source_items_by_identity.setdefault(
                    (location, statement_sha), []
                ).append((key, source_item))

    raw_items = payload.get("items")
    items = raw_items if isinstance(raw_items, list) else []
    if not items:
        errors.append("intake freeze has no source obligations")
    orders: list[int] = []
    identities: set[tuple[str, str]] = set()
    for index, raw_item in enumerate(items, start=1):
        if not isinstance(raw_item, Mapping):
            errors.append(f"intake item {index} is not an object")
            continue
        location = str(raw_item.get("source_location") or "").strip()
        statement_sha = (
            str(raw_item.get("source_statement_sha256") or "").strip().lower()
        )
        if not location or not SHA256_RE.fullmatch(statement_sha):
            errors.append(
                f"intake item {index} lacks a locator-bound statement identity"
            )
        elif (location, statement_sha) in identities:
            errors.append(f"intake item {index} duplicates a semantic source identity")
        else:
            identities.add((location, statement_sha))
        mapped_items = source_items_by_identity.get((location, statement_sha), [])
        if len(mapped_items) != 1:
            errors.append(
                f"intake item {index} does not identify exactly one current source-map item by location and normalized statement"
            )
        else:
            mapped_item = mapped_items[0][1]
            if (
                str(mapped_item.get("source_artifact_path") or "").strip()
                != map_artifact_text
                or str(mapped_item.get("source_artifact_sha256") or "").strip().lower()
                != map_artifact_digest
            ):
                errors.append(
                    f"intake item {index} source-map route is not bound to the canonical artifact"
                )
        order = raw_item.get("dependency_order")
        if not isinstance(order, int) or isinstance(order, bool) or order <= 0:
            errors.append(f"intake item {index} has no positive dependency order")
        else:
            orders.append(order)
        owner = str(raw_item.get("owner") or "").strip().lower()
        if not owner or owner == "unassigned":
            errors.append(f"intake item {index} has no proof owner")
        conditions = raw_item.get("acceptance_conditions")
        if (
            not isinstance(conditions, list)
            or not conditions
            or not all(
                isinstance(condition, str) and condition.strip()
                for condition in conditions
            )
        ):
            errors.append(f"intake item {index} has incomplete acceptance conditions")
        atoms = raw_item.get("source_atoms")
        if not isinstance(atoms, list) or not atoms:
            errors.append(f"intake item {index} has no byte-pinned source atoms")
            continue
        for atom_index, atom in enumerate(atoms, start=1):
            if not isinstance(atom, Mapping):
                errors.append(f"intake item {index} atom {atom_index} is not an object")
                continue
            quote = str(atom.get("quoted_text") or "")
            quote_sha = str(atom.get("quoted_text_sha256") or "").strip().lower()
            atom_location = str(atom.get("source_location") or "").strip()
            byte_start = atom.get("byte_start")
            byte_end = atom.get("byte_end")
            exact_slice = (
                atom_artifact_bytes[byte_start:byte_end]
                if atom_artifact_bytes is not None
                and isinstance(byte_start, int)
                and not isinstance(byte_start, bool)
                and isinstance(byte_end, int)
                and not isinstance(byte_end, bool)
                and 0 <= byte_start < byte_end <= len(atom_artifact_bytes)
                else None
            )
            if (
                not quote.strip()
                or not atom_location
                or not SHA256_RE.fullmatch(quote_sha)
                or hashlib.sha256(quote.encode("utf-8")).hexdigest() != quote_sha
                or exact_slice != quote.encode("utf-8")
            ):
                errors.append(
                    f"intake item {index} atom {atom_index} lacks an exact artifact byte slice"
                )
    if orders and sorted(orders) != list(range(1, len(items) + 1)):
        errors.append("intake dependency order is not a total 1..N order")
    expected_identities = set(source_items_by_identity)
    if identities != expected_identities:
        missing_count = len(expected_identities - identities)
        unexpected_count = len(identities - expected_identities)
        errors.append(
            "intake freeze identities do not exactly equal the current source-map "
            f"inventory (missing={missing_count}, unexpected={unexpected_count})"
        )
    return {
        "ready": not errors,
        "state": "sealed" if not errors else "incomplete",
        "path": str(path.relative_to(root)),
        "errors": errors,
    }


def _intake_freeze_readiness(folder: Path) -> dict[str, Any]:
    """Compatibility alias for tests and older planner integrations."""

    return intake_freeze_readiness(folder)


def _planner_corrected_scope_current(
    folder: Path, status_payload: Mapping[str, Any]
) -> bool:
    """Ask the evidence gate whether a whole-paper corrected scope is current.

    This is used only to mirror the strict document exception.  Failure is
    deliberately conservative: a planner cannot waive the source-first audit
    when the exact corrected-scope contract is unavailable.
    """

    try:
        try:
            from scripts.audit_evidence_integrity import (
                author_approved_corrected_scope_contract_is_current,
            )
        except ModuleNotFoundError:
            from audit_evidence_integrity import (
                author_approved_corrected_scope_contract_is_current,
            )
        return bool(
            author_approved_corrected_scope_contract_is_current(
                folder, dict(status_payload)
            )
        )
    except Exception:
        return False


def _static_closeout_document_hard_errors(
    folder: Path, status_payload: Mapping[str, Any] | None
) -> list[tuple[Path, str]]:
    """Mirror strict document ERRORs without paying for the intake scan.

    The corrected-scope contract is evaluated only when the ordinary
    source-first audit is itself a blocker.  That keeps the common valid-doc
    preflight cheap while preserving the strict exception exactly.
    """

    errors = closeout_document_hard_errors(
        folder, corrected_scope_current=False
    )
    agent_audit = folder / AGENT_SOURCE_AUDIT_RELATIVE_PATH
    if (
        isinstance(status_payload, Mapping)
        and any(error.path == agent_audit for error in errors)
        and _planner_corrected_scope_current(folder, status_payload)
    ):
        errors = closeout_document_hard_errors(
            folder, corrected_scope_current=True
        )
    return [(error.path, error.message) for error in errors]


def static_closeout_readiness(
    folder: Path, *, include_intake: bool = True
) -> dict[str, Any]:
    """Find deterministic paper-local blockers before any manifest hashing.

    This advisory preflight intentionally does not reproduce semantic audit
    logic. Unknown semantic lanes remain delegated to the authoritative strict
    closeout and never become acceptance evidence here.  ``include_intake``
    controls the prospective intake's exact source-artifact/atom scan: callers
    that only need metadata diagnostics can defer that byte-heavy work until a
    paper has passed the cheap status-eligibility gate.
    """

    required = [
        folder / "PaperInterface.lean",
        folder / "status.json",
        folder / "audit" / "paper_statement_map.json",
        folder / "FINAL_VALIDATION_REPORT.md",
        folder / "docs" / "DependencyDAG.tex",
        folder / "docs" / "DependencyDAG.pdf",
        ROOT / "papers" / f"{folder.name}.lean",
    ]
    missing = [str(path.relative_to(ROOT)) for path in required if not path.is_file()]
    placeholder_pattern = re.compile(
        r"(?<![A-Za-z0-9_'])(?:sorry|admit)(?![A-Za-z0-9_'])"
    )
    placeholders: list[str] = []
    preflight_paths = {
        folder / "PaperInterface.lean",
        ROOT / "papers" / f"{folder.name}.lean",
    }
    assumptions_path = folder / "Assumptions.lean"
    if assumptions_path.is_file():
        preflight_paths.add(assumptions_path)
    for path in sorted(preflight_paths, key=str):
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            placeholders.append(f"{path.relative_to(ROOT)}: unreadable ({exc})")
            continue
        if "sorry" not in text and "admit" not in text:
            continue
        for line_number, code in _lean_code_lines(text):
            if placeholder_pattern.search(code):
                placeholders.append(f"{path.relative_to(ROOT)}:{line_number}")

    report_status_errors: tuple[str, ...] = ()
    status_payload: Mapping[str, Any] | None = None
    status_path = folder / "status.json"
    report_path = folder / "FINAL_VALIDATION_REPORT.md"
    if status_path.is_file() and report_path.is_file():
        try:
            decoded_status_payload = json.loads(status_path.read_text(encoding="utf-8"))
            report_text = report_path.read_text(encoding="utf-8")
        except (OSError, json.JSONDecodeError):
            # Status decoding itself is handled by the status preflight below;
            # this lane only owns a valid status/report contract mismatch.
            pass
        else:
            if isinstance(decoded_status_payload, Mapping):
                status_payload = decoded_status_payload
                report_status_errors = report_status_alignment_errors(
                    status_payload.get("status"), report_text
                )

    document_errors = _static_closeout_document_hard_errors(
        folder, status_payload
    )
    cheap_blockers = [
        *[f"missing required closeout artifact: {path}" for path in missing],
        *[f"paper-local Lean placeholder: {location}" for location in placeholders],
        *[
            "final validation report/status alignment: " + error
            for error in report_status_errors
        ],
        *[
            "closeout document: "
            + str(path.relative_to(ROOT))
            + ": "
            + message
            for path, message in document_errors
        ],
    ]

    if include_intake and not cheap_blockers:
        intake = intake_freeze_readiness(folder)
    elif include_intake:
        intake = {
            "ready": None,
            "state": "deferred_due_to_static_blocker",
            "errors": [],
            "reason": (
                "exact source-artifact and atom validation is deferred until "
                "the listed cheap closeout blockers are resolved"
            ),
        }
    else:
        intake = {
            "ready": None,
            "state": "deferred_until_closeout_eligibility",
            "errors": [],
            "reason": (
                "exact source-artifact and atom validation is deferred until "
                "the paper is eligible for closeout"
            ),
        }
    blockers = [
        *cheap_blockers,
        *[
            f"intake freeze: {error}"
            for error in intake.get("errors", [])
            if include_intake
        ],
    ]
    return {
        "ready": not blockers,
        "acceptance_credential": False,
        "lanes": {
            "required_artifacts": {
                "ready": not missing,
                "missing": missing,
            },
            "paper_local_proof_surface": {
                "ready": not placeholders,
                "potential_placeholders": placeholders,
                "scope": "explicit interface/assumptions/root preflight only",
            },
            "final_validation_report_status": {
                "ready": not report_status_errors,
                "errors": list(report_status_errors),
                "scope": "controlled Closeout Status/status.json agreement only",
            },
            "strict_closeout_documents": {
                "ready": not document_errors,
                "errors": [
                    {
                        "path": str(path.relative_to(ROOT)),
                        "message": message,
                    }
                    for path, message in document_errors
                ],
                "scope": "strict ERROR-class report and source-first audit gates",
            },
            "prospective_intake_freeze": intake,
            "semantic_and_recursive_gates": {
                "state": "deferred_to_authoritative_closeout",
                "proof_placeholder_scope": "exact Lean-loaded import closure",
                "reason": (
                    "the planner does not duplicate semantic receipt producers or "
                    "turn legacy missing fields into new closeout requirements"
                ),
            },
        },
        "blockers": blockers,
    }


def _paper_closeout_status_preflight(folder: Path) -> tuple[str, str]:
    """Return the declared status and a closeout-eligibility error, if any."""

    try:
        payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return "", f"paper-local status metadata is unavailable: {exc}"
    if not isinstance(payload, Mapping):
        return "", "paper-local status metadata is not an object"
    status = str(payload.get("status") or "").strip().lower()
    if not status:
        return "", "paper-local status metadata has no status"
    if status in CLOSEOUT_PLANNER_ELIGIBLE_STATUSES:
        return status, ""
    return (
        status,
        "paper is not eligible for closeout while its status is "
        f"`{status}`; resolve the mathematical/source-model boundary before "
        "running receipt or manifest work",
    )


def _authenticated_semantic_contract_replay_identity(
    folder: Path,
    raw_audit: Mapping[str, Any],
) -> tuple[str, str]:
    """Check whether the evidence gate can authenticate a saved raw receipt.

    The raw producer deliberately retains its own representation diagnostics.
    A paper-local replay may suppress only the two structurally replayable
    diagnostics, and only after its exact raw/map/manifest pins validate.
    Planner preflight must not disagree with the evidence gate about that
    narrow case, but it also must not turn an artifact into a cache shortcut.
    Reuse the gate's complete current-identity check, including the current
    source/configuration fingerprint, before returning ``validated``.

    ``not_applicable`` deliberately leaves the producer helper authoritative;
    ``rejected`` is diagnostic only and likewise grants no reuse credit.
    """

    artifact_path = (
        folder / "audit" / "source_record_semantic_contract_revalidation.json"
    )
    if not artifact_path.is_file():
        return "not_applicable", ""
    try:
        try:
            from scripts import audit_evidence_integrity as evidence
        except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
            import audit_evidence_integrity as evidence

        projection, replay_error = (
            evidence.source_record_semantic_contract_revalidation_context(
                folder, raw_audit
            )
        )
    except Exception as exc:  # noqa: BLE001 - advisory replay must fail closed.
        return (
            "rejected",
            "could not validate semantic-contract revalidation: "
            f"{type(exc).__name__}: {exc}",
        )
    if replay_error:
        return "rejected", "semantic-contract revalidation is invalid: " + replay_error

    try:
        expected_map_sha256 = evidence.current_paper_statement_map_sha256(folder)
        identity_error = evidence.source_record_audit_identity_error(
            dict(raw_audit),
            expected_paper_statement_map_sha256=expected_map_sha256,
            folder=folder,
            semantic_contract_revalidation=projection,
            prevalidated_semantic_contract_revalidation_error=replay_error,
        )
    except Exception as exc:  # noqa: BLE001 - advisory replay must fail closed.
        return (
            "rejected",
            "could not validate replayed source-record identity: "
            f"{type(exc).__name__}: {exc}",
        )
    if identity_error:
        return "rejected", identity_error
    return "validated", ""


def current_raw_semantic_repair_required(identity: Mapping[str, Any]) -> bool:
    """Recognize a current raw with one repairable semantic-surface defect.

    This is deliberately a closed structured predicate. The fast producer
    independently reports source/configuration identity, raw receipt
    integrity, scan completeness, reusable-item metadata, snapshot stability,
    and generated semantic-surface validity. A rendered error string, row
    name, or declaration name must never decide whether a closeout can avoid a
    costly raw reissue.
    """

    if (
        identity.get("current") is not False
        or identity.get("identity_scope")
        != "repository_sources_and_configuration_only"
        or identity.get("observed_source_record_fingerprint_schema") != 10
    ):
        return False
    dimensions = identity.get("validation_dimensions")
    if not isinstance(dimensions, Mapping):
        return False

    def state(name: str) -> str:
        value = dimensions.get(name)
        return str(value.get("state") or "") if isinstance(value, Mapping) else ""

    if {
        "raw_receipt_integrity": state("raw_receipt_integrity"),
        "raw_scan_completeness": state("raw_scan_completeness"),
        "reusable_item_metadata": state("reusable_item_metadata"),
        "raw_bytes": state("raw_bytes"),
        "source_configuration_identity": state(
            "source_configuration_identity"
        ),
        "generated_semantic_surface": state("generated_semantic_surface"),
    } != {
        "raw_receipt_integrity": "valid",
        "raw_scan_completeness": "valid",
        "reusable_item_metadata": "valid",
        "raw_bytes": "stable",
        "source_configuration_identity": "current",
        "generated_semantic_surface": "invalid",
    }:
        return False
    semantic = dimensions.get("generated_semantic_surface")
    return isinstance(semantic, Mapping) and bool(
        str(semantic.get("reason") or "").strip()
    )


def fast_saved_source_record_preflight(folder: Path) -> dict[str, Any]:
    """Read only enough saved evidence to order expensive closeout work.

    This is a non-accepting preflight.  It invokes the producer's bounded
    repository-source identity mode and compares the configured judgment
    sidecar's raw-receipt binding.  It cannot certify semantic adequacy: the
    worker still performs the strict external-artifact and TOCTOU checks.
    """

    result: dict[str, Any] = {
        "schema": 1,
        "paper": folder.name,
        "acceptance_credential": False,
        "scope": "saved raw source/configuration identity and configured judgment binding only",
        "state": "identity_inspection_required",
    }
    try:
        status_payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        result["reason"] = f"could not read paper-local status metadata: {exc}"
        return result
    if not isinstance(status_payload, dict):
        result["reason"] = "paper-local status metadata is not an object"
        return result
    try:
        try:
            from scripts.audit_evidence_integrity import source_record_review_sidecar_path
        except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
            from audit_evidence_integrity import source_record_review_sidecar_path

        raw_path, raw_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    except Exception as exc:  # noqa: BLE001 - preflight must not guess paths.
        result["reason"] = "could not resolve configured source-record paths: " + str(exc)
        return result
    if raw_path_error or match_path_error or raw_path is None or match_path is None:
        result["reason"] = (
            raw_path_error
            or match_path_error
            or "configured source-record paths are unavailable"
        )
        return result
    try:
        raw_relative = raw_path.relative_to(ROOT)
        match_relative = match_path.relative_to(ROOT)
    except ValueError:
        result["reason"] = "configured source-record paths are outside the repository"
        return result
    result.update(
        {
            "raw_path": str(raw_relative),
            "judgment_path": str(match_relative),
        }
    )

    def read_saved_sidecars() -> tuple[
        Mapping[str, Any] | None, Mapping[str, Any] | None, str
    ]:
        try:
            raw = json.loads(raw_path.read_text(encoding="utf-8"))
            match = json.loads(match_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            return (
                None,
                None,
                f"saved source-record raw or judgment sidecar is unreadable: {exc}",
            )
        if not isinstance(raw, Mapping) or not isinstance(match, Mapping):
            return None, None, "saved source-record raw or judgment sidecar is not an object"
        return raw, match, ""

    def record_raw_and_judgment_digests(
        raw: Mapping[str, Any], match: Mapping[str, Any]
    ) -> object:
        raw_digest = str(raw.get("source_record_audit_sha256") or "").strip()
        match_digest = str(match.get("source_record_audit_sha256") or "").strip()
        fingerprint = raw.get("source_record_input_fingerprint")
        fingerprint_schema = (
            fingerprint.get("schema") if isinstance(fingerprint, Mapping) else None
        )
        result.update(
            {
                "raw_audit_sha256": raw_digest,
                "judgment_audit_sha256": match_digest,
                "raw_fingerprint_schema": fingerprint_schema,
            }
        )
        return fingerprint_schema

    canonical_raw_path = (folder / "audit" / "source_record_audit.json").resolve()
    if raw_path.resolve() != canonical_raw_path:
        result["configured_raw_is_canonical"] = False
        raw, match, sidecar_error = read_saved_sidecars()
        if sidecar_error:
            # Reissuing the canonical producer cannot repair a status entry
            # that names a different raw/judgment pair.  Stop for an explicit
            # routing repair instead of overwriting an unrelated canonical
            # receipt and presenting the same action again on the next plan.
            result.update(
                {
                    "state": "identity_inspection_required",
                    "reason": sidecar_error,
                }
            )
            return result
        assert raw is not None and match is not None
        record_raw_and_judgment_digests(raw, match)
        result["reason"] = (
            "configured source-record raw receipt is noncanonical; the bounded "
            "identity helper validates only the canonical receipt"
        )
        return result
    result["configured_raw_is_canonical"] = True
    helper = ROOT / FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE
    if not helper.is_file():
        result["reason"] = "fast source-record identity helper is unavailable"
        return result
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(helper),
                "--root",
                str(ROOT),
                "--paper",
                folder.name,
                "--fast-saved-identity",
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        result["reason"] = "fast source-record identity helper timed out"
        return result
    except OSError as exc:
        result["reason"] = "could not start fast source-record identity helper: " + str(exc)
        return result
    try:
        identity = json.loads(proc.stdout)
    except json.JSONDecodeError:
        detail = " ".join((proc.stderr or proc.stdout or "").splitlines()[-3:])
        result["reason"] = "fast source-record identity helper returned invalid JSON" + (
            ": " + detail if detail else ""
        )
        return result
    if not isinstance(identity, Mapping):
        result["reason"] = "fast source-record identity helper returned a non-object"
        return result
    result["identity"] = dict(identity)
    identity_reason = str(identity.get("reason") or "").strip()
    if proc.returncode == 0 and identity.get("current") is True:
        # A current v11 raw-source-to-expanded-Spec lane deliberately replaces
        # the historical generated source-record LLM ledger.  Do not schedule
        # a legacy judgment rebind merely because its raw-receipt digest is
        # old: the direct lane separately verifies every selected source item,
        # its transparent Spec, and material library semantics.  The final
        # closure receipt remains the acceptance authority.
        try:
            try:
                from scripts.audit_evidence_integrity import (
                    v11_direct_semantic_review_state,
                )
            except ModuleNotFoundError:  # Direct script execution.
                from audit_evidence_integrity import (  # type: ignore
                    v11_direct_semantic_review_state,
                )
            current_v11, v11_error = v11_direct_semantic_review_state(
                folder,
                str(status_payload.get("status") or "").strip(),
            )
        except Exception as exc:  # noqa: BLE001 - a v11 probe cannot authorize.
            current_v11, v11_error = False, str(exc)
        if current_v11:
            result.update(
                {
                    "state": "current_v11_direct_semantic_review",
                    "raw_audit_sha256": str(
                        identity.get("source_record_audit_sha256") or ""
                    ).strip(),
                    "raw_fingerprint_schema": 10,
                    "v11_direct_semantic_review": "current",
                    "reason": "",
                }
            )
            return result
        if v11_error:
            result["v11_direct_semantic_review"] = "not_current: " + v11_error
        try:
            match = json.loads(match_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            result.update(
                {
                    "state": "current_raw_judgment_rebuild_required",
                    "raw_audit_sha256": str(
                        identity.get("source_record_audit_sha256") or ""
                    ).strip(),
                    "raw_fingerprint_schema": 10,
                    "reason": "saved source-record judgment sidecar is unreadable: "
                    + str(exc),
                }
            )
            return result
        if not isinstance(match, Mapping):
            result.update(
                {
                    "state": "current_raw_judgment_rebuild_required",
                    "raw_audit_sha256": str(
                        identity.get("source_record_audit_sha256") or ""
                    ).strip(),
                    "raw_fingerprint_schema": 10,
                    "reason": "saved source-record judgment sidecar is not an object",
                }
            )
            return result
        # A current helper result has already validated the canonical raw
        # receipt and requires its schema-10 fingerprint. Avoid rereading that
        # potentially hundred-megabyte JSON merely to recover these fields.
        raw_digest = str(identity.get("source_record_audit_sha256") or "").strip()
        match_digest = str(match.get("source_record_audit_sha256") or "").strip()
        result.update(
            {
                "raw_audit_sha256": raw_digest,
                "judgment_audit_sha256": match_digest,
                "raw_fingerprint_schema": 10,
            }
        )
        if not raw_digest or raw_digest != match_digest:
            result.update(
                {
                    "state": "current_raw_judgment_delta",
                    "reason": (
                        "configured source-record judgment sidecar is bound to a "
                        "different raw receipt"
                    ),
                }
            )
        else:
            result.update({"state": "current_raw_judgment_bound", "reason": ""})
        return result

    # The fast producer correctly keeps raw representation diagnostics in its
    # own output. When a paper has installed the separately authenticated
    # structural replay, consult the exact same effective-surface and current
    # identity path as the evidence gate. This exceptional branch rereads the
    # raw JSON only when such an artifact exists; ordinary stale/helper paths
    # retain the one-read fast preflight behavior below.
    replay_artifact = (
        folder / "audit" / "source_record_semantic_contract_revalidation.json"
    )
    if replay_artifact.is_file():
        raw, match, sidecar_error = read_saved_sidecars()
        if not sidecar_error:
            assert raw is not None and match is not None
            replay_state, replay_detail = (
                _authenticated_semantic_contract_replay_identity(folder, raw)
            )
            result["semantic_contract_revalidation"] = {
                "state": replay_state,
                **({"reason": replay_detail} if replay_detail else {}),
            }
            if replay_state == "validated":
                fingerprint_schema = record_raw_and_judgment_digests(raw, match)
                # The evidence identity validator should already imply this,
                # but retain the planner's schema-10 cache boundary locally.
                if fingerprint_schema == 10:
                    raw_digest = str(raw.get("source_record_audit_sha256") or "").strip()
                    match_digest = str(
                        match.get("source_record_audit_sha256") or ""
                    ).strip()
                    if raw_digest and raw_digest == match_digest:
                        result.update(
                            {
                                "state": "current_raw_judgment_bound",
                                "reason": "",
                            }
                        )
                    else:
                        result.update(
                            {
                                "state": "current_raw_judgment_delta",
                                "reason": (
                                    "configured source-record judgment sidecar is bound "
                                    "to a different raw receipt"
                                ),
                            }
                        )
                    return result
                result["semantic_contract_revalidation"] = {
                    "state": "rejected",
                    "reason": (
                        "replayed source-record identity did not retain the "
                        "planner's schema-10 fingerprint boundary"
                    ),
                }
        else:
            result["semantic_contract_revalidation"] = {
                "state": "rejected",
                "reason": sidecar_error,
            }

    # The bounded helper has already parsed and integrity-checked a
    # well-formed stale raw receipt.  Reuse only its declared digest/schema to
    # avoid parsing the same large raw JSON a second time; any absent or
    # malformed observation falls back to the conservative full sidecar read.
    observed_raw_digest = str(
        identity.get("observed_source_record_audit_sha256") or ""
    ).strip()
    observed_schema = identity.get("observed_source_record_fingerprint_schema")
    if SHA256_RE.fullmatch(observed_raw_digest) and isinstance(observed_schema, int):
        if current_raw_semantic_repair_required(identity):
            observed_state = "current_raw_semantic_repair_required"
        else:
            dimensions = identity.get("validation_dimensions")
            source_identity = (
                dimensions.get("source_configuration_identity")
                if isinstance(dimensions, Mapping)
                else None
            )
            source_identity_state = (
                str(source_identity.get("state") or "")
                if isinstance(source_identity, Mapping)
                else ""
            )
            observed_state = (
                "raw_reissue_required"
                if observed_schema != 10 or source_identity_state == "stale"
                else "identity_inspection_required"
            )
        try:
            match = json.loads(match_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            result.update(
                {
                    "state": observed_state,
                    "raw_audit_sha256": observed_raw_digest,
                    "raw_fingerprint_schema": observed_schema,
                    "reason": identity_reason
                    or "saved source-record judgment sidecar is unreadable: "
                    + str(exc),
                }
            )
            return result
        if not isinstance(match, Mapping):
            result.update(
                {
                    "state": observed_state,
                    "raw_audit_sha256": observed_raw_digest,
                    "raw_fingerprint_schema": observed_schema,
                    "reason": identity_reason
                    or "saved source-record judgment sidecar is not an object",
                }
            )
            return result
        result.update(
            {
                "raw_audit_sha256": observed_raw_digest,
                "judgment_audit_sha256": str(
                    match.get("source_record_audit_sha256") or ""
                ).strip(),
                "raw_fingerprint_schema": observed_schema,
                "state": observed_state,
                "reason": identity_reason
                or "saved source-record identity is not current",
            }
        )
        return result
    raw, match, sidecar_error = read_saved_sidecars()
    if sidecar_error:
        result.update({"state": "raw_reissue_required", "reason": sidecar_error})
        return result
    assert raw is not None and match is not None
    fingerprint_schema = record_raw_and_judgment_digests(raw, match)
    if fingerprint_schema != 10 or "source/configuration identity differs" in identity_reason:
        result["state"] = "raw_reissue_required"
    result["reason"] = identity_reason or "saved source-record identity is not current"
    return result


def source_record_scan_lock_observation() -> tuple[dict[str, object] | None, str]:
    """Read the raw producer's repository-wide scan lock without taking it.

    The lock lives with the producer because its children inherit the lock file
    descriptor through isolated Lean work.  The planner only needs the
    producer's read-only observation after it has already established that a
    raw reissue is necessary.  This avoids queueing a current receipt behind
    unrelated work while preventing a lost terminal stream from looking like a
    second safe raw-reissue action.
    """

    helper = ROOT / FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE
    if not helper.is_file():
        return None, "source-record lock observer is unavailable"
    command = [
        sys.executable,
        str(helper),
        "--root",
        str(ROOT),
        "--lock-status",
    ]
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=SOURCE_RECORD_LOCK_STATUS_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return None, "source-record lock observer timed out"
    except OSError as exc:
        return None, "could not start source-record lock observer: " + str(exc)
    if proc.returncode != 0:
        detail = " ".join((proc.stderr or proc.stdout or "").splitlines()[-3:])
        return (
            None,
            "source-record lock observer returned a nonzero exit status"
            + (f": {detail}" if detail else ""),
        )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        detail = " ".join((proc.stderr or proc.stdout or "").splitlines()[-3:])
        return (
            None,
            "source-record lock observer returned invalid JSON"
            + (f": {detail}" if detail else ""),
        )
    if not isinstance(payload, Mapping):
        return None, "source-record lock observer returned a non-object"
    if payload.get("schema") != SOURCE_RECORD_LOCK_STATUS_SCHEMA:
        return None, "source-record lock observer returned an unsupported schema"
    held = payload.get("held")
    state = str(payload.get("state") or "").strip()
    if not isinstance(held, bool):
        return None, "source-record lock observer did not provide a boolean held field"
    if held and state != "held":
        return None, "source-record lock observer reported inconsistent held state"
    if not held and state not in {"absent", "available"}:
        return None, "source-record lock observer reported unavailable lock state"
    return dict(payload), ""


def _closeout_raw_reissue_lock_path() -> Path:
    """Return the operational lease used by normal raw-reissue wrappers."""

    return ROOT / CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH


def _closeout_raw_reissue_lock_metadata(
    paper: str, *, operation_id: str = ""
) -> dict[str, object]:
    """Return advisory holder metadata for a transition-serialization lease."""

    metadata: dict[str, object] = {
        "schema": CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
        "paper": paper,
        "operation": "freeze_then_raw_reissue",
    }
    if operation_id:
        metadata["operation_id"] = operation_id
    return metadata


def _try_acquire_closeout_raw_reissue_lock(
    paper: str, *, operation_id: str = ""
) -> tuple[object | None, str]:
    """Take the normal-wrapper lease without waiting behind another paper.

    This is an operational single-flight lock, separate from the raw
    producer's evidence lock.  It closes the window between a planner's
    lock observation and the producer invocation, so two closeout wrappers
    cannot both preserve the same kind of predecessor and then race to start
    an exclusive raw scan.  Direct producer invocations still remain guarded
    by the producer-owned evidence lock below.
    """

    path = _closeout_raw_reissue_lock_path()
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        handle = path.open("a+", encoding="utf-8")
    except OSError as exc:
        return None, "could not open closeout raw-reissue transition lock: " + str(exc)
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        handle.close()
        return None, ""
    except OSError as exc:
        handle.close()
        return None, "could not acquire closeout raw-reissue transition lock: " + str(exc)
    try:
        handle.seek(0)
        handle.truncate()
        handle.write(
            json.dumps(
                _closeout_raw_reissue_lock_metadata(paper, operation_id=operation_id),
                sort_keys=True,
            )
        )
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    except OSError as exc:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        finally:
            handle.close()
        return None, "could not record closeout raw-reissue transition lease: " + str(exc)
    return handle, ""


def _release_closeout_raw_reissue_lock(handle: object) -> None:
    """Release one best-effort transition lease after its raw action ends."""

    if not hasattr(handle, "fileno"):
        return
    try:
        try:
            handle.seek(0)
            handle.truncate()
            handle.flush()
            os.fsync(handle.fileno())
        except OSError:
            pass
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        handle.close()


def closeout_raw_reissue_lock_observation() -> tuple[dict[str, object] | None, str]:
    """Observe the normal-wrapper lease without treating metadata as evidence."""

    return closeout_raw_reissue_wrapper_lease_observation(ROOT)


def _replan_after_closeout_raw_reissue_action(paper: str) -> dict[str, Any]:
    """Return the non-accepting recovery action after a wrapper lease race."""

    replan_argv = ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper]
    return {
        "id": "replan_after_closeout_raw_reissue",
        "state": "ready_now",
        "required": True,
        "argv": replan_argv,
        "command": shlex.join(replan_argv),
        "reason": (
            "a concurrent raw-reissue wrapper may have completed or changed this "
            "paper's recovery state; replan from current evidence instead of "
            "reusing the stale transition decision"
        ),
    }


def _raw_reissue_operation_recovery_action(
    paper: str, operation_state: Mapping[str, object]
) -> dict[str, Any]:
    """Require an explicit decision for a prior interrupted raw operation."""

    status_argv = [
        "python3",
        "scripts/closeout_reuse_plan.py",
        "--paper",
        paper,
        "--raw-reissue-status",
    ]
    recover_argv = [
        "python3",
        "scripts/closeout_reuse_plan.py",
        "--paper",
        paper,
        "--acknowledge-stale-raw-reissue-operation",
    ]
    state = str(operation_state.get("state") or "invalid")
    return {
        "id": "recover_raw_reissue_operation",
        "state": "ready_now",
        "required": True,
        "argv": status_argv,
        "command": shlex.join(status_argv),
        "after_inspection": {
            "id": "acknowledge_stale_raw_reissue_operation",
            "argv": recover_argv,
            "command": shlex.join(recover_argv),
        },
        "reason": (
            "the prior raw-reissue operation is "
            + state
            + "; inspect its durable receipt and current locks, then explicitly "
            "acknowledge it only when no scan remains active. The wrapper will not "
            "overwrite an uncertain operation or repeat its raw scan automatically"
            + (
                ": " + str(operation_state.get("reason") or "")
                if operation_state.get("reason")
                else ""
            )
        ),
    }


def _inspect_closeout_raw_reissue_transition_lock_action(
    reason: str,
) -> dict[str, Any]:
    """Return a concrete repair action when the wrapper lease is unreadable."""

    return {
        "id": "inspect_closeout_raw_reissue_transition_lock",
        "state": "ready_now",
        "required": True,
        "reason": (
            "could not establish whether another closeout raw-reissue wrapper "
            "is active; inspect the transition lock before preserving raw evidence: "
            + reason
        ),
    }


def closeout_raw_reissue_lock_action(paper: str) -> dict[str, Any] | None:
    """Stop before competing closeout wrappers create duplicate transitions."""

    observation, observation_error = closeout_raw_reissue_lock_observation()
    if observation_error:
        return _inspect_closeout_raw_reissue_transition_lock_action(observation_error)
    assert observation is not None
    if observation.get("held") is not True:
        return None
    return {
        "id": "wait_for_closeout_raw_reissue",
        "state": "waiting",
        "required": True,
        "closeout_raw_reissue_lock": observation,
        "after_wait": _replan_after_closeout_raw_reissue_action(paper),
        "reason": (
            "another closeout raw-reissue wrapper owns the transition lease; "
            "wait for its terminal result, then replan instead of preserving a "
            "second predecessor or starting a competing scan"
        ),
    }


def raw_reissue_transition_lock_action(paper: str) -> dict[str, Any] | None:
    """Return the first operational or producer lock boundary for a raw action."""

    return closeout_raw_reissue_lock_action(paper) or source_record_reissue_lock_action(
        paper
    )


def source_record_reissue_lock_action(paper: str) -> dict[str, Any] | None:
    """Return a non-executable stop when a stale raw cannot start safely."""

    observation, observation_error = source_record_scan_lock_observation()
    if observation_error:
        return {
            "id": "inspect_source_record_scan_lock",
            "state": "ready_now",
            "required": True,
            "reason": (
                "could not establish whether the repository-wide source-record "
                "scan lock is available; inspect it before preserving or replacing "
                "raw evidence: " + observation_error
            ),
        }
    assert observation is not None
    if observation.get("held") is not True:
        return None
    replan_argv = ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper]
    return {
        "id": "wait_for_source_record_scan",
        "state": "waiting",
        "required": True,
        "source_record_lock": observation,
        "after_wait": {
            "id": "replan_after_source_record_scan",
            "argv": replan_argv,
            "command": shlex.join(replan_argv),
        },
        "reason": (
            "another repository source-record scan owns the exclusive lock; do not "
            "preserve or replace raw evidence while it runs"
        ),
    }


def _reset_closeout_wave_engine_snapshot_action(
    paper: str, *, reason: str
) -> dict[str, Any]:
    """Require an explicit new engine wave before another raw reissue."""

    reset_argv = [
        "python3",
        "scripts/closeout_reuse_plan.py",
        "--paper",
        paper,
        "--reset-closeout-wave-engine-snapshot",
    ]
    return {
        "id": "reset_closeout_wave_engine_snapshot",
        "state": "ready_now",
        "required": True,
        "argv": reset_argv,
        "command": shlex.join(reset_argv),
        "reason": (
            "start a deliberate new closeout engine wave before another raw "
            "reissue; this preserves the prior wave's evidence rather than "
            "silently repeating it after an engine transition"
            + (f": {reason}" if reason else "")
        ),
    }


def closeout_wave_engine_action(paper: str) -> dict[str, Any] | None:
    """Stop stale-wave raw work before observing the producer lock."""

    wave_state = closeout_wave_engine_snapshot_state(ROOT)
    state = str(wave_state.get("state") or "").strip()
    if state in {"not_started", "current"}:
        return None
    reason = str(wave_state.get("reason") or "").strip()
    if state == "engine_registration_required":
        return {
            "id": "inspect_engine_registration",
            "state": "ready_now",
            "required": True,
            "reason": reason
            or "the registered formalization engine cannot be read for this wave",
        }
    return _reset_closeout_wave_engine_snapshot_action(paper, reason=reason)


def source_record_preflight_action(
    paper: str, preflight: Mapping[str, Any]
) -> dict[str, Any] | None:
    """Convert a non-accepting preflight state into one ordered manual action."""

    state = str(preflight.get("state") or "").strip()
    reason = str(preflight.get("reason") or "").strip()
    if state in {
        "current_raw_judgment_bound",
        "current_v11_direct_semantic_review",
    }:
        return None
    if state == "current_raw_judgment_delta":
        return {
            "id": "review_current_source_record_delta",
            "state": "ready_now",
            "required": True,
            "reason": (
                "the raw source-record receipt is current, but its configured "
                "judgment sidecar is not bound to that receipt; review and bind "
                "only the current semantic delta before replanning"
            ),
        }
    if state == "current_raw_judgment_rebuild_required":
        return {
            "id": "rebuild_current_source_record_judgments",
            "state": "ready_now",
            "required": True,
            "reason": (
                "the raw source-record receipt is current, but the configured "
                "judgment sidecar is absent, unreadable, or malformed; create and "
                "review a complete sidecar bound to that exact current raw receipt "
                "before replanning"
                + (f": {reason}" if reason else "")
            ),
        }
    if state == "current_raw_semantic_repair_required":
        return {
            "id": "repair_current_source_record_semantic_surface",
            "state": "ready_now",
            "required": True,
            "reason": (
                "the raw source/configuration identity is current and every "
                "transport/completeness metadata check passed, but its generated "
                "semantic surface has a concrete invalidity; repair that surface "
                "or install an independently authenticated structural replay "
                "where the evidence protocol permits it, then replan without "
                "reissuing unchanged raw inputs"
                + (f": {reason}" if reason else "")
            ),
        }
    if state == "raw_reissue_required":
        wave_action = closeout_wave_engine_action(paper)
        if wave_action is not None:
            return wave_action
        lock_action = raw_reissue_transition_lock_action(paper)
        if lock_action is not None:
            return lock_action
        reissue_argv = [
            "python3",
            "scripts/closeout_reuse_plan.py",
            "--paper",
            paper,
            "--execute-freeze-raw-reissue",
        ]
        replan_argv = ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper]
        return {
            "id": "freeze_then_raw_reissue",
            "state": "ready_now",
            "required": True,
            "argv": reissue_argv,
            "command": shlex.join(reissue_argv),
            "after_success": {
                "id": "replan_after_raw_reissue",
                "argv": replan_argv,
                "command": shlex.join(replan_argv),
            },
            "reason": (
                "freeze paper-interface/map/source-model edits, then issue one "
                "new raw source-record receipt and review only its semantic delta"
                + (f": {reason}" if reason else "")
            ),
        }
    return {
        "id": "inspect_saved_source_record_identity",
        "state": "ready_now",
        "required": True,
        "reason": (
            "the bounded source-record preflight could not classify the saved "
            "receipt as current or safely stale; inspect its structural identity "
            "before scheduling a build or raw reissue"
            + (f": {reason}" if reason else "")
        ),
    }


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _paper_local_reissue_path(folder: Path, value: object) -> Path | None:
    """Resolve one preflight path only when it stays inside this paper."""

    raw_path = str(value or "").strip()
    if not raw_path:
        return None
    candidate = Path(raw_path)
    if not candidate.is_absolute():
        candidate = ROOT / candidate
    try:
        resolved = candidate.resolve()
        resolved.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved


def _normalized_raw_reissue_folder(folder: Path) -> Path:
    """Normalize a paper folder before any recovery artifact is written."""

    candidate = folder if folder.is_absolute() else ROOT / folder
    try:
        resolved = candidate.resolve()
        resolved.relative_to(ROOT.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise RuntimeError(
            "raw-reissue paper folder must resolve inside the repository"
        ) from exc
    return resolved


def _archive_raw_reissue_predecessors(
    folder: Path, preflight: Mapping[str, Any]
) -> tuple[Path, dict[str, object]]:
    """Preserve only the replaceable raw/sidecar bytes before a raw scan.

    These ignored hard-link snapshots are recovery material, never human
    judgment evidence or a closeout credential.  A later semantic-delta
    reviewer must deliberately select durable predecessor provenance rather
    than relying on this transient operational trace.
    """

    folder = _normalized_raw_reissue_folder(folder)
    trace_dir = folder / ".review_traces" / RAW_REISSUE_TRACE_DIRECTORY
    try:
        trace_dir.relative_to(ROOT.resolve())
    except ValueError as exc:  # Defensive: folder containment above should imply this.
        raise RuntimeError("raw-reissue trace directory is outside the repository") from exc

    entries: list[dict[str, object]] = []
    snapshots: list[tuple[Path, Path, str]] = []
    for role, field in (
        ("raw", "raw_path"),
        ("judgment", "judgment_path"),
    ):
        source = _paper_local_reissue_path(folder, preflight.get(field))
        if source is None or not source.is_file():
            entries.append({"role": role, "state": "unavailable"})
            continue
        digest = _file_sha256(source)
        destination = trace_dir / f"{role}-{digest}.json"
        try:
            source_relative = source.relative_to(ROOT.resolve())
            destination_relative = destination.relative_to(ROOT.resolve())
        except ValueError as exc:
            raise RuntimeError(
                "raw-reissue predecessor source or destination is outside the repository"
            ) from exc
        if destination.exists():
            if _file_sha256(destination) != digest:
                raise RuntimeError(
                    f"existing raw-reissue snapshot has unexpected bytes: {destination}"
                )
        else:
            snapshots.append((source, destination, digest))
        entries.append(
            {
                "role": role,
                "state": "preserved",
                "source_path": str(source_relative),
                "sha256": digest,
                "snapshot_path": str(destination_relative),
            }
        )
    identity = _digest({"paper": folder.name, "entries": entries})
    receipt_path = trace_dir / f"predecessor-{identity}.json"
    try:
        receipt_path.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise RuntimeError("raw-reissue predecessor receipt is outside the repository") from exc
    receipt: dict[str, object] = {
        "schema": RAW_REISSUE_TRACE_SCHEMA,
        "paper": folder.name,
        "acceptance_credential": False,
        "operational_recovery_only": True,
        "preflight_state": str(preflight.get("state") or ""),
        "preflight_reason": str(preflight.get("reason") or ""),
        "entries": entries,
    }

    # Validate every path, digest, and pre-existing snapshot before producing
    # even the trace directory. A receipt is written last, and only newly made
    # snapshots are removed on a failed transaction; pre-existing recovery
    # material remains immutable.
    created: list[Path] = []
    try:
        trace_dir.mkdir(parents=True, exist_ok=True)
        for source, destination, digest in snapshots:
            try:
                os.link(source, destination)
            except OSError:
                if destination.exists():
                    raise RuntimeError(
                        "raw-reissue predecessor snapshot appeared during "
                        f"publication: {destination}"
                    )
                # Cross-device worktrees are uncommon, but recovery must not
                # silently disappear when hard links are unavailable.
                try:
                    shutil.copyfile(source, destination)
                except OSError:
                    # A failed copy can leave a partial destination. It was
                    # absent during the full prevalidation pass, so this
                    # wrapper owns its cleanup under the transition lease.
                    try:
                        destination.unlink()
                    except OSError:
                        pass
                    raise
            created.append(destination)
            if _file_sha256(destination) != digest:
                raise RuntimeError(
                    "raw-reissue predecessor copy did not preserve "
                    f"{destination.name} bytes"
                )
        atomic_write_json(receipt_path, receipt)
    except Exception:
        for destination in reversed(created):
            try:
                destination.unlink()
            except OSError:
                pass
        raise
    return receipt_path, receipt


def raw_reissue_operation_receipt_path(folder: Path) -> Path:
    """Return the one mutable, non-evidence terminal receipt for a raw action."""

    normalized = _normalized_raw_reissue_folder(folder)
    path = closeout_raw_reissue_operation_receipt_path(ROOT, normalized.name)
    if path is None:
        raise RuntimeError("raw-reissue operation receipt is outside the repository")
    return path


def _bounded_operational_text(value: object, *, limit: int = 4096) -> str:
    """Keep recovery receipts useful without copying multi-megabyte tool logs."""

    normalized = " ".join(str(value or "").split())
    if len(normalized) <= limit:
        return normalized
    return normalized[: max(limit - 20, 0)] + " [truncated]"


def _raw_reissue_preflight_projection(value: Mapping[str, Any] | None) -> dict[str, object]:
    """Keep only bounded identity/status fields in an operational receipt."""

    if not isinstance(value, Mapping):
        return {}
    projection: dict[str, object] = {}
    for key in (
        "state",
        "raw_audit_sha256",
        "judgment_audit_sha256",
        "raw_fingerprint_schema",
        "observed_source_record_audit_sha256",
        "observed_source_record_fingerprint_schema",
    ):
        if key in value:
            projection[key] = value[key]
    reason = _bounded_operational_text(value.get("reason"))
    if reason:
        projection["reason"] = reason
    return projection


def _raw_reissue_preflight_guard(value: Mapping[str, Any] | None) -> str:
    """Hash the receipt-bound inputs that must survive the wrapper-lease race.

    The full preflight includes explanatory text and may grow with new
    diagnostics.  This intentionally small projection carries the saved raw
    pair, the producer's source/configuration identity, and authenticated
    replay state.  A mismatch stops before predecessor preservation; it never
    converts a changed paper into a second automatic raw scan.
    """

    if not isinstance(value, Mapping):
        return ""
    projection = {
        key: value.get(key)
        for key in (
            "state",
            "raw_path",
            "judgment_path",
            "configured_raw_is_canonical",
            "raw_audit_sha256",
            "judgment_audit_sha256",
            "raw_fingerprint_schema",
            "identity",
            "semantic_contract_revalidation",
        )
        if key in value
    }
    return _digest(projection)


def _raw_reissue_next_action_projection(value: object) -> dict[str, object] | None:
    if not isinstance(value, Mapping):
        return None
    projection: dict[str, object] = {}
    for key in ("id", "state", "required"):
        if key in value:
            projection[key] = value[key]
    reason = _bounded_operational_text(value.get("reason"), limit=1024)
    if reason:
        projection["reason"] = reason
    return projection or None


def _raw_reissue_operation_terminal_state(result: Mapping[str, object]) -> str:
    state = str(result.get("state") or "")
    if state == "raw_reissue_completed":
        return "completed"
    if result.get("raw_scan_started") is True:
        return "failed"
    return "stopped"


def _write_raw_reissue_operation_receipt(
    path: Path, payload: Mapping[str, Any]
) -> None:
    """Write the mutable operational receipt through the repository atomic writer."""

    atomic_write_json(path, payload)


def _start_raw_reissue_operation_receipt(
    folder: Path,
    *,
    paper: str,
    preflight: Mapping[str, Any],
    wave_snapshot: Mapping[str, Any],
    command: list[str],
    operation_id: str,
) -> tuple[Path, dict[str, object]]:
    """Persist a running marker before predecessor preservation or a raw scan."""

    prior_state = closeout_raw_reissue_operation_receipt_state(ROOT, paper)
    if str(prior_state.get("state") or "") in {"running", "invalid"}:
        raise RuntimeError(
            "raw-reissue operation recovery is required before replacing its "
            + str(prior_state.get("state") or "unknown")
            + " receipt"
        )
    path = raw_reissue_operation_receipt_path(folder)
    try:
        relative_path = path.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise RuntimeError("raw-reissue operation receipt is outside the repository") from exc
    payload: dict[str, object] = {
        "schema": RAW_REISSUE_OPERATION_TRACE_SCHEMA,
        "kind": "source_record_raw_reissue_operation",
        "acceptance_credential": False,
        "operational_recovery_only": True,
        "operation_id": operation_id,
        "paper": paper,
        "state": "running",
        "started_at": utc_now(),
        "preflight": _raw_reissue_preflight_projection(preflight),
        "engine_registration": dict(wave_snapshot["engine_registration"]),
        "wave_id": str(wave_snapshot["wave_id"]),
        "command": list(command),
        "receipt_path": str(relative_path),
    }
    _write_raw_reissue_operation_receipt(path, payload)
    return path, payload


def _finish_raw_reissue_operation_receipt(
    path: Path,
    payload: Mapping[str, Any],
    result: Mapping[str, object],
) -> None:
    """Replace the running marker with one bounded terminal operation result."""

    terminal = dict(payload)
    terminal.update(
        {
            "state": _raw_reissue_operation_terminal_state(result),
            "finished_at": utc_now(),
            "wrapper_state": str(result.get("state") or "unknown"),
            "raw_scan_started": result.get("raw_scan_started") is True,
        }
    )
    if isinstance(result.get("producer_exit_code"), int):
        terminal["producer_exit_code"] = result["producer_exit_code"]
    predecessor_snapshot = str(result.get("predecessor_snapshot") or "").strip()
    if predecessor_snapshot:
        terminal["predecessor_snapshot"] = predecessor_snapshot
    postflight = result.get("postflight")
    if isinstance(postflight, Mapping):
        terminal["postflight"] = _raw_reissue_preflight_projection(postflight)
    next_action = _raw_reissue_next_action_projection(result.get("next_action"))
    if next_action is not None:
        terminal["next_action"] = next_action
    reason = _bounded_operational_text(result.get("reason"))
    if reason:
        terminal["reason"] = reason
    producer_detail = _bounded_operational_text(result.get("producer_detail"))
    if producer_detail:
        terminal["producer_detail"] = producer_detail
    _write_raw_reissue_operation_receipt(path, terminal)


def _raw_reissue_material_errors(folder: Path) -> list[str]:
    """Reject deterministic later planner blockers before a raw scan."""

    audit = folder / "audit"
    paths = [
        audit / "statement_match_llm.json",
        audit / "paper_coverage_llm.json",
        audit / "paper_statement_map.json",
        audit / "source_proof_fidelity.json",
    ]
    _payloads, _material, errors = _captured_json_payloads(paths)
    return errors


def execute_freeze_then_raw_reissue(folder: Path) -> int:
    """Run the one machine-safe raw-reissue transition for a frozen paper.

    This wrapper owns only raw evidence generation.  It never creates,
    approves, or binds a judgment sidecar, so a replan still stops at the
    semantically appropriate delta/reconstruction action.
    """

    paper = folder.name
    result: dict[str, object] = {
        "schema": 1,
        "paper": paper,
        "acceptance_credential": False,
        "operation": "freeze_then_raw_reissue",
    }
    operation_receipt_path: Path | None = None
    operation_receipt_payload: dict[str, object] | None = None
    operation_receipt_finalized = False

    def finish(exit_code: int) -> int:
        """Persist the terminal operational state before exposing this result."""

        nonlocal operation_receipt_finalized
        if (
            operation_receipt_path is not None
            and operation_receipt_payload is not None
            and not operation_receipt_finalized
        ):
            try:
                _finish_raw_reissue_operation_receipt(
                    operation_receipt_path, operation_receipt_payload, result
                )
            except OSError as exc:
                # The raw may have completed, but a lost terminal receipt makes
                # that fact unsafe to rely on. Do not print a success result.
                result.update(
                    {
                        "state": "raw_reissue_operation_receipt_finalization_failed",
                        "reason": "could not persist terminal raw-reissue operation receipt: "
                        + str(exc),
                    }
                )
                exit_code = 2
            operation_receipt_finalized = True
        print(json.dumps(result, indent=2, sort_keys=True))
        return exit_code

    active = running_execution_summary(closeout_worker_state_path(paper))
    if active is None:
        active = running_execution_summary(default_closeout_execution_path(ROOT, paper))
    if active is not None:
        result.update(
            {
                "state": "closeout_already_running",
                "active_execution": active,
                "reason": "do not replace raw evidence while a strict closeout is active",
            }
        )
        return finish(2)
    _prior, recovery_error, recovery_namespace, recovery_path = (
        effective_closeout_execution_state(ROOT, paper)
    )
    if recovery_error:
        result.update(
            {
                "state": "closeout_recovery_required",
                "execution_namespace": recovery_namespace,
                "execution_path": str(recovery_path.relative_to(ROOT)),
                "reason": recovery_error,
            }
        )
        return finish(2)

    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        result.update({"state": "engine_registration_required", "reason": engine_error})
        return finish(2)
    status, status_error = _paper_closeout_status_preflight(folder)
    if status_error:
        result.update(
            {
                "state": "paper_closeout_eligibility_required",
                "paper_status": status,
                "reason": status_error,
            }
        )
        return finish(2)
    readiness = static_closeout_readiness(folder)
    if readiness.get("ready") is not True:
        result.update(
            {
                "state": "static_closeout_readiness_required",
                "readiness_matrix": readiness,
                "reason": "deterministic paper-local closeout inputs are incomplete",
            }
        )
        return finish(2)
    material_errors = _raw_reissue_material_errors(folder)
    if material_errors:
        result.update(
            {
                "state": "audit_material_readiness_required",
                "reason": " ; ".join(material_errors),
            }
        )
        return finish(2)

    preflight = fast_saved_source_record_preflight(folder)
    result["preflight"] = preflight
    state = str(preflight.get("state") or "")
    if state in {"current_raw_judgment_bound", "current_v11_direct_semantic_review"}:
        result.update({"state": "already_current", "raw_scan_started": False})
        return finish(0)
    if state != "raw_reissue_required":
        result.update(
            {
                "state": "raw_reissue_not_applicable",
                "next_action": source_record_preflight_action(paper, preflight),
            }
        )
        return finish(2)

    wave_action = closeout_wave_engine_action(paper)
    if wave_action is not None:
        result.update(
            {
                "state": "closeout_wave_engine_reset_required",
                "raw_scan_started": False,
                "next_action": wave_action,
            }
        )
        return finish(2)

    lock_action = closeout_raw_reissue_lock_action(paper)
    if lock_action is not None:
        result.update(
            {
                "state": (
                    "raw_reissue_deferred_by_closeout_raw_reissue"
                    if lock_action.get("id") == "wait_for_closeout_raw_reissue"
                    else "closeout_raw_reissue_lock_inspection_required"
                ),
                "raw_scan_started": False,
                "next_action": lock_action,
            }
        )
        return finish(2)

    operation_id = str(uuid4())
    transition_lease, transition_lease_error = _try_acquire_closeout_raw_reissue_lock(
        paper, operation_id=operation_id
    )
    if transition_lease is None:
        if transition_lease_error:
            inspection_action = _inspect_closeout_raw_reissue_transition_lock_action(
                transition_lease_error
            )
            result.update(
                {
                    "state": "closeout_raw_reissue_lock_inspection_required",
                    "raw_scan_started": False,
                    "reason": transition_lease_error,
                    "next_action": inspection_action,
                }
            )
        else:
            # A concurrent wrapper claimed the lease after our observation.
            # Re-read its advisory state for a useful, non-accepting wait
            # action, but never archive a predecessor in this race branch.
            deferred_action = (
                closeout_raw_reissue_lock_action(paper)
                or _replan_after_closeout_raw_reissue_action(paper)
            )
            result.update(
                {
                    "state": "raw_reissue_deferred_by_closeout_raw_reissue",
                    "raw_scan_started": False,
                    "next_action": deferred_action,
                }
            )
        return finish(2)

    try:
        # A direct producer invocation can still acquire the producer-owned
        # evidence lock independently of the normal-wrapper lease. Recheck it
        # while owning the wrapper lease, before preserving any predecessor.
        lock_action = source_record_reissue_lock_action(paper)
        if lock_action is not None:
            result.update(
                {
                    "state": (
                        "raw_reissue_deferred_by_source_record_scan"
                        if lock_action.get("id") == "wait_for_source_record_scan"
                        else "source_record_scan_lock_inspection_required"
                    ),
                    "raw_scan_started": False,
                    "next_action": lock_action,
                }
            )
            return finish(2)

        helper = ROOT / FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE
        if not helper.is_file():
            result.update(
                {
                    "state": "raw_reissue_helper_unavailable",
                    "raw_scan_started": False,
                    "reason": f"source-record producer is unavailable: {helper}",
                }
            )
            return finish(2)

        # The initial observation preceded the wrapper lease. Re-read the
        # bounded identity while serialized, so a just-completed competing
        # transition or a paper-input edit cannot be archived as our stale
        # predecessor. A changed guard always stops for a fresh plan.
        leased_preflight = fast_saved_source_record_preflight(folder)
        result["preflight_after_lease"] = leased_preflight
        if _raw_reissue_preflight_guard(leased_preflight) != _raw_reissue_preflight_guard(
            preflight
        ):
            result.update(
                {
                    "state": "raw_reissue_preflight_changed",
                    "raw_scan_started": False,
                    "reason": (
                        "the saved raw/source-configuration identity changed after "
                        "the raw-reissue decision and before predecessor preservation"
                    ),
                    "next_action": _replan_after_closeout_raw_reissue_action(paper),
                }
            )
            return finish(2)

        operation_state = closeout_raw_reissue_operation_receipt_state(ROOT, paper)
        if str(operation_state.get("state") or "") in {"running", "invalid"}:
            result.update(
                {
                    "state": "raw_reissue_operation_recovery_required",
                    "raw_scan_started": False,
                    "operation_state": operation_state,
                    "next_action": _raw_reissue_operation_recovery_action(
                        paper, operation_state
                    ),
                }
            )
            return finish(2)

        wave_snapshot, wave_created, wave_error = (
            ensure_closeout_wave_engine_snapshot(ROOT)
        )
        if wave_snapshot is None:
            wave_action = closeout_wave_engine_action(paper)
            result.update(
                {
                    "state": "closeout_wave_engine_reset_required",
                    "raw_scan_started": False,
                    "reason": wave_error
                    or "could not bind the current closeout engine wave",
                    "next_action": wave_action
                    or _reset_closeout_wave_engine_snapshot_action(
                        paper, reason=wave_error
                    ),
                }
            )
            return finish(2)
        result["closeout_wave_engine"] = {
            "wave_id": wave_snapshot["wave_id"],
            "snapshot_created": wave_created,
            "engine_registration": wave_snapshot["engine_registration"],
        }
        command = [
            sys.executable,
            str(helper),
            "--root",
            str(ROOT),
            "--paper",
            paper,
            "--closeout-raw-reissue",
            "--closeout-raw-reissue-operation-id",
            operation_id,
        ]
        try:
            operation_receipt_path, operation_receipt_payload = (
                _start_raw_reissue_operation_receipt(
                    folder,
                    paper=paper,
                    preflight=leased_preflight,
                    wave_snapshot=wave_snapshot,
                    command=command,
                    operation_id=operation_id,
                )
            )
        except (OSError, RuntimeError) as exc:
            result.update(
                {
                    "state": "raw_reissue_operation_receipt_start_failed",
                    "raw_scan_started": False,
                    "reason": str(exc),
                }
            )
            return finish(2)
        result["operation_receipt"] = str(operation_receipt_path.relative_to(ROOT))

        try:
            predecessor_path, predecessor = _archive_raw_reissue_predecessors(
                folder, leased_preflight
            )
        except (OSError, RuntimeError) as exc:
            result.update(
                {"state": "predecessor_preservation_failed", "reason": str(exc)}
            )
            return finish(2)
        result["predecessor_snapshot"] = str(predecessor_path.relative_to(ROOT))
        result["predecessor_entries"] = predecessor["entries"]
        try:
            proc = subprocess.run(
                command,
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except OSError as exc:
            result.update({"state": "raw_reissue_start_failed", "reason": str(exc)})
            return finish(2)
        result["raw_scan_started"] = True
        result["producer_exit_code"] = proc.returncode
        if proc.returncode != 0:
            # The producer uses exit 4 both for a lock race and for an input-change
            # rejection. Reclassify only a currently held lock; every other exit-4
            # result stays an inspection failure rather than inviting an automatic
            # retry of a scan whose frozen inputs may have changed.
            if proc.returncode == 4:
                lock_action = source_record_reissue_lock_action(paper)
                if (
                    lock_action is not None
                    and lock_action.get("id") == "wait_for_source_record_scan"
                ):
                    result.update(
                        {
                            "state": "raw_reissue_deferred_by_source_record_scan",
                            "raw_scan_started": False,
                            "next_action": lock_action,
                        }
                    )
                    return finish(2)
            detail = " ".join((proc.stderr or proc.stdout or "").splitlines()[-4:])
            result.update(
                {
                    "state": "raw_reissue_failed",
                    "reason": detail or "source-record producer returned nonzero",
                    "producer_detail": detail,
                }
            )
            return finish(proc.returncode if proc.returncode > 0 else 2)

        post_wave = closeout_wave_engine_snapshot_state(ROOT)
        post_snapshot = post_wave.get("snapshot")
        if (
            post_wave.get("state") != "current"
            or not isinstance(post_snapshot, Mapping)
            or post_snapshot.get("wave_id") != wave_snapshot.get("wave_id")
            or post_snapshot.get("engine_registration")
            != wave_snapshot.get("engine_registration")
        ):
            wave_action = closeout_wave_engine_action(paper)
            result.update(
                {
                    "state": "raw_reissue_engine_transitioned_during_scan",
                    "reason": str(post_wave.get("reason") or "")
                    or "the closeout engine wave changed while the raw scan ran",
                    "next_action": wave_action
                    or _replan_after_closeout_raw_reissue_action(paper),
                }
            )
            return finish(2)

        postflight = fast_saved_source_record_preflight(folder)
        result["postflight"] = postflight
        post_state = str(postflight.get("state") or "")
        if post_state not in {
            "current_raw_judgment_bound",
            "current_v11_direct_semantic_review",
            "current_raw_judgment_delta",
            "current_raw_judgment_rebuild_required",
            "current_raw_semantic_repair_required",
        }:
            result.update(
                {
                    "state": "raw_reissue_postcondition_failed",
                    "reason": str(
                        postflight.get("reason") or "raw receipt is not current"
                    ),
                }
            )
            return finish(2)
        result.update(
            {
                "state": "raw_reissue_completed",
                "next_action": source_record_preflight_action(paper, postflight),
            }
        )
        return finish(0)
    except BaseException as exc:
        if (
            operation_receipt_path is not None
            and operation_receipt_payload is not None
            and not operation_receipt_finalized
        ):
            result.update(
                {
                    "state": "raw_reissue_aborted",
                    "reason": "unexpected raw-reissue wrapper interruption: "
                    + _bounded_operational_text(exc, limit=1024),
                }
            )
            try:
                _finish_raw_reissue_operation_receipt(
                    operation_receipt_path, operation_receipt_payload, result
                )
            except OSError:
                pass
            operation_receipt_finalized = True
        raise
    finally:
        _release_closeout_raw_reissue_lock(transition_lease)


def reset_closeout_wave_engine_snapshot_for_paper(folder: Path) -> int:
    """Explicitly start a new operational engine wave while raw work is idle."""

    paper = folder.name
    result: dict[str, object] = {
        "schema": 1,
        "paper": paper,
        "acceptance_credential": False,
        "operation": "reset_closeout_wave_engine_snapshot",
    }
    active = running_execution_summary(closeout_worker_state_path(paper))
    if active is None:
        active = running_execution_summary(default_closeout_execution_path(ROOT, paper))
    if active is not None:
        result.update(
            {
                "state": "closeout_already_running",
                "active_execution": active,
                "reason": "do not reset a closeout engine wave while strict closeout runs",
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        result.update({"state": "engine_registration_required", "reason": engine_error})
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    lock_action = closeout_raw_reissue_lock_action(paper)
    if lock_action is not None:
        result.update(
            {
                "state": "closeout_wave_engine_reset_deferred",
                "next_action": lock_action,
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    transition_lease, transition_lease_error = _try_acquire_closeout_raw_reissue_lock(
        paper
    )
    if transition_lease is None:
        action = (
            _inspect_closeout_raw_reissue_transition_lock_action(transition_lease_error)
            if transition_lease_error
            else _replan_after_closeout_raw_reissue_action(paper)
        )
        result.update(
            {
                "state": "closeout_wave_engine_reset_deferred",
                "reason": transition_lease_error,
                "next_action": action,
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    try:
        source_lock_action = source_record_reissue_lock_action(paper)
        if source_lock_action is not None:
            result.update(
                {
                    "state": "closeout_wave_engine_reset_deferred",
                    "next_action": source_lock_action,
                }
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 2
        snapshot, snapshot_error = reset_closeout_wave_engine_snapshot(ROOT)
        if snapshot is None:
            result.update(
                {
                    "state": "closeout_wave_engine_reset_failed",
                    "reason": snapshot_error,
                }
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 2
        result.update(
            {
                "state": "closeout_wave_engine_snapshot_reset",
                "wave_id": snapshot["wave_id"],
                "engine_registration": snapshot["engine_registration"],
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    finally:
        _release_closeout_raw_reissue_lock(transition_lease)


def raw_reissue_operation_status(folder: Path) -> int:
    """Diagnose a raw operation with receipt, locks, and current wave state."""

    paper = folder.name
    result: dict[str, object] = {
        "schema": 1,
        "paper": paper,
        "acceptance_credential": False,
        "diagnostic_only": True,
    }
    operation_state = closeout_raw_reissue_operation_receipt_state(ROOT, paper)
    result["operation_state"] = operation_state
    wrapper_lease, wrapper_error = closeout_raw_reissue_lock_observation()
    source_lock, source_error = source_record_scan_lock_observation()
    wave_state = closeout_wave_engine_snapshot_state(ROOT)
    if wrapper_error:
        result["wrapper_lease_error"] = wrapper_error
    else:
        result["wrapper_lease"] = wrapper_lease
    if source_error:
        result["source_record_lock_error"] = source_error
    else:
        result["source_record_lock"] = source_lock
    result["closeout_wave_engine"] = wave_state

    state = str(operation_state.get("state") or "invalid")
    if state == "not_started":
        result["state"] = "raw_reissue_not_started"
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    if state == "invalid":
        result.update(
            {
                "state": "raw_reissue_operation_receipt_inspection_required",
                "reason": str(operation_state.get("reason") or ""),
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    if state != "running":
        result["state"] = "raw_reissue_operation_status"
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0

    # A running receipt is live whenever either serializing lock remains held.
    # Do not infer liveness from a PID or a timestamp: both are advisory and
    # can outlive a process. An idle pair is instead an explicit recovery stop.
    locks_unknown = bool(wrapper_error or source_error)
    wrapper_held = isinstance(wrapper_lease, Mapping) and wrapper_lease.get("held") is True
    source_held = isinstance(source_lock, Mapping) and source_lock.get("held") is True
    if locks_unknown or wrapper_held or source_held:
        result["state"] = "raw_reissue_operation_running"
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    result.update(
        {
            "state": "raw_reissue_operation_recovery_required",
            "next_action": _raw_reissue_operation_recovery_action(
                paper, operation_state
            ),
            "reason": (
                "the raw-reissue operation is marked running but neither its "
                "wrapper lease nor the source-record scan lock is held"
            ),
        }
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2


def acknowledge_stale_raw_reissue_operation(folder: Path) -> int:
    """Explicitly terminalize an orphaned operation after proving both locks idle.

    This is recovery bookkeeping, not an audit action. It deliberately does
    not launch a scan, replace raw evidence, or mark a paper accepted; callers
    must replan from the resulting current receipt before another raw reissue.
    """

    paper = folder.name
    result: dict[str, object] = {
        "schema": 1,
        "paper": paper,
        "acceptance_credential": False,
        "operation": "acknowledge_stale_raw_reissue_operation",
    }
    operation_state = closeout_raw_reissue_operation_receipt_state(ROOT, paper)
    if str(operation_state.get("state") or "") != "running":
        result.update(
            {
                "state": "raw_reissue_operation_recovery_not_applicable",
                "operation_state": operation_state,
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    lock_action = closeout_raw_reissue_lock_action(paper)
    if lock_action is not None:
        result.update(
            {
                "state": "raw_reissue_operation_recovery_deferred",
                "next_action": lock_action,
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    recovery_operation_id = "recovery-" + str(uuid4())
    transition_lease, transition_lease_error = _try_acquire_closeout_raw_reissue_lock(
        paper, operation_id=recovery_operation_id
    )
    if transition_lease is None:
        result.update(
            {
                "state": "raw_reissue_operation_recovery_deferred",
                "reason": transition_lease_error,
                "next_action": (
                    _inspect_closeout_raw_reissue_transition_lock_action(
                        transition_lease_error
                    )
                    if transition_lease_error
                    else _replan_after_closeout_raw_reissue_action(paper)
                ),
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    try:
        source_lock_action = source_record_reissue_lock_action(paper)
        if source_lock_action is not None:
            result.update(
                {
                    "state": "raw_reissue_operation_recovery_deferred",
                    "next_action": source_lock_action,
                }
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 2
        operation_state = closeout_raw_reissue_operation_receipt_state(ROOT, paper)
        receipt = operation_state.get("receipt")
        if (
            str(operation_state.get("state") or "") != "running"
            or not isinstance(receipt, Mapping)
        ):
            result.update(
                {
                    "state": "raw_reissue_operation_recovery_replan_required",
                    "operation_state": operation_state,
                    "next_action": _replan_after_closeout_raw_reissue_action(paper),
                }
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 2
        recovered = dict(receipt)
        recovered.update(
            {
                "state": "stopped",
                "finished_at": utc_now(),
                "wrapper_state": "raw_reissue_recovery_acknowledged",
                "recovery_preflight": _raw_reissue_preflight_projection(
                    fast_saved_source_record_preflight(folder)
                ),
                "reason": (
                    "explicit recovery acknowledgement after observing no active "
                    "wrapper lease or source-record scan lock"
                ),
            }
        )
        try:
            _write_raw_reissue_operation_receipt(
                raw_reissue_operation_receipt_path(folder), recovered
            )
        except OSError as exc:
            result.update(
                {
                    "state": "raw_reissue_operation_recovery_write_failed",
                    "reason": str(exc),
                }
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 2
        result.update(
            {
                "state": "raw_reissue_operation_recovery_acknowledged",
                "operation_receipt": str(
                    raw_reissue_operation_receipt_path(folder).relative_to(ROOT)
                ),
                "next_action": _replan_after_closeout_raw_reissue_action(paper),
            }
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    finally:
        _release_closeout_raw_reissue_lock(transition_lease)


def _item_plan(
    raw_items: object,
    decisions: Mapping[str, Any],
    *,
    reusable_action: str,
    invalid_action: str,
    current_keys: set[str] | None = None,
    current_navigation_field: str = "",
) -> dict[str, dict[str, Any]]:
    """Report old, new, renamed, and retired items without name-based reuse."""

    items = raw_items if isinstance(raw_items, Mapping) else {}
    current_keys = current_keys or set()
    plan: dict[str, dict[str, Any]] = {}
    mapped_current_keys: set[str] = set()
    for raw_key, raw_item in items.items():
        key = str(raw_key).strip()
        if not key:
            continue
        decision = decisions.get(key)
        decision_map = decision if isinstance(decision, Mapping) else {}
        accepted = decision_map.get("accepted") is True
        bootstrap_required = accepted and decision_map.get("bootstrap_current") is True
        reason = (
            (
                "current audited evidence validates fully for this closeout; "
                "seal a future-reuse pin only at the next intentional semantic edit"
            )
            if bootstrap_required
            else "all semantic material and reviewer identities match uniquely"
            if accepted
            else str(
                decision_map.get("reason") or "item is malformed or has no decision"
            )
        )
        if not isinstance(raw_item, Mapping):
            accepted = False
            reason = "review item is not an object"
        plan[key] = {
            "action": reusable_action if accepted else invalid_action,
            "reusable": accepted,
            "reason": reason,
            **({"future_reuse_pin_missing": True} if bootstrap_required else {}),
        }
        if decision_map:
            for navigation_field in ("current_row", "current_source_item"):
                if decision_map.get(navigation_field):
                    plan[key][navigation_field] = decision_map[navigation_field]
            current_navigation = str(
                decision_map.get(current_navigation_field) or ""
            ).strip()
            if current_navigation:
                mapped_current_keys.add(current_navigation)
        if (
            not accepted
            and key not in current_keys
            and not str(decision_map.get(current_navigation_field) or "").strip()
        ):
            plan[key]["action"] = "retire_or_rebind_obsolete_review_item"
            plan[key]["retirement_candidate"] = True

    for current_key in sorted(current_keys - mapped_current_keys):
        existing = plan.get(current_key)
        if existing is not None:
            existing["action"] = invalid_action
            existing["reusable"] = False
            existing["reason"] = str(
                (
                    decisions.get(current_key)
                    if isinstance(decisions.get(current_key), Mapping)
                    else {}
                ).get("reason")
                or "current obligation has no accepted semantic reuse decision"
            )
            existing.pop("retirement_candidate", None)
            continue
        plan[current_key] = {
            "action": invalid_action,
            "reusable": False,
            "reason": "new current obligation has no prior semantic review item",
            "new_current_obligation": True,
        }
    return plan


def semantic_reuse_plan(
    *,
    statement_sidecar: Mapping[str, Any],
    coverage_sidecar: Mapping[str, Any],
    current_rows: list[Any],
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_statement_inventory: Mapping[str, Mapping[str, Any]],
    current_coverage_inventory: Mapping[str, Mapping[str, Any]],
    current_mode: str,
    current_anchor_errors: Mapping[str, list[str]],
    current_source_map: Mapping[str, Any],
    current_review_surface_sha256: str,
    current_source_proof_fidelity: Mapping[str, Any] | None,
    include_direct_expressions: bool = False,
) -> dict[str, Any]:
    statement_validator_supports_direct_expressions = (
        "include_direct_expressions"
        in inspect.signature(_statement_validator).parameters
    )
    statement_validators, statement_validator_errors = review_validator_identities(
        statement_sidecar,
        expected_prompt_version=review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
    )
    coverage_validators, coverage_validator_errors = review_validator_identities(
        coverage_sidecar,
        expected_prompt_version=(
            review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
        ),
    )
    _statement, _coverage, decisions = migrate_sidecars(
        statement_sidecar,
        coverage_sidecar,
        current_rows=current_rows,
        current_inventory=current_inventory,
        current_statement_inventory=current_statement_inventory,
        current_coverage_inventory=current_coverage_inventory,
        current_mode=current_mode,
        current_anchor_errors=current_anchor_errors,
        current_source_map=current_source_map,
        canonical_coverage_projection_validated=True,
        current_review_surface_sha256=current_review_surface_sha256,
        current_source_proof_fidelity=current_source_proof_fidelity,
        statement_validator_identities=statement_validators,
        coverage_validator_identities=coverage_validators,
        validate_statement=lambda entry, row, inventory: _validate_statement_for_plan(
            entry,
            row,
            inventory,
            include_direct_expressions=include_direct_expressions,
            supports_direct_expression_parameter=(
                statement_validator_supports_direct_expressions
            ),
        ),
        bootstrap_current=True,
    )
    statement_plan = _item_plan(
        statement_sidecar.get("items"),
        decisions.get("statement", {}),
        reusable_action="reuse_human_semantic_review",
        invalid_action="fresh_human_semantic_review",
        current_keys={
            str(row.name).strip() for row in current_rows if str(row.name).strip()
        },
        current_navigation_field="current_row",
    )
    coverage_plan = _item_plan(
        coverage_sidecar.get("items"),
        decisions.get("coverage", {}),
        reusable_action="reuse_source_coverage_review",
        invalid_action="fresh_source_coverage_review",
        current_keys={
            str(key).strip() for key in current_coverage_inventory if str(key).strip()
        },
        current_navigation_field="current_source_item",
    )
    return {
        "schema": 1,
        "acceptance_credential": False,
        "requires_fresh_strict_closeout": True,
        "statement": statement_plan,
        "coverage": coverage_plan,
        "summary": {
            "statement_reusable": sum(
                item["reusable"] for item in statement_plan.values()
            ),
            "statement_requires_review": sum(
                not item["reusable"] for item in statement_plan.values()
            ),
            "statement_future_reuse_pin_missing": sum(
                bool(item.get("future_reuse_pin_missing"))
                for item in statement_plan.values()
            ),
            "coverage_reusable": sum(
                item["reusable"] for item in coverage_plan.values()
            ),
            "coverage_requires_review": sum(
                not item["reusable"] for item in coverage_plan.values()
            ),
            "coverage_future_reuse_pin_missing": sum(
                bool(item.get("future_reuse_pin_missing"))
                for item in coverage_plan.values()
            ),
            "retirement_candidates": sum(
                bool(item.get("retirement_candidate"))
                for item in (*statement_plan.values(), *coverage_plan.values())
            ),
        },
        "validator_identity_errors": {
            "statement": statement_validator_errors,
            "coverage": coverage_validator_errors,
        },
        **(
            {"global_error": decisions["global_error"]}
            if decisions.get("global_error")
            else {}
        ),
    }


def closeout_action_schedule(
    paper: str,
    *,
    cache_reusable: bool,
    compiled_artifacts_ready: bool | None = None,
    summary: Mapping[str, Any] | None = None,
    global_error: str = "",
    validator_identity_errors: Mapping[str, Any] | None = None,
    plan_identity: str = "",
    prior_execution: Mapping[str, Any] | None = None,
    prior_execution_error: str = "",
    deep_paper_prose: bool = False,
    legacy_adoption: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Return a dependency-ordered operational schedule.

    Actions are scheduling advice, not acceptance evidence. Only the first
    ``ready_now`` action is executable; later actions make the required
    transition explicit so a cache refresh cannot accidentally skip replanning.
    """

    summary = summary or {}
    validator_identity_errors = validator_identity_errors or {}
    prior_execution = prior_execution or {}
    legacy_adoption = legacy_adoption or {}
    compiled_artifacts_ready = (
        cache_reusable if compiled_artifacts_ready is None else compiled_artifacts_ready
    )
    statement_review = int(summary.get("statement_requires_review") or 0)
    coverage_review = int(summary.get("coverage_requires_review") or 0)
    statement_unsealed = int(summary.get("statement_future_reuse_pin_missing") or 0)
    coverage_unsealed = int(summary.get("coverage_future_reuse_pin_missing") or 0)
    validator_errors = sum(
        len(value) if isinstance(value, list) else bool(value)
        for value in validator_identity_errors.values()
    )
    semantic_ready = _semantic_reuse_ready(
        cache_reusable=cache_reusable,
        summary=summary,
        global_error=global_error,
        validator_identity_errors=validator_identity_errors,
    )
    state_path = closeout_worker_state_path(paper)
    actions: list[dict[str, Any]] = []

    def add_action(
        action_id: str,
        argv: list[str],
        *,
        state: str,
        reason: str,
        **extra: Any,
    ) -> None:
        actions.append(
            {
                "id": action_id,
                "state": state,
                "required": True,
                "argv": argv,
                "command": shlex.join(argv),
                "reason": reason,
                **extra,
            }
        )

    if not cache_reusable:
        add_action(
            "paper_build",
            ["env", "LEAN_NUM_THREADS=1", "lake", "build", paper],
            state="ready_now",
            reason="compile the frozen paper once before creating a new manifest cache",
        )
        add_action(
            "fresh_manifest_batch",
            [
                "python3",
                "scripts/refresh_closeout_manifest_cache.py",
                "--paper",
                paper,
            ],
            state="after_paper_build",
            reason=(
                "project the independently validated current raw-manifest batch into "
                "the dashboard cache; exact roots reuse the raw batch and only "
                "context misses require fresh Lean"
            ),
        )
        add_action(
            "replan_after_manifest",
            ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper],
            state="after_manifest_refresh",
            reason="recompute item-level reuse from the newly frozen manifest snapshot",
        )
    elif global_error or validator_errors or statement_review or coverage_review:
        add_action(
            "inspect_invalid_semantic_items",
            ["python3", "scripts/semantic_audit_reuse.py", "--paper", paper],
            state="ready_now",
            reason=(
                f"{statement_review} statement and {coverage_review} coverage "
                "items lack exact reusable decisions; this is a read-only worklist, "
                "not an automatic human-review refresh"
            ),
        )
        add_action(
            "replan_after_manual_semantic_repair",
            ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper],
            state="after_manual_semantic_repair",
            reason="confirm that the refreshed items are the only reopened obligations",
        )
    elif semantic_ready:
        if not compiled_artifacts_ready:
            add_action(
                "paper_build",
                ["env", "LEAN_NUM_THREADS=1", "lake", "build", paper],
                state="ready_now",
                reason="restore the compiled paper artifact without reopening semantic review",
            )
            add_action(
                "replan_after_build",
                ["python3", "scripts/closeout_reuse_plan.py", "--paper", paper],
                state="after_paper_build",
                reason=(
                    "validate the rebuilt artifact before scheduling strict closeout; "
                    "never advance from stale compiled metadata"
                ),
            )
        else:
            result = prior_execution.get("result")
            prior_plan_identity = (
                str(result.get("operational_plan_identity") or "")
                if isinstance(result, Mapping)
                else ""
            )
            prior_plan_schema = (
                str(result.get("operational_plan_identity_schema") or "")
                if isinstance(result, Mapping)
                else ""
            )
            same_completed_plan = (
                prior_execution.get("state") == "complete"
                and bool(plan_identity)
                and prior_plan_schema == OPERATIONAL_PLAN_IDENTITY_SCHEMA
                and prior_plan_identity == plan_identity
            )
            same_completed_plan_passed = (
                same_completed_plan
                and prior_execution.get("exit_code") == 0
                and isinstance(result, Mapping)
                and result.get("semantic_closeout_passed") is True
            )
            legacy_completed_plan = (
                prior_execution.get("state") == "complete" and prior_plan_schema == ""
            )
            unknown_plan_schema = prior_execution.get(
                "state"
            ) == "complete" and prior_plan_schema not in {
                "",
                OPERATIONAL_PLAN_IDENTITY_SCHEMA,
            }
            prior_request = prior_execution.get("request")
            legacy_profile = (
                prior_request.get("deep_paper_prose")
                if isinstance(prior_request, Mapping)
                else None
            )
            legacy_result_passed = (
                prior_execution.get("exit_code") == 0
                and isinstance(result, Mapping)
                and result.get("semantic_closeout_passed") is True
            )
            legacy_deep_profile_insufficient = (
                legacy_completed_plan
                and deep_paper_prose
                and legacy_profile is not True
            )
            legacy_known_failure = legacy_completed_plan and (
                prior_execution.get("exit_code") not in {None, 0}
                or (
                    isinstance(result, Mapping)
                    and result.get("semantic_closeout_passed") is False
                )
            )
            closeout_argv = [
                "python3",
                "scripts/run_paper_closeout.py",
                "--paper",
                paper,
            ]
            if deep_paper_prose:
                closeout_argv.append("--deep-paper-prose")
            if plan_identity:
                closeout_argv.extend(["--plan-identity", plan_identity])
            if prior_execution and not same_completed_plan_passed:
                closeout_argv.append("--new-run")

            status_argv = [
                "python3",
                "scripts/run_paper_closeout.py",
                "--paper",
                paper,
                "--status",
            ]
            if prior_execution_error:
                add_action(
                    "inspect_closeout_recovery",
                    status_argv,
                    state="ready_now",
                    reason=(
                        "the prior operational state is unreadable; inspect it before "
                        "explicitly authorizing a replacement run"
                    ),
                    state_error=prior_execution_error,
                )
            elif same_completed_plan:
                add_action(
                    "inspect_existing_closeout",
                    status_argv,
                    state="ready_now",
                    reason=(
                        "the same complete current-input identity already has a terminal "
                        "execution record; inspect it rather than rerunning"
                    ),
                )
                if not same_completed_plan_passed:
                    add_action(
                        "strict_closeout_after_failure_confirmation",
                        closeout_argv,
                        state="after_operator_confirms_retry_required",
                        reason=(
                            "the exact-input terminal record did not establish a "
                            "successful semantic closeout; retry only after inspecting "
                            "the recorded failure"
                        ),
                    )
            elif unknown_plan_schema:
                add_action(
                    "inspect_unknown_closeout_schema",
                    status_argv,
                    state="ready_now",
                    reason=(
                        "the terminal record claims an unknown operational plan schema; "
                        "inspect it without treating it as either current or grandfathered"
                    ),
                )
            elif legacy_deep_profile_insufficient or legacy_known_failure:
                add_action(
                    "strict_closeout",
                    closeout_argv,
                    state="ready_now",
                    state_path=str(state_path.relative_to(ROOT)),
                    reason=(
                        "the legacy completion failed or does not establish the "
                        "requested deep-paper profile; run one profile-correct closeout"
                    ),
                )
            elif legacy_completed_plan and legacy_adoption.get("state") == "error":
                add_action(
                    "inspect_legacy_adoption_recovery",
                    status_argv,
                    state="ready_now",
                    reason=str(
                        legacy_adoption.get("error") or "legacy adoption failed"
                    ),
                )
            elif (
                legacy_completed_plan
                and legacy_adoption.get("state") == "material_changed"
            ):
                add_action(
                    "strict_closeout",
                    closeout_argv,
                    state="ready_now",
                    state_path=str(state_path.relative_to(ROOT)),
                    reason=(
                        "current material differs from the one-time adopted legacy "
                        "baseline; run one current-input closeout"
                    ),
                )
            elif legacy_completed_plan:
                add_action(
                    "inspect_legacy_closeout",
                    status_argv,
                    state="ready_now",
                    reason=(
                        "this completion predates complete input identities; preserve it "
                        "without forcing a rerun, and use --new-run only after confirming "
                        "that a new closeout is actually required"
                        + (
                            " (its recorded semantic result passed)"
                            if legacy_result_passed
                            else " (its pass/profile metadata is incomplete)"
                        )
                    ),
                )
                if legacy_adoption.get("state") != "current":
                    add_action(
                        "strict_closeout_after_legacy_confirmation",
                        closeout_argv,
                        state="after_operator_confirms_new_closeout_required",
                        reason="run only when current paper changes require a new closeout",
                    )
            else:
                add_action(
                    "strict_closeout",
                    closeout_argv,
                    state="ready_now",
                    state_path=str(state_path.relative_to(ROOT)),
                    reason=(
                        "run the one durable, duplicate-safe authoritative closeout transaction"
                    ),
                )

    next_action = next(
        (action for action in actions if action.get("state") == "ready_now"),
        None,
    )
    return {
        "semantic_review_reuse_ready": semantic_ready,
        "compiled_artifacts_ready": compiled_artifacts_ready,
        "next_action": next_action,
        "future_reuse_pin_maintenance": {
            "required_for_this_closeout": False,
            "statement_items": statement_unsealed,
            "coverage_items": coverage_unsealed,
            "policy": (
                "do not rewrite an existing audited paper during closeout; "
                "seal these pins at its next intentional semantic refresh"
            ),
        },
        "actions": actions,
    }


def _semantic_reuse_ready(
    *,
    cache_reusable: bool,
    summary: Mapping[str, Any] | None,
    global_error: str,
    validator_identity_errors: Mapping[str, Any] | None,
) -> bool:
    """Return whether a semantic plan can advance to build/strict scheduling.

    This deliberately consumes only content-derived plan fields.  It must stay
    identical to the manual-repair branch in ``closeout_action_schedule`` so a
    planner never constructs a strict receipt for work that still stops at the
    semantic worklist.
    """

    summary = summary or {}
    validator_identity_errors = validator_identity_errors or {}
    statement_review = int(summary.get("statement_requires_review") or 0)
    coverage_review = int(summary.get("coverage_requires_review") or 0)
    validator_errors = sum(
        len(value) if isinstance(value, list) else bool(value)
        for value in validator_identity_errors.values()
    )
    return (
        cache_reusable
        and not global_error
        and validator_errors == 0
        and statement_review == 0
        and coverage_review == 0
    )


def _semantic_plan_requires_manual_repair(plan: Mapping[str, Any]) -> bool:
    """Return whether a reusable plan must stop before operational freezing."""

    summary = plan.get("summary")
    validator_identity_errors = plan.get("validator_identity_errors")
    return (
        plan.get("cache_reusable") is True
        and not _semantic_reuse_ready(
            cache_reusable=True,
            summary=summary if isinstance(summary, Mapping) else {},
            global_error=str(plan.get("global_error") or ""),
            validator_identity_errors=(
                validator_identity_errors
                if isinstance(validator_identity_errors, Mapping)
                else {}
            ),
        )
    )


def compact_plan_for_output(plan: Mapping[str, Any], paper: str) -> dict[str, Any]:
    """Omit successful item receipts while retaining every repair obligation."""

    compact = dict(plan)
    omitted: dict[str, int] = {}
    for lane in ("statement", "coverage"):
        raw_items = plan.get(lane)
        if not isinstance(raw_items, Mapping):
            continue
        compact[lane] = {
            key: value
            for key, value in raw_items.items()
            if not isinstance(value, Mapping) or value.get("reusable") is not True
        }
        omitted[lane] = len(raw_items) - len(compact[lane])
    compact["reusable_items_omitted_from_output"] = omitted
    compact["full_item_plan_command"] = (
        f"python3 scripts/closeout_reuse_plan.py --paper {paper} --all-items"
    )
    return compact


def _closeout_plan_input_paths(
    folder: Path,
    *,
    strict_transaction_content_snapshot: Mapping[str, object],
) -> tuple[list[Path], list[Path]]:
    """Select exact target material without walking ambient paper trees."""

    status_path = folder / "status.json"
    statement_map_path = folder / "audit" / "paper_statement_map.json"
    try:
        status_bytes = status_path.read_bytes()
        statement_map_bytes = statement_map_path.read_bytes()
        status_payload = json.loads(status_bytes)
        source_map = json.loads(statement_map_bytes)
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not acquire target closeout path configuration: {exc}"
        ) from exc
    if not isinstance(status_payload, Mapping) or not isinstance(source_map, Mapping):
        raise CloseoutPlanReceiptError("paper status or statement map is not an object")

    content_paths = {
        *(folder / relative for relative in MATERIAL_ARTIFACT_PATHS),
        folder / "FINAL_VALIDATION_REPORT.md",
        folder / "docs" / "DependencyDAG.tex",
        folder / "docs" / "DependencyDAG.pdf",
        folder / "docs" / "AGENT_SOURCE_AUDIT.md",
        folder / "docs" / "POST_FORMALIZATION_AUDIT.md",
        *(ROOT / str(relative) for relative in strict_transaction_content_snapshot),
    }
    if status_payload.get("intake_freeze_required") is True:
        content_paths.add(folder / "audit" / "intake_freeze.json")
    content_paths.update(
        {
            ROOT / "papers" / f"{folder.name}.lean",
            folder / ".review_traces" / "paper_theorem_validations.jsonl",
            *_semantic_direct_input_paths(folder, source_map),
        }
    )
    try:
        content_paths.update(
            review_dashboard.required_dashboard_audit_input_paths(
                folder,
                status_bytes=status_bytes,
                statement_map_bytes=statement_map_bytes,
                repository_root=ROOT,
            )
        )
    except (OSError, RuntimeError, ValueError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not select exact dashboard closeout inputs: {exc}"
        ) from exc
    return sorted(content_paths, key=str), []


@dataclass(frozen=True)
class CloseoutPlanReceiptPublication:
    """Result of attempting to freeze the exact strict-closeout input set."""

    receipt: dict[str, Any] | None
    error: str
    disposition: str
    input_identity_sha256: str

    def __post_init__(self) -> None:
        if self.disposition not in PLAN_RECEIPT_PUBLICATION_DISPOSITIONS:
            raise ValueError(
                "unknown closeout-plan receipt publication disposition: "
                + self.disposition
            )
        if not SHA256_RE.fullmatch(self.input_identity_sha256):
            raise ValueError("closeout-plan receipt publication has invalid input identity")


def _closeout_plan_publication_input_identity(
    *,
    folder: Path,
    source_ledger: object,
    compiled_ledger: object,
    strict_transaction_snapshot: object,
    lean_closure_projection: object,
    audit_material_sha256: object,
) -> str:
    """Pin the exact planner inputs relevant to one publication attempt."""

    return _digest(
        {
            "paper": folder.name,
            "source_ledger": source_ledger,
            "compiled_ledger": compiled_ledger,
            "strict_transaction_snapshot": strict_transaction_snapshot,
            "lean_closure_projection": lean_closure_projection,
            "audit_material_sha256": str(audit_material_sha256 or ""),
        }
    )


def _write_current_closeout_plan_receipt(
    plan: dict[str, Any],
    *,
    folder: Path,
    deep_paper_prose: bool,
) -> CloseoutPlanReceiptPublication:
    source_ledger = plan.pop("_execution_source_artifact_mutation_snapshot", None)
    compiled_ledger = plan.pop("_execution_compiled_artifact_mutation_snapshot", None)
    strict_transaction_snapshot = plan.pop(
        "_execution_strict_transaction_content_snapshot", None
    )
    lean_closure_projection = plan.pop(
        "_execution_lean_import_closure_projection", None
    )
    input_identity_sha256 = _closeout_plan_publication_input_identity(
        folder=folder,
        source_ledger=source_ledger,
        compiled_ledger=compiled_ledger,
        strict_transaction_snapshot=strict_transaction_snapshot,
        lean_closure_projection=lean_closure_projection,
        audit_material_sha256=plan.get("audit_material_sha256"),
    )

    def failed(
        error: str, disposition: str
    ) -> CloseoutPlanReceiptPublication:
        return CloseoutPlanReceiptPublication(
            receipt=None,
            error=error,
            disposition=disposition,
            input_identity_sha256=input_identity_sha256,
        )

    if not isinstance(source_ledger, Mapping) or not isinstance(
        compiled_ledger, Mapping
    ):
        return failed(
            "planner has no exact Lean source/compiled input ledgers",
            "deterministic_input",
        )
    if not _mutation_snapshot_is_current(source_ledger):
        return failed("Lean source closure changed before plan publication", "source_race")
    if not _mutation_snapshot_is_current(compiled_ledger):
        return failed(
            "compiled Lean closure changed before plan publication", "compiled_race"
        )
    if (
        not isinstance(lean_closure_projection, Mapping)
        or lean_closure_projection.get("state") != "present"
    ):
        return failed(
            "Lean-authored paper-root closure projection is unavailable",
            "deterministic_input",
        )
    if not isinstance(strict_transaction_snapshot, Mapping):
        return failed(
            "planner has no exact strict-transaction input snapshot",
            "deterministic_input",
        )
    audit = folder / "audit"
    current_audit_material = _file_material_snapshot(
        [
            audit / "statement_match_llm.json",
            audit / "paper_coverage_llm.json",
            audit / "paper_statement_map.json",
            audit / "source_proof_fidelity.json",
        ]
    )
    if _digest(_material_content_projection(current_audit_material)) != str(
        plan.get("audit_material_sha256") or ""
    ):
        return failed(
            "semantic audit material changed before plan publication", "source_race"
        )
    try:
        content_paths, stat_paths = _closeout_plan_input_paths(
            folder,
            strict_transaction_content_snapshot=strict_transaction_snapshot,
        )
        reusable_compiled_inputs = _load_compiled_input_cache(folder)
        receipt = build_closeout_plan_receipt(
            ROOT,
            paper=folder.name,
            deep_paper_prose=deep_paper_prose,
            content_paths=content_paths,
            stat_paths=stat_paths,
            source_ledger=source_ledger,
            compiled_ledger=compiled_ledger,
            lean_import_closure_projection=lean_closure_projection,
            lean_import_closure_projection_validated=True,
            reusable_content_inputs=strict_transaction_snapshot,
            reusable_compiled_inputs=reusable_compiled_inputs,
        )
    except CloseoutPlanReceiptError as exc:
        return failed(str(exc), "deterministic_input")
    except (OSError, RuntimeError, ValueError) as exc:
        return failed(str(exc), "publication_io")
    receipt_identity = str(receipt["plan_identity_sha256"])
    path = closeout_plan_receipt_path(ROOT, folder.name, receipt_identity)
    try:
        atomic_write_json(path, receipt)
        published = json.loads(path.read_text(encoding="utf-8"))
        if published != receipt:
            raise CloseoutPlanReceiptError(
                "published closeout plan receipt does not equal this planner's receipt"
            )
        validated_closeout_plan_receipt(
            ROOT,
            published,
            paper=folder.name,
            deep_paper_prose=deep_paper_prose,
            expected_plan_identity=receipt_identity,
        )
        raw_compiled_inputs = receipt.get("compiled_inputs")
        if isinstance(raw_compiled_inputs, Mapping):
            _write_compiled_input_cache(folder, raw_compiled_inputs)
    except OSError as exc:
        return failed(str(exc), "publication_io")
    except (CloseoutPlanReceiptError, json.JSONDecodeError) as exc:
        return failed(str(exc), "deterministic_input")
    if not _mutation_snapshot_is_current(source_ledger):
        return failed("Lean source closure changed during plan publication", "source_race")
    if not _mutation_snapshot_is_current(compiled_ledger):
        return failed(
            "compiled Lean closure changed during plan publication", "compiled_race"
        )
    return CloseoutPlanReceiptPublication(
        receipt=receipt,
        error="",
        disposition="published",
        input_identity_sha256=input_identity_sha256,
    )


def finalize_operational_plan(
    plan: dict[str, Any],
    *,
    folder: Path,
    source_coverage_mode: str,
    execution_path: Path,
    static_readiness: Mapping[str, Any],
) -> dict[str, Any]:
    """Attach current execution scheduling without changing semantic decisions."""

    plan["readiness_matrix"] = dict(static_readiness)
    deep_paper_prose = source_coverage_mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
    plan["source_coverage_mode"] = source_coverage_mode
    if _semantic_plan_requires_manual_repair(plan):
        # A semantic worklist cannot launch a worker, so it has no use for a
        # strict-input receipt, compiled ledger, or prior execution identity.
        # Returning before those operations prevents an invalid sidecar from
        # repeatedly paying for strict-context construction.
        plan.update(
            closeout_action_schedule(
                folder.name,
                cache_reusable=True,
                compiled_artifacts_ready=(
                    plan.get("compiled_artifacts_ready") is True
                ),
                summary=(
                    plan.get("summary")
                    if isinstance(plan.get("summary"), Mapping)
                    else {}
                ),
                global_error=str(plan.get("global_error") or ""),
                validator_identity_errors=(
                    plan.get("validator_identity_errors")
                    if isinstance(plan.get("validator_identity_errors"), Mapping)
                    else {}
                ),
            )
        )
        return plan
    if (
        plan.get("cache_reusable") is True
        and plan.get("compiled_artifacts_ready") is not True
    ):
        # A focused build necessarily changes the compiled closure.  Schedule
        # it before freezing strict inputs or a worker receipt, then replan
        # against the rebuilt artifact without reopening semantic review.
        plan.update(
            closeout_action_schedule(
                folder.name,
                cache_reusable=True,
                compiled_artifacts_ready=False,
                summary=(
                    plan.get("summary")
                    if isinstance(plan.get("summary"), Mapping)
                    else {}
                ),
                global_error=str(plan.get("global_error") or ""),
                validator_identity_errors=(
                    plan.get("validator_identity_errors")
                    if isinstance(plan.get("validator_identity_errors"), Mapping)
                    else {}
                ),
            )
        )
        return plan
    (
        prior_execution,
        prior_execution_error,
        prior_execution_namespace,
        _effective_execution_path,
    ) = effective_closeout_execution_state(ROOT, folder.name)
    if not prior_execution_error and prior_execution is not None:
        plan["last_closeout_execution"] = {
            "namespace": prior_execution_namespace,
            "state": prior_execution.get("state"),
            "launch_id": prior_execution.get("launch_id"),
            "started_at": prior_execution.get("started_at"),
            "completed_at": prior_execution.get("completed_at"),
            "exit_code": prior_execution.get("exit_code"),
            "result": prior_execution.get("result"),
            "acceptance_credential": False,
        }
    elif prior_execution_error:
        plan["last_closeout_execution_error"] = prior_execution_error
    plan["plan_identity_schema"] = OPERATIONAL_PLAN_IDENTITY_SCHEMA
    publication = _write_current_closeout_plan_receipt(
        plan,
        folder=folder,
        deep_paper_prose=deep_paper_prose,
    )
    if publication.receipt is None:
        replan_argv = [
            "python3",
            "scripts/closeout_reuse_plan.py",
            "--paper",
            folder.name,
        ]
        replan_action = {
            "id": "replan_current_inputs",
            "state": "ready_now",
            "required": True,
            "argv": replan_argv,
            "command": shlex.join(replan_argv),
            "retryable": publication.disposition
            in {"source_race", "compiled_race"},
            "publication_disposition": publication.disposition,
            "input_identity_sha256": publication.input_identity_sha256,
            "reason": (
                "the exact operational input snapshot could not be frozen; "
                "discard this plan and reacquire current inputs: " + publication.error
            ),
        }
        plan.update(
            {
                "plan_identity_sha256": "",
                "plan_identity_input_path_count": 0,
                "operational_plan_error": publication.error,
                "operational_plan_publication_disposition": publication.disposition,
                "next_action": replan_action,
                "actions": [replan_action],
            }
        )
        return plan
    receipt = publication.receipt
    plan["plan_identity_sha256"] = str(receipt["plan_identity_sha256"])
    plan["plan_identity_input_path_count"] = len(
        receipt.get("content_inputs", {})
    ) + len(receipt.get("compiled_inputs", {}))
    plan["plan_receipt_path"] = str(
        closeout_plan_receipt_path(
            ROOT,
            folder.name,
            plan["plan_identity_sha256"],
        ).relative_to(ROOT)
    )
    plan["plan_receipt_acceptance_credential"] = False
    legacy_rollout_baseline: Mapping[str, Any] = {
        "ready": False,
        "state": "error",
        "errors": ["legacy rollout baseline was not requested"],
    }
    if (
        known_success_legacy_completion(
            prior_execution,
            paper=folder.name,
            deep_paper_prose=deep_paper_prose,
        )
        and not legacy_adoption_path(
            ROOT, folder.name, deep_paper_prose=deep_paper_prose
        ).is_file()
    ):
        legacy_rollout_baseline = _legacy_rollout_material_readiness(folder, receipt)
    legacy_adoption = adopt_or_validate_legacy_completion(
        ROOT,
        paper=folder.name,
        plan_identity=plan["plan_identity_sha256"],
        deep_paper_prose=deep_paper_prose,
        prior_execution=prior_execution,
        rollout_baseline=legacy_rollout_baseline,
    )
    if legacy_adoption.get("state") != "not_applicable":
        plan["legacy_closeout_adoption"] = legacy_adoption
    schedule = closeout_action_schedule(
        folder.name,
        cache_reusable=plan.get("cache_reusable") is True,
        compiled_artifacts_ready=plan.get("compiled_artifacts_ready") is True,
        summary=plan.get("summary") if isinstance(plan.get("summary"), Mapping) else {},
        global_error=str(plan.get("global_error") or ""),
        validator_identity_errors=(
            plan.get("validator_identity_errors")
            if isinstance(plan.get("validator_identity_errors"), Mapping)
            else {}
        ),
        plan_identity=plan["plan_identity_sha256"],
        prior_execution=(
            prior_execution if isinstance(prior_execution, Mapping) else {}
        ),
        prior_execution_error=prior_execution_error,
        deep_paper_prose=deep_paper_prose,
        legacy_adoption=legacy_adoption,
    )
    plan.update(schedule)
    return plan


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--paper", required=True, help="Paper folder name under papers/."
    )
    parser.add_argument(
        "--all-items",
        action="store_true",
        help="include successful reusable items as well as repair obligations",
    )
    parser.add_argument(
        "--verify-compiled-content",
        action="store_true",
        help=(
            "force the diagnostic exact-content manifest path; ordinary planning "
            "already retains exact hashes and refreshes only changed stat guards"
        ),
    )
    parser.add_argument(
        "--diagnose",
        action="store_true",
        help=(
            "read only static/status paper readiness; never writes a plan, runs "
            "semantic reuse, or grants acceptance"
        ),
    )
    parser.add_argument(
        "--execute-freeze-raw-reissue",
        action="store_true",
        help=(
            "run the planner-issued raw-receipt transition after rechecking "
            "engine, paper, and deterministic closeout readiness"
        ),
    )
    parser.add_argument(
        "--reset-closeout-wave-engine-snapshot",
        action="store_true",
        help=(
            "explicitly begin a new operational engine wave while no raw "
            "reissue or source-record scan is active"
        ),
    )
    parser.add_argument(
        "--raw-reissue-status",
        action="store_true",
        help=(
            "read the durable raw-reissue operation receipt without planning, "
            "scanning, or changing evidence"
        ),
    )
    parser.add_argument(
        "--acknowledge-stale-raw-reissue-operation",
        action="store_true",
        help=(
            "explicitly terminalize an orphaned running raw-operation receipt "
            "after checking that both operational locks are idle; never runs a scan"
        ),
    )
    args = parser.parse_args()

    folder = resolve_paper_folder(ROOT, args.paper)
    if folder is None:
        raise SystemExit(f"unknown paper folder: {args.paper}")
    if args.execute_freeze_raw_reissue:
        if (
            args.diagnose
            or args.all_items
            or args.verify_compiled_content
            or args.reset_closeout_wave_engine_snapshot
            or args.raw_reissue_status
            or args.acknowledge_stale_raw_reissue_operation
        ):
            raise SystemExit(
                "--execute-freeze-raw-reissue cannot be combined with planner-only options"
            )
        return execute_freeze_then_raw_reissue(folder)
    if args.reset_closeout_wave_engine_snapshot:
        if (
            args.diagnose
            or args.all_items
            or args.verify_compiled_content
            or args.raw_reissue_status
            or args.acknowledge_stale_raw_reissue_operation
        ):
            raise SystemExit(
                "--reset-closeout-wave-engine-snapshot cannot be combined with planner-only options"
            )
        return reset_closeout_wave_engine_snapshot_for_paper(folder)
    if args.raw_reissue_status:
        if (
            args.diagnose
            or args.all_items
            or args.verify_compiled_content
            or args.acknowledge_stale_raw_reissue_operation
        ):
            raise SystemExit("--raw-reissue-status cannot be combined with planner-only options")
        return raw_reissue_operation_status(folder)
    if args.acknowledge_stale_raw_reissue_operation:
        if args.diagnose or args.all_items or args.verify_compiled_content:
            raise SystemExit(
                "--acknowledge-stale-raw-reissue-operation cannot be combined with planner-only options"
            )
        return acknowledge_stale_raw_reissue_operation(folder)
    if args.diagnose:
        # Diagnose is a read-only aggregation surface. It reports operational
        # execution disposition alongside every deterministic local blocker;
        # normal planning below keeps the exclusive worker/recovery returns.
        execution_path = closeout_worker_state_path(args.paper)
        active_execution = running_execution_summary(execution_path)
        legacy_execution_path = default_closeout_execution_path(ROOT, args.paper)
        legacy_active_execution = running_execution_summary(legacy_execution_path)
        if active_execution is None:
            active_execution = legacy_active_execution
        (
            _prior_execution,
            early_execution_error,
            early_execution_namespace,
            early_execution_path,
        ) = effective_closeout_execution_state(ROOT, args.paper)
        engine_error = runtime_engine_registration_error(ROOT)
        # Diagnose reports cheap paper-local metadata only.  The exact intake
        # atom scan is deliberately reserved for an eligible normal closeout.
        static_readiness = static_closeout_readiness(folder, include_intake=False)
        paper_status, status_error = _paper_closeout_status_preflight(folder)
        diagnostic_actions: list[dict[str, Any]] = []
        if active_execution is not None:
            diagnostic_actions.append(
                {
                    "id": "inspect_active_closeout",
                    "state": "ready_now",
                    "required": True,
                    "reason": (
                        "an existing closeout execution is active; inspect its status "
                        "before starting another closeout"
                    ),
                }
            )
        if early_execution_error:
            status_argv = [
                "python3",
                "scripts/run_paper_closeout.py",
                "--paper",
                args.paper,
                "--status",
            ]
            diagnostic_actions.append(
                {
                    "id": "inspect_closeout_recovery",
                    "state": "ready_now",
                    "required": True,
                    "argv": status_argv,
                    "command": shlex.join(status_argv),
                    "reason": early_execution_error,
                }
            )
        if engine_error:
            diagnostic_actions.append(
                {
                    "id": "commit_registered_engine_transition",
                    "state": "ready_now",
                    "required": True,
                    "reason": engine_error,
                }
            )
        if not static_readiness["ready"]:
            diagnostic_actions.append(
                {
                    "id": "resolve_static_closeout_blockers",
                    "state": "ready_now",
                    "required": True,
                    "reason": "finish the listed deterministic paper-local obligations",
                }
            )
        if status_error:
            diagnostic_actions.append(
                {
                    "id": "resolve_paper_closeout_eligibility",
                    "state": "ready_now",
                    "required": True,
                    "reason": status_error,
                }
            )
        if not diagnostic_actions:
            diagnostic_actions.append(
                {
                    "id": "run_frozen_closeout_planner",
                    "state": "ready_now",
                    "required": True,
                    "reason": (
                        "static/status readiness passed; rerun without --diagnose to "
                        "perform the bounded raw-identity preflight and plan work"
                    ),
                }
            )
        payload: dict[str, Any] = {
            "schema": 2,
            "paper": args.paper,
            "acceptance_credential": False,
            "diagnostic_only": True,
            "strict_closeout_required_for_acceptance": True,
            "expensive_planning_deferred": True,
            "readiness_matrix": static_readiness,
            "next_action": diagnostic_actions[0],
            "actions": diagnostic_actions,
        }
        if active_execution is not None:
            payload.update(
                {
                    "start_another_closeout": False,
                    "closeout_start_disposition": "already_running",
                    "active_execution": active_execution,
                }
            )
        if early_execution_error:
            payload.update(
                {
                    "execution_namespace": early_execution_namespace,
                    "execution_path": str(early_execution_path.relative_to(ROOT)),
                }
            )
        if engine_error:
            payload["engine_registration_error"] = engine_error
            payload["after_engine_registration"] = (
                "rerun closeout_reuse_plan without --diagnose; no semantic cache, "
                "raw receipt, or execution identity was used"
            )
        if paper_status:
            payload["paper_status"] = paper_status
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0

    execution_path = closeout_worker_state_path(args.paper)
    active_execution = running_execution_summary(execution_path)
    legacy_execution_path = default_closeout_execution_path(ROOT, args.paper)
    legacy_active_execution = running_execution_summary(legacy_execution_path)
    if active_execution is None:
        active_execution = legacy_active_execution
    if active_execution is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "start_another_closeout": False,
                    "closeout_start_disposition": "already_running",
                    "active_execution": active_execution,
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    (
        _prior_execution,
        early_execution_error,
        early_execution_namespace,
        early_execution_path,
    ) = effective_closeout_execution_state(ROOT, args.paper)
    if early_execution_error:
        status_argv = [
            "python3",
            "scripts/run_paper_closeout.py",
            "--paper",
            args.paper,
            "--status",
        ]
        recovery_action = {
            "id": "inspect_closeout_recovery",
            "state": "ready_now",
            "required": True,
            "argv": status_argv,
            "command": shlex.join(status_argv),
            "reason": early_execution_error,
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "expensive_planning_deferred": True,
                    "execution_namespace": early_execution_namespace,
                    "execution_path": str(early_execution_path.relative_to(ROOT)),
                    "next_action": recovery_action,
                    "actions": [recovery_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        registration_action = {
            "id": "inspect_engine_registration",
            "state": "ready_now",
            "required": True,
            "reason": engine_error,
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "expensive_planning_deferred": True,
                    "next_action": registration_action,
                    "actions": [registration_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2

    paper_status, status_error = _paper_closeout_status_preflight(folder)
    if status_error:
        # Keep a status-stop response informative without opening source
        # artifacts.  Eligible papers use the one full static pass below,
        # rather than scanning the same Lean/report surface twice.
        static_readiness = static_closeout_readiness(folder, include_intake=False)
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "paper_status": paper_status,
                    "readiness_matrix": static_readiness,
                    "expensive_planning_deferred": True,
                    "next_action": {
                        "id": "resolve_paper_closeout_eligibility",
                        "state": "ready_now",
                        "required": True,
                        "reason": status_error,
                    },
                    "actions": [
                        {
                            "id": "resolve_paper_closeout_eligibility",
                            "state": "ready_now",
                            "required": True,
                            "reason": status_error,
                        }
                    ],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # An ineligible paper above does not pay the prospective intake's exact
    # source-artifact/atom scan.  An eligible paper gets exactly one full
    # deterministic readiness pass before raw evidence or cache state.
    static_readiness = static_closeout_readiness(folder)
    if not static_readiness["ready"]:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "expensive_planning_deferred": True,
                    "next_action": {
                        "id": "resolve_static_closeout_blockers",
                        "state": "ready_now",
                        "reason": (
                            "finish the listed deterministic paper-local obligations "
                            "before hashing manifests or running semantic reuse"
                        ),
                    },
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    source_record_preflight = fast_saved_source_record_preflight(folder)
    source_record_action = source_record_preflight_action(
        args.paper, source_record_preflight
    )
    if source_record_action is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "source_record_preflight": source_record_preflight,
                    "expensive_planning_deferred": True,
                    "next_action": source_record_action,
                    "actions": [source_record_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    audit = folder / "audit"
    audit_material_paths = [
        audit / "statement_match_llm.json",
        audit / "paper_coverage_llm.json",
        audit / "paper_statement_map.json",
        audit / "source_proof_fidelity.json",
    ]
    audit_payloads, audit_material_before, audit_capture_errors = (
        _captured_json_payloads(audit_material_paths)
    )
    if audit_capture_errors:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "cache_reusable": False,
                    "invalidation_reasons": audit_capture_errors,
                    "expensive_planning_deferred": True,
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    statement_map_path = audit / "paper_statement_map.json"
    statement_sidecar_path = audit / "statement_match_llm.json"
    coverage_sidecar_path = audit / "paper_coverage_llm.json"
    source_proof_fidelity_path = audit / "source_proof_fidelity.json"
    statement_map = audit_payloads[statement_map_path]
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "cache_reusable": False,
                    "invalidation_reasons": [
                        f"current source coverage mode is invalid: {mode_error}"
                    ],
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    inventory = inventory_from_source_map(folder, statement_map)
    coverage_inventory, coverage_projection_error = (
        canonical_coverage_inventory_projection(
            folder,
            current_inventory=inventory,
            current_mode=mode,
        )
    )
    if coverage_projection_error:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "cache_reusable": False,
                    "invalidation_reasons": [coverage_projection_error],
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    advisory_input_sha256, advisory_input_material = _advisory_plan_input_identity(
        folder,
        source_map=statement_map,
        audit_material=audit_material_before,
        current_mode=mode,
        current_inventory=inventory,
        current_coverage_inventory=coverage_inventory,
    )
    if not args.verify_compiled_content:
        advisory_plan = _read_advisory_plan_cache(
            folder,
            advisory_input_sha256,
            current_input_mutation_snapshot=advisory_input_material.get(
                "_mutation_snapshot"
            ),
        )
        if advisory_plan is not None:
            if not _advisory_input_material_is_current(advisory_input_material):
                print(
                    json.dumps(
                        {
                            "schema": 2,
                            "paper": args.paper,
                            "acceptance_credential": False,
                            "invalidation_reasons": [
                                "planner inputs changed while loading advisory reuse"
                            ],
                        },
                        indent=2,
                        sort_keys=True,
                    )
                )
                return 2
            plan = finalize_operational_plan(
                advisory_plan,
                folder=folder,
                source_coverage_mode=mode,
                execution_path=execution_path,
                static_readiness=static_readiness,
            )
            output_plan = (
                plan if args.all_items else compact_plan_for_output(plan, args.paper)
            )
            print(json.dumps(output_plan, indent=2, sort_keys=True))
            return 0
    cached, cache_errors = cached_review_snapshot(
        folder,
        verify_compiled_content=args.verify_compiled_content,
    )
    if cached is None:
        schedule = closeout_action_schedule(
            args.paper,
            cache_reusable=False,
        )
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "cache_reusable": False,
                    "invalidation_reasons": cache_errors,
                    "readiness_matrix": static_readiness,
                    **schedule,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    statement_sidecar = audit_payloads[statement_sidecar_path]
    coverage_sidecar = audit_payloads[coverage_sidecar_path]
    source_proof_fidelity = audit_payloads[source_proof_fidelity_path]
    statement_inventory = dict(inventory)
    for component_inventory in (
        review_dashboard.paper_source_component_route_inventory(folder),
        review_dashboard.paper_source_definition_component_route_inventory(folder),
    ):
        for key, item in component_inventory.items():
            prior = statement_inventory.get(key)
            if prior is not None and dict(prior) != dict(item):
                raise SystemExit(
                    "current statement component inventory has conflicting "
                    f"semantic content at {key!r}"
                )
            statement_inventory[key] = item
    anchor_errors = _current_anchor_errors(folder, inventory.keys())
    for key, item in statement_inventory.items():
        parent = str(item.get("source_component_of") or "").strip()
        if parent and parent in anchor_errors:
            anchor_errors[key] = list(anchor_errors[parent])
    current_rows = row_snapshots_from_dashboard(cached.rows)
    direct_expression_policy_available = callable(
        getattr(
            review_dashboard,
            "llm_direct_expression_semantics_review_required",
            None,
        )
    )
    include_direct_expressions = _direct_expression_review_required(folder)
    plan = semantic_reuse_plan(
        statement_sidecar=statement_sidecar,
        coverage_sidecar=coverage_sidecar,
        current_rows=current_rows,
        current_inventory=inventory,
        current_statement_inventory=statement_inventory,
        current_coverage_inventory=coverage_inventory,
        current_mode=mode,
        current_anchor_errors=anchor_errors,
        current_source_map=statement_map,
        current_review_surface_sha256=review_dashboard.review_surface_digest(
            cached.rows
        ),
        current_source_proof_fidelity=source_proof_fidelity or None,
        include_direct_expressions=include_direct_expressions,
    )
    final_invalidation_reasons = cached_snapshot_invalidation_reasons(folder, cached)
    if _file_material_snapshot(audit_material_paths) != audit_material_before:
        final_invalidation_reasons.append(
            "semantic audit material changed during planning"
        )
    if final_invalidation_reasons:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "cache_reusable": False,
                    "invalidation_reasons": final_invalidation_reasons,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    plan.update(
        {
            "schema": 2,
            "paper": args.paper,
            "cache_reusable": True,
            "intermediate_focused_build": (
                "reuse_exact_cached_build"
                if cached.compiled_validation_mode == "exact_content"
                and cached.compiled_artifacts_ready
                else "reuse_metadata_current_build_candidate"
                if cached.compiled_artifacts_ready
                else "paper_build_required_without_semantic_rereview"
            ),
            "final_focused_build": "run_via_strict_closeout",
            "source_material_sha256": cached.source_material_sha256,
            "compiled_material_sha256": cached.compiled_material_sha256,
            "compiled_artifacts_ready": cached.compiled_artifacts_ready,
            "compiled_validation_mode": cached.compiled_validation_mode,
            "compiled_invalidation_reasons": list(cached.compiled_invalidation_reasons),
            "source_artifact_stat_identity_sha256": _digest(
                cached.source_artifact_mutation_snapshot
            ),
            "compiled_artifact_stat_identity_sha256": _digest(
                cached.compiled_artifact_mutation_snapshot
            ),
            "audit_material_sha256": _digest(
                _material_content_projection(audit_material_before)
            ),
            "readiness_matrix": static_readiness,
            "planner_compatibility": {
                "direct_expression_policy_api_available": (
                    direct_expression_policy_available
                ),
                "direct_expression_review_required": include_direct_expressions,
                "strict_closeout_remains_authoritative": True,
            },
        }
    )
    if not _advisory_input_material_is_current(advisory_input_material):
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "invalidation_reasons": [
                        "planner inputs changed before semantic repair could be scheduled"
                    ],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    if _semantic_plan_requires_manual_repair(plan):
        plan = finalize_operational_plan(
            plan,
            folder=folder,
            source_coverage_mode=mode,
            execution_path=execution_path,
            static_readiness=static_readiness,
        )
        output_plan = plan if args.all_items else compact_plan_for_output(plan, args.paper)
        print(json.dumps(output_plan, indent=2, sort_keys=True))
        return 0
    if plan.get("compiled_artifacts_ready") is not True:
        # The next action is a focused build followed by an explicit replan.
        # A strict input inventory and operational receipt made before that
        # build are necessarily obsolete, so defer both until the rebuilt
        # compiled closure is available.
        plan = finalize_operational_plan(
            plan,
            folder=folder,
            source_coverage_mode=mode,
            execution_path=execution_path,
            static_readiness=static_readiness,
        )
        output_plan = (
            plan if args.all_items else compact_plan_for_output(plan, args.paper)
        )
        print(json.dumps(output_plan, indent=2, sort_keys=True))
        return 0
    strict_transaction_snapshot, strict_transaction_error = (
        _strict_transaction_content_snapshot(folder)
    )
    if strict_transaction_snapshot is None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "invalidation_reasons": [strict_transaction_error],
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    if not _advisory_input_material_is_current(advisory_input_material):
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "invalidation_reasons": [
                        "planner inputs changed before advisory reuse could be saved"
                    ],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    final_advisory_input_material = advisory_input_material
    external_tool_projection = _declared_semantic_hash_tool_projection(
        cached.signature_contexts
    )
    (
        operational_compiled_ledger,
        _external_tool_guards,
        compiled_ledger_error,
    ) = _partition_operational_compiled_ledger(
        ROOT,
        cached.compiled_artifact_mutation_snapshot,
        signature_contexts=cached.signature_contexts,
    )
    if compiled_ledger_error:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "invalidation_reasons": [compiled_ledger_error],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    _write_advisory_plan_cache(
        folder,
        input_identity_sha256=advisory_input_sha256,
        input_material=final_advisory_input_material,
        semantic_plan=plan,
        source_artifact_mutation_snapshot=(cached.source_artifact_mutation_snapshot),
        compiled_artifact_mutation_snapshot=(
            cached.compiled_artifact_mutation_snapshot
        ),
        strict_transaction_content_snapshot=strict_transaction_snapshot,
        lean_import_closure_projection=cached.lean_import_closure_projection,
        declared_external_tool_projection=external_tool_projection,
    )
    plan["advisory_plan_cache"] = {
        "hit": False,
        "written": True,
        "path": str(_advisory_plan_cache_path(folder).relative_to(ROOT)),
        "acceptance_credential": False,
    }
    plan["_execution_source_artifact_mutation_snapshot"] = dict(
        cached.source_artifact_mutation_snapshot
    )
    plan["_execution_compiled_artifact_mutation_snapshot"] = operational_compiled_ledger
    plan["_execution_strict_transaction_content_snapshot"] = dict(
        strict_transaction_snapshot
    )
    plan["_execution_lean_import_closure_projection"] = dict(
        cached.lean_import_closure_projection
    )
    plan = finalize_operational_plan(
        plan,
        folder=folder,
        source_coverage_mode=mode,
        execution_path=execution_path,
        static_readiness=static_readiness,
    )
    output_plan = plan if args.all_items else compact_plan_for_output(plan, args.paper)
    print(json.dumps(output_plan, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
