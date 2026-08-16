#!/usr/bin/env python3
"""Authenticate reuse across a no-op partial-to-formalized status transition.

The source-record generator normally includes the paper-local status in its
aggregate input fingerprint because a partially formalized paper may use a
strictly narrower precloseout projection.  That is the right default: a status
flip must not quietly erase an obligation.  This helper covers the narrower
case where the generated raw receipt proves that the partial-only projection
covered *nothing*.  It records the exact prior status payload while it is
still current, then permits the canonical raw receipt to remain reusable only
after the current payload differs by exactly one top-level change:
``status: partially formalized -> formalized``.

This is neither a source equivalence judgment nor a declaration-name bridge.
It never scans Lean or reruns the source-record generator. A nonempty ordinary
direct-statement ledger is retained only after the generator's static
descriptor validator rechecks exact source routes, declaration contents,
elaborated-signature receipts, and statement atoms. Generated judgment keys
only coordinate that exact check; they never establish equivalence by their
spelling. Every other generator input remains byte/semantic-identity bound
through the existing v10 fingerprint.
"""

from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.source_record_integrity import source_record_audit_receipt_error


SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_BASENAME = (
    "source_record_partial_to_formalized_transition.json"
)
SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_SCHEMA = 2
SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_POLICY_VERSION = (
    "source-record-partial-to-formalized-maximal-input-surface-v3"
)
SOURCE_RECORD_PROMPT_VERSION = "source-record-v10-semantic-conclusion-boundary-contract"
_SHA256_HEX_LENGTH = 64
_STATUS_TRANSITION_ENGINE_IDENTITY_NAME = (
    "PARTIAL_TO_FORMALIZED_STATUS_TRANSITION_ENGINE_IDENTITY"
)


class SourceRecordPartialToFormalizedTransitionError(ValueError):
    """Raised when a closeout status transition is not exact and reusable."""


def _canonical_json(value: object) -> str:
    """Canonicalize mapping keys without weakening list order."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_sha256(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _is_sha256(value: object) -> bool:
    text = str(value or "").strip().lower()
    return len(text) == _SHA256_HEX_LENGTH and all(
        character in "0123456789abcdef" for character in text
    )


def _load_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordPartialToFormalizedTransitionError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordPartialToFormalizedTransitionError(
            f"{path} is not a JSON object"
        )
    return payload, contents


def _atomic_write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _relative_to_paper(path: Path, paper_dir: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordPartialToFormalizedTransitionError(
            f"{label} must remain inside {paper_dir}"
        ) from exc


def _paper_path(path: Path, paper_dir: Path, *, label: str) -> Path:
    candidate = path if path.is_absolute() else paper_dir / path
    try:
        resolved = candidate.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordPartialToFormalizedTransitionError(
            f"{label} must remain inside {paper_dir}"
        ) from exc
    return resolved


def _raw_v10_receipt_error(raw: Mapping[str, Any], *, paper: str) -> str:
    if str(raw.get("paper") or "").strip() != paper:
        return "raw source-record audit paper does not match the transition paper"
    if str(raw.get("prompt_version") or "").strip() != SOURCE_RECORD_PROMPT_VERSION:
        return "raw source-record audit does not use the current v10 prompt"
    fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping):
        return "raw source-record audit has no input fingerprint"
    if fingerprint.get("no_lean") is not False:
        return "raw source-record audit was not produced by a full no_lean=false run"
    if not isinstance(fingerprint.get("max_depth"), int):
        return "raw source-record audit input fingerprint has malformed max_depth"
    if not _is_sha256(raw.get("source_record_audit_sha256")):
        return "raw source-record audit aggregate receipt is missing or malformed"
    if not _is_sha256(raw.get("source_record_audit_integrity_sha256")):
        return "raw source-record audit integrity receipt is missing or malformed"
    return source_record_audit_receipt_error(raw)


def _saved_direct_statement_ledger_keys(
    raw: Mapping[str, Any],
) -> tuple[set[str] | None, str]:
    """Return the authenticated ordinary direct-ledger subset, fail closed.

    The raw ledger is a union of ordinary direct-source coverage and the
    partial-only direct/Spec projection.  The latter must remain empty for a
    status transition, while the former is safe only after the static
    no-Lean validator proves it is still current at the formalized status.
    Judgment keys are opaque generated coordinates here; their membership is
    checked against the raw input inventory and current descriptor evidence,
    never inferred from their spelling.
    """

    raw_covered = raw.get("statement_ledger_covered_boundary_input_keys")
    raw_precloseout = raw.get("precloseout_contract_covered_boundary_input_keys")
    if not isinstance(raw_covered, list) or not isinstance(raw_precloseout, list):
        return None, "raw audit has malformed statement-ledger coverage"
    expected_raw = raw.get("expected_input_judgment_keys")
    if not raw_covered and not raw_precloseout:
        # Minimal identity receipts may omit the inventory when no generated
        # input was suppressed. There is nothing to preserve in that case.
        return set(), ""
    if not isinstance(expected_raw, list):
        return None, "raw audit has no input inventory for saved ledger coverage"

    def parse_keys(value: object, *, label: str) -> tuple[set[str] | None, str]:
        if not isinstance(value, list):
            return None, f"raw audit has malformed {label}"
        keys: set[str] = set()
        for raw_key in value:
            if not isinstance(raw_key, str) or not raw_key.strip():
                return None, f"raw audit has blank or malformed {label} key"
            key = raw_key.strip()
            if key in keys:
                return None, f"raw audit has duplicate {label} key"
            keys.add(key)
        return keys, ""

    expected, error = parse_keys(expected_raw, label="input inventory")
    if error:
        return None, error
    assert expected is not None
    covered, error = parse_keys(raw_covered, label="statement-ledger coverage")
    if error:
        return None, error
    precloseout, error = parse_keys(
        raw_precloseout, label="partial-only precloseout coverage"
    )
    if error:
        return None, error
    assert covered is not None and precloseout is not None
    if not covered <= expected or not precloseout <= covered:
        return None, "raw audit ledger coverage is not a subset of its input inventory"
    return covered - precloseout, ""


def _maximal_partial_input_surface_error(raw: Mapping[str, Any]) -> str:
    """Reject a partial raw that could omit a status-dependent formalized input.

    A partial-only direct/Spec projection can remove an ordinary source-record
    input solely because the paper was not yet formalized. It must therefore
    be empty. Ordinary direct-statement-ledger coverage is different: it can
    retain fewer input obligations only when an exact current no-Lean
    revalidation proves the same source route, declaration content,
    elaborated signature, and statement atoms still hold. That revalidation
    is enforced separately by the transition receipt.
    """

    covered = raw.get("precloseout_contract_covered_boundary_input_keys")
    if covered != []:
        return "raw audit did not prove an empty partial-only precloseout coverage set"
    projection = raw.get("precloseout_exact_contract_projection")
    if not isinstance(projection, Mapping):
        return "raw audit lacks the partial-only precloseout projection"
    if projection.get("schema") != 1:
        return "raw audit has an unsupported precloseout projection schema"
    if str(projection.get("status") or "").strip() != "partially formalized":
        return "raw audit was not generated at partially formalized status"
    if projection.get("items") != []:
        return "raw audit's partial-only precloseout projection has covered items"
    if projection.get("covered_boundary_input_keys") != []:
        return "raw audit's partial-only projection has covered input keys"
    if projection.get("covered_boundary_input_keys_sha256") != _payload_sha256([]):
        return "raw audit's empty partial-only projection has an invalid digest"
    _saved_direct, ledger_error = _saved_direct_statement_ledger_keys(raw)
    if ledger_error:
        return ledger_error
    return ""


def _normalized_key_set(
    value: object, *, label: str
) -> tuple[set[str] | None, str]:
    """Normalize a caller-supplied static coverage set without name matching."""

    if value is None:
        return None, f"{label} is unavailable"
    if not isinstance(value, (set, frozenset, list, tuple)):
        return None, f"{label} is malformed"
    values = list(value)
    keys: set[str] = set()
    for raw_key in values:
        if not isinstance(raw_key, str) or not raw_key.strip():
            return None, f"{label} contains a blank or malformed key"
        key = raw_key.strip()
        if key in keys:
            return None, f"{label} contains a duplicate key"
        keys.add(key)
    return keys, ""


def _current_direct_statement_ledger_covered_keys(
    *, root: Path, paper_dir: Path, raw_audit: Mapping[str, Any]
) -> tuple[set[str] | None, str]:
    """Run the generator-owned static direct-ledger revalidator once.

    This helper is used only by the standalone receipt-preparation command.
    The aggregate cache supplies the same result directly to avoid loading a
    second copy of its own module. The loaded function only reads current map,
    interface, cached signature, and sidecar artifacts; it must never run Lean
    or scan a source paper.
    """

    helper = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper.is_file():
        return None, "source-record static direct-ledger helper is unavailable"
    module_name = "_source_record_transition_static_ledger"
    spec = importlib.util.spec_from_file_location(module_name, helper)
    if spec is None or spec.loader is None:
        return None, "source-record static direct-ledger helper could not load"
    module = importlib.util.module_from_spec(spec)
    previous = sys.modules.get(module_name)
    sys.modules[module_name] = module
    try:
        spec.loader.exec_module(module)
        validator = getattr(
            module,
            "current_direct_statement_ledger_covered_boundary_input_keys_without_lean",
            None,
        )
        if not callable(validator):
            return None, "source-record static direct-ledger validator is unavailable"
        current = validator(root, paper_dir, raw_audit)
    except Exception as exc:  # noqa: BLE001 - unavailable static evidence is fail-closed.
        return None, (
            "source-record static direct-ledger validator failed: "
            f"{type(exc).__name__}: {exc}"
        )
    finally:
        if previous is None:
            sys.modules.pop(module_name, None)
        else:
            sys.modules[module_name] = previous
    return _normalized_key_set(
        current, label="current static direct-ledger coverage"
    )


def _fingerprint_without_status(
    fingerprint: Mapping[str, Any],
) -> dict[str, Any] | None:
    if not isinstance(fingerprint, Mapping):
        return None
    status_hash = fingerprint.get("relevant_status_sha256")
    if not _is_sha256(status_hash):
        return None
    projection = copy.deepcopy(dict(fingerprint))
    projection.pop("relevant_status_sha256", None)
    return projection


def _raw_binding(raw: Mapping[str, Any], *, raw_relative_path: str) -> dict[str, str]:
    fingerprint = raw.get("source_record_input_fingerprint")
    assert isinstance(fingerprint, Mapping)
    return {
        "path": raw_relative_path,
        "source_record_audit_sha256": str(raw.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": str(
            raw.get("source_record_audit_integrity_sha256")
        ),
        "source_record_input_fingerprint_sha256": _payload_sha256(fingerprint),
    }


def _status_transition_engine_identity(root: Path) -> tuple[dict[str, str] | None, str]:
    """Read the compatibility contract without loading the full generator.

    The contract is a literal producer version in the source-record helper.
    Its semantics are intentionally narrow: a partial raw may cross to a full
    status only when partial-only coverage is empty and every saved ordinary
    direct-ledger key remains covered by the exact current static validator.
    Full-status direct coverage can only retain fewer ordinary inputs and
    therefore cannot make the partial raw under-approximate the formalized
    obligation surface. Any change to that rule must bump the literal version.
    """

    helper = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    try:
        tree = ast.parse(helper.read_text(encoding="utf-8"), filename=str(helper))
    except (OSError, SyntaxError) as exc:
        return None, f"could not read partial-to-formalized engine identity: {exc}"
    matching_nodes: list[ast.Assign | ast.AnnAssign] = []
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        if not any(
            isinstance(target, ast.Name)
            and target.id == _STATUS_TRANSITION_ENGINE_IDENTITY_NAME
            for target in targets
        ):
            continue
        matching_nodes.append(node)
    if len(matching_nodes) != 1:
        return (
            None,
            "partial-to-formalized engine identity must appear exactly once",
        )
    try:
        value = ast.literal_eval(matching_nodes[0].value)
    except (TypeError, ValueError) as exc:
        return None, "partial-to-formalized engine identity must be a literal object"
    if not isinstance(value, dict) or set(value) != {
        "path",
        "surface_semantic_version",
    }:
        return None, "partial-to-formalized engine identity is malformed"
    path = value.get("path")
    version = value.get("surface_semantic_version")
    if not isinstance(path, str) or not path.strip():
        return None, "partial-to-formalized engine identity path is malformed"
    if not isinstance(version, str) or not version.strip():
        return None, "partial-to-formalized engine identity version is malformed"
    return {"path": path, "surface_semantic_version": version}, ""


def _transition_receipt_sha256(payload: Mapping[str, Any]) -> str:
    bare = dict(payload)
    bare.pop("receipt_sha256", None)
    return _payload_sha256(bare)


def build_source_record_partial_to_formalized_transition(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    raw_relative_path: str,
    prior_status_payload: Mapping[str, Any],
    current_input_fingerprint: Mapping[str, Any],
    transition_engine_identity: Mapping[str, Any],
    current_direct_ledger_covered_keys: object = None,
) -> tuple[dict[str, Any] | None, str]:
    """Build a receipt while the partial status is still the live status."""

    if error := _raw_v10_receipt_error(raw_audit, paper=paper):
        return None, error
    if str(prior_status_payload.get("status") or "").strip() != "partially formalized":
        return None, "current status payload is not partially formalized"
    if error := _maximal_partial_input_surface_error(raw_audit):
        return None, error
    saved_direct_keys, ledger_error = _saved_direct_statement_ledger_keys(raw_audit)
    if ledger_error:
        return None, ledger_error
    assert saved_direct_keys is not None
    current_direct_keys, current_ledger_error = _normalized_key_set(
        current_direct_ledger_covered_keys,
        label="current static direct-ledger coverage",
    )
    if saved_direct_keys and current_ledger_error:
        return None, current_ledger_error
    if saved_direct_keys and not saved_direct_keys <= (current_direct_keys or set()):
        return (
            None,
            "current static direct-ledger coverage no longer covers every saved direct key",
        )
    stored_fingerprint = raw_audit.get("source_record_input_fingerprint")
    assert isinstance(stored_fingerprint, Mapping)
    if dict(stored_fingerprint) != dict(current_input_fingerprint):
        return None, "raw source-record input fingerprint is not current before transition"
    status_hash = stored_fingerprint.get("relevant_status_sha256")
    if not _is_sha256(status_hash):
        return None, "raw source-record input fingerprint has no valid status identity"
    if set(transition_engine_identity) != {"path", "surface_semantic_version"} or not all(
        isinstance(transition_engine_identity.get(field), str)
        and str(transition_engine_identity.get(field)).strip()
        for field in ("path", "surface_semantic_version")
    ):
        return None, "partial-to-formalized engine identity is malformed"
    receipt: dict[str, Any] = {
        "schema": SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_SCHEMA,
        "policy_version": SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_POLICY_VERSION,
        "paper": paper,
        "raw_source_record": _raw_binding(
            raw_audit, raw_relative_path=raw_relative_path
        ),
        "prior_status": {
            "path": "status.json",
            "payload": copy.deepcopy(dict(prior_status_payload)),
            "payload_sha256": _payload_sha256(prior_status_payload),
            "relevant_status_sha256": str(status_hash),
        },
        "transition": {
            "from_status": "partially formalized",
            "to_status": "formalized",
            "requires_exact_status_payload_except_status": True,
            "requires_empty_partial_precloseout_projection": True,
            "requires_current_static_direct_ledger_subset": True,
        },
        "direct_ledger_revalidation": {
            "schema": 1,
            "kind": "current-v10-static-direct-ledger-subset",
            "saved_direct_ledger_key_count": len(saved_direct_keys),
            "saved_direct_ledger_keys_sha256": _payload_sha256(
                sorted(saved_direct_keys)
            ),
        },
        "transition_engine_identity": dict(transition_engine_identity),
    }
    receipt["receipt_sha256"] = _transition_receipt_sha256(receipt)
    return receipt, ""


def validate_source_record_partial_to_formalized_transition(
    *,
    root: Path = ROOT,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    current_input_fingerprint: Mapping[str, Any],
    receipt_path: Path | None = None,
    transition_engine_identity: Mapping[str, Any] | None = None,
    current_direct_ledger_covered_keys: object = None,
) -> str:
    """Return an error unless the saved raw may cross this exact status flip."""

    path = receipt_path or (
        paper_dir
        / "audit"
        / SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_BASENAME
    )
    try:
        receipt, _receipt_bytes = _load_json_object(path)
    except SourceRecordPartialToFormalizedTransitionError as exc:
        return str(exc)
    expected_keys = {
        "schema",
        "policy_version",
        "paper",
        "raw_source_record",
        "prior_status",
        "transition",
        "direct_ledger_revalidation",
        "transition_engine_identity",
        "receipt_sha256",
    }
    if set(receipt) != expected_keys:
        return "partial-to-formalized transition receipt has an unexpected schema"
    if receipt.get("schema") != SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_SCHEMA:
        return "partial-to-formalized transition receipt has an unsupported schema"
    if (
        receipt.get("policy_version")
        != SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_POLICY_VERSION
    ):
        return "partial-to-formalized transition receipt has an unsupported policy"
    if str(receipt.get("paper") or "").strip() != paper:
        return "partial-to-formalized transition receipt has a paper mismatch"
    current_engine_identity = transition_engine_identity
    if current_engine_identity is None:
        current_engine_identity, engine_error = _status_transition_engine_identity(root)
        if engine_error:
            return engine_error
    if not isinstance(current_engine_identity, Mapping) or set(current_engine_identity) != {
        "path",
        "surface_semantic_version",
    }:
        return "partial-to-formalized engine identity is malformed"
    if receipt.get("transition_engine_identity") != dict(current_engine_identity):
        return "partial-to-formalized transition engine identity changed"
    if not _is_sha256(receipt.get("receipt_sha256")) or (
        str(receipt.get("receipt_sha256")).lower()
        != _transition_receipt_sha256(receipt)
    ):
        return "partial-to-formalized transition receipt digest is invalid"
    if error := _raw_v10_receipt_error(raw_audit, paper=paper):
        return error
    if error := _maximal_partial_input_surface_error(raw_audit):
        return error
    saved_direct_keys, ledger_error = _saved_direct_statement_ledger_keys(raw_audit)
    if ledger_error:
        return ledger_error
    assert saved_direct_keys is not None
    raw_binding = receipt.get("raw_source_record")
    if not isinstance(raw_binding, Mapping):
        return "partial-to-formalized transition receipt has no raw binding"
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    assert isinstance(raw_fingerprint, Mapping)
    expected_raw_binding = _raw_binding(
        raw_audit, raw_relative_path="audit/source_record_audit.json"
    )
    if dict(raw_binding) != expected_raw_binding:
        return "partial-to-formalized transition receipt does not bind the current raw receipt"
    prior_status = receipt.get("prior_status")
    if not isinstance(prior_status, Mapping):
        return "partial-to-formalized transition receipt has no prior status payload"
    expected_prior_keys = {
        "path",
        "payload",
        "payload_sha256",
        "relevant_status_sha256",
    }
    if set(prior_status) != expected_prior_keys:
        return "partial-to-formalized transition receipt prior-status schema is invalid"
    prior_payload = prior_status.get("payload")
    if not isinstance(prior_payload, Mapping):
        return "partial-to-formalized transition receipt prior status is malformed"
    if prior_status.get("path") != "status.json":
        return "partial-to-formalized transition receipt prior status path is invalid"
    if not _is_sha256(prior_status.get("payload_sha256")):
        return "partial-to-formalized transition receipt prior status hash is invalid"
    if str(prior_status.get("payload_sha256")).lower() != _payload_sha256(prior_payload):
        return "partial-to-formalized transition receipt prior status payload digest is invalid"
    if str(prior_payload.get("status") or "").strip() != "partially formalized":
        return "partial-to-formalized transition receipt prior status is not partial"
    if str(prior_status.get("relevant_status_sha256") or "").lower() != str(
        raw_fingerprint.get("relevant_status_sha256") or ""
    ).lower():
        return "partial-to-formalized transition receipt does not bind raw status identity"
    transition = receipt.get("transition")
    if transition != {
        "from_status": "partially formalized",
        "to_status": "formalized",
        "requires_exact_status_payload_except_status": True,
        "requires_empty_partial_precloseout_projection": True,
        "requires_current_static_direct_ledger_subset": True,
    }:
        return "partial-to-formalized transition receipt transition policy is invalid"
    direct_ledger_revalidation = receipt.get("direct_ledger_revalidation")
    if direct_ledger_revalidation != {
        "schema": 1,
        "kind": "current-v10-static-direct-ledger-subset",
        "saved_direct_ledger_key_count": len(saved_direct_keys),
        "saved_direct_ledger_keys_sha256": _payload_sha256(
            sorted(saved_direct_keys)
        ),
    }:
        return "partial-to-formalized transition direct-ledger receipt is invalid"
    current_direct_keys, current_ledger_error = _normalized_key_set(
        current_direct_ledger_covered_keys,
        label="current static direct-ledger coverage",
    )
    if saved_direct_keys and current_ledger_error:
        return current_ledger_error
    if saved_direct_keys and not saved_direct_keys <= (current_direct_keys or set()):
        return "current static direct-ledger coverage no longer covers every saved direct key"
    try:
        current_status, _current_status_bytes = _load_json_object(paper_dir / "status.json")
    except SourceRecordPartialToFormalizedTransitionError as exc:
        return str(exc)
    expected_current_status = copy.deepcopy(dict(prior_payload))
    expected_current_status["status"] = "formalized"
    if current_status != expected_current_status:
        return (
            "current status payload is not the exact prior payload with only "
            "partially formalized -> formalized changed"
        )
    raw_without_status = _fingerprint_without_status(raw_fingerprint)
    current_without_status = _fingerprint_without_status(current_input_fingerprint)
    if raw_without_status is None or current_without_status is None:
        return "source-record input fingerprint status identity is malformed"
    if raw_without_status != current_without_status:
        return "source-record inputs changed beyond the closeout status transition"
    if str(raw_fingerprint.get("relevant_status_sha256")).lower() == str(
        current_input_fingerprint.get("relevant_status_sha256")
    ).lower():
        return "source-record status identity did not change across the transition"
    return ""


def _current_input_fingerprint(
    *, root: Path, paper: str, raw_audit: Mapping[str, Any]
) -> dict[str, Any]:
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping):
        raise SourceRecordPartialToFormalizedTransitionError(
            "raw source-record audit has no input fingerprint"
        )
    max_depth = fingerprint.get("max_depth")
    if not isinstance(max_depth, int) or max_depth < 0:
        raise SourceRecordPartialToFormalizedTransitionError(
            "raw source-record audit input fingerprint has malformed max_depth"
        )
    helper = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper.is_file():
        raise SourceRecordPartialToFormalizedTransitionError(
            "source-record identity helper is unavailable"
        )
    command = [
        sys.executable,
        str(helper),
        "--root",
        str(root),
        "--paper",
        paper,
        "--identity-only",
        "--max-depth",
        str(max_depth),
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SourceRecordPartialToFormalizedTransitionError(
            f"source-record identity helper could not run: {exc}"
        ) from exc
    if completed.returncode != 0:
        detail = " ".join(completed.stderr.split())[-500:]
        raise SourceRecordPartialToFormalizedTransitionError(
            "source-record identity helper failed"
            + (": " + detail if detail else "")
        )
    try:
        payload = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SourceRecordPartialToFormalizedTransitionError(
            "source-record identity helper did not emit JSON"
        ) from exc
    if not isinstance(payload, Mapping) or payload.get("paper") != paper:
        raise SourceRecordPartialToFormalizedTransitionError(
            "source-record identity helper returned a paper mismatch"
        )
    current = payload.get("source_record_input_fingerprint")
    if not isinstance(current, Mapping):
        raise SourceRecordPartialToFormalizedTransitionError(
            "source-record identity helper returned no input fingerprint"
        )
    return dict(current)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the prepared receipt; otherwise validate that it can be prepared",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise SourceRecordPartialToFormalizedTransitionError(
                f"paper directory does not exist: {paper_dir}"
            )
        raw_path = _paper_path(
            args.raw_audit or Path("audit/source_record_audit.json"),
            paper_dir,
            label="--raw-audit",
        )
        out_path = _paper_path(
            args.out
            or Path("audit") / SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_BASENAME,
            paper_dir,
            label="--out",
        )
        raw_audit, _raw_bytes = _load_json_object(raw_path)
        prior_status, _prior_status_bytes = _load_json_object(paper_dir / "status.json")
        current = _current_input_fingerprint(
            root=root, paper=args.paper, raw_audit=raw_audit
        )
        saved_direct_keys, ledger_error = _saved_direct_statement_ledger_keys(
            raw_audit
        )
        if ledger_error:
            raise SourceRecordPartialToFormalizedTransitionError(ledger_error)
        assert saved_direct_keys is not None
        if saved_direct_keys:
            current_direct_keys, current_ledger_error = (
                _current_direct_statement_ledger_covered_keys(
                    root=root, paper_dir=paper_dir, raw_audit=raw_audit
                )
            )
            if current_ledger_error:
                raise SourceRecordPartialToFormalizedTransitionError(
                    current_ledger_error
                )
        else:
            current_direct_keys = set()
        engine_identity, engine_error = _status_transition_engine_identity(root)
        if engine_error:
            raise SourceRecordPartialToFormalizedTransitionError(engine_error)
        assert engine_identity is not None
        receipt, error = build_source_record_partial_to_formalized_transition(
            paper=args.paper,
            raw_audit=raw_audit,
            raw_relative_path=_relative_to_paper(raw_path, paper_dir, label="--raw-audit"),
            prior_status_payload=prior_status,
            current_input_fingerprint=current,
            transition_engine_identity=engine_identity,
            current_direct_ledger_covered_keys=current_direct_keys,
        )
        if error:
            raise SourceRecordPartialToFormalizedTransitionError(error)
        assert receipt is not None
    except SourceRecordPartialToFormalizedTransitionError as exc:
        print(
            f"{args.paper}: partial-to-formalized source-record transition refused: {exc}",
            file=sys.stderr,
        )
        return 1
    contents = json.dumps(receipt, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(out_path, contents)
        print(
            f"{args.paper}: wrote partial-to-formalized source-record transition to "
            f"{out_path}"
        )
    else:
        print(
            f"{args.paper}: partial-to-formalized source-record transition can be "
            "prepared; rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
