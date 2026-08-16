#!/usr/bin/env python3
"""Bind a completed v3 current-revalidation attestation to sidecar bytes.

The original complete current-revalidation flow intentionally writes the
attestation before its output sidecar, so it cannot include the output hash
without creating a hash cycle.  This narrow v4 receipt does not perform a new
semantic review or copy a response: it validates the immutable v3 ancestry,
then records the exact already-reviewed sidecar bytes and current raw surface.
It is useful when a later item-level transport needs both the semantic-review
attestation and a byte-pinned response ledger.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from scripts import source_record_current_revalidation as CURRENT
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import source_record_current_revalidation as CURRENT


SCHEMA = 1
ARTIFACT_KIND = "source_record_current_semantic_revalidation_attestation"
LEGACY_POLICY_VERSION = "source-record-current-manual-semantic-revalidation-v3"
POLICY_VERSION = "source-record-current-manual-semantic-revalidation-v4"
REVIEW_SCOPE = "all_current_generated_judgment_keys"
SEMANTIC_SCOPE = "all_current_semantic_model_judgment_groups"
_SHA256_HEX_LENGTH = 64


class SourceRecordCurrentRevalidationSidecarBindingError(ValueError):
    """Raised when no exact v3 semantic-review ancestry can be bound."""


def _sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    if len(candidate) != _SHA256_HEX_LENGTH:
        return ""
    try:
        int(candidate, 16)
    except ValueError:
        return ""
    return candidate


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            f"{label} at {path} is not a JSON object"
        )
    return value


def _relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _resolve_paper_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_path(path, paper_dir) != text:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            f"{label} is not canonical"
        )
    return path


def _non_scaffold(value: Mapping[str, Any]) -> bool:
    return not any(
        bool(value.get(field))
        for field in (
            "non_evidence_scaffold",
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
        )
    )


def _current_group_ledger(raw_audit: Mapping[str, Any]) -> tuple[set[str], set[str]]:
    groups = CURRENT.generated_judgment_items(raw_audit)
    if not groups:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "current raw audit has no generated judgment groups"
        )
    semantic = CURRENT.semantic_model_judgment_keys(raw_audit)
    return set(groups), set(semantic)


def build_sidecar_bound_current_revalidation_attestation(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    legacy_attestation: Mapping[str, Any],
    sidecar_path: Path,
    legacy_attestation_path: Path,
) -> dict[str, Any]:
    """Return a v4 byte-binding receipt for an exact completed v3 review."""

    if error := CURRENT._raw_audit_error(raw_audit, paper=paper):
        raise SourceRecordCurrentRevalidationSidecarBindingError(error)
    keys, semantic_keys = _current_group_ledger(raw_audit)
    raw_items = sidecar.get("items")
    if not isinstance(raw_items, Mapping) or set(str(key) for key in raw_items) != keys:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "sidecar does not cover exactly the current generated judgment ledger"
        )
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    key_digest = CURRENT.generated_judgment_keys_sha256(raw_audit)
    surface_digest = CURRENT.generated_judgment_surface_sha256(raw_audit)
    sidecar_relative = _relative_path(sidecar_path, paper_dir)
    legacy_relative = _relative_path(legacy_attestation_path, paper_dir)
    legacy_sha256 = _file_sha256(legacy_attestation_path)
    metadata = sidecar.get("current_semantic_revalidation")
    if not isinstance(metadata, Mapping) or (
        metadata.get("schema") != SCHEMA
        or str(metadata.get("policy_version") or "").strip()
        != LEGACY_POLICY_VERSION
        or str(metadata.get("attestation_path") or "").strip() != legacy_relative
        or _sha256(metadata.get("attestation_sha256")) != legacy_sha256
        or str(metadata.get("current_judgment_sidecar_path") or "").strip()
        != sidecar_relative
        or _sha256(metadata.get("current_source_record_audit_sha256")) != raw_digest
        or _sha256(metadata.get("generated_judgment_keys_sha256")) != key_digest
        or _sha256(metadata.get("generated_judgment_surface_sha256"))
        != surface_digest
        or str(metadata.get("review_scope") or "").strip() != REVIEW_SCOPE
    ):
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "sidecar has no exact completed v3 current-revalidation metadata"
        )
    if (
        legacy_attestation.get("schema") != SCHEMA
        or legacy_attestation.get("artifact_kind") != ARTIFACT_KIND
        or str(legacy_attestation.get("policy_version") or "").strip()
        != LEGACY_POLICY_VERSION
        or legacy_attestation.get("paper") != paper
        or legacy_attestation.get("reviewed_current_semantics") is not True
        or str(legacy_attestation.get("review_scope") or "").strip()
        != REVIEW_SCOPE
        or _sha256(legacy_attestation.get("current_source_record_audit_sha256"))
        != raw_digest
        or _sha256(legacy_attestation.get("generated_judgment_keys_sha256"))
        != key_digest
        or _sha256(legacy_attestation.get("generated_judgment_surface_sha256"))
        != surface_digest
        or not str(legacy_attestation.get("reviewer") or "").strip()
        or not str(legacy_attestation.get("validated_at") or "").strip()
        or not str(legacy_attestation.get("review_notes") or "").strip()
        or not _non_scaffold(legacy_attestation)
    ):
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "legacy attestation is not a complete current v3 semantic review"
        )
    replay_errors = CURRENT.validate_rebound_sidecar(
        raw_audit,
        sidecar,
        paper=paper,
        paper_dir=paper_dir,
        output_sidecar_path=sidecar_path,
    )
    if replay_errors:
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "sidecar fails complete current-revalidation replay: "
            + "; ".join(replay_errors[:5])
        )
    reported_count = legacy_attestation.get("semantic_model_group_count")
    if reported_count is not None and reported_count != len(semantic_keys):
        raise SourceRecordCurrentRevalidationSidecarBindingError(
            "legacy attestation has stale semantic-model group coverage"
        )
    output: dict[str, Any] = {
        "schema": SCHEMA,
        "artifact_kind": ARTIFACT_KIND,
        "policy_version": POLICY_VERSION,
        "paper": paper,
        "current_source_record_audit_sha256": raw_digest,
        "generated_judgment_keys_sha256": key_digest,
        "generated_judgment_surface_sha256": surface_digest,
        "review_scope": REVIEW_SCOPE,
        "scope": SEMANTIC_SCOPE,
        "semantic_model_group_count": len(semantic_keys),
        "reviewed_current_semantics": True,
        "reviewer": str(legacy_attestation["reviewer"]),
        "validated_at": str(legacy_attestation["validated_at"]),
        "review_notes": (
            str(legacy_attestation["review_notes"])
            + "\n\nThis v4 receipt makes no semantic amendment. It binds the completed "
            "v3 current review to the exact current judgment-sidecar bytes named below."
        ),
        "current_judgment_sidecar_path": sidecar_relative,
        "current_judgment_sidecar_sha256": _file_sha256(sidecar_path),
        "legacy_current_semantic_attestation_path": legacy_relative,
        "legacy_current_semantic_attestation_sha256": legacy_sha256,
        "legacy_current_semantic_attestation_policy_version": LEGACY_POLICY_VERSION,
        "semantic_preservation_rule": (
            "The v3 attestation is the semantic-review ancestry. This v4 receipt "
            "adds only exact sidecar-byte provenance and may not amend responses."
        ),
    }
    for field in (
        "judgment_amendments",
        "judgment_amendment_provenance",
        "semantic_model_content_amendments",
        "semantic_model_dimension_amendments",
        "semantic_model_dimension_association_amendments",
    ):
        if field in legacy_attestation:
            output[field] = legacy_attestation[field]
    return output


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
        mode="w",
        encoding="utf-8",
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Bind a completed v3 source-record current review to exact sidecar bytes."
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--sidecar", type=Path, required=True)
    parser.add_argument("--legacy-attestation", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    raw_path = args.raw_audit or paper_dir / "audit" / "source_record_audit.json"
    try:
        for path, label in (
            (raw_path, "--raw-audit"),
            (args.sidecar, "--sidecar"),
            (args.legacy_attestation, "--legacy-attestation"),
            (args.out, "--out"),
        ):
            _relative_path(path, paper_dir)
        result = build_sidecar_bound_current_revalidation_attestation(
            paper=args.paper,
            paper_dir=paper_dir,
            raw_audit=_read_json_object(raw_path, label="raw audit"),
            sidecar=_read_json_object(args.sidecar, label="current judgment sidecar"),
            legacy_attestation=_read_json_object(
                args.legacy_attestation, label="legacy current attestation"
            ),
            sidecar_path=args.sidecar,
            legacy_attestation_path=args.legacy_attestation,
        )
    except SourceRecordCurrentRevalidationSidecarBindingError as exc:
        print(f"{args.paper}: sidecar binding refused: {exc}", file=sys.stderr)
        return 1
    if args.write:
        _atomic_write(args.out, json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(f"{args.paper}: wrote sidecar-bound current revalidation at {args.out}")
    else:
        print(f"{args.paper}: sidecar-bound current revalidation validates; rerun with --write")
    return 0


if __name__ == "__main__":  # pragma: no cover - command-line entry point.
    raise SystemExit(main())
