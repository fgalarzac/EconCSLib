#!/usr/bin/env python3
"""Materialize authenticated selected-review and differential-overlay evidence.

This command is for a narrow historical closeout transition: a prior raw v10
receipt has a descriptor-authenticated differential overlay plus a selected
manual current-review sidecar.  It replays both artifacts against the exact
historical raw bytes and emits their complete current evidence ledger.  It
does not run a source-record scan, invoke Lean, or infer equivalence from a
judgment key, binder, declaration, or function name.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in tests.
    from scripts import source_record_current_revalidation as REVALIDATION
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import source_record_current_revalidation as REVALIDATION


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read JSON object at {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{path} is not a JSON object")
    return payload


def _paper_path(path: Path, paper_dir: Path, *, label: str) -> Path:
    try:
        resolved = path.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise ValueError(f"{label} must remain inside {paper_dir}") from exc
    return resolved


def _archived_replay_provenance_path(
    historical_raw_path: Path,
    historical_provenance_path: Path,
    *,
    canonical_raw_path: Path,
    provenance_was_explicit: bool,
) -> Path | None:
    """Choose archived versus live target validation from receipt identity.

    A selected-review composition can legitimately use the live canonical raw
    receipt as its input. In that case the current source map and proof-fidelity
    files must validate corrected targets; marking it historical would reject
    those current checks merely because the command accepts archived receipts
    too. An external raw receipt, or an explicitly supplied logical provenance
    path, stays in archived-replay mode. This decision compares filesystem
    receipt identity only, never a paper, declaration, or judgment name.
    """

    if (
        not provenance_was_explicit
        and historical_raw_path.resolve() == canonical_raw_path.resolve()
    ):
        return None
    return historical_provenance_path


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False, mode="w", encoding="utf-8"
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
        description=(
            "Replay an archived differential overlay plus selected current review "
            "into one complete v10 prior-evidence sidecar."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--historical-raw-audit", type=Path, required=True)
    parser.add_argument("--selected-current-sidecar", type=Path, required=True)
    parser.add_argument("--differential-overlay", type=Path, required=True)
    parser.add_argument(
        "--differential-overlay-provenance-path",
        type=Path,
        help=(
            "logical overlay path recorded by a selected review; defaults to "
            "audit/source_record_differential_revalidation.json"
        ),
    )
    parser.add_argument(
        "--historical-provenance-path",
        type=Path,
        help=(
            "logical raw-audit path recorded when the overlay was issued; defaults "
            "to audit/source_record_audit.json"
        ),
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        historical_raw_path = _paper_path(
            args.historical_raw_audit, paper_dir, label="--historical-raw-audit"
        )
        selected_path = _paper_path(
            args.selected_current_sidecar,
            paper_dir,
            label="--selected-current-sidecar",
        )
        overlay_path = _paper_path(
            args.differential_overlay, paper_dir, label="--differential-overlay"
        )
        overlay_provenance_path = _paper_path(
            args.differential_overlay_provenance_path
            or paper_dir / "audit" / "source_record_differential_revalidation.json",
            paper_dir,
            label="--differential-overlay-provenance-path",
        )
        output_path = _paper_path(args.out, paper_dir, label="--out")
        provenance_path = _paper_path(
            args.historical_provenance_path
            or paper_dir / "audit" / "source_record_audit.json",
            paper_dir,
            label="--historical-provenance-path",
        )
        archived_replay_provenance_path = _archived_replay_provenance_path(
            historical_raw_path,
            provenance_path,
            canonical_raw_path=paper_dir / "audit" / "source_record_audit.json",
            provenance_was_explicit=args.historical_provenance_path is not None,
        )
        raw_audit = _load_json_object(historical_raw_path)
        selected_sidecar = _load_json_object(selected_path)
        materialized = REVALIDATION.materialize_authenticated_selected_evidence(
            raw_audit,
            selected_sidecar,
            paper=args.paper,
            paper_dir=paper_dir,
            selected_sidecar_path=selected_path,
            raw_audit_path=historical_raw_path,
            raw_audit_provenance_path=archived_replay_provenance_path,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
        )
        errors = REVALIDATION.materialized_authenticated_selected_evidence_errors(
            materialized,
            raw_audit,
            selected_sidecar,
            paper=args.paper,
            paper_dir=paper_dir,
            selected_sidecar_path=selected_path,
            raw_audit_path=historical_raw_path,
            raw_audit_provenance_path=archived_replay_provenance_path,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
        )
        if errors:
            raise ValueError("; ".join(errors))
    except (ValueError, REVALIDATION.SourceRecordCurrentRevalidationError) as exc:
        print(f"{args.paper}: evidence composition refused: {exc}", file=sys.stderr)
        return 1
    encoded = json.dumps(materialized, indent=2, sort_keys=True) + "\n"
    if args.write:
        _atomic_write(output_path, encoded)
        print(
            f"{args.paper}: wrote authenticated composed prior evidence to {output_path} "
            f"({len(materialized.get('items', {}))} current groups)"
        )
    else:
        print(
            f"{args.paper}: authenticated evidence composition validates "
            f"({len(materialized.get('items', {}))} current groups); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
