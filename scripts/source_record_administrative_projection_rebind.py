#!/usr/bin/env python3
"""Create a verified direct-``source_status`` transport rebind receipt.

This helper never runs the expensive source-record audit and never rewrites a
raw audit or human judgment sidecar.  It can only produce a receipt when every
affected schema-2 association still names an exact current raw source-map item
and its stored semantic hash is provably the immediately preceding projection
for one direct ``source_status`` field: either the schema-4 projection that
retained that field or the schema-4 projection that had already excluded it.
The latter is a schema-only transition and remains a distinct receipt-bound
case.
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

try:
    from scripts.source_record_target_disposition import (
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        build_administrative_projection_rebind,
        validate_administrative_projection_rebind,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from source_record_target_disposition import (
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        build_administrative_projection_rebind,
        validate_administrative_projection_rebind,
    )


class AdministrativeProjectionRebindError(ValueError):
    """Raised when a rebind input is not a current paper-local artifact."""


def _paper_path(value: Path, paper_dir: Path, *, label: str) -> Path:
    candidate = value if value.is_absolute() else paper_dir / value
    try:
        resolved = candidate.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise AdministrativeProjectionRebindError(
            f"{label} must remain inside the paper directory"
        ) from exc
    return resolved


def _relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise AdministrativeProjectionRebindError(
            "serialized artifact path must remain inside the paper directory"
        ) from exc


def _load_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise AdministrativeProjectionRebindError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise AdministrativeProjectionRebindError(f"{path} is not a JSON object")
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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--statement-map", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the validated receipt; otherwise only validate it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise AdministrativeProjectionRebindError(
                f"paper directory does not exist: {paper_dir}"
            )
        raw_path = _paper_path(
            args.raw_audit or Path("audit/source_record_audit.json"),
            paper_dir,
            label="--raw-audit",
        )
        map_path = _paper_path(
            args.statement_map or Path("audit/paper_statement_map.json"),
            paper_dir,
            label="--statement-map",
        )
        output_path = _paper_path(
            args.out
            or Path("audit") / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
            paper_dir,
            label="--out",
        )
        raw_audit, raw_bytes = _load_json_object(raw_path)
        statement_map, map_bytes = _load_json_object(map_path)
        receipt, error = build_administrative_projection_rebind(
            paper=args.paper,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_relative_path(raw_path, paper_dir),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_relative_path(map_path, paper_dir),
        )
        if error:
            raise AdministrativeProjectionRebindError(error)
        assert receipt is not None
        _context, error = validate_administrative_projection_rebind(
            receipt,
            paper=args.paper,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_relative_path(raw_path, paper_dir),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_relative_path(map_path, paper_dir),
        )
        if error:
            raise AdministrativeProjectionRebindError(
                "internal receipt validation failed: " + error
            )
    except AdministrativeProjectionRebindError as exc:
        print(
            f"{args.paper}: administrative source-status rebind refused: {exc}",
            file=sys.stderr,
        )
        return 1
    contents = json.dumps(receipt, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(output_path, contents)
        print(
            f"{args.paper}: wrote direct source-status projection rebind to "
            f"{output_path} ({len(receipt['association_rebinds'])} associations)"
        )
    else:
        print(
            f"{args.paper}: direct source-status projection rebind validates "
            f"({len(receipt['association_rebinds'])} associations); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
