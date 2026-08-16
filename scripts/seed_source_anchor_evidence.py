#!/usr/bin/env python3
"""Materialize byte-verified source-line evidence for a paper statement map.

This is an intake convenience, not a semantic source review.  It copies each
declared ``file:line[-line]`` slice from the map's already pinned canonical
source artifact and hashes the exact normalized bytes.  It refuses anchors
outside that artifact and refuses to overwrite non-generated evidence unless
``--replace`` is explicit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Iterator

try:
    from scripts.audit_evidence_integrity import (
        ROOT,
        SOURCE_FILE_LINE_RE,
        normalized_source_line_excerpt,
        normalized_source_lines,
        normalized_source_text,
        resolve_paper_source_path,
    )
except ModuleNotFoundError:  # Direct script execution.
    from audit_evidence_integrity import (
        ROOT,
        SOURCE_FILE_LINE_RE,
        normalized_source_line_excerpt,
        normalized_source_lines,
        normalized_source_text,
        resolve_paper_source_path,
    )


def iter_source_location_nodes(value: Any) -> Iterator[dict[str, Any]]:
    """Yield every structured source-location node without using map keys."""

    if isinstance(value, dict):
        if "source_location" in value:
            yield value
        for key, child in value.items():
            if key != "source_anchor_evidence":
                yield from iter_source_location_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_source_location_nodes(child)


def generated_evidence(
    folder: Path, payload: dict[str, Any], node: dict[str, Any]
) -> list[dict[str, Any]]:
    """Return canonical quote entries for one source-location node."""

    source_path, error = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    if source_path is None:
        raise ValueError(f"invalid source_artifact_path: {error}")
    raw = source_path.read_bytes()
    expected_digest = str(payload.get("source_artifact_sha256") or "").lower()
    actual_digest = hashlib.sha256(raw).hexdigest()
    if actual_digest != expected_digest:
        raise ValueError("canonical source artifact does not match its pinned SHA-256")
    try:
        lines = normalized_source_lines(normalized_source_text(raw))
    except UnicodeDecodeError as exc:
        raise ValueError("canonical source artifact is not UTF-8 text") from exc

    raw_location = node.get("source_location")
    if not isinstance(raw_location, str) or not raw_location.strip():
        raise ValueError("source_location must be a nonempty string")
    matches = list(SOURCE_FILE_LINE_RE.finditer(raw_location))
    if not matches:
        raise ValueError(f"source_location has no file:line anchor: {raw_location!r}")

    entries: list[dict[str, Any]] = []
    for match in matches:
        raw_anchor_path = match.group("path")
        candidate, path_error = resolve_paper_source_path(folder, raw_anchor_path)
        if candidate is None:
            raise ValueError(f"invalid source anchor {raw_anchor_path!r}: {path_error}")
        if candidate != source_path:
            raise ValueError(
                f"source anchor {raw_anchor_path!r} does not name the canonical artifact"
            )
        line_start = int(match.group("start"))
        line_end = int(match.group("end") or line_start)
        quote = normalized_source_line_excerpt(lines, line_start, line_end)
        if quote is None:
            raise ValueError(
                f"source anchor {raw_anchor_path}:{line_start}-{line_end} is out of range"
            )
        entries.append(
            {
                "path": raw_anchor_path,
                "line_start": line_start,
                "line_end": line_end,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
            }
        )
    return entries


def source_location_nodes_for_seed(
    payload: dict[str, Any], *, item_key: str | None = None
) -> Iterator[dict[str, Any]]:
    """Yield all nodes, or every source node below one selected map item.

    ``item_key`` is only an operational selection for a scoped refresh.  The
    emitted quote remains determined exclusively by the declared
    ``source_location`` and the pinned canonical source artifact.
    """

    if item_key is None:
        yield from iter_source_location_nodes(payload)
        return
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        raise ValueError("paper statement map has no items object")
    item = raw_items.get(item_key)
    if not isinstance(item, dict):
        raise ValueError(f"paper statement map has no object item `{item_key}`")
    yield from iter_source_location_nodes(item)


def seed_payload(
    payload: dict[str, Any],
    folder: Path,
    *,
    replace: bool,
    item_key: str | None = None,
) -> int:
    """Attach canonical evidence to selected source-location nodes and count changes."""

    changed = 0
    for node in source_location_nodes_for_seed(payload, item_key=item_key):
        expected = generated_evidence(folder, payload, node)
        existing = node.get("source_anchor_evidence")
        if existing == expected:
            continue
        if existing is not None and not replace:
            raise ValueError(
                "existing source_anchor_evidence differs from canonical generated "
                "evidence; rerun with --replace only after review"
            )
        node["source_anchor_evidence"] = expected
        changed += 1
    return changed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder name")
    parser.add_argument(
        "--write", action="store_true", help="write the updated statement map"
    )
    parser.add_argument(
        "--replace",
        action="store_true",
        help="replace existing non-generated source-anchor evidence",
    )
    parser.add_argument(
        "--item-key",
        help=(
            "refresh only this paper-statement-map item and nested source context; "
            "the key is an operational selector, never semantic evidence"
        ),
    )
    args = parser.parse_args()

    folder = (ROOT / "papers" / args.paper).resolve()
    try:
        folder.relative_to((ROOT / "papers").resolve())
    except ValueError:
        parser.error("--paper must identify a paper folder")
    map_path = folder / "audit" / "paper_statement_map.json"
    try:
        payload = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        parser.error(f"could not read {map_path}: {exc}")
    if not isinstance(payload, dict):
        parser.error("paper statement map must be a JSON object")

    try:
        changed = seed_payload(
            payload, folder, replace=args.replace, item_key=args.item_key
        )
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    if args.write:
        map_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    selection = f" item `{args.item_key}`" if args.item_key else ""
    print(
        f"{args.paper}:{selection} {changed} source-location node(s) "
        f"{'written' if args.write else 'would change'}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
