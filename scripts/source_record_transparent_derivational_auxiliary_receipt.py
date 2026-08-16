#!/usr/bin/env python3
"""Materialize a semantically raw-bound closeout receipt for proof-local auxiliaries.

This is intentionally not an audit rerun.  It consumes an already-current v10
raw receipt plus its authenticated reachable-auxiliary supplement, then writes
only the exact current proof bodies, resolved PaperInterface lexical closures,
and source-associated selected-root routes.  Schema 2 binds the complete raw
dependency manifest consumed by that authorization rather than unrelated raw
serialization bytes.  The shared validator rejects the receipt on any body,
closure, source-map, or route drift.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from scripts.internal_derivational_auxiliary import (
        _DERIVATIONAL_AUXILIARY_RECEIPT_FILE,
        _DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
        _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
        _derivational_root_path_identity,
        _normalized_declaration_identity,
        _receipt_source_association,
        _source_parser,
        _terminal_root_source_association_error,
        auxiliary_receipt_semantic_raw_binding,
        derivational_auxiliary_local_closure,
        derivational_auxiliary_local_closure_sha256,
    )
    from scripts.source_record_auxiliary_routing_supplement import (
        current_auxiliary_routing_context,
    )
except ModuleNotFoundError:  # pragma: no cover - direct execution fallback.
    from internal_derivational_auxiliary import (
        _DERIVATIONAL_AUXILIARY_RECEIPT_FILE,
        _DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
        _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
        _derivational_root_path_identity,
        _normalized_declaration_identity,
        _receipt_source_association,
        _source_parser,
        _terminal_root_source_association_error,
        auxiliary_receipt_semantic_raw_binding,
        derivational_auxiliary_local_closure,
        derivational_auxiliary_local_closure_sha256,
    )
    from source_record_auxiliary_routing_supplement import (
        current_auxiliary_routing_context,
    )


class DerivationalReceiptError(ValueError):
    """Raised when an exact proof-local receipt cannot be constructed."""


def _read_json(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as error:
        raise DerivationalReceiptError(f"could not read {path}: {error}") from error
    if not isinstance(payload, dict):
        raise DerivationalReceiptError(f"{path} is not a JSON object")
    return payload, contents


def _atomic_write(path: Path, payload: Mapping[str, object]) -> None:
    encoded = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        handle.write(encoded)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _raw_binding(payload: Mapping[str, object]) -> dict[str, object]:
    binding, error = auxiliary_receipt_semantic_raw_binding(
        payload, receipt_kind=_DERIVATIONAL_AUXILIARY_RECEIPT_KIND
    )
    if binding is None:
        raise DerivationalReceiptError(
            "raw v10 receipt has no complete auxiliary dependency manifest: " + error
        )
    return binding


def _candidate_items(payload: Mapping[str, object]) -> list[dict[str, Any]]:
    candidates = [
        dict(item)
        for item in payload.get("unresolved_reachable_paper_interface_auxiliaries")
        or []
        if isinstance(item, Mapping)
        and str(item.get("kind") or "").strip() in {"theorem", "lemma"}
        and str(item.get("disposition") or "").strip()
        == "missing_source_map_route_or_quarantine"
        and item.get("source_map_routes") == []
        and item.get("quarantined") is False
        and not str(item.get("quarantine_source_reason") or "").strip()
    ]
    candidates.sort(key=lambda item: str(item.get("declaration") or ""))
    names = [str(item.get("declaration") or "").strip() for item in candidates]
    if not candidates or not all(names) or len(set(names)) != len(names):
        raise DerivationalReceiptError(
            "authenticated routing ledger has no unique unresolved theorem-helper set"
        )
    return candidates


def build_receipt(*, paper: str) -> dict[str, object]:
    paper_dir = ROOT / "papers" / paper
    raw_path = paper_dir / "audit" / "source_record_audit.json"
    raw, _raw_bytes = _read_json(raw_path)
    if str(raw.get("paper") or "").strip() != paper:
        raise DerivationalReceiptError("raw audit paper does not match --paper")
    routing_context, routing_error = current_auxiliary_routing_context(
        root=ROOT,
        paper_dir=paper_dir,
        paper=paper,
        audit_payload=raw,
    )
    if routing_context is None:
        raise DerivationalReceiptError(
            "current reachable-auxiliary supplement is unavailable: " + routing_error
        )
    payload, augmentation_error = routing_context.audit_payload_with_authenticated_ledger(raw)
    if payload is None:
        raise DerivationalReceiptError(
            "current reachable-auxiliary supplement cannot bind raw receipt: "
            + augmentation_error
        )
    candidates = _candidate_items(payload)

    parser, parser_error = _source_parser()
    if parser is None:
        raise DerivationalReceiptError(parser_error)
    interface_path = paper_dir / "PaperInterface.lean"
    declarations = parser.parse_local_declarations(ROOT, [interface_path])
    by_name = {declaration.name: declaration for declaration in declarations}
    if len(by_name) != len(declarations):
        raise DerivationalReceiptError("PaperInterface has duplicate parsed declaration identities")
    statement_map, _ = _read_json(paper_dir / "audit" / "paper_statement_map.json")
    semantic_items = payload.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        raise DerivationalReceiptError("raw audit has no semantic-model item ledger")

    entries: list[dict[str, object]] = []
    for item in candidates:
        target = str(item.get("declaration") or "").strip()
        declaration = by_name.get(target)
        if declaration is None:
            raise DerivationalReceiptError(f"{target} is absent from current PaperInterface")
        if (
            declaration.kind != str(item.get("kind") or "").strip()
            or declaration.source_file.replace("\\", "/")
            != str(item.get("source_file") or "").strip().replace("\\", "/")
            or declaration.line != item.get("line")
        ):
            raise DerivationalReceiptError(
                f"{target} does not match its frozen raw source coordinate"
            )
        closure, closure_error = derivational_auxiliary_local_closure(
            parser, declarations, target
        )
        if closure_error or closure is None:
            raise DerivationalReceiptError(f"{target}: {closure_error}")
        routes = item.get("transitively_referenced_from")
        if not isinstance(routes, list) or not routes:
            raise DerivationalReceiptError(f"{target} has no selected-root route")
        root_paths: list[dict[str, object]] = []
        for route in routes:
            if not isinstance(route, Mapping):
                raise DerivationalReceiptError(f"{target} has a malformed selected-root route")
            parent_name = str(route.get("selected_declaration") or "").strip()
            parent_matches = [
                candidate
                for candidate in semantic_items
                if isinstance(candidate, Mapping)
                and str(candidate.get("qualified_declaration") or "").strip()
                == parent_name
            ]
            if len(parent_matches) != 1:
                raise DerivationalReceiptError(
                    f"{target} route root {parent_name} has no unique semantic-model item"
                )
            parent = parent_matches[0]
            parent_row = str(parent.get("row") or "").strip()
            if not parent_row:
                raise DerivationalReceiptError(f"{target} route root has no review row")
            parent_declaration = by_name.get(parent_name)
            if parent_declaration is None:
                raise DerivationalReceiptError(
                    f"{target} route root {parent_name} is absent from PaperInterface"
                )
            association_error = _terminal_root_source_association_error(
                parser=parser,
                parent=parent,
                parent_qualified=parent_name,
                parent_declaration=parent_declaration,
                statement_map=statement_map,
                administrative_projection_rebind=None,
            )
            if association_error:
                raise DerivationalReceiptError(
                    f"{target} route root source association is not current: {association_error}"
                )
            association = _receipt_source_association(parent, None)
            if association is None:
                raise DerivationalReceiptError(
                    f"{target} route root has no direct source association"
                )
            root_paths.append(
                _derivational_root_path_identity(
                    route,
                    parent,
                    judgment_key=f"semantic-model::{parent_row}",
                    association=association,
                )
            )
        entries.append(
            {
                "declaration": target,
                "target_identity": _normalized_declaration_identity(
                    parser, declaration
                ),
                "local_lexical_closure": closure,
                "local_lexical_closure_sha256": derivational_auxiliary_local_closure_sha256(
                    closure
                ),
                "root_paths": sorted(
                    root_paths,
                    key=lambda path: (
                        str(path["selected_declaration"]),
                        str(path["raw_route_sha256"]),
                    ),
                ),
            }
        )
    return {
        "schema": _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
        "kind": _DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
        "paper": paper,
        "complete_for_current_raw": True,
        "raw_source_record": _raw_binding(payload),
        "entries": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the receipt in the selected paper audit directory",
    )
    args = parser.parse_args()
    try:
        receipt = build_receipt(paper=args.paper)
    except DerivationalReceiptError as error:
        print(f"{args.paper}: {error}", file=sys.stderr)
        return 1
    if args.write:
        path = ROOT / "papers" / args.paper / "audit" / _DERIVATIONAL_AUXILIARY_RECEIPT_FILE
        _atomic_write(path, receipt)
        print(f"{args.paper}: wrote {path}")
    else:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
