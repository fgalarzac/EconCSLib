#!/usr/bin/env python3
"""Materialize exact receipts for audited transparent terminal propositions.

The source-record scan already exposes transparent terminal definitions in the
expanded semantic surface.  This utility does not rerun Lean or source review:
it pins every currently unresolved ``abbrev : Prop`` terminal to its inspected
body, each selected source-associated root path, and the schema-2 raw
dependency manifest those checks consume.  The shared validator remains the
authority at consumption time.
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
        _TRANSPARENT_TERMINAL_RECEIPT_FILE,
        _TRANSPARENT_TERMINAL_RECEIPT_KIND,
        _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
        _TRANSPARENT_TERMINAL_REQUIRED_SEMANTIC_FLAGS,
        _normalized_declaration_identity,
        _source_parser,
        _terminal_root_source_association_error,
        _terminal_route_identity,
        _transparent_terminal_target_closure_error,
        _transparent_terminal_record_identity,
        auxiliary_receipt_semantic_raw_binding,
    )
    from scripts.source_record_auxiliary_routing_supplement import (
        current_auxiliary_routing_context,
    )
except ModuleNotFoundError:  # pragma: no cover - direct execution fallback.
    from internal_derivational_auxiliary import (
        _TRANSPARENT_TERMINAL_RECEIPT_FILE,
        _TRANSPARENT_TERMINAL_RECEIPT_KIND,
        _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
        _TRANSPARENT_TERMINAL_REQUIRED_SEMANTIC_FLAGS,
        _normalized_declaration_identity,
        _source_parser,
        _terminal_root_source_association_error,
        _terminal_route_identity,
        _transparent_terminal_target_closure_error,
        _transparent_terminal_record_identity,
        auxiliary_receipt_semantic_raw_binding,
    )
    from source_record_auxiliary_routing_supplement import (
        current_auxiliary_routing_context,
    )


class TerminalReceiptError(ValueError):
    """Raised when the exact terminal receipt cannot be constructed."""


def _read_json(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as error:
        raise TerminalReceiptError(f"could not read {path}: {error}") from error
    if not isinstance(payload, dict):
        raise TerminalReceiptError(f"{path} is not a JSON object")
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
        payload, receipt_kind=_TRANSPARENT_TERMINAL_RECEIPT_KIND
    )
    if binding is None:
        raise TerminalReceiptError(
            "raw v10 receipt has no complete auxiliary dependency manifest: " + error
        )
    return binding


def _candidates(payload: Mapping[str, object]) -> list[dict[str, Any]]:
    candidates = [
        dict(item)
        for item in payload.get("unresolved_reachable_paper_interface_auxiliaries")
        or []
        if isinstance(item, Mapping)
        and str(item.get("kind") or "").strip() == "abbrev"
        and str(item.get("disposition") or "").strip()
        == "missing_source_map_route_or_quarantine"
        and item.get("source_map_routes") == []
        and item.get("quarantined") is False
        and not str(item.get("quarantine_source_reason") or "").strip()
    ]
    candidates.sort(key=lambda item: str(item.get("declaration") or ""))
    names = [str(item.get("declaration") or "").strip() for item in candidates]
    if not candidates or not all(names) or len(set(names)) != len(names):
        raise TerminalReceiptError(
            "authenticated routing ledger has no unique unresolved terminal-abbrev set"
        )
    return candidates


def build_receipt(*, paper: str) -> dict[str, object]:
    paper_dir = ROOT / "papers" / paper
    raw_path = paper_dir / "audit" / "source_record_audit.json"
    raw, _raw_bytes = _read_json(raw_path)
    if str(raw.get("paper") or "").strip() != paper:
        raise TerminalReceiptError("raw audit paper does not match --paper")
    routing_context, routing_error = current_auxiliary_routing_context(
        root=ROOT,
        paper_dir=paper_dir,
        paper=paper,
        audit_payload=raw,
    )
    if routing_context is None:
        raise TerminalReceiptError(
            "current reachable-auxiliary supplement is unavailable: " + routing_error
        )
    payload, augmentation_error = routing_context.audit_payload_with_authenticated_ledger(raw)
    if payload is None:
        raise TerminalReceiptError(
            "current reachable-auxiliary supplement cannot bind raw receipt: "
            + augmentation_error
        )
    candidates = _candidates(payload)
    parser, parser_error = _source_parser()
    if parser is None:
        raise TerminalReceiptError(parser_error)
    interface_path = paper_dir / "PaperInterface.lean"
    declarations = parser.parse_local_declarations(ROOT, [interface_path])
    by_name = {declaration.name: declaration for declaration in declarations}
    if len(by_name) != len(declarations):
        raise TerminalReceiptError("PaperInterface has duplicate parsed declaration identities")
    statement_map, _ = _read_json(paper_dir / "audit" / "paper_statement_map.json")
    semantic_items = payload.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        raise TerminalReceiptError("raw audit has no semantic-model item ledger")

    entries: list[dict[str, object]] = []
    for item in candidates:
        target = str(item.get("declaration") or "").strip()
        declaration = by_name.get(target)
        if declaration is None or declaration.kind != "abbrev":
            raise TerminalReceiptError(f"{target} is not a current PaperInterface abbrev")
        if (
            declaration.source_file.replace("\\", "/")
            != str(item.get("source_file") or "").strip().replace("\\", "/")
            or declaration.line != item.get("line")
        ):
            raise TerminalReceiptError(
                f"{target} does not match its frozen raw source coordinate"
            )
        target_identity = _normalized_declaration_identity(parser, declaration)
        if target_identity["result_type"] != "Prop":
            raise TerminalReceiptError(f"{target} is not an explicit proposition surface")
        routes = item.get("transitively_referenced_from")
        if not isinstance(routes, list) or not routes:
            raise TerminalReceiptError(f"{target} has no selected-root route")
        terminal_identity: dict[str, object] | None = None
        root_paths: list[dict[str, object]] = []
        for route in routes:
            if not isinstance(route, Mapping):
                raise TerminalReceiptError(f"{target} has a malformed selected-root route")
            parent_name = str(route.get("selected_declaration") or "").strip()
            parent_matches = [
                candidate
                for candidate in semantic_items
                if isinstance(candidate, Mapping)
                and str(candidate.get("qualified_declaration") or "").strip()
                == parent_name
            ]
            if len(parent_matches) != 1:
                raise TerminalReceiptError(
                    f"{target} route root {parent_name} has no unique semantic-model item"
                )
            parent = parent_matches[0]
            parent_row = str(parent.get("row") or "").strip()
            parent_declaration = by_name.get(parent_name)
            if not parent_row or parent_declaration is None:
                raise TerminalReceiptError(f"{target} route root is incomplete")
            association_error = _terminal_root_source_association_error(
                parser=parser,
                parent=parent,
                parent_qualified=parent_name,
                parent_declaration=parent_declaration,
                statement_map=statement_map,
                administrative_projection_rebind=None,
            )
            if association_error:
                raise TerminalReceiptError(
                    f"{target} route root source association is not current: {association_error}"
                )
            expanded = parent.get("expanded_lean_surface")
            surface = (
                expanded.get("terminal_term_dependency_surface")
                if isinstance(expanded, Mapping)
                else None
            )
            if not isinstance(surface, Mapping) or surface.get("scan_complete") is not True:
                raise TerminalReceiptError(f"{target} route root has no complete terminal scan")
            target_closure_error = _transparent_terminal_target_closure_error(
                surface, target
            )
            if target_closure_error:
                raise TerminalReceiptError(
                    f"{target} route root {target_closure_error}"
                )
            matches = [
                record
                for record in surface.get("transparent_definitions") or []
                if isinstance(record, Mapping)
                and str(record.get("declaration") or "").strip() == target
            ]
            if len(matches) != 1:
                raise TerminalReceiptError(
                    f"{target} route root does not expose exactly one terminal body"
                )
            record = matches[0]
            current_terminal = _transparent_terminal_record_identity(record)
            flags = current_terminal.get("semantic_construct_flags")
            if (
                current_terminal.get("kind") != "abbrev"
                or current_terminal.get("result_type") != "Prop"
                or current_terminal.get("body_surface_inspectable") is not True
                or current_terminal.get("semantic_relevant") is not True
                or not isinstance(flags, Mapping)
                or any(flags.get(flag) is not True for flag in _TRANSPARENT_TERMINAL_REQUIRED_SEMANTIC_FLAGS)
            ):
                raise TerminalReceiptError(
                    f"{target} route root lacks a full inspected model/payoff terminal body"
                )
            chain = [
                str(value).strip()
                for value in record.get("dependency_chain") or []
                if str(value).strip()
            ]
            if not chain or chain[-1] != target:
                raise TerminalReceiptError(
                    f"{target} route root lacks a complete terminal dependency chain"
                )
            if terminal_identity is None:
                terminal_identity = current_terminal
            elif terminal_identity != current_terminal:
                raise TerminalReceiptError(
                    f"{target} has inconsistent inspected terminal bodies across roots"
                )
            root_paths.append(
                _terminal_route_identity(
                    route,
                    parent,
                    judgment_key=f"semantic-model::{parent_row}",
                    transparent_definition_chain=chain,
                )
            )
        if terminal_identity is None:
            raise TerminalReceiptError(f"{target} has no inspected terminal body")
        entries.append(
            {
                "declaration": target,
                "target_identity": target_identity,
                "transparent_definition": terminal_identity,
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
        "schema": _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
        "kind": _TRANSPARENT_TERMINAL_RECEIPT_KIND,
        "paper": paper,
        "raw_source_record": _raw_binding(payload),
        "entries": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    try:
        receipt = build_receipt(paper=args.paper)
    except TerminalReceiptError as error:
        print(f"{args.paper}: {error}", file=sys.stderr)
        return 1
    if args.write:
        path = ROOT / "papers" / args.paper / "audit" / _TRANSPARENT_TERMINAL_RECEIPT_FILE
        _atomic_write(path, receipt)
        print(f"{args.paper}: wrote {path}")
    else:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
