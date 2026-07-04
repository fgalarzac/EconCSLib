#!/usr/bin/env python3
"""Scaffold source-first holistic audit notes for public paper folders.

This script intentionally does not write PASS artifacts. A holistic source
audit must be agent-authored after reading the source paper/inventory and the
Lean interface, because its purpose is to catch omissions that sidecar-driven
row-local checks can miss.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from textwrap import shorten


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
CLOSEOUT_STATUSES = {
    "formalized",
    "formalized with caveat",
    "formalized with documented caveat",
}


def load_json(path: Path) -> dict:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def json_sidecar(folder: Path, filename: str) -> Path | None:
    for candidate in (folder / "audit" / filename, folder / filename):
        if candidate.exists():
            return candidate
    return None


def rel(path: Path | None) -> str:
    if path is None:
        return "missing"
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def markdown_escape(text: object) -> str:
    return str(text).replace("\n", " ").strip()


def source_items(source_map: dict) -> dict:
    raw = source_map.get("items")
    return raw if isinstance(raw, dict) else {}


def sidecar_items(payload: dict) -> dict:
    raw = payload.get("items")
    return raw if isinstance(raw, dict) else {}


def coverage_counts(payload: dict) -> tuple[int, int, int, int]:
    items = sidecar_items(payload)
    covered = conditional = support = missing = 0
    for item in items.values():
        if not isinstance(item, dict):
            missing += 1
            continue
        status = str(item.get("coverage") or item.get("judgment") or "").strip().lower()
        if status in {"covered", "direct", "covered_directly", "matches"}:
            covered += 1
        elif status in {"conditional", "covered_with_conditional_boundaries"}:
            conditional += 1
        elif status in {"support", "support_declaration", "support_only"}:
            support += 1
        else:
            missing += 1
    return covered, conditional, support, missing


def statement_counts(payload: dict) -> tuple[int, int, int]:
    items = sidecar_items(payload)
    matches = mismatches = unknown = 0
    for item in items.values():
        if not isinstance(item, dict):
            unknown += 1
            continue
        if item.get("matches") is True or str(item.get("judgment") or "").lower() == "matches":
            matches += 1
        elif item.get("matches") is False or str(item.get("judgment") or "").lower() in {
            "mismatch",
            "does_not_match",
        }:
            mismatches += 1
        else:
            unknown += 1
    return matches, mismatches, unknown


def source_record_summary(folder: Path) -> str:
    audit_path = json_sidecar(folder, "source_record_audit.json")
    judge_path = json_sidecar(folder, "source_record_match_llm.json")
    audit = load_json(audit_path) if audit_path else {}
    judge = load_json(judge_path) if judge_path else {}
    boundary = audit.get("boundary_input_count", 0)
    recursive = audit.get("recursive_field_count", 0)
    judgments = len(sidecar_items(judge))
    if not audit_path and not judge_path:
        return "No source-record boundary inputs are recorded for this paper."
    return (
        f"{boundary} boundary-shaped visible input(s), {recursive} recursive "
        f"source-record field(s), and {judgments} current source-record judgment(s) "
        f"from `{rel(audit_path)}` and `{rel(judge_path)}`."
    )


def assumption_summary(folder: Path, status: dict) -> str:
    review_surface = status.get("review_surface")
    review_surface = review_surface if isinstance(review_surface, dict) else {}
    assumption_names = review_surface.get("assumption_names")
    if not isinstance(assumption_names, list):
        assumption_names = []
    assumption_path = json_sidecar(folder, "assumption_match_llm.json")
    assumptions = sidecar_items(load_json(assumption_path)) if assumption_path else {}
    if not assumption_names:
        return "No explicit source-condition or assumption rows are listed."
    return (
        f"{len(assumption_names)} explicit source-condition/assumption row(s) are listed; "
        f"{len(assumptions)} row(s) have LLM provenance judgments in `{rel(assumption_path)}`."
    )


def write_audit(folder: Path, *, overwrite: bool = False) -> bool:
    out_path = folder / "docs" / "AGENT_SOURCE_AUDIT.md"
    if out_path.exists() and not overwrite:
        return False
    out_path.parent.mkdir(parents=True, exist_ok=True)

    status_path = folder / "status.json"
    status = load_json(status_path)
    paper_id = status.get("id") or folder.name
    title = status.get("title") or folder.name
    authors = status.get("authors") or "authors not recorded"
    source_version = status.get("source_version") or "source version not recorded"
    build_target = status.get("build_target") or f"lake build {paper_id}"
    review_surface = status.get("review_surface")
    review_surface = review_surface if isinstance(review_surface, dict) else {}
    include_names = review_surface.get("include_names")
    if not isinstance(include_names, list):
        include_names = []
    assumption_names = review_surface.get("assumption_names")
    if not isinstance(assumption_names, list):
        assumption_names = []
    auxiliary_names = review_surface.get("auxiliary_names")
    if not isinstance(auxiliary_names, list):
        auxiliary_names = []

    candidate_map_path = folder / "audit" / "paper_statement_map.json"
    map_path = candidate_map_path if candidate_map_path.exists() else None
    coverage_path = json_sidecar(folder, "paper_coverage_llm.json")
    statement_path = json_sidecar(folder, "statement_match_llm.json")
    source_map = load_json(map_path) if map_path else {}
    coverage = load_json(coverage_path) if coverage_path else {}
    statements = load_json(statement_path) if statement_path else {}
    inventory = source_items(source_map)
    covered, conditional, support, missing = coverage_counts(coverage)
    matches, mismatches, unknown = statement_counts(statements)

    lines: list[str] = [
        f"# Agent Source Audit: {paper_id}",
        "",
        "## Overall status: NEEDS AGENT REVIEW",
        "",
        (
            "This is a scaffold for a source-first holistic audit of the current public "
            f"{paper_id} formalization of "
            f"*{markdown_escape(title)}* by {markdown_escape(authors)}."
        ),
        "",
        (
            "Before changing this status to PASS, an agent must perform an "
            "independent source-first read of the source paper or source text, "
            "build or verify the source inventory from the source itself, "
            "inspect the paper-facing `PaperInterface.lean` and Lean statements "
            "for omissions, hidden strengthening/weakening, and semantic mismatches, "
            "and then use the source-to-dashboard, "
            "row-local statement, assumption-provenance, and source-record "
            "sidecars only as supporting evidence. A completed audit must not "
            "merely summarize existing sidecars; it must explain the agent's own "
            "holistic judgment about coverage and semantic fit."
        ),
        "",
        f"- Source version: {markdown_escape(source_version)}",
        f"- Source inventory sidecar: `{rel(map_path)}`",
        f"- Coverage sidecar: `{rel(coverage_path)}`",
        f"- Statement sidecar: `{rel(statement_path)}`",
        f"- Lean build target: `{markdown_escape(build_target)}`",
        "",
        "## Source Inventory",
        "",
        f"The curated source inventory contains {len(inventory)} source-facing item(s):",
        "",
    ]

    if inventory:
        for key, item in inventory.items():
            item = item if isinstance(item, dict) else {}
            statement = shorten(
                markdown_escape(item.get("statement") or item.get("source_statement") or key),
                width=320,
                placeholder="...",
            )
            location = markdown_escape(
                item.get("source_location")
                or item.get("source_evidence")
                or item.get("source_text_file")
                or "source location recorded in sidecar"
            )
            lines.append(f"- `{key}` ({location}): {statement}")
    else:
        lines.append("- No structured source inventory was found; this should be treated as a blocker.")

    lines.extend(
        [
            "",
            "## Lean Interface Comparison",
            "",
            (
                f"The paper-facing interface exposes {len(include_names)} reviewed "
                f"row(s), {len(assumption_names)} explicit source-condition/assumption "
                f"row(s), and {len(auxiliary_names)} auxiliary proof-facing row(s)."
            ),
            "",
            f"- Interface path: `{markdown_escape(review_surface.get('source_file') or status.get('paper_interface', {}).get('path') or 'PaperInterface.lean')}`",
            f"- Reviewed rows: {', '.join(f'`{name}`' for name in include_names) if include_names else 'none recorded'}",
            f"- Assumption rows: {', '.join(f'`{name}`' for name in assumption_names) if assumption_names else 'none'}",
        ]
    )
    if auxiliary_names:
        lines.append(f"- Auxiliary rows: {', '.join(f'`{name}`' for name in auxiliary_names)}")

    lines.extend(
        [
            "",
            "## Machine Audit Results",
            "",
            (
                f"- Source-to-dashboard coverage: {covered}/{len(sidecar_items(coverage))} "
                f"covered directly, {conditional} conditional, {support} support-only, "
                f"{missing} missing/unknown."
            ),
            (
                f"- Row-local statement matching: {matches}/{len(sidecar_items(statements))} "
                f"matches, {mismatches} mismatch, {unknown} unknown."
            ),
            f"- Assumption/source-condition provenance: {assumption_summary(folder, status)}",
            f"- Source-record audit: {source_record_summary(folder)}",
            "",
            "## Findings",
            "",
        ]
    )

    caveat = str(status.get("main_caveat") or "").strip()
    if missing or mismatches or unknown:
        lines.append(
            "The structured sidecars contain non-passing rows. Do not treat this "
            "paper as fully closed until those rows are resolved."
        )
    elif caveat:
        lines.append(
            "The structured audit lanes pass for the current public status. The "
            f"paper records this explicit status note: {caveat}"
        )
    else:
        lines.append(
            "This scaffold has not performed the independent source-first read. "
            "A human or agent must replace this finding after reading the source "
            "and Lean interface holistically."
        )

    lines.extend(
        [
            "",
            "## Why This Audit Exists",
            "",
            (
                "The structured LLM-as-judge lanes are row-local. This artifact "
                "records a separate source-inventory-to-interface pass so future "
                "agents must start from the paper's claims rather than from the "
                "rows that already happen to be exposed."
            ),
            "",
        ]
    )

    out_path.write_text("\n".join(lines), encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper", action="append", help="paper folder to generate")
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    changed: list[str] = []
    folders = [PAPERS / paper for paper in args.paper] if args.paper else sorted(PAPERS.iterdir())
    for folder in folders:
        if not folder.is_dir():
            continue
        status = load_json(folder / "status.json")
        if status.get("status") not in CLOSEOUT_STATUSES:
            continue
        if write_audit(folder, overwrite=args.overwrite):
            changed.append(folder.name)
    for paper_id in changed:
        print(paper_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
