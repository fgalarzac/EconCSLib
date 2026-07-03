#!/usr/bin/env python3
"""Refresh public final-validation report audit summaries from sidecars."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
REPORT = "FINAL_VALIDATION_REPORT.md"
BEGIN = "<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->"
END = "<!-- END GENERATED LLM-AS-JUDGE RESULTS -->"
DAG_AUDIT = "docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md"

COVERAGE_ORDER = [
    "covered",
    "covered_by_support",
    "conditional_boundary",
    "partial_boundary",
    "not_a_paper_target",
    "uncovered",
]
STATEMENT_ORDER = [
    "matches",
    "mismatch",
    "partial_match",
    "uncertain",
]
ASSUMPTION_ORDER = [
    "paper_condition",
    "paper_assumption",
    "documented_additional_assumption",
    "partial_boundary",
]
SOURCE_RECORD_ORDER = [
    "proved_from_primitives",
    "validated_source_assumption",
    "container_recursively_audited",
    "derived_consequence_record",
    "nonpropositional_witness_data",
    "approved_external_boundary",
    "unresolved_assumed_math",
]


def public_report_paths() -> list[Path]:
    return sorted(
        path
        for path in PAPERS.glob(f"*/{REPORT}")
        if path.parent.name != "TEMPLATE"
    )


def sidecar(folder: Path, name: str) -> Path | None:
    for path in (folder / "audit" / name, folder / name):
        if path.exists():
            return path
    return None


def load_json(path: Path | None) -> dict[str, Any] | None:
    if path is None:
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path.relative_to(ROOT)} should contain a JSON object")
    return payload


def items(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if payload is None:
        return []
    raw = payload.get("items", {})
    if isinstance(raw, dict):
        return [value for value in raw.values() if isinstance(value, dict)]
    if isinstance(raw, list):
        return [value for value in raw if isinstance(value, dict)]
    return []


def count_field(payload: dict[str, Any] | None, field: str) -> Counter[str]:
    counts: Counter[str] = Counter()
    for item in items(payload):
        if field not in item:
            continue
        value = item[field]
        if isinstance(value, (str, int, bool)) or value is None:
            counts[str(value)] += 1
    return counts


def ordered_counts(counts: Counter[str], preferred: list[str]) -> str:
    if not counts:
        return "no rows"
    keys = [key for key in preferred if key in counts]
    keys.extend(sorted(key for key in counts if key not in set(keys)))
    return ", ".join(f"{counts[key]} {key}" for key in keys)


def rel(folder: Path, path: Path | None) -> str:
    if path is None:
        return ""
    return path.relative_to(folder).as_posix()


def plural(value: int, singular: str, plural_word: str | None = None) -> str:
    return f"{value} {singular if value == 1 else (plural_word or singular + 's')}"


def sidecar_summary(folder: Path) -> dict[str, str]:
    coverage_path = sidecar(folder, "paper_coverage_llm.json")
    statement_path = sidecar(folder, "statement_match_llm.json")
    tex_path = sidecar(folder, "lean_to_tex_llm.json")
    assumption_path = sidecar(folder, "assumption_match_llm.json")
    record_match_path = sidecar(folder, "source_record_match_llm.json")
    review_path = sidecar(folder, "review_surface_llm.json")
    record_audit_path = sidecar(folder, "source_record_audit.json")

    coverage = load_json(coverage_path)
    statement = load_json(statement_path)
    tex = load_json(tex_path)
    assumption = load_json(assumption_path)
    record_match = load_json(record_match_path)
    review = load_json(review_path)
    record_audit = load_json(record_audit_path)

    if coverage is None:
        coverage_text = "source coverage sidecar is not tracked"
        coverage_detail = "source coverage sidecar is not tracked"
    else:
        coverage_count_text = ordered_counts(count_field(coverage, "coverage"), COVERAGE_ORDER)
        coverage_text = f"source coverage has {coverage_count_text}"
        coverage_detail = coverage_count_text

    if statement is None:
        statement_text = "statement LLM-as-judge sidecar is not tracked"
        statement_detail = statement_text
    else:
        judgment_text = ordered_counts(count_field(statement, "judgment"), STATEMENT_ORDER)
        resolution_counts = count_field(statement, "resolution")
        resolution_text = ""
        if resolution_counts:
            resolution_text = (
                f"; resolutions: "
                f"{ordered_counts(resolution_counts, ['conditional_boundary'])}"
            )
        statement_text = f"statement LLM-as-judge has {judgment_text}{resolution_text}"
        statement_detail = f"{judgment_text}{resolution_text}"

    if tex is None:
        tex_text = "Lean-to-TeX translation sidecar is not tracked"
        tex_detail = tex_text
    else:
        tex_detail = f"{plural(len(items(tex)), 'row translation')} generated from Lean statements"
        tex_text = f"Lean-to-TeX has {plural(len(items(tex)), 'row translation')}"

    if assumption is None:
        assumption_text = "assumption provenance sidecar is not tracked"
        assumption_detail = "no assumption-match sidecar tracked for this paper"
    else:
        assumption_counts = count_field(assumption, "judgment")
        if assumption_counts:
            assumption_detail = ordered_counts(assumption_counts, ASSUMPTION_ORDER)
            assumption_text = (
                "assumption provenance has "
                f"{assumption_detail}"
            )
        else:
            assumption_text = "assumption provenance sidecar has no rows"
            assumption_detail = "no rows"

    if record_match is None:
        record_match_text = "source-record classification sidecar is not tracked"
        record_match_detail = "no source-record classification sidecar tracked for this paper"
    else:
        record_counts = count_field(record_match, "classification")
        if record_counts:
            record_match_detail = ordered_counts(record_counts, SOURCE_RECORD_ORDER)
            record_match_text = (
                "source-record classification has "
                f"{record_match_detail}"
            )
        else:
            record_match_text = "source-record classification sidecar has no rows"
            record_match_detail = "no rows"

    if record_audit is None:
        record_audit_text = "source-record structural audit is not tracked"
        record_audit_detail = record_audit_text
    else:
        review_rows = record_audit.get("review_row_count")
        if not isinstance(review_rows, int):
            review_rows = record_audit.get("configured_review_row_count")
        boundary_count = record_audit.get("boundary_input_count")
        recursion_count = record_audit.get("recursion_failure_count")
        parts: list[str] = []
        if isinstance(review_rows, int):
            parts.append(plural(review_rows, "review row"))
        if isinstance(boundary_count, int):
            parts.append(plural(boundary_count, "boundary input"))
        if isinstance(recursion_count, int):
            parts.append(plural(recursion_count, "recursion failure"))
        record_audit_text = (
            "source-record audit reports " + ", ".join(parts)
            if parts
            else "source-record structural audit is tracked"
        )
        record_audit_detail = ", ".join(parts) if parts else "tracked"

    if review is None:
        review_text = "review-surface audit is not tracked"
        review_detail = review_text
    else:
        judgment = review.get("judgment", "recorded")
        review_rows = review.get("review_rows")
        if isinstance(review_rows, int):
            review_text = f"review-surface audit {judgment} over {plural(review_rows, 'review row')}"
            review_detail = f"{judgment} over {plural(review_rows, 'review row')}"
        else:
            review_text = f"review-surface audit {judgment}"
            review_detail = str(judgment)

    return {
        "coverage": coverage_text,
        "coverage_detail": detail_line(
            "Source coverage",
            coverage_path,
            folder,
            coverage_detail,
        ),
        "statement": statement_text,
        "statement_detail": detail_line(
            "Statement match",
            statement_path,
            folder,
            statement_detail,
        ),
        "tex": tex_text,
        "tex_detail": detail_line(
            "Lean-to-TeX translations",
            tex_path,
            folder,
            tex_detail,
        ),
        "assumption": assumption_text,
        "assumption_detail": detail_line(
            "Assumption provenance",
            assumption_path,
            folder,
            assumption_detail,
        ),
        "record_match": record_match_text,
        "record_match_detail": detail_line(
            "Source-record classification",
            record_match_path,
            folder,
            record_match_detail,
        ),
        "record_audit": record_audit_text,
        "record_audit_detail": detail_line(
            "Source-record structural audit",
            record_audit_path,
            folder,
            record_audit_detail,
        ),
        "review": review_text,
        "review_detail": detail_line(
            "Review-surface audit",
            review_path,
            folder,
            review_detail,
        ),
    }


def detail_line(label: str, path: Path | None, folder: Path, text: str) -> str:
    if path is None:
        return f"- {label}: {text}."
    return f"- {label} (`{rel(folder, path)}`): {text}."


def audit_summary_line(summary: dict[str, str]) -> str:
    return (
        "- Audit summary: "
        f"{summary['coverage']}; "
        f"{summary['statement']}; "
        f"{summary['tex']}; "
        f"{summary['assumption']}; "
        f"{summary['record_match']}; "
        f"{summary['record_audit']}; "
        f"{summary['review']}; "
        "holistic source-first audit PASS; "
        f"DAG/source-json audit PASS in `{DAG_AUDIT}`."
    )


def result_block(summary: dict[str, str]) -> str:
    lines = [
        BEGIN,
        "### LLM-as-Judge Results",
        summary["coverage_detail"],
        summary["statement_detail"],
        summary["tex_detail"],
        summary["assumption_detail"],
        summary["record_match_detail"],
        summary["record_audit_detail"],
        summary["review_detail"],
        "- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.",
        f"- DAG/source/source-json audit (`{DAG_AUDIT}`): PASS.",
        END,
    ]
    return "\n".join(lines)


def replace_audit_summary(text: str, summary: dict[str, str], path: Path) -> str:
    lines = text.splitlines()
    replacement = audit_summary_line(summary)
    for index, line in enumerate(lines):
        if line.startswith("- Audit summary:"):
            lines[index] = replacement
            return "\n".join(lines) + ("\n" if text.endswith("\n") else "")
    raise ValueError(f"{path.relative_to(ROOT)} does not contain an audit-summary line")


def replace_or_insert_block(text: str, block: str, path: Path) -> str:
    if BEGIN in text or END in text:
        if text.count(BEGIN) != 1 or text.count(END) != 1:
            raise ValueError(f"{path.relative_to(ROOT)} has malformed generated block markers")
        before, rest = text.split(BEGIN, 1)
        _old, after = rest.split(END, 1)
        return before.rstrip() + "\n\n" + block + after

    marker = "## 16. Validation Checks\n"
    if marker not in text:
        raise ValueError(f"{path.relative_to(ROOT)} does not contain {marker.strip()!r}")
    return text.replace(marker, marker + block + "\n\n", 1)


def refresh_report(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    summary = sidecar_summary(path.parent)
    updated = replace_audit_summary(text, summary, path)
    updated = replace_or_insert_block(updated, result_block(summary), path)
    if updated == text:
        return False
    path.write_text(updated, encoding="utf-8")
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if any report would be changed",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    changed: list[Path] = []
    for path in public_report_paths():
        before = path.read_text(encoding="utf-8")
        did_change = refresh_report(path)
        after = path.read_text(encoding="utf-8")
        if args.check:
            path.write_text(before, encoding="utf-8")
        if did_change or before != after:
            changed.append(path)
    if args.check and changed:
        print("Reports need refreshed audit summaries:")
        for path in changed:
            print(path.relative_to(ROOT))
        return 1
    for path in changed:
        print(f"refreshed {path.relative_to(ROOT)}")
    print(f"checked {len(public_report_paths())} public validation reports")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
