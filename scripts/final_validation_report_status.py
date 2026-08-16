#!/usr/bin/env python3
"""Lightweight controlled-status checks for human-facing final reports.

This module deliberately depends only on Markdown text. The closeout planner
uses it before expensive evidence or Lean work, while the repository audit
uses the same parsing contract for its final human-facing validation.
"""

from __future__ import annotations

import re


CONTROLLED_PAPER_STATUSES = frozenset(
    {
        "formalized",
        "formalized with caveat",
        "conditional",
        "partially formalized",
        "not formalized",
        "paper draft",
        "not started",
    }
)
FINAL_REPORT_STATUS_LINE_RE = re.compile(
    r"^\s*(?:[-*+]\s*)?(?:Completion status|Lean formalization status)\s*:\s*"
    r"(?P<status>.+?)\s*$"
)
FINAL_REPORT_CLOSEOUT_STATUS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Closeout\s+Status\b"
)
_STATUS_LABELS = (
    "partially formalized",
    "formalized with caveat",
    "not formalized",
    "paper draft",
    "not started",
    "formalized",
    "conditional",
    "complete",
    "completed",
)


def normalized_paper_status(value: object) -> str:
    """Return one status spelling suitable for exact controlled comparisons."""

    return value.strip().lower() if isinstance(value, str) else ""


def final_report_declared_statuses(report_text: str) -> set[str]:
    """Extract controlled whole-paper statuses from the Closeout Status section.

    Historical discussion and fenced examples do not count. The parser accepts
    ordinary Markdown emphasis around a controlled status and a trailing
    explanatory clause, but never derives status from theorem text.
    """

    statuses: set[str] = set()
    heading_level: int | None = None
    in_fence = False
    for raw_line in report_text.splitlines():
        stripped = raw_line.lstrip()
        if stripped.startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if heading_level is None:
            heading = FINAL_REPORT_CLOSEOUT_STATUS_RE.match(raw_line)
            if heading is None:
                continue
            marker = re.match(r"^(#+)", raw_line)
            if marker is None:
                continue
            heading_level = len(marker.group(1))
            continue
        next_heading = re.match(r"^(#+)\s+", raw_line)
        if next_heading is not None and len(next_heading.group(1)) <= heading_level:
            break
        line = re.sub(r"[`*_]", "", raw_line)
        match = FINAL_REPORT_STATUS_LINE_RE.match(line)
        if match is None:
            continue
        value = match.group("status").strip().lower()
        for label in _STATUS_LABELS:
            if re.match(rf"{re.escape(label)}(?=$|[\s.;,:/])", value):
                statuses.add("formalized" if label in {"complete", "completed"} else label)
                break
    return statuses


def report_status_alignment_errors(status: object, report_text: str) -> tuple[str, ...]:
    """Return deterministic report/status contract errors for a controlled status."""

    normalized_status = normalized_paper_status(status)
    declared = final_report_declared_statuses(report_text)
    errors: list[str] = []
    if len(declared) > 1:
        errors.append(
            "final validation report has mutually exclusive whole-paper status "
            "declarations in its Closeout Status section: "
            + ", ".join(sorted(declared))
        )
    if normalized_status not in CONTROLLED_PAPER_STATUSES:
        return tuple(errors)
    if not declared:
        errors.append(
            "final validation report has no parseable controlled whole-paper status "
            "in its Closeout Status section; it must match paper-local status.json "
            f"(`{normalized_status}`)"
        )
    elif declared != {normalized_status}:
        errors.append(
            "final validation report declares `"
            + ", ".join(sorted(declared))
            + "` in its Closeout Status section, but paper-local status.json "
            + f"declares `{normalized_status}`"
        )
    return tuple(errors)
