#!/usr/bin/env python3
"""Shared deterministic document gates for paper closeout.

The planner may use these checks to avoid work that the strict closeout would
unconditionally reject.  They are never acceptance evidence: the strict
transaction still rereads the same files and validates all semantic and Lean
inputs at its final boundary.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


AGENT_SOURCE_AUDIT_RELATIVE_PATH = Path("docs/AGENT_SOURCE_AUDIT.md")
FINAL_VALIDATION_REPORT_NAME = "FINAL_VALIDATION_REPORT.md"
POST_FORMALIZATION_AUDIT_RELATIVE_PATH = Path("docs/POST_FORMALIZATION_AUDIT.md")

STALE_PLACEHOLDER_RE = re.compile(
    r"(?mi)"
    r"^\s*-\s*(?:Rendered artifact|Topology|Layout)\s*:\s*not checked\s*$|"
    r"^\s*-\s*Not run\.\s*$|"
    r"\b(?:TODO|TBD|to be filled|not yet rendered|not inspected)\b"
)
_AGENT_SOURCE_AUDIT_PASS_RE = re.compile(r"^##\s+Overall status:\s+PASS\s*$", re.M)
_AGENT_SOURCE_AUDIT_SCAFFOLD_RE = re.compile(
    r"NEEDS AGENT REVIEW|scaffold has not performed", re.I
)
_AGENT_SOURCE_AUDIT_REQUIRED_PHRASES = (
    "independent source-first",
    "not merely summarize existing sidecars",
    "source inventory from the source itself",
    "omissions, hidden strengthening/weakening, and semantic mismatches",
)


@dataclass(frozen=True)
class CloseoutDocumentHardError:
    """One strict ERROR-class document condition, with its owning path."""

    path: Path
    message: str


def closeout_document_hard_errors(
    folder: Path,
    *,
    corrected_scope_current: bool,
    post_formalization_audit: Path | None = None,
) -> list[CloseoutDocumentHardError]:
    """Return strict ERROR-class document failures for one paper.

    ``corrected_scope_current`` must be the evidence-gate result used by the
    caller. ``post_formalization_audit`` permits the strict legacy-reader path
    while the planner uses the organized default. The corrected-scope exception
    applies only to the historical source-first audit requirement; it never
    suppresses stale template text in the researcher-facing reports.
    """

    errors: list[CloseoutDocumentHardError] = []
    report = folder / FINAL_VALIDATION_REPORT_NAME
    post_audit = post_formalization_audit or (
        folder / POST_FORMALIZATION_AUDIT_RELATIVE_PATH
    )
    agent_source_audit = folder / AGENT_SOURCE_AUDIT_RELATIVE_PATH

    if report.is_file():
        try:
            report_text = report.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                CloseoutDocumentHardError(
                    report,
                    "completed-paper final validation report is unreadable: " + str(exc),
                )
            )
        else:
            if STALE_PLACEHOLDER_RE.search(report_text):
                errors.append(
                    CloseoutDocumentHardError(
                        report,
                        "completed-paper final validation report still contains stale "
                        "placeholder audit language",
                    )
                )

    if post_audit.is_file():
        try:
            post_audit_text = post_audit.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                CloseoutDocumentHardError(
                    post_audit,
                    "completed-paper post-formalization audit is unreadable: " + str(exc),
                )
            )
        else:
            if STALE_PLACEHOLDER_RE.search(post_audit_text):
                errors.append(
                    CloseoutDocumentHardError(
                        post_audit,
                        "completed-paper post-formalization audit still contains stale "
                        "placeholder audit language",
                    )
                )

    if corrected_scope_current:
        return errors

    if not agent_source_audit.is_file():
        errors.append(
            CloseoutDocumentHardError(
                agent_source_audit,
                "completed paper is missing `docs/AGENT_SOURCE_AUDIT.md` "
                "source-first holistic audit",
            )
        )
        return errors

    try:
        agent_audit_text = agent_source_audit.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(
            CloseoutDocumentHardError(
                agent_source_audit,
                "completed-paper source-first holistic audit is unreadable: " + str(exc),
            )
        )
        return errors

    normalized_agent_audit_text = re.sub(r"\s+", " ", agent_audit_text)
    if not _AGENT_SOURCE_AUDIT_PASS_RE.search(agent_audit_text):
        errors.append(
            CloseoutDocumentHardError(
                agent_source_audit,
                "`docs/AGENT_SOURCE_AUDIT.md` should record "
                "`## Overall status: PASS`",
            )
        )
    if _AGENT_SOURCE_AUDIT_SCAFFOLD_RE.search(agent_audit_text):
        errors.append(
            CloseoutDocumentHardError(
                agent_source_audit,
                "`docs/AGENT_SOURCE_AUDIT.md` is still a scaffold, not a completed "
                "holistic audit",
            )
        )
    if any(
        phrase not in normalized_agent_audit_text
        for phrase in _AGENT_SOURCE_AUDIT_REQUIRED_PHRASES
    ):
        errors.append(
            CloseoutDocumentHardError(
                agent_source_audit,
                "`docs/AGENT_SOURCE_AUDIT.md` must document an independent "
                "source-paper/source-text read, source-inventory construction from "
                "the source itself, and Lean-interface comparison for omissions, hidden "
                "strengthening/weakening, and semantic mismatches; it must not merely "
                "summarize existing sidecars",
            )
        )
    return errors
