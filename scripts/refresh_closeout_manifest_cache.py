#!/usr/bin/env python3
"""Refresh one dashboard cache from independently validated raw-manifest rows.

This is operational closeout infrastructure.  It does not produce source-record
evidence, alter human judgments, or authorize a paper status.  Its only role is
to carry the current raw audit's already authenticated manifest bindings into a
mutable dashboard-cache refresh, so the dashboard can reuse exact current
manifests rather than immediately re-elaborating the same Lean declarations.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from scripts import audit_repository, review_dashboard
    from scripts.closeout_execution_state import resolve_paper_folder
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    import audit_repository
    import review_dashboard
    from closeout_execution_state import resolve_paper_folder


HANDOFF_SCHEMA = 1


def _finding_messages(findings: Iterable[object]) -> list[str]:
    """Project audit findings into bounded operational diagnostics."""

    messages: list[str] = []
    for finding in findings:
        message = str(getattr(finding, "message", finding) or "").strip()
        if message:
            messages.append(message)
    return messages[:8]


def _has_error(findings: Iterable[object]) -> bool:
    """Treat only explicit audit errors as a handoff blocker."""

    return any(
        str(getattr(finding, "severity", "ERROR")).upper() == "ERROR"
        for finding in findings
    )


def _result(
    paper: str,
    state: str,
    *,
    reason: str = "",
    **extra: object,
) -> dict[str, object]:
    """Return non-evidence machine-readable operation output."""

    payload: dict[str, object] = {
        "schema": HANDOFF_SCHEMA,
        "paper": paper,
        "operation": "refresh_closeout_manifest_cache",
        "acceptance_credential": False,
        "state": state,
    }
    if reason:
        payload["reason"] = reason
    payload.update(extra)
    return payload


def refresh_closeout_manifest_cache(
    paper: str,
    *,
    folder: Path | None = None,
) -> dict[str, object]:
    """Refresh one mutable dashboard cache using a current raw-row handoff.

    The raw producer cannot authorize reuse of its own saved rows.  This helper
    therefore first acquires the existing builder-issued closeout transaction.
    It passes that transaction's validated configured rows to the dashboard's
    authenticated manifest-store primer.  The dashboard still performs fresh
    Lean extraction for every exact-context miss.

    Dashboard rows must be persisted from live files so the normal cache can be
    reused outside this process.  We deliberately do not pass frozen dashboard
    inputs here: strict frozen extraction is read-only by design.  Instead, the
    helper uses the transaction-owned build provider and runs the existing final
    transaction/build mutation checks before making either mutable cache write.
    The written cache and manifest store remain non-authoritative optimizations;
    later consumers independently validate their bindings and contexts.
    """

    paper = str(paper or "").strip()
    if not paper:
        return _result("", "invalid_paper", reason="a nonempty paper id is required")
    if folder is None:
        folder = resolve_paper_folder(ROOT, paper)
    if not isinstance(folder, Path):
        return _result(paper, "unknown_paper", reason="paper folder is unavailable")
    folder = folder.resolve()

    try:
        evidence_context = audit_repository.build_paper_closeout_evidence_context(paper)
        run_context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            paper,
            folder,
            evidence_context=evidence_context,
        )
    except Exception as exc:  # noqa: BLE001 - the operation must fail closed.
        return _result(
            paper,
            "evidence_context_unavailable",
            reason=f"could not acquire the exact closeout context: {type(exc).__name__}: {exc}",
        )

    try:
        prebuild_findings = audit_repository.paper_closeout_evidence_context_prebuild_findings(
            paper, evidence_context
        )
    except Exception as exc:  # noqa: BLE001 - an unverified raw receipt cannot hand off.
        return _result(
            paper,
            "raw_context_validation_unavailable",
            reason=f"could not validate the current raw context: {type(exc).__name__}: {exc}",
        )
    if _has_error(prebuild_findings):
        return _result(
            paper,
            "raw_context_invalid",
            reason="; ".join(_finding_messages(prebuild_findings)),
        )

    try:
        configured_rows = run_context.current_configured_review_rows_for_manifest_reuse()
    except Exception as exc:  # noqa: BLE001 - no independent row authority on failure.
        return _result(
            paper,
            "manifest_handoff_unavailable",
            reason=f"could not materialize current configured rows: {type(exc).__name__}: {exc}",
        )
    if configured_rows is None:
        return _result(
            paper,
            "manifest_handoff_unavailable",
            reason=(
                "the exact closeout transaction did not validate complete current "
                "configured review rows"
            ),
        )

    provider = run_context.build_input_provider

    def progress(message: str) -> None:
        try:
            print(f"closeout-manifest-cache: {paper}: {message}", file=sys.stderr, flush=True)
        except (BrokenPipeError, OSError, ValueError):
            pass

    try:
        items = list(
            review_dashboard.review_items_for_paper(
                folder,
                use_cache=False,
                render_images=False,
                require_current_signatures=True,
                # Persistence happens only after the transaction's final mutation
                # check below, rather than during the live extraction.
                persist_cache_rebind=False,
                build_input_provider=provider,
                validated_configured_review_rows=configured_rows,
                progress=progress,
                publish_manifest_store=False,
            )
        )
        signature_contexts = review_dashboard.current_review_signature_contexts(
            folder, build_input_provider=provider
        )
        if not isinstance(signature_contexts, Mapping) or not signature_contexts:
            return _result(
                paper,
                "dashboard_context_unavailable",
                reason="could not reconstruct current dashboard manifest contexts",
                configured_review_row_count=len(configured_rows),
            )
        source_hashes = review_dashboard._cache_source_hashes(  # noqa: SLF001
            folder, build_input_provider=provider
        )
        if not isinstance(source_hashes, Mapping):
            return _result(
                paper,
                "dashboard_source_hashes_unavailable",
                reason="could not compute current dashboard cache source hashes",
                configured_review_row_count=len(configured_rows),
            )
    except Exception as exc:  # noqa: BLE001 - current Lean/cache extraction fails closed.
        return _result(
            paper,
            "dashboard_refresh_failed",
            reason=f"dashboard extraction failed: {type(exc).__name__}: {exc}",
            configured_review_row_count=len(configured_rows),
        )

    try:
        mutation_findings = audit_repository.paper_closeout_context_mutation_findings(
            evidence_context,
            build_input_provider=provider,
        )
    except Exception as exc:  # noqa: BLE001 - publication cannot follow an unchecked run.
        return _result(
            paper,
            "final_mutation_validation_unavailable",
            reason=f"could not finalize transaction inputs: {type(exc).__name__}: {exc}",
            configured_review_row_count=len(configured_rows),
        )
    if _has_error(mutation_findings):
        return _result(
            paper,
            "input_mutation_detected",
            reason="; ".join(_finding_messages(mutation_findings)),
            configured_review_row_count=len(configured_rows),
        )

    try:
        review_dashboard.write_cached_review_rows(
            folder,
            items,
            signature_contexts=dict(signature_contexts),
            source_hashes=dict(source_hashes),
        )
    except Exception as exc:  # noqa: BLE001 - an unwritten cache is an ordinary miss.
        return _result(
            paper,
            "dashboard_cache_write_failed",
            reason=f"could not write dashboard rows: {type(exc).__name__}: {exc}",
            configured_review_row_count=len(configured_rows),
        )

    publication_error = ""
    published_count = 0
    try:
        published = review_dashboard.publish_review_signature_manifest_store(
            folder,
            items,
            signature_contexts,
        )
        published_count = len(published)
    except Exception as exc:  # noqa: BLE001 - a valid row cache remains useful.
        publication_error = f"{type(exc).__name__}: {exc}"

    return _result(
        paper,
        "completed",
        configured_review_row_count=len(configured_rows),
        dashboard_row_count=len(items),
        manifest_context_count=len(signature_contexts),
        manifest_store_published_count=published_count,
        **(
            {"manifest_store_publication_error": publication_error}
            if publication_error
            else {}
        ),
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Refresh one dashboard cache using the current independently validated "
            "source-record manifest handoff."
        )
    )
    parser.add_argument("--paper", required=True, help="Paper folder name under papers/.")
    args = parser.parse_args()
    result = refresh_closeout_manifest_cache(args.paper)
    print(json.dumps(result, ensure_ascii=True, indent=2, sort_keys=True))
    return 0 if result.get("state") == "completed" else 2


if __name__ == "__main__":
    raise SystemExit(main())
