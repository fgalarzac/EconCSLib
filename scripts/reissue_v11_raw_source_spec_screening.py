#!/usr/bin/env python3
"""Reissue selected raw-source-to-expanded-Spec screening rows.

This writer deliberately does not decide whether a source claim and a Lean
``Spec`` match.  A reviewer supplies an explicit verdict and explanation for
each selected row.  The command reconstructs the exact byte-pinned source
bundle and the exact transparent ``PaperInterface`` declaration, then replaces
only the hash-bound transport fields.  It refuses an unknown source row, a
thin/non-``Spec`` target, a missing source context role, or a verdict without
an explanation.

Use this after a source/context or PaperInterface change made an existing v11
screening stale.  It is a screening reissue, not a replacement for the
atom-level source-spec correspondence receipt or Lean proof endpoint.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

import review_dashboard  # noqa: E402
import review_dashboard_packet  # noqa: E402


SCREENING_RELATIVE = Path("audit") / "v11_raw_source_spec_screening.json"
SCREENING_SCHEMA = 2
PROMPT_VERSION = "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2"
SOURCE_PROTOCOL = "verbatim_source_anchor_bundle_v1"
LEAN_PROTOCOL = "lean_transparent_paper_expansion_v1"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
VALID_VERDICTS = frozenset(
    {"matches", "mismatch", "uncertain", APPROVED_CORRECTED_TARGET_MATCH}
)


class ScreeningReissueError(ValueError):
    """Raised when a reissue request cannot be verified mechanically."""


def _load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ScreeningReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ScreeningReissueError(f"{label} must be a JSON object")
    return payload


def _decision_rows(path: Path, *, paper: str) -> dict[str, dict[str, str]]:
    payload = _load_object(path, label="decision file")
    if payload.get("schema") != 1:
        raise ScreeningReissueError("decision file schema must be 1")
    if payload.get("paper") != paper:
        raise ScreeningReissueError("decision file paper does not match --paper")
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise ScreeningReissueError("decision file needs a nonempty items object")
    decisions: dict[str, dict[str, str]] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise ScreeningReissueError("each decision must have a nonempty name and object")
        verdict = str(raw.get("judgment") or "").strip().lower()
        reason = str(raw.get("reason") or "").strip()
        if verdict not in VALID_VERDICTS:
            raise ScreeningReissueError(f"{name}: unsupported judgment `{verdict}`")
        if not reason:
            raise ScreeningReissueError(f"{name}: a reviewer explanation is required")
        decisions[name] = {"judgment": verdict, "reason": reason}
    return decisions


def _records_by_spec(source_map: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise ScreeningReissueError("paper statement map has no items object")
    records: dict[str, dict[str, Any]] = {}
    for source_key, raw in raw_items.items():
        if not isinstance(raw, Mapping):
            continue
        contract = raw.get("semantic_contract")
        if not isinstance(contract, Mapping):
            continue
        spec = str(contract.get("spec_declaration") or "").strip()
        if spec:
            if spec in records:
                raise ScreeningReissueError(
                    "one semantic Spec may not represent multiple source claims: "
                    f"`{spec}` is routed by more than one statement-map item "
                    f"(including `{source_key}`)"
                )
            records[spec] = dict(raw)
    return records


def reissued_row(
    full_name: str,
    *,
    paper_dir: Path,
    record: Mapping[str, Any],
    interface_item: Mapping[str, Any],
    semantic_target: Mapping[str, Any],
    decision: Mapping[str, str],
) -> dict[str, object]:
    """Construct one current v11 row from an explicit reviewer decision."""

    source_error = review_dashboard.source_anchor_file_error(paper_dir, record)
    if source_error:
        raise ScreeningReissueError(
            f"{full_name}: raw source bundle is invalid: {source_error}"
        )
    source_text, source_digest, source_error = review_dashboard.source_semantic_input_bundle(
        record, require_context_roles=True
    )
    if source_error or not source_text or not source_digest:
        raise ScreeningReissueError(f"{full_name}: raw source bundle is invalid: {source_error}")
    lean_text = str(interface_item.get("lean_statement") or "")
    expanded_text = str(semantic_target.get("display") or "")
    expanded_digest = str(semantic_target.get("display_sha256") or "").strip().lower()
    interface_digest = str(
        semantic_target.get("paper_interface_sha256") or ""
    ).strip().lower()
    if (
        not lean_text
        or not expanded_text
        or not re.fullmatch(r"[0-9a-f]{64}", expanded_digest)
        or not re.fullmatch(r"[0-9a-f]{64}", interface_digest)
        or not full_name.endswith("Spec")
        or str(interface_item.get("kind") or "") != "def"
        or re.search(r":\s*Prop\s*:=", lean_text, flags=re.DOTALL) is None
    ):
        raise ScreeningReissueError(
            f"{full_name}: the semantic target must be one explicit `def ...Spec : Prop :=` in PaperInterface"
        )
    verdict = str(decision["judgment"])
    corrected_target = record.get("corrected_target")
    approved_correction = verdict == APPROVED_CORRECTED_TARGET_MATCH
    is_corrected_source_statement = (
        str(record.get("coverage_status") or "").strip()
        == "corrected_source_statement"
    )
    if approved_correction:
        if (
            str(record.get("coverage_status") or "").strip()
            != "corrected_source_statement"
            or not isinstance(corrected_target, Mapping)
            or corrected_target.get("archival_equivalence_claimed") is not False
            or not str(corrected_target.get("corrected_target_sha256") or "").strip()
        ):
            raise ScreeningReissueError(
                f"{full_name}: approved-corrected-target judgment requires a current "
                "corrected_source_statement map record"
            )
    elif is_corrected_source_statement:
        raise ScreeningReissueError(
            f"{full_name}: a corrected_source_statement retains different archival "
            "text and therefore requires the "
            "`matches_approved_corrected_target` verdict"
        )
    row: dict[str, object] = {
        "judgment": verdict,
        "reason": str(decision["reason"]),
        "source_input_protocol": SOURCE_PROTOCOL,
        "source_input_bundle_sha256": source_digest,
        "paper_statement_sha256": source_digest,
        "lean_target_protocol": LEAN_PROTOCOL,
        "semantic_target_declaration": full_name,
        "lean_expanded_statement_sha256": expanded_digest,
        "paper_interface_sha256": interface_digest,
    }
    if approved_correction:
        assert isinstance(corrected_target, Mapping)
        row["corrected_target_protocol"] = "approved_corrected_target_v1"
        row["corrected_target_sha256"] = str(
            corrected_target["corrected_target_sha256"]
        ).strip().lower()
    return row


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, str]],
    *,
    validator: str,
    require_build: bool = True,
    replace_current_surface: bool = False,
) -> dict[str, Any]:
    source_map = _load_object(paper_dir / "audit" / "paper_statement_map.json", label="source map")
    interface_items = review_dashboard_packet._paperinterface_items(paper_dir)
    records = _records_by_spec(source_map)
    semantic_targets = review_dashboard_packet.semantic_expanded_spec_targets(
        paper_dir, decisions, require_build=require_build
    )
    current_path = paper_dir / SCREENING_RELATIVE
    current = _load_object(current_path, label="current v11 screening") if current_path.is_file() else {}
    raw_items = current.get("items")
    if replace_current_surface:
        expected = set(records)
        if set(decisions) != expected:
            missing = sorted(expected - set(decisions))
            extra = sorted(set(decisions) - expected)
            details: list[str] = []
            if missing:
                details.append("missing decision(s) for " + ", ".join(missing))
            if extra:
                details.append("out-of-surface decision(s) for " + ", ".join(extra))
            raise ScreeningReissueError(
                "--replace-current-surface requires exact current Spec decisions: "
                + "; ".join(details)
            )
        items: dict[str, object] = {}
    else:
        items = dict(raw_items) if isinstance(raw_items, Mapping) else {}
    for full_name, decision in decisions.items():
        record = records.get(full_name)
        interface_item = interface_items.get(full_name)
        semantic_target = semantic_targets.get(full_name)
        if record is None:
            raise ScreeningReissueError(f"{full_name}: no source-map semantic Spec route")
        if interface_item is None:
            raise ScreeningReissueError(f"{full_name}: no transparent PaperInterface Spec declaration")
        if semantic_target is None:
            raise ScreeningReissueError(
                f"{full_name}: Lean could not produce a complete transparent semantic target"
            )
        items[full_name] = reissued_row(
            full_name,
            paper_dir=paper_dir,
            record=record,
            interface_item=interface_item,
            semantic_target=semantic_target,
            decision=decision,
        )
    return {
        "schema": SCREENING_SCHEMA,
        "paper": paper_dir.name,
        "audit_kind": "raw_source_to_expanded_spec_screening",
        "prompt_version": PROMPT_VERSION,
        "validator": validator,
        "validated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "comment": (
            "Each listed verdict compares the exact byte-pinned source-anchor bundle "
            "and explicitly pinned semantic context with Lean's fully expanded "
            "paper-local semantic target. The paired proof endpoint is reviewed separately."
        ),
        "items": dict(sorted(items.items())),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--decisions", type=Path, required=True)
    parser.add_argument("--validator", required=True)
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help=(
            "obtain fresh Lean displays without invoking an additional build; use only "
            "immediately after a successful focused paper build in the same checkout"
        ),
    )
    parser.add_argument(
        "--replace-current-surface",
        action="store_true",
        help=(
            "require decisions for every current selected Spec and replace the screening "
            "ledger, removing rows from a retired review surface"
        ),
    )
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    decisions = _decision_rows(args.decisions, paper=args.paper)
    payload = reissue(
        paper_dir,
        decisions,
        validator=str(args.validator).strip(),
        require_build=not args.skip_build,
        replace_current_surface=args.replace_current_surface,
    )
    if not args.write:
        print(f"{args.paper}: validated {len(decisions)} v11 screening decision(s); rerun with --write")
        return 0
    path = paper_dir / SCREENING_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} ({len(decisions)} reissued decision(s))")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ScreeningReissueError as exc:
        print(f"v11 screening reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
