#!/usr/bin/env python3
"""Reissue source reviews for paper-local semantic prerequisites.

Lean identifies these structures/inductives only after expanding a source
claim's transparent paper-local definitions.  This command never decides the
source match.  It rebuilds exact Lean declaration and byte-pinned source
digests around an explicit reviewer decision, then writes the one canonical
ledger used by the packet and closeout gate.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

import review_dashboard_packet  # noqa: E402


LEDGER_RELATIVE = Path("audit") / "paper_semantic_prerequisites.json"
VALID_VERDICTS = frozenset({"matches", "mismatch", "uncertain"})


class PaperPrerequisiteReissueError(ValueError):
    """Raised when a paper-prerequisite review cannot be validated."""


def _load(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise PaperPrerequisiteReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise PaperPrerequisiteReissueError(f"{label} must be a JSON object")
    return payload


def _decisions(path: Path, *, paper: str) -> dict[str, dict[str, Any]]:
    payload = _load(path, label="decision file")
    if payload.get("schema") != 1 or payload.get("paper") != paper:
        raise PaperPrerequisiteReissueError("decision file has the wrong schema or paper")
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise PaperPrerequisiteReissueError("decision file needs a nonempty items object")
    raw_redirects = payload.get("source_item_redirects", {})
    if not isinstance(raw_redirects, Mapping) or not all(
        isinstance(source, str)
        and source.strip()
        and isinstance(target, str)
        and target.strip()
        for source, target in raw_redirects.items()
    ):
        raise PaperPrerequisiteReissueError(
            "source_item_redirects must be a map of nonempty source-map item ids"
        )
    redirects = {str(source).strip(): str(target).strip() for source, target in raw_redirects.items()}
    out: dict[str, dict[str, Any]] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise PaperPrerequisiteReissueError("each decision needs a declaration name and object")
        judgment = str(raw.get("judgment") or "").strip().lower()
        reason = str(raw.get("reason") or "").strip()
        if judgment not in VALID_VERDICTS or not reason:
            raise PaperPrerequisiteReissueError(
                f"{name}: each decision needs a supported judgment and nonempty reason"
            )
        decision = {**dict(raw), "judgment": judgment, "reason": reason}
        source_item = decision.get("source_item")
        if isinstance(source_item, str) and source_item.strip() in redirects:
            decision["source_item"] = redirects[source_item.strip()]
        out[name] = decision
    return out


def _semantic_targets(
    paper_dir: Path,
    *,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    source_map = _load(paper_dir / "audit" / "paper_statement_map.json", label="source map")
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise PaperPrerequisiteReissueError("source map has no items object")
    specs = sorted(
        {
            str(contract.get("spec_declaration") or "").strip()
            for item in raw_items.values()
            if isinstance(item, Mapping)
            for contract in [item.get("semantic_contract")]
            if isinstance(contract, Mapping)
            and str(contract.get("spec_declaration") or "").strip()
        }
    )
    if not specs:
        raise PaperPrerequisiteReissueError("source map has no source-facing Specs")
    if semantic_targets_override is not None:
        targets = {
            str(name): dict(target)
            for name, target in semantic_targets_override.items()
            if str(name).strip() and isinstance(target, Mapping)
        }
        missing = sorted(set(specs) - set(targets))
        if missing:
            raise PaperPrerequisiteReissueError(
                "packet Lean cache lacks source-facing Spec targets: "
                + ", ".join(missing[:4])
            )
        return {name: targets[name] for name in specs}
    return review_dashboard_packet.semantic_expanded_spec_targets(
        paper_dir, specs, require_build=require_build
    )


def _merged_items(
    existing: Mapping[str, Any], decisions: Mapping[str, Mapping[str, Any]]
) -> dict[str, dict[str, Any]]:
    prior_items = existing.get("items") if isinstance(existing, Mapping) else {}
    prior_items = prior_items if isinstance(prior_items, Mapping) else {}
    merged: dict[str, dict[str, Any]] = {}
    for name, decision in decisions.items():
        prior = prior_items.get(name)
        row = dict(prior) if isinstance(prior, Mapping) else {}
        for field in (
            "source_item",
            "source_location",
            "source_anchor_evidence",
            "semantic_context_requirements",
        ):
            if field in decision:
                row[field] = decision[field]
        # A deliberate direct source anchor replaces an older broad
        # source-map connection.  Retaining that key would silently make the
        # packet and digest use the old bundle instead of the reviewer-selected
        # anchor.
        if "source_anchor_evidence" in decision and "source_item" not in decision:
            row.pop("source_item", None)
        merged[name] = row
    return merged


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, Any]],
    *,
    validator: str,
    require_build: bool = True,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    prerequisite_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    if not validator.strip():
        raise PaperPrerequisiteReissueError("--validator must be nonempty")
    targets = _semantic_targets(
        paper_dir,
        semantic_targets_override=semantic_targets_override,
        require_build=require_build,
    )
    current_path = paper_dir / LEDGER_RELATIVE
    existing = _load(current_path, label="current prerequisite ledger") if current_path.is_file() else {}
    merged = _merged_items(existing, decisions)
    provisional = {
        "schema": review_dashboard_packet.PAPER_PREREQUISITE_SCHEMA,
        "paper": paper_dir.name,
        "prompt_version": review_dashboard_packet.PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": review_dashboard_packet.PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "items": merged,
    }
    entries = review_dashboard_packet.paper_semantic_prerequisites(
        paper_dir,
        targets,
        ledger_payload=provisional,
        require_build=require_build,
        semantic_targets_by_name_override=prerequisite_targets_override,
    )
    expected = {str(entry.get("lean_name") or "").strip() for entry in entries}
    if set(decisions) != expected:
        missing = sorted(expected - set(decisions))
        extra = sorted(set(decisions) - expected)
        parts = []
        if missing:
            parts.append("missing decisions for " + ", ".join(missing))
        if extra:
            parts.append("decisions outside the prerequisite surface: " + ", ".join(extra))
        raise PaperPrerequisiteReissueError("prerequisite decision coverage is not exact: " + "; ".join(parts))
    records: dict[str, Any] = {}
    for entry in entries:
        name = str(entry["lean_name"])
        decision = decisions[name]
        if not str(entry.get("paper_declaration_source") or "").strip():
            raise PaperPrerequisiteReissueError(f"{name}: exact Lean declaration is unavailable")
        if not str(entry.get("paper_semantic_target") or "").strip():
            raise PaperPrerequisiteReissueError(
                f"{name}: Lean paper-prerequisite semantic target is unavailable: "
                + str(entry.get("paper_semantic_target_error") or "")
            )
        if not str(entry.get("verbatim_source_input") or "").strip():
            raise PaperPrerequisiteReissueError(
                f"{name}: exact paper source connection is unavailable: "
                + str(entry.get("source_connection_error") or "")
            )
        raw = merged[name]
        record = {
            key: raw[key]
            for key in (
                "source_item",
                "source_location",
                "source_anchor_evidence",
                "semantic_context_requirements",
            )
            if key in raw
        }
        record.update(
            {
                "paper_declaration": name,
                "paper_source_path": entry["paper_source_path"],
                "paper_line_start": entry["paper_line_start"],
                "paper_declaration_sha256": entry["paper_declaration_sha256"],
                "paper_semantic_target_sha256": entry[
                    "paper_semantic_target_sha256"
                ],
                "paper_semantic_target_protocol": review_dashboard_packet.PAPER_PREREQUISITE_TARGET_PROTOCOL,
                "source_input_bundle_sha256": entry["source_input_bundle_sha256"],
                "judgment": decision["judgment"],
                "reason": decision["reason"],
                "validator": validator.strip(),
                "validator_type": "llm_as_judge",
                "validated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
            }
        )
        records[name] = record
    return {
        "schema": review_dashboard_packet.PAPER_PREREQUISITE_SCHEMA,
        "paper": paper_dir.name,
        "prompt_version": review_dashboard_packet.PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": review_dashboard_packet.PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "comment": (
            "Each verdict compares a Lean-owned own-body semantic target and exact "
            "paper-local declaration with its selected byte-pinned paper-source bundle. "
            "These are semantic prerequisites, not additional paper-claim rows."
        ),
        "items": records,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--decisions", type=Path, required=True)
    parser.add_argument("--validator", required=True)
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help=(
            "obtain fresh Lean displays without an additional build; use only immediately "
            "after a successful focused paper build in the same checkout"
        ),
    )
    parser.add_argument(
        "--packet-lean-cache",
        action="store_true",
        help=(
            "reuse the exact-current staged packet Lean-display cache; use only after "
            "a successful focused paper build in the same checkout"
        ),
    )
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper_dir = args.root.resolve() / "papers" / args.paper
    decisions = _decisions(args.decisions, paper=args.paper)
    packet_cache = None
    if args.packet_lean_cache:
        source_map = _load(paper_dir / "audit" / "paper_statement_map.json", label="source map")
        raw_items = source_map.get("items")
        specs = sorted(
            {
                str(contract.get("spec_declaration") or "").strip()
                for item in (raw_items.values() if isinstance(raw_items, Mapping) else ())
                if isinstance(item, Mapping)
                for contract in [item.get("semantic_contract")]
                if isinstance(contract, Mapping)
                and str(contract.get("spec_declaration") or "").strip()
            }
        )
        packet_cache = review_dashboard_packet._current_packet_lean_cache(paper_dir, specs)
        if packet_cache is None:
            raise PaperPrerequisiteReissueError(
                "no exact-current packet Lean cache; prepare its specifications and "
                "paper-prerequisites stages first"
            )
    payload = reissue(
        paper_dir,
        decisions,
        validator=args.validator,
        require_build=not args.skip_build,
        semantic_targets_override=(
            packet_cache.get("semantic_targets") if packet_cache is not None else None
        ),
        prerequisite_targets_override=(
            packet_cache.get("paper_prerequisite_targets") if packet_cache is not None else None
        ),
    )
    if not args.write:
        print(f"{args.paper}: validated {len(decisions)} paper-prerequisite decisions; rerun with --write")
        return 0
    path = paper_dir / LEDGER_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} ({len(decisions)} reissued decisions)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except PaperPrerequisiteReissueError as exc:
        print(f"paper-prerequisite reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
