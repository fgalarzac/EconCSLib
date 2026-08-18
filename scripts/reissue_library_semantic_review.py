#!/usr/bin/env python3
"""Reissue current source-to-library semantic-review records.

The reviewer, not this command, decides whether a reusable EconCSLib
declaration matches its selected paper-source bundle.  This command requires
an explicit judgment and reason for every material library declaration on the
selected PaperInterface surface, rebuilds the exact source, Lean-produced
semantic-target, and bounded Lean-declaration digests, and writes the one
canonical paper-local ledger.

It is intentionally parallel to the v11 source-to-Spec screening writer.  It
never turns a declaration name, docstring, dashboard gloss, or old hash into a
semantic verdict.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

import review_dashboard  # noqa: E402
import review_dashboard_packet  # noqa: E402


LEDGER_RELATIVE = Path("audit") / "library_semantic_review.json"
PROMPT_VERSION = "library-statement-match-v2-verbatim-source-anchor-lean-display-exact-code"
TARGET_PROTOCOL = "lean-library-display-plus-exact-code-v1"
DIRECT_SPEC_DEPENDENCY_PROTOCOL = "lean-expanded-paper-spec-library-surface-v1"
VALID_VERDICTS = frozenset({"matches", "mismatch", "uncertain"})


class LibraryReviewReissueError(ValueError):
    """Raised when a library-review reissue cannot be checked mechanically."""


def _load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LibraryReviewReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise LibraryReviewReissueError(f"{label} must be a JSON object")
    return payload


def _decisions(path: Path, *, paper: str) -> dict[str, dict[str, Any]]:
    payload = _load_object(path, label="decision file")
    if payload.get("schema") != 1:
        raise LibraryReviewReissueError("decision file schema must be 1")
    if payload.get("paper") != paper:
        raise LibraryReviewReissueError("decision file paper does not match --paper")
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise LibraryReviewReissueError("decision file needs a nonempty items object")
    raw_redirects = payload.get("source_item_redirects", {})
    if not isinstance(raw_redirects, Mapping) or not all(
        isinstance(source, str)
        and source.strip()
        and isinstance(target, str)
        and target.strip()
        for source, target in raw_redirects.items()
    ):
        raise LibraryReviewReissueError(
            "source_item_redirects must be a map of nonempty source-map item ids"
        )
    redirects = {str(source).strip(): str(target).strip() for source, target in raw_redirects.items()}
    decisions: dict[str, dict[str, Any]] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise LibraryReviewReissueError("each decision needs a nonempty library name and object")
        judgment = str(raw.get("judgment") or "").strip().lower()
        reason = str(raw.get("reason") or "").strip()
        if judgment not in VALID_VERDICTS:
            raise LibraryReviewReissueError(f"{name}: unsupported judgment `{judgment}`")
        if not reason:
            raise LibraryReviewReissueError(f"{name}: reviewer reason is required")
        decision = dict(raw)
        decision["judgment"] = judgment
        decision["reason"] = reason
        source_item = decision.get("source_item")
        if isinstance(source_item, str) and source_item.strip() in redirects:
            decision["source_item"] = redirects[source_item.strip()]
        decisions[name] = decision
    return decisions


def _selected_claims(paper_dir: Path, source_map: Mapping[str, Any]) -> list[dict[str, str]]:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise LibraryReviewReissueError("paper statement map has no items object")
    specs = {
        str(contract.get("spec_declaration") or "").strip()
        for item in raw_items.values()
        if isinstance(item, Mapping)
        for contract in [item.get("semantic_contract")]
        if isinstance(contract, Mapping)
        and str(contract.get("spec_declaration") or "").strip()
    }
    claims = [
        {
            "interface_source": str(source),
            "lean_statement": str(source),
            "semantic_spec_declaration": str(full),
        }
        for _kind, _short, full, source, _comment, _line, _path in review_dashboard.parse_review_source_declarations(
            paper_dir / "PaperInterface.lean"
        )
        if str(full) in specs
    ]
    if not claims:
        raise LibraryReviewReissueError("no source-facing PaperInterface Specs were found")
    return claims


def _expanded_spec_dependency_surface(
    paper_dir: Path,
    claims: list[dict[str, str]],
    *,
    require_build: bool = True,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Obtain the current Lean-expanded reusable-library surface.

    This is deliberately separate from the reviewer decisions below.  Lean
    resolves unqualified/open-namespace names; the reviewer then gives an
    explicit source-to-definition verdict for every resulting material owner.
    """

    specifications = sorted(
        {
            str(claim.get("semantic_spec_declaration") or "").strip()
            for claim in claims
            if str(claim.get("semantic_spec_declaration") or "").strip()
        }
    )
    if not specifications:
        raise LibraryReviewReissueError("no source-facing PaperInterface Specs were found")
    if semantic_targets_override is None:
        try:
            resolved = review_dashboard_packet.semantic_expanded_spec_targets(
                paper_dir, specifications, require_build=require_build
            )
        except ValueError as exc:
            raise LibraryReviewReissueError(
                "Lean could not produce the expanded source-facing Spec surface: " + str(exc)
            ) from exc
    else:
        resolved = {
            str(name): dict(target)
            for name, target in semantic_targets_override.items()
            if str(name).strip() and isinstance(target, Mapping)
        }
    if set(resolved) != set(specifications):
        missing = sorted(set(specifications) - set(resolved))
        raise LibraryReviewReissueError(
            "Lean could not produce the complete expanded-library dependency surface"
            + (": " + ", ".join(missing) if missing else "")
        )
    try:
        interface_bytes = (paper_dir / "PaperInterface.lean").read_bytes()
    except OSError as exc:
        raise LibraryReviewReissueError(
            f"could not read PaperInterface.lean for dependency surface: {exc}"
        ) from exc
    source_by_spec = {
        str(claim["semantic_spec_declaration"]): str(claim["interface_source"])
        for claim in claims
    }
    items: dict[str, Any] = {}
    for spec in specifications:
        direct = list(resolved[spec].get("library_declarations", ()))
        owners = sorted(
            {
                review_dashboard.library_review_owner_declaration(name)
                for name in direct
            }
        )
        items[spec] = {
            "spec_source_sha256": review_dashboard.statement_digest(source_by_spec[spec]),
            "semantic_target_sha256": str(
                resolved[spec].get("display_sha256") or ""
            ),
            "direct_library_declarations": direct,
            "review_owner_declarations": owners,
        }
    return {
        "schema": 1,
        "protocol": DIRECT_SPEC_DEPENDENCY_PROTOCOL,
        "paper_interface_sha256": hashlib.sha256(interface_bytes).hexdigest(),
        "items": items,
    }


def _direct_surface_owners(surface: Mapping[str, Any]) -> set[str]:
    """Return the declared material owners, rejecting malformed injected data."""

    items = surface.get("items")
    if not isinstance(items, Mapping):
        raise LibraryReviewReissueError("direct-library dependency surface has no items object")
    owners: set[str] = set()
    for spec, raw in items.items():
        if not str(spec or "").strip() or not isinstance(raw, Mapping):
            raise LibraryReviewReissueError("direct-library dependency surface has malformed item")
        raw_owners = raw.get("review_owner_declarations")
        if not isinstance(raw_owners, list) or any(
            not isinstance(name, str) or not name.startswith("EconCSLib.")
            for name in raw_owners
        ):
            raise LibraryReviewReissueError(
                "direct-library dependency surface has malformed review-owner declarations"
            )
        owners.update(raw_owners)
    return owners


def _lean_expanded_library_owners(
    paper_dir: Path, source_map: Mapping[str, Any]
) -> set[str]:
    """Return every reusable declaration left in Lean's expanded Spec target."""

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise LibraryReviewReissueError("paper statement map has no items object")
    specifications = sorted(
        {
            str(contract.get("spec_declaration") or "").strip()
            for item in raw_items.values()
            if isinstance(item, Mapping)
            for contract in [item.get("semantic_contract")]
            if isinstance(contract, Mapping)
            and str(contract.get("spec_declaration") or "").strip()
        }
    )
    if not specifications:
        raise LibraryReviewReissueError("no source-facing PaperInterface Specs were found")
    try:
        targets = review_dashboard_packet.semantic_expanded_spec_targets(
            paper_dir, specifications
        )
    except ValueError as exc:
        raise LibraryReviewReissueError(
            "Lean could not produce expanded semantic library targets: " + str(exc)
        ) from exc
    if set(targets) != set(specifications):
        raise LibraryReviewReissueError(
            "Lean did not return every selected expanded semantic library target"
        )
    return {
        review_dashboard.library_review_owner_declaration(declaration)
        for target in targets.values()
        for declaration in target.get("library_declarations", ())
        if str(declaration).strip().startswith("EconCSLib.")
    }


def _merged_ledger(
    existing: Mapping[str, Any], decisions: Mapping[str, Mapping[str, Any]]
) -> dict[str, Any]:
    raw_existing = existing.get("items")
    existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
    merged: dict[str, Any] = {}
    for name, decision in decisions.items():
        prior = existing_items.get(name)
        row = dict(prior) if isinstance(prior, Mapping) else {}
        for field in (
            "source_item",
            "source_location",
            "source_anchor_evidence",
            "semantic_context_requirements",
            "library_source_path",
            "library_line_start",
            "library_line_end",
            "label",
        ):
            if field in decision:
                row[field] = decision[field]
        # An explicit direct anchor is a selected replacement for a prior
        # source-map bundle, not supplemental metadata on that broader route.
        if "source_anchor_evidence" in decision and "source_item" not in decision:
            row.pop("source_item", None)
        row["library_declaration"] = name
        merged[name] = row
    return merged


def _material_entries(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    ledger_items: Mapping[str, Any],
    direct_surface: Mapping[str, Any],
    prerequisite_owners: set[str],
    library_semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    library_semantic_target_errors_override: Mapping[str, str] | None = None,
) -> list[dict[str, Any]]:
    """Build entries through the dashboard's exact source/code extractors.

    The dashboard is given a temporary in-memory ledger through a narrow mock
    of its loader.  This avoids a write-before-validation path while retaining
    one implementation of source-bundle and bounded-declaration parsing.
    """

    claims = _selected_claims(paper_dir, source_map)
    owners = sorted(_direct_surface_owners(direct_surface))
    for claim in claims:
        claim["library_review_owner_declarations"] = owners
    if prerequisite_owners:
        claims.append(
            {
                "library_review_owner_declarations": sorted(prerequisite_owners),
            }
        )
    original = review_dashboard._library_semantic_review_payload

    def loader(folder: Path) -> tuple[Mapping[str, Any], str]:
        if folder.resolve() != paper_dir.resolve():
            return original(folder)
        return {
            "schema": 1,
            "paper": paper_dir.name,
            "prompt_version": PROMPT_VERSION,
            "target_protocol": TARGET_PROTOCOL,
            "items": ledger_items,
        }, ""

    review_dashboard._library_semantic_review_payload = loader
    try:
        return review_dashboard.human_review_library_prerequisites(
            paper_dir,
            claims,
            semantic_targets_override=library_semantic_targets_override,
            semantic_target_errors_override=library_semantic_target_errors_override,
        )
    finally:
        review_dashboard._library_semantic_review_payload = original


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, Any]],
    *,
    validator: str,
    direct_dependency_surface: Mapping[str, Any] | None = None,
    require_build: bool = True,
    packet_lean_cache: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if not validator.strip():
        raise LibraryReviewReissueError("--validator must be nonempty")
    source_map = _load_object(paper_dir / "audit" / "paper_statement_map.json", label="source map")
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        raise LibraryReviewReissueError("paper statement map has no items object")
    specs = sorted(
        {
            str(contract.get("spec_declaration") or "").strip()
            for item in source_items.values()
            if isinstance(item, Mapping)
            for contract in [item.get("semantic_contract")]
            if isinstance(contract, Mapping)
            and str(contract.get("spec_declaration") or "").strip()
        }
    )
    cached_semantic_targets: Mapping[str, Mapping[str, Any]] | None = None
    cached_prerequisite_targets: Mapping[str, Mapping[str, Any]] | None = None
    cached_library_targets: Mapping[str, Mapping[str, Any]] | None = None
    cached_library_errors: Mapping[str, str] | None = None
    if packet_lean_cache is not None:
        raw_specs = packet_lean_cache.get("specifications")
        raw_semantic = packet_lean_cache.get("semantic_targets")
        raw_prerequisites = packet_lean_cache.get("paper_prerequisite_targets")
        raw_library = packet_lean_cache.get("library_semantic_targets")
        raw_library_errors = packet_lean_cache.get("library_semantic_target_errors")
        if (
            raw_specs != specs
            or not isinstance(raw_semantic, Mapping)
            or not isinstance(raw_prerequisites, Mapping)
            or not isinstance(raw_library, Mapping)
            or not isinstance(raw_library_errors, Mapping)
        ):
            raise LibraryReviewReissueError(
                "packet Lean cache is incomplete for the current selected Spec surface"
            )
        cached_semantic_targets = raw_semantic
        cached_prerequisite_targets = raw_prerequisites
        cached_library_targets = raw_library
        cached_library_errors = {
            str(name): str(error)
            for name, error in raw_library_errors.items()
            if str(name).strip() and str(error).strip()
        }
    if isinstance(direct_dependency_surface, Mapping):
        direct_surface = dict(direct_dependency_surface)
    else:
        direct_surface = _expanded_spec_dependency_surface(
            paper_dir,
            _selected_claims(paper_dir, source_map),
            require_build=require_build,
            semantic_targets_override=cached_semantic_targets,
        )
    current_path = paper_dir / LEDGER_RELATIVE
    current = _load_object(current_path, label="current library ledger") if current_path.is_file() else {}
    merged = _merged_ledger(current, decisions)
    try:
        semantic_targets = (
            {
                str(name): dict(target)
                for name, target in cached_semantic_targets.items()
                if str(name).strip() and isinstance(target, Mapping)
            }
            if cached_semantic_targets is not None
            else (
                review_dashboard_packet.semantic_expanded_spec_targets(
                    paper_dir, specs, require_build=require_build
                )
                if specs
                else {}
            )
        )
        paper_prerequisites = review_dashboard_packet.paper_semantic_prerequisites(
            paper_dir,
            semantic_targets,
            require_build=require_build,
            semantic_targets_by_name_override=cached_prerequisite_targets,
        )
    except ValueError as exc:
        raise LibraryReviewReissueError(
            "could not obtain paper-prerequisite library surface: " + str(exc)
        ) from exc
    prerequisite_owners = {
        review_dashboard.library_review_owner_declaration(declaration)
        for prerequisite in paper_prerequisites
        for declaration in prerequisite.get("direct_library_declarations", ())
        if str(declaration).strip().startswith("EconCSLib.")
    }
    entries = _material_entries(
        paper_dir,
        source_map,
        merged,
        direct_surface,
        prerequisite_owners,
        library_semantic_targets_override=cached_library_targets,
        library_semantic_target_errors_override=cached_library_errors,
    )
    material_names = {str(entry.get("lean_name") or "").strip() for entry in entries}
    if set(decisions) != material_names:
        missing = sorted(material_names - set(decisions))
        extra = sorted(set(decisions) - material_names)
        parts: list[str] = []
        if missing:
            parts.append("missing decisions for " + ", ".join(missing))
        if extra:
            parts.append("decisions outside the material surface: " + ", ".join(extra))
        raise LibraryReviewReissueError("library decision coverage is not exact: " + "; ".join(parts))

    records: dict[str, Any] = {}
    by_name = {str(entry.get("lean_name") or "").strip(): entry for entry in entries}
    for name in sorted(material_names):
        entry = by_name[name]
        decision = decisions[name]
        if not str(entry.get("library_definition") or "").strip():
            raise LibraryReviewReissueError(
                f"{name}: exact bounded library declaration is unavailable: "
                + str(entry.get("library_definition_error") or "")
            )
        if not str(entry.get("library_semantic_target") or "").strip():
            raise LibraryReviewReissueError(
                f"{name}: Lean semantic target is unavailable: "
                + str(entry.get("library_semantic_target_error") or "")
            )
        if not str(entry.get("verbatim_source_input") or "").strip():
            raise LibraryReviewReissueError(
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
                "library_source_path",
                "library_line_start",
                "library_line_end",
                "label",
            )
            if key in raw
        }
        record.update(
            {
                "library_declaration": name,
                "library_source_path": entry["library_source_path"],
                "library_line_start": entry["library_line_start"],
                "library_line_end": entry["library_line_end"],
                "library_definition_sha256": entry["library_definition_sha256"],
                "library_semantic_target_sha256": entry[
                    "library_semantic_target_sha256"
                ],
                "library_semantic_target_protocol": TARGET_PROTOCOL,
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
        "schema": 1,
        "paper": paper_dir.name,
        "prompt_version": PROMPT_VERSION,
        "target_protocol": TARGET_PROTOCOL,
        "comment": (
            "Each verdict compares the byte-pinned paper-source bundle with Lean's "
            "current semantic target and exact bounded declaration code. These "
            "prerequisites are not additional paper-claim rows."
        ),
        "direct_spec_dependency_surface": direct_surface,
        "items": records,
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
        "--packet-lean-cache",
        action="store_true",
        help=(
            "reuse the exact-current staged packet Lean-display cache; use only after "
            "a successful focused paper build in the same checkout"
        ),
    )
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = args.root.resolve() / "papers" / args.paper
    decisions = _decisions(args.decisions, paper=args.paper)
    packet_cache = None
    if args.packet_lean_cache:
        source_map = _load_object(
            paper_dir / "audit" / "paper_statement_map.json", label="source map"
        )
        source_items = source_map.get("items")
        specs = sorted(
            {
                str(contract.get("spec_declaration") or "").strip()
                for item in (source_items.values() if isinstance(source_items, Mapping) else ())
                if isinstance(item, Mapping)
                for contract in [item.get("semantic_contract")]
                if isinstance(contract, Mapping)
                and str(contract.get("spec_declaration") or "").strip()
            }
        )
        packet_cache = review_dashboard_packet._current_packet_lean_cache(
            paper_dir, specs
        )
        if packet_cache is None:
            raise LibraryReviewReissueError(
                "no exact-current packet Lean cache; prepare its three stages first"
            )
    payload = reissue(
        paper_dir,
        decisions,
        validator=args.validator,
        require_build=not args.skip_build,
        packet_lean_cache=packet_cache,
    )
    if not args.write:
        print(f"{args.paper}: validated {len(decisions)} library decisions; rerun with --write")
        return 0
    path = paper_dir / LEDGER_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} ({len(decisions)} library decisions)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except LibraryReviewReissueError as exc:
        print(f"library semantic reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
