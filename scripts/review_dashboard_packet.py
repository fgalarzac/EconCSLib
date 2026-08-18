#!/usr/bin/env python3
"""Generate a concise human-review TeX/PDF packet from audit sidecars.

The ordinary dashboard is the interactive reviewer surface.  This companion
creates a durable, mark-up-friendly compact claim packet: the exact
byte-pinned source input, expanded PaperInterface specification, paired proof
endpoint, and saved statement-judge assessment.  Source-map summaries and
Lean-to-TeX paraphrases are deliberately excluded from this semantic review
surface.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

try:
    from scripts import review_dashboard
    from scripts.lean_signature_manifest import (
        paper_owned_module_names_in_import_closure,
        run_lean_transparent_paper_declaration_displays,
        run_lean_transparent_paper_spec_displays,
    )
except ModuleNotFoundError:  # Direct `python scripts/review_dashboard_packet.py` execution.
    import review_dashboard
    from lean_signature_manifest import (  # type: ignore[no-redef]
        paper_owned_module_names_in_import_closure,
        run_lean_transparent_paper_declaration_displays,
        run_lean_transparent_paper_spec_displays,
    )


ROOT = Path(__file__).resolve().parents[1]
TEMPLATE_PATH = Path(__file__).with_name("templates") / "HUMAN_REVIEW_PACKET.tex.in"
PACKET_NAME = "HUMAN_REVIEW_PACKET"
SOURCE_MAP_NAME = "audit/paper_statement_map.json"
INTAKE_FREEZE_NAME = "audit/intake_freeze.json"
V11_SCREENING_NAME = "audit/v11_raw_source_spec_screening.json"
V11_SCREENING_SCHEMA = 2
V11_SCREENING_PROMPT_VERSION = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2"
)
V11_LEAN_TARGET_PROTOCOL = "lean_transparent_paper_expansion_v1"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
PAPER_PREREQUISITE_LEDGER_NAME = "audit/paper_semantic_prerequisites.json"
PAPER_PREREQUISITE_SCHEMA = 1
PAPER_PREREQUISITE_PROMPT_VERSION = (
    "paper-prerequisite-match-v2-verbatim-source-anchor-lean-expanded-target-exact-code"
)
PAPER_PREREQUISITE_TARGET_PROTOCOL = "lean_paper_declaration_display_v1"
PACKET_LEAN_CACHE_NAME = "audit/human_review_packet_lean_cache.json"
PACKET_LEAN_CACHE_SCHEMA = 3

def _tex_escape(value: object) -> str:
    text = str(value or "")
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "#": r"\#",
        "$": r"\$",
        "%": r"\%",
        "&": r"\&",
        "_": r"\_",
        "^": r"\textasciicircum{}",
        "~": r"\textasciitilde{}",
    }
    return "".join(replacements.get(character, character) for character in text)


def _tex_identifier(value: object) -> str:
    """Escape a Lean identifier while allowing graceful segment-level breaks."""

    escaped = _tex_escape(value)
    return escaped.replace(".", ".\\allowbreak{}").replace(
        r"\_", r"\_\allowbreak{}"
    )


def _tex_locator(value: object) -> str:
    """Render an audit locator with safe breakpoints for long local paths."""

    escaped = _tex_escape(value)
    for separator in ("/", ":", "-", ";", "."):
        escaped = escaped.replace(separator, separator + r"\allowbreak{}")
    return r"{\footnotesize\raggedright " + escaped + r"\par}"


def _tex_breakable_text(value: object) -> str:
    """Escape ordinary text while permitting breaks inside path-like references."""

    escaped = _tex_escape(value)
    for separator in ("/", ":", "-", ";", "."):
        escaped = escaped.replace(separator, separator + r"\allowbreak{}")
    escaped = escaped.replace(r"\_", r"\_\allowbreak{}")
    return escaped


def _packet_anchor(prefix: str, identity: object) -> str:
    """Return a short deterministic PDF anchor safe for arbitrary Lean names."""

    digest = hashlib.sha256(str(identity or "").encode("utf-8")).hexdigest()[:16]
    return f"{prefix}-{digest}"


def _verbatim(value: object) -> str:
    """Render untrusted audit text as TeX verbatim without ending its block."""

    text = str(value or "").strip()
    if not text:
        text = "[No record available.]"
    # A source or Lean declaration cannot normally contain this delimiter, but
    # prevent a malformed sidecar from terminating generated TeX early.
    text = text.replace(r"\end{ReviewVerbatim}", r"\textbackslash{}end{ReviewVerbatim}")
    # DejaVu Sans Mono does not contain every Unicode mathematical-alphabet
    # glyph that appears in Lean pretty-printing.  Keep the compact review
    # packet readable rather than emitting missing-character boxes.
    text = text.replace("𝓕", "calF")
    text = text.replace("ℓ", "ell")
    text = text.replace("⦃", "{{").replace("⦄", "}}")
    # Lean's pretty printer can emit private-use pieces of extensible
    # delimiters.  The packet font cannot render those pieces; retain an
    # explicit marker instead of silently deleting an unknown mathematical
    # glyph from a reviewer-visible target.
    for codepoint in (0xF8EB, 0xF8ED, 0xF8F1, 0xF8F2, 0xF8F3, 0xF8F4, 0xF8F6, 0xF8F8):
        text = text.replace(chr(codepoint), f"[U+{codepoint:04X} delimiter glyph]")
    # Lean's exact private-use pieces can vary by version.  Keep an unlisted
    # piece visible rather than emitting a missing glyph into the reviewer
    # packet.
    text = "".join(
        f"[U+{ord(character):04X} private-use glyph]"
        if unicodedata.category(character) == "Co"
        else character
        for character in text
    )
    # PDF-to-text sources sometimes retain page controls or an unprintable
    # epsilon-like control byte.  They are part of the source extraction, but
    # XeTeX cannot place them in a verbatim environment.  Render a visible,
    # deterministic marker rather than silently dropping any source content.
    rendered: list[str] = []
    for character in text:
        codepoint = ord(character)
        if character in {"\n", "\t"} or codepoint >= 32:
            rendered.append(character)
        elif character == "\f":
            rendered.append("\n[form-feed in source extraction]\n")
        else:
            rendered.append(f"[U+{codepoint:04X} control character]")
    text = "".join(rendered)
    return "\\begin{ReviewVerbatim}\n" + text + "\n\\end{ReviewVerbatim}\n"


def _read_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def _paper_lean_tree_sha256(paper_dir: Path) -> str:
    """Hash the exact paper-local Lean sources behind a cached display pass."""

    digest = hashlib.sha256()
    for path in sorted(paper_dir.rglob("*.lean")):
        relative = path.relative_to(paper_dir).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _lean_source_tree_sha256(root: Path) -> str:
    """Hash the exact Lean source tree that can affect a cached display.

    Packet targets deliberately leave reusable-library declarations named, but
    the declarations' own semantic target and dependency closure are still
    produced by Lean.  A packet cache therefore must not remain current after
    a library source edit merely because its paper-local interface is stable.
    Hashing source bytes is inexpensive and gives this cache the same
    invalidation discipline as its paper-local half without expanding the
    library in every integrity pass.
    """

    digest = hashlib.sha256()
    if not root.is_dir():
        return ""
    for path in sorted(root.rglob("*.lean")):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _packet_lean_display_engine_sha256() -> str:
    """Return a fingerprint of the local code producing cached Lean displays."""

    digest = hashlib.sha256()
    for path in (
        Path(__file__),
        Path(__file__).with_name("review_dashboard.py"),
        Path(__file__).with_name("lean_signature_manifest.py"),
    ):
        relative = path.name.encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _packet_lean_cache_path(paper_dir: Path) -> Path:
    return paper_dir / PACKET_LEAN_CACHE_NAME


def _current_packet_lean_cache(
    paper_dir: Path, specification_names: Iterable[str]
) -> dict[str, Any] | None:
    """Return a cache only when it belongs to this exact paper Lean surface.

    The cache is a transport optimization for the human packet, not an audit
    receipt.  It lets a large paper perform the three independent Lean walks
    in separate bounded commands; final audit gates still rerun their own
    build-backed checks.
    """

    path = _packet_lean_cache_path(paper_dir)
    if not path.is_file():
        return None
    try:
        payload = _read_json(path)
    except ValueError:
        return None
    names = sorted({str(name).strip() for name in specification_names if str(name).strip()})
    if (
        payload.get("schema") != PACKET_LEAN_CACHE_SCHEMA
        or payload.get("paper") != paper_dir.name
        or payload.get("paper_lean_tree_sha256") != _paper_lean_tree_sha256(paper_dir)
        or payload.get("library_lean_tree_sha256")
        != _lean_source_tree_sha256(ROOT / "EconCSLib")
        or payload.get("lean_display_engine_sha256")
        != _packet_lean_display_engine_sha256()
        or payload.get("specifications") != names
    ):
        return None
    for field in (
        "semantic_targets",
        "paper_prerequisite_targets",
        "library_semantic_targets",
        "library_semantic_target_errors",
    ):
        if not isinstance(payload.get(field), Mapping):
            return None
    return payload


def _write_packet_lean_cache(paper_dir: Path, payload: Mapping[str, Any]) -> None:
    path = _packet_lean_cache_path(paper_dir)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def prepare_packet_lean_cache(paper: str, *, stage: str) -> str:
    """Run one bounded Lean-display stage for a human-review packet.

    Large source surfaces can exceed a command runner's wall-clock budget if
    the Spec, paper-prerequisite, and library walks are attempted monolithically.
    This records each exact Lean display after it succeeds, so the eventual
    packet remains complete without weakening any closeout gate.
    """

    paper_dir = ROOT / "papers" / paper
    if not paper_dir.is_dir():
        raise ValueError(f"unknown paper: {paper}")
    source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
    interface_items = _paperinterface_items(paper_dir)
    claim_rows = _claim_review_rows(paper_dir, source_map, interface_items)
    specifications = sorted(
        {
            str(item.get("full_name") or "").strip()
            for item, _records, _proof in claim_rows
            if str(item.get("full_name") or "").strip()
        }
    )
    cached = _current_packet_lean_cache(paper_dir, specifications)
    payload: dict[str, Any] = (
        dict(cached)
        if cached is not None
        else {
            "schema": PACKET_LEAN_CACHE_SCHEMA,
            "paper": paper,
            "paper_lean_tree_sha256": _paper_lean_tree_sha256(paper_dir),
            "library_lean_tree_sha256": _lean_source_tree_sha256(ROOT / "EconCSLib"),
            "lean_display_engine_sha256": _packet_lean_display_engine_sha256(),
            "specifications": specifications,
            "semantic_targets": {},
            "paper_prerequisite_targets": {},
            "library_semantic_targets": {},
            "library_semantic_target_errors": {},
        }
    )
    if stage == "specifications":
        targets = semantic_expanded_spec_targets(
            paper_dir, specifications, require_build=False
        )
        if set(targets) != set(specifications):
            raise ValueError("Lean returned an incomplete transparent Spec display set")
        payload["semantic_targets"] = targets
    elif stage == "paper-prerequisites":
        semantic_targets = payload.get("semantic_targets")
        if not isinstance(semantic_targets, Mapping) or set(semantic_targets) != set(specifications):
            raise ValueError(
                "prepare the specifications cache first with --stage specifications"
            )
        names = sorted(
            {
                str(name).strip()
                for target in semantic_targets.values()
                if isinstance(target, Mapping)
                for name in target.get("prerequisite_declarations", ())
                if str(name).strip()
            }
        )
        targets = paper_semantic_prerequisite_targets(
            paper_dir, names, require_build=False
        )
        if not set(names).issubset(targets):
            raise ValueError("Lean returned an incomplete paper-prerequisite display set")
        payload["paper_prerequisite_targets"] = targets
    elif stage == "library":
        semantic_targets = payload.get("semantic_targets")
        prerequisite_targets = payload.get("paper_prerequisite_targets")
        if not isinstance(semantic_targets, Mapping) or set(semantic_targets) != set(specifications):
            raise ValueError(
                "prepare the specifications cache first with --stage specifications"
            )
        if not isinstance(prerequisite_targets, Mapping):
            raise ValueError(
                "prepare the paper-prerequisites cache first with --stage paper-prerequisites"
            )
        direct_names = {
            str(name).strip()
            for target in [*semantic_targets.values(), *prerequisite_targets.values()]
            if isinstance(target, Mapping)
            for name in target.get("library_declarations", target.get("direct_library_declarations", ()))
            if str(name).strip().startswith("EconCSLib.")
        }
        targets, errors = review_dashboard.library_semantic_targets(
            paper_dir, direct_names, require_build=False
        )
        payload["library_semantic_targets"] = targets
        payload["library_semantic_target_errors"] = errors
    else:
        raise ValueError(f"unknown packet Lean-cache stage: {stage}")
    _write_packet_lean_cache(paper_dir, payload)
    return f"{paper}: prepared packet Lean-cache stage `{stage}`"


def _source_records_by_declaration(
    source_map: Mapping[str, Any],
) -> dict[str, list[Mapping[str, Any]]]:
    """Index source-map records by every paper-facing Lean route they name."""

    out: dict[str, list[Mapping[str, Any]]] = {}
    raw_items = source_map.get("items")
    items: Iterable[tuple[str, Any]]
    if isinstance(raw_items, Mapping):
        items = raw_items.items()
    elif isinstance(raw_items, list):
        items = (
            (str(item.get("id") or item.get("source_item") or ""), item)
            for item in raw_items
            if isinstance(item, Mapping)
        )
    else:
        return out
    for _key, raw_item in items:
        if not isinstance(raw_item, Mapping):
            continue
        routes: set[str] = set()
        for field in ("lean_declarations", "review_rows"):
            values = raw_item.get(field)
            if isinstance(values, list):
                routes.update(str(value).strip() for value in values if str(value).strip())
        contract = raw_item.get("semantic_contract")
        if isinstance(contract, Mapping):
            for field in ("spec_declaration", "evidence_declaration"):
                value = str(contract.get(field) or "").strip()
                if value:
                    routes.add(value)
        for route in routes:
            out.setdefault(route, []).append(raw_item)
    return out


def _source_map_records(source_map: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    """Return source-map records in their declared, stable source order."""

    raw_items = source_map.get("items")
    if isinstance(raw_items, Mapping):
        return [item for item in raw_items.values() if isinstance(item, Mapping)]
    if isinstance(raw_items, list):
        return [item for item in raw_items if isinstance(item, Mapping)]
    return []


def _short_declaration_name(value: object) -> str:
    return str(value or "").strip().rsplit(".", 1)[-1]


def _intake_dependency_order(paper_dir: Path) -> dict[str, int]:
    """Read the approved claim-level order, when the paper has an intake map.

    The intake order is the source-claim DAG's deterministic linearization.
    It is intentionally used only to order human rows; it does not replace the
    Lean closure evidence used for formal closeout.
    """

    path = paper_dir / INTAKE_FREEZE_NAME
    if not path.is_file():
        return {}
    try:
        payload = _read_json(path)
    except ValueError:
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list):
        return {}
    order: dict[str, int] = {}
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            continue
        raw_rank = raw_item.get("dependency_order")
        if not isinstance(raw_rank, int) or raw_rank < 0:
            continue
        for field in ("spec_declaration", "proof_declaration"):
            name = _short_declaration_name(raw_item.get(field))
            if name:
                order[name] = raw_rank
    return order


def _semantic_route(record: Mapping[str, Any], field: str) -> str:
    contract = record.get("semantic_contract")
    if isinstance(contract, Mapping):
        value = str(contract.get(field) or "").strip()
        if value:
            return value
    return ""


def _paperinterface_items(paper_dir: Path) -> dict[str, dict[str, Any]]:
    """Read the one transparent ``Spec`` declaration for each review row.

    This deliberately avoids the dashboard's Lean-Meta extraction path.  A
    human packet is a source/Spec review surface, so it needs the exact
    declaration text in ``PaperInterface.lean`` and no theorem wrapper or
    Lean-to-TeX paraphrase.  The paired proof endpoint is displayed only as
    separately built evidence.
    """

    source_path = paper_dir / "PaperInterface.lean"
    items: dict[str, dict[str, Any]] = {}
    for kind, name, full_name, source, comment, _line, _path in (
        review_dashboard.parse_review_source_declarations(source_path)
    ):
        if not name.endswith("Spec"):
            continue
        items[full_name] = {
            "kind": kind,
            "name": name,
            "full_name": full_name,
            "interface_source": source,
            "lean_statement": source,
            "comment": comment or "",
        }
    return items


def _paper_declaration_sources(
    paper_dir: Path,
    *,
    wanted_names: Iterable[str] = (),
) -> dict[str, dict[str, Any]]:
    """Read exact top-level paper declarations available as semantic prerequisites."""

    entries: dict[str, dict[str, Any]] = {}
    for source_path in sorted(paper_dir.rglob("*.lean")):
        for kind, _short, full_name, source, _comment, line, path in (
            review_dashboard.parse_review_source_declarations(source_path)
        ):
            name = str(full_name or "").strip()
            declaration = str(source or "").strip()
            if not name or not declaration or name in entries:
                continue
            try:
                relative = path.resolve().relative_to(ROOT).as_posix()
            except ValueError:
                continue
            entries[name] = {
                "paper_declaration": name,
                "paper_declaration_kind": str(kind or "").strip(),
                "paper_declaration_source": declaration,
                "paper_declaration_sha256": hashlib.sha256(
                    declaration.encode("utf-8")
                ).hexdigest(),
                "paper_source_path": relative,
                "paper_line_start": int(line),
            }
    # The regular dashboard parser is deliberately conservative: one malformed
    # or unusually nested implementation declaration must not make it guess at
    # later dashboard rows.  For a named, Lean-selected prerequisite, however,
    # we can safely recover its exact local declaration by scanning only for
    # that requested terminal name.  This avoids silently omitting a semantic
    # review card merely because an earlier implementation block confused the
    # presentation parser.  The fallback does not infer a declaration name;
    # it is accepted only when one requested fully qualified name has that
    # unique terminal spelling.
    missing = {
        str(name).strip()
        for name in wanted_names
        if str(name).strip() and str(name).strip() not in entries
    }
    by_terminal: dict[str, list[str]] = {}
    for name in missing:
        by_terminal.setdefault(name.rsplit(".", 1)[-1], []).append(name)
    for source_path in sorted(paper_dir.rglob("*.lean")):
        if not by_terminal:
            break
        try:
            lines = source_path.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for index, line in enumerate(lines):
            match = review_dashboard.DECL_RE.match(line)
            if match is None:
                continue
            terminal = str(match.group("name") or "").strip()
            candidates = by_terminal.get(terminal, ())
            if len(candidates) != 1:
                continue
            full_name = candidates[0]
            collected = review_dashboard.collect_review_decl_text(
                lines, index, str(match.group("kind") or "")
            )
            if collected is None:
                continue
            declaration, _next_index = collected
            try:
                relative = source_path.resolve().relative_to(ROOT).as_posix()
            except ValueError:
                continue
            entries[full_name] = {
                "paper_declaration": full_name,
                "paper_declaration_kind": str(match.group("kind") or "").strip(),
                "paper_declaration_source": declaration,
                "paper_declaration_sha256": hashlib.sha256(
                    declaration.encode("utf-8")
                ).hexdigest(),
                "paper_source_path": relative,
                "paper_line_start": index + 1,
            }
            del by_terminal[terminal]
    return entries


def paper_semantic_prerequisite_targets(
    paper_dir: Path,
    initial_names: Iterable[str],
    *,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    """Return Lean-owned displays for the full paper-prerequisite closure.

    The Spec display retains a paper-local state/model/policy name instead of
    inlining it into a giant implementation term.  This second Lean walk opens
    each such declaration at its own root, then reports every remaining
    paper-local or reusable-library dependency as a separate review input.
    """

    names = sorted({str(name).strip() for name in initial_names if str(name).strip()})
    if not names:
        return {}
    interface_path = paper_dir / "PaperInterface.lean"
    if not interface_path.is_file():
        raise ValueError(f"missing PaperInterface: {interface_path}")
    try:
        source_module = review_dashboard.review_source_module(paper_dir, interface_path)
        paper_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            paper_dir,
            source_module,
        )
        targets = run_lean_transparent_paper_declaration_displays(
            ROOT,
            source_module,
            names,
            paper_modules,
            require_build=require_build,
        )
    except Exception as exc:  # Lean unavailability is a review-surface failure.
        raise ValueError(
            f"could not obtain Lean paper-prerequisite semantic targets: {exc}"
        ) from exc
    if not set(names).issubset(targets):
        missing = sorted(set(names) - set(targets))
        raise ValueError(
            "Lean could not produce a complete paper-prerequisite target for: "
            + ", ".join(missing[:4])
            + ("; ..." if len(missing) > 4 else "")
        )
    return targets


def paper_semantic_prerequisites(
    paper_dir: Path,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    *,
    ledger_payload: Mapping[str, Any] | None = None,
    require_build: bool = True,
    semantic_targets_by_name_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Return source-connected paper-local primitives retained in Spec displays.

    An inductive state, transition relation, or structure is not a harmless
    unexpanded name.  Lean identifies it while expanding the paper claim; this
    function then requires the same raw-source connection and independent
    semantic judgment used for a reusable library primitive.  These cards are
    prerequisite review material, not additional paper-claim denominator rows.
    """

    names = sorted(
        {
            str(name).strip()
            for target in semantic_targets.values()
            for name in target.get("prerequisite_declarations", ())
            if str(name).strip()
        }
    )
    if not names:
        return []
    if semantic_targets_by_name_override is not None:
        semantic_targets_by_name = {
            str(name).strip(): dict(target)
            for name, target in semantic_targets_by_name_override.items()
            if str(name).strip() and isinstance(target, Mapping)
        }
        missing = sorted(set(names) - set(semantic_targets_by_name))
        semantic_target_error = (
            "packet Lean-cache is missing paper-prerequisite targets: "
            + ", ".join(missing[:4])
            if missing
            else ""
        )
    else:
        try:
            semantic_targets_by_name = paper_semantic_prerequisite_targets(
                paper_dir,
                names,
                require_build=require_build,
            )
        except ValueError as exc:
            semantic_targets_by_name = {}
            semantic_target_error = str(exc)
        else:
            semantic_target_error = ""
    names = sorted(set(semantic_targets_by_name) or set(names))
    declarations = _paper_declaration_sources(paper_dir, wanted_names=names)
    try:
        source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
    except ValueError:
        source_map = {}
    source_items = {
        str(key).strip(): raw
        for key, raw in (
            source_map.get("items", {}).items()
            if isinstance(source_map.get("items"), Mapping)
            else []
        )
        if str(key).strip() and isinstance(raw, Mapping)
    }
    if ledger_payload is None:
        ledger_path = paper_dir / PAPER_PREREQUISITE_LEDGER_NAME
        try:
            ledger = _read_json(ledger_path) if ledger_path.is_file() else {}
        except ValueError:
            ledger = {}
    else:
        ledger = dict(ledger_payload)
    ledger_is_current_protocol = bool(
        ledger.get("schema") == PAPER_PREREQUISITE_SCHEMA
        and ledger.get("paper") == paper_dir.name
        and ledger.get("prompt_version") == PAPER_PREREQUISITE_PROMPT_VERSION
        and ledger.get("target_protocol") == PAPER_PREREQUISITE_TARGET_PROTOCOL
    )
    raw_items = ledger.get("items") if isinstance(ledger, Mapping) else {}
    ledger_items = raw_items if isinstance(raw_items, Mapping) else {}
    entries: list[dict[str, Any]] = []
    for name in names:
        declaration = declarations.get(name, {})
        semantic_target = semantic_targets_by_name.get(name, {})
        raw = ledger_items.get(name)
        raw = raw if isinstance(raw, Mapping) else {}
        source_item_key = str(raw.get("source_item") or "").strip()
        source_record = source_items.get(source_item_key)
        source_input = ""
        source_digest = ""
        source_error = ""
        source_locator = ""
        if source_item_key and source_record is None:
            source_error = f"registered source item `{source_item_key}` is absent from the statement map"
        elif source_record is not None:
            source_locator = str(source_record.get("source_location") or "not recorded")
            source_error = review_dashboard.source_anchor_file_error(paper_dir, source_record)
            if not source_error:
                source_input, source_digest, source_error = review_dashboard.source_semantic_input_bundle(
                    source_record, require_context_roles=True
                )
        elif isinstance(raw.get("source_anchor_evidence"), list):
            source_locator = str(raw.get("source_location") or "not recorded")
            source_error = review_dashboard.source_anchor_file_error(paper_dir, raw)
            if not source_error:
                source_input, source_digest, source_error = review_dashboard.source_semantic_input_bundle(
                    raw, require_context_roles=True
                )
        else:
            source_error = "no explicit byte-pinned paper source connection is registered"
        judgment = str(raw.get("judgment") or "").strip().lower()
        has_metadata = bool(
            str(raw.get("validator") or "").strip()
            and str(raw.get("validated_at") or "").strip()
        )
        declaration_digest = str(declaration.get("paper_declaration_sha256") or "")
        semantic_target_text = str(semantic_target.get("display") or "").strip()
        semantic_target_digest = str(semantic_target.get("display_sha256") or "").strip()
        current = bool(
            ledger_is_current_protocol
            and declaration
            and semantic_target_text
            and not source_error
            and judgment in {"matches", "mismatch", "uncertain"}
            and str(raw.get("paper_declaration") or "").strip() == name
            and str(raw.get("paper_source_path") or "").strip()
            == str(declaration.get("paper_source_path") or "")
            and raw.get("paper_line_start") == declaration.get("paper_line_start")
            and str(raw.get("paper_declaration_sha256") or "").strip().lower()
            == declaration_digest
            and str(raw.get("paper_semantic_target_sha256") or "").strip().lower()
            == semantic_target_digest
            and str(raw.get("paper_semantic_target_protocol") or "").strip()
            == PAPER_PREREQUISITE_TARGET_PROTOCOL
            and str(raw.get("source_input_bundle_sha256") or "").strip().lower()
            == source_digest
            and has_metadata
        )
        if not declaration:
            status = "Lean retained a paper-local prerequisite with no exact source declaration"
        elif not semantic_target_text:
            status = semantic_target_error or "Lean did not produce a paper-prerequisite semantic target"
        elif not ledger_is_current_protocol:
            status = "paper-prerequisite semantic-review ledger is missing or stale"
        elif source_error:
            status = source_error
        elif not judgment:
            status = "source connection is registered; semantic judgment is pending"
        elif not current:
            status = "recorded paper-prerequisite semantic judgment is stale or incomplete"
        else:
            status = "current"
        entries.append(
            {
                **declaration,
                "lean_name": name,
                "source_item": source_item_key,
                "source_locator": source_locator,
                "verbatim_source_input": source_input,
                "source_input_bundle_sha256": source_digest,
                "source_connection_error": source_error,
                "paper_semantic_target": semantic_target_text,
                "paper_semantic_target_sha256": semantic_target_digest,
                "paper_semantic_target_kind": str(
                    semantic_target.get("declaration_kind") or ""
                ).strip(),
                "paper_semantic_target_root_expanded": semantic_target.get(
                    "root_expanded"
                ),
                "paper_semantic_target_error": semantic_target_error,
                "direct_paper_declarations": list(
                    semantic_target.get("direct_paper_declarations", ())
                ),
                "direct_library_declarations": list(
                    semantic_target.get("direct_library_declarations", ())
                ),
                "semantic_judgment": judgment or "not recorded",
                "semantic_reason": str(raw.get("reason") or "").strip(),
                "semantic_current": current,
                "semantic_status": status,
            }
        )
    return entries


def semantic_expanded_spec_targets(
    paper_dir: Path,
    specification_names: Iterable[str],
    *,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    """Return Lean-produced, source-reviewable semantic targets for ``Spec`` rows.

    The result is intentionally not a parser-produced macro expansion.  Lean
    elaborates and unfolds transparent wrappers defined in the review module,
    then pretty-prints the semantic proposition.  Definitions from the
    paper's source-model/procedure modules remain named paper-local
    prerequisites, just as reusable-library declarations remain named library
    prerequisites.  Their exact code and source connection are checked on
    their own cards rather than expanding implementation records into a claim.
    """

    specifications = sorted(
        {str(name).strip() for name in specification_names if str(name).strip()}
    )
    if not specifications:
        return {}
    interface_path = paper_dir / "PaperInterface.lean"
    if not interface_path.is_file():
        raise ValueError(f"missing PaperInterface: {interface_path}")
    try:
        source_module = review_dashboard.review_source_module(paper_dir, interface_path)
        paper_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            paper_dir,
            source_module,
        )
        targets = run_lean_transparent_paper_spec_displays(
            ROOT,
            source_module,
            specifications,
            paper_modules,
            require_build=require_build,
        )
    except Exception as exc:  # Lean unavailability is a review-surface failure.
        raise ValueError(f"could not obtain Lean-expanded semantic targets: {exc}") from exc
    if set(targets) != set(specifications):
        missing = sorted(set(specifications) - set(targets))
        raise ValueError(
            "Lean could not produce a complete transparent semantic target for: "
            + ", ".join(missing[:4])
            + ("; ..." if len(missing) > 4 else "")
        )
    interface_sha256 = hashlib.sha256(interface_path.read_bytes()).hexdigest()
    return {
        name: {
            **dict(target),
            "paper_interface_sha256": interface_sha256,
            "lean_expansion_protocol": V11_LEAN_TARGET_PROTOCOL,
        }
        for name, target in targets.items()
    }


def _v11_screening_rows(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    interface_items: Mapping[str, Mapping[str, Any]],
    semantic_targets: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Load current raw-source-to-Spec screening outcomes, if present.

    The record states what source bundle and full ``Spec`` were compared and
    any discrepancy found.  It is hash-bound, so a packet can never display a
    verdict for stale source text or a changed ``Spec`` declaration.
    """

    path = paper_dir / V11_SCREENING_NAME
    if not path.is_file():
        return {}
    try:
        payload = _read_json(path)
    except ValueError:
        return {}
    if (
        payload.get("schema") != V11_SCREENING_SCHEMA
        or payload.get("paper") != paper_dir.name
        or payload.get("prompt_version")
        != V11_SCREENING_PROMPT_VERSION
    ):
        return {}
    raw_items = payload.get("items")
    source_records = _source_map_records(source_map)
    records_by_spec = {
        _semantic_route(record, "spec_declaration"): record
        for record in source_records
        if _semantic_route(record, "spec_declaration")
    }
    if not isinstance(raw_items, Mapping):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for full_name, raw in raw_items.items():
        name = str(full_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            continue
        record = records_by_spec.get(name)
        item = interface_items.get(name)
        target = semantic_targets.get(name)
        if record is None or item is None or target is None:
            continue
        _source_text, source_digest, source_error = review_dashboard.source_semantic_input_bundle(
            record, require_context_roles=True
        )
        spec_digest = str(target.get("display_sha256") or "").strip().lower()
        interface_digest = str(target.get("paper_interface_sha256") or "").strip().lower()
        verdict = str(raw.get("judgment") or "").strip().lower()
        corrected_target = record.get("corrected_target")
        approved_corrected_target = bool(
            verdict == APPROVED_CORRECTED_TARGET_MATCH
            and str(record.get("coverage_status") or "").strip()
            == "corrected_source_statement"
            and isinstance(corrected_target, Mapping)
            and corrected_target.get("archival_equivalence_claimed") is False
            and str(raw.get("corrected_target_protocol") or "").strip()
            == "approved_corrected_target_v1"
            and str(raw.get("corrected_target_sha256") or "").strip().lower()
            == str(corrected_target.get("corrected_target_sha256") or "").strip().lower()
        )
        has_metadata = bool(
            str(raw.get("validator") or payload.get("validator") or "").strip()
            and str(raw.get("validated_at") or payload.get("validated_at") or "").strip()
        )
        current = bool(
            (
                approved_corrected_target
                if str(record.get("coverage_status") or "").strip()
                == "corrected_source_statement"
                else verdict in {"matches", "mismatch", "uncertain"}
            )
            and not source_error
            and raw.get("source_input_bundle_sha256") == source_digest
            and raw.get("paper_statement_sha256") == source_digest
            and raw.get("lean_expanded_statement_sha256") == spec_digest
            and raw.get("paper_interface_sha256") == interface_digest
            and raw.get("source_input_protocol") == "verbatim_source_anchor_bundle_v1"
            and raw.get("lean_target_protocol") == V11_LEAN_TARGET_PROTOCOL
            and raw.get("semantic_target_declaration") == name
            and has_metadata
        )
        out[name] = {
            "judgment": verdict or "not recorded",
            "reason": str(raw.get("reason") or "").strip(),
            "validator": str(raw.get("validator") or payload.get("validator") or "").strip(),
            "validated_at": str(raw.get("validated_at") or payload.get("validated_at") or "").strip(),
            "current": current,
        }
    return out


def _claim_review_rows(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    interface_items: Mapping[str, Mapping[str, Any]] | Iterable[Mapping[str, Any]],
) -> list[tuple[Mapping[str, Any], list[Mapping[str, Any]], str]]:
    """Select one human row per source claim, in approved DAG order.

    Each source-map item pairs a transparent ``Spec`` review proposition with a
    theorem whose type is that proposition.  The dashboard deliberately shows
    both Lean declarations; the packet instead shows the ``Spec`` once and
    names the paired theorem as its verification endpoint.  That keeps the
    human surface source-claim based and prevents duplicate review rows.
    """

    if not isinstance(interface_items, Mapping):
        interface_items = {
            str(item.get("full_name") or "").strip(): item
            for item in interface_items
            if str(item.get("full_name") or "").strip()
        }
    records_by_declaration = _source_records_by_declaration(source_map)
    order = _intake_dependency_order(paper_dir)
    selected: list[tuple[int, int, Mapping[str, Any], list[Mapping[str, Any]], str]] = []
    covered: set[str] = set()
    for source_index, record in enumerate(_source_map_records(source_map)):
        spec_name = _semantic_route(record, "spec_declaration")
        proof_name = _semantic_route(record, "evidence_declaration")
        if not spec_name:
            routes = record.get("lean_declarations")
            if isinstance(routes, list):
                spec_name = next((str(route).strip() for route in routes if str(route).strip()), "")
        item = interface_items.get(spec_name)
        if item is None:
            continue
        covered.add(spec_name)
        if proof_name:
            covered.add(proof_name)
        rank = order.get(_short_declaration_name(spec_name), 10_000 + source_index)
        selected.append(
            (
                rank,
                source_index,
                item,
                records_by_declaration.get(spec_name, [record]),
                proof_name,
            )
        )

    # A malformed or legacy map must not hide a PaperInterface specification.
    # Keep any unpaired declarations after the mapped source claims and label
    # their absent proof endpoint explicitly.
    for fallback_index, item in enumerate(interface_items.values(), start=len(selected)):
        full_name = str(item.get("full_name") or "").strip()
        if not full_name or full_name in covered:
            continue
        selected.append(
            (
                20_000 + fallback_index,
                fallback_index,
                item,
                records_by_declaration.get(full_name, []),
                "",
            )
        )
    return [
        (item, records, proof_name)
        for _rank, _index, item, records, proof_name in sorted(selected, key=lambda entry: entry[:2])
    ]


def _dependency_first_entries(
    entries: Iterable[Mapping[str, Any]],
    *,
    name_field: str,
    dependency_field: str,
    normalize_dependency: Callable[[str], str] | None = None,
) -> list[Mapping[str, Any]]:
    """Return a deterministic dependency-first ordering for review cards.

    The order is solely a human-reading aid.  It makes a definition visible
    before the card which uses it, without trying to recreate Lean's proof or
    elaboration traversal in Python.  Lean has already supplied the direct
    dependencies in the cached display targets; Python merely topologically
    presents those reported edges.  Cycles, which should be impossible in the
    transparent declaration surface, are retained deterministically rather
    than silently discarded.
    """

    materialized = [entry for entry in entries if str(entry.get(name_field) or "").strip()]
    by_name = {
        str(entry.get(name_field) or "").strip(): entry for entry in materialized
    }
    order: list[Mapping[str, Any]] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def normalized(raw: object) -> str:
        value = str(raw or "").strip()
        return normalize_dependency(value) if normalize_dependency and value else value

    def visit(name: str) -> None:
        if name in permanent:
            return
        if name in temporary:
            # Preserve a cyclic item in stable order, while avoiding an
            # infinite display walk.  The Lean/audit lanes remain responsible
            # for treating an invalid closure as a failure.
            return
        entry = by_name.get(name)
        if entry is None:
            return
        temporary.add(name)
        raw_dependencies = entry.get(dependency_field, ())
        dependencies = (
            raw_dependencies if isinstance(raw_dependencies, (list, tuple, set)) else ()
        )
        for dependency in sorted({normalized(raw) for raw in dependencies if normalized(raw)}):
            if dependency in by_name:
                visit(dependency)
        temporary.remove(name)
        permanent.add(name)
        order.append(entry)

    for name in sorted(by_name):
        visit(name)
    return order


def _prerequisites_tex(
    paper_dir: Path,
    items: Iterable[Mapping[str, Any]],
    *,
    require_build: bool = True,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    semantic_target_errors_override: Mapping[str, str] | None = None,
    entries_override: Iterable[Mapping[str, Any]] | None = None,
) -> str:
    """Render source-connected library definitions before dependent claims.

    A library primitive is review material, not an unexplained glossary word.
    The shared dashboard helper returns the exact declaration body, a selected
    byte-pinned paper-source bundle, and the freshness of the independent
    source-to-library semantic judgment.  The packet deliberately preserves
    the raw source and code rather than rendering a curator paraphrase.
    """

    entries = (
        list(entries_override)
        if entries_override is not None
        else review_dashboard.human_review_library_prerequisites(
            paper_dir,
            items,
            require_build=require_build,
            semantic_targets_override=semantic_targets_override,
            semantic_target_errors_override=semantic_target_errors_override,
        )
    )
    if not entries:
        return ""
    rendered = [
        "\\clearpage",
        "\\hypertarget{" + _packet_anchor("library-section", paper_dir.name) + "}{}",
        "\\section*{Material library prerequisites}",
    ]
    entries = _dependency_first_entries(
        entries,
        name_field="lean_name",
        dependency_field="direct_library_declarations",
        normalize_dependency=review_dashboard.library_review_owner_declaration,
    )
    for entry_index, entry in enumerate(entries):
        rendered.extend(
            [
                *( ["\\clearpage"] if entry_index else [] ),
                "\\hypertarget{"
                + _packet_anchor("library-prerequisite", entry.get("lean_name"))
                + "}{}",
                "\\subsection*{\\small\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("label") or entry.get("lean_name"))
                + "}",
            ]
        )
        source_input = str(entry.get("verbatim_source_input") or "").strip()
        if source_input:
            # A library prerequisite is independently reviewable.  Even when
            # multiple declarations share a byte-pinned source bundle, repeat
            # its verbatim input here instead of asking a reviewer to find an
            # earlier prerequisite page.
            rendered.extend(
                [
                    "\\textbf{Source locator:} "
                    + _tex_locator(entry.get("source_locator") or "not recorded"),
                    "\\paragraph{Verbatim paper-source connection}",
                    _verbatim(source_input),
                ]
            )
        else:
            rendered.append(
                "\\textbf{Source connection:} "
                + _tex_escape(entry.get("source_connection_error") or "not recorded")
                + "."
            )
        rendered.extend(
            [
                "\\paragraph{"
                + (
                    "Lean-expanded library semantic target"
                    if entry.get("library_semantic_target_kind") in {"definition", "abbrev"}
                    else "Lean declaration type (metadata)"
                )
                + "}",
                _verbatim(
                    entry.get("library_semantic_target")
                    or entry.get("library_semantic_target_error")
                ),
                "\\paragraph{Exact Lean library declaration}",
                _verbatim(entry.get("library_definition") or entry.get("library_definition_error")),
            ]
        )
        rendered.extend(
            [
                "\\paragraph{Recorded source-to-library screening}",
                "\\textbf{Verdict:} \\texttt{"
                + _tex_escape(entry.get("semantic_judgment") or "not recorded")
                + "}",
            ]
        )
        reason = str(entry.get("semantic_reason") or "").strip()
        if reason:
            rendered.append("\\\\\n\\textbf{Reason:} " + _tex_escape(reason))
        rendered.extend(
            [
                "\\reviewmatch{Matches source input}",
                "\\noindent\\textbf{Reviewer annotation}\\par",
                "\\reviewerbox",
            ]
        )
    return "\n".join(rendered)


def _paper_prerequisites_tex(entries: Iterable[Mapping[str, Any]]) -> str:
    """Render paper-local semantic prerequisites before their dependent claims."""

    entries = _dependency_first_entries(
        entries,
        name_field="lean_name",
        dependency_field="direct_paper_declarations",
    )
    if not entries:
        return ""
    rendered = [
        "\\hypertarget{" + _packet_anchor("paper-prerequisite-section", "all") + "}{}",
        "\\section*{Paper-specific semantic prerequisites}",
        "These paper-local state, policy, or transition declarations remain named in the "
        "Lean-expanded claim because they are independent semantic objects. Each is shown "
        "with its own verbatim source connection and reviewer annotation before the claim "
        "that uses it. They are prerequisites, not extra paper-claim rows.",
    ]
    for entry_index, entry in enumerate(entries):
        rendered.extend(
            [
                *( ["\\clearpage"] if entry_index else [] ),
                "\\hypertarget{"
                + _packet_anchor("paper-prerequisite", entry.get("lean_name"))
                + "}{}",
                "\\subsection*{\\small\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("lean_name"))
                + "}",
                "\\noindent\\textbf{Paper-local declaration:}\\par",
                "{\\footnotesize\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("lean_name"))
                + "\\par}",
            ]
        )
        source_input = str(entry.get("verbatim_source_input") or "").strip()
        if source_input:
            rendered.extend(
                [
                    "\\textbf{Source locator:} "
                    + _tex_locator(entry.get("source_locator") or "not recorded"),
                    "\\paragraph{Verbatim paper-source connection}",
                    _verbatim(source_input),
                ]
            )
        else:
            rendered.append(
                "\\textbf{Source connection:} "
                + _tex_escape(entry.get("source_connection_error") or "not recorded")
                + "."
            )
        rendered.extend(
            [
                "\\paragraph{"
                + (
                    "Lean-expanded paper semantic target"
                    if entry.get("paper_semantic_target_kind") in {"definition", "abbrev"}
                    else "Lean-elaborated paper signature"
                )
                + "}",
                _verbatim(
                    entry.get("paper_semantic_target")
                    or entry.get("paper_semantic_target_error")
                    or "Lean paper-prerequisite semantic target is unavailable."
                ),
                "\\paragraph{Recorded source-to-declaration screening}",
                "\\textbf{Verdict:} \\texttt{"
                + _tex_escape(entry.get("semantic_judgment") or "not recorded")
                + "}",
            ]
        )
        reason = str(entry.get("semantic_reason") or "").strip()
        if reason:
            rendered.append("\\\\\n\\textbf{Reason:} " + _tex_escape(reason))
        rendered.extend(
            [
                "\\reviewmatch{Matches source input}",
                "\\noindent\\textbf{Reviewer annotation}\\par",
                "\\reviewerbox",
            ]
        )
    return "\n".join(rendered)


def public_arxiv_tex_source_error(paper: str) -> str:
    """Return why a paper cannot expose its source excerpts publicly.

    This is intentionally narrow.  It permits only the canonical TeX artifact
    of a source map whose cited version is hosted by arXiv; it is not a general
    permission to publish an extracted PDF/text cache or a private archive.
    """

    paper_dir = ROOT / "papers" / paper
    try:
        source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
    except ValueError as exc:
        return str(exc)
    url = str(source_map.get("source_url") or "").strip().lower()
    raw_path = str(source_map.get("source_artifact_path") or "").strip()
    digest = str(source_map.get("source_artifact_sha256") or "").strip().lower()
    if not re.match(r"https?://(?:export\.)?arxiv\.org/(?:abs|e-print)/", url):
        return "the canonical source map does not cite an official arXiv source URL"
    candidate = Path(raw_path)
    if not raw_path or candidate.is_absolute() or ".." in candidate.parts or candidate.suffix.lower() != ".tex":
        return "the canonical source artifact is not a paper-local .tex file"
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        return "the canonical source map has no valid source-artifact SHA-256"
    return ""


def _record_source_blocks(
    records: Iterable[Mapping[str, Any]],
    verbatim_source_input: object,
) -> str:
    records = list(records)
    if not records:
        return "\\paragraph{Verbatim source input}\n" + _verbatim(verbatim_source_input)
    locations = [
        str(record.get("source_location") or "not recorded")
        for record in records
    ]
    chunks = [
        "\\textbf{Source locator:} " + _tex_locator("; ".join(locations)),
        "\\paragraph{Verbatim source input}",
        _verbatim(verbatim_source_input),
    ]
    return "\n".join(chunks)


def _approved_corrected_target_tex(records: Iterable[Mapping[str, Any]]) -> str:
    """Render the reviewer-visible replacement for a false archival statement.

    The archival source bundle remains first on the page.  When its map row
    deliberately records a different, approved target, the reviewer must also
    see that target and the human-facing basis for it.  A digest alone would
    make the exceptional correction lane impossible to review.
    """

    corrected: list[Mapping[str, Any]] = []
    for record in records:
        target = record.get("corrected_target")
        if (
            str(record.get("coverage_status") or "").strip()
            == "corrected_source_statement"
            and isinstance(target, Mapping)
        ):
            corrected.append(target)
    if not corrected:
        return ""
    if len(corrected) != 1:
        return (
            "\\paragraph{Approved corrected review target}\\textbf{Error:} "
            "multiple corrected targets are routed to one source claim."
        )
    target = corrected[0]
    approval = target.get("approval")
    approval_reference = (
        str(approval.get("reference") or "").strip()
        if isinstance(approval, Mapping)
        else "not recorded"
    )
    archival_locator = str(target.get("archival_source_locator") or "not recorded")
    return "\n".join(
        [
            "\\paragraph{Approved corrected review target}",
            "The archival source above is not asserted equivalent to this replacement.",
            _verbatim(target.get("statement")),
            "\\textbf{Archival source anchor:} " + _tex_locator(archival_locator),
            "\\paragraph{Recorded basis}\n" + _tex_breakable_text(approval_reference),
        ]
    )


def _row_tex(
    item: Mapping[str, Any],
    records: Iterable[Mapping[str, Any]],
    proof_endpoint: str,
    row_number: int,
    *,
    presentation_section: str = "",
    presentation_section_anchor: str = "",
) -> str:
    verdict = str(item.get("llm_match_judgment") or "not recorded")
    reason = str(item.get("llm_match_reason") or "not recorded")
    correction_target = _approved_corrected_target_tex(records)
    reviewer_label = (
        "Matches approved corrected target"
        if correction_target
        else "Matches source input"
    )

    heading = (
        [
         "\\hypertarget{" + presentation_section_anchor + "}{}"
         if presentation_section_anchor
         else "",
         "\\section*{" + _tex_escape(presentation_section) + "}",
         "\\subsection*{Review row " + str(row_number) + "}"]
        if presentation_section
        else ["\\section*{Review row " + str(row_number) + "}"]
    )
    return "\n".join(
        [
            "\\clearpage",
            "\\hypertarget{"
            + _packet_anchor("source-claim", item.get("full_name") or item.get("name"))
            + "}{}",
            *heading,
            _record_source_blocks(
                records,
                item.get("verbatim_source_input") or item.get("paper_statement"),
            ),
            correction_target,
            "\\paragraph{Expanded PaperInterface specification}",
            _verbatim(
                item.get("semantic_expanded_statement")
                or item.get("lean_statement")
                or item.get("interface_source")
            ),
            "\\paragraph{Lean proof endpoint (built separately)}"
            + _verbatim(proof_endpoint)
            if proof_endpoint
            else "",
            "\\paragraph{Recorded source-to-Spec screening}",
            "\\textbf{Verdict:} \\texttt{" + _tex_escape(verdict) + "}",
            "\\\\\n\\textbf{Reason:} " + _tex_escape(reason),
            "\\reviewmatch{" + reviewer_label + "}",
            "\\noindent\\textbf{Reviewer annotation}\\par",
            "\\reviewerbox",
        ]
    )


def _claim_presentation_sections(
    status: Mapping[str, Any],
    rows: list[tuple[dict[str, Any], list[Mapping[str, Any]], str]],
) -> list[tuple[str, list[tuple[dict[str, Any], list[Mapping[str, Any]], str]]]]:
    """Group source cards for human reading without changing audit coverage.

    A paper can place appendix/supplement claims after main-text claims in its
    human review packet.  The group setting is presentation metadata only:
    every configured card remains in the same source-claim denominator, and
    material dependency cards are still shown before all source claims.
    """

    review_surface = status.get("review_surface")
    raw_sections = (
        review_surface.get("presentation_sections")
        if isinstance(review_surface, Mapping)
        else None
    )
    if raw_sections is None:
        return [("", rows)]
    if not isinstance(raw_sections, list) or not raw_sections:
        raise ValueError("review_surface.presentation_sections must be a nonempty list")

    lookup: dict[str, tuple[dict[str, Any], list[Mapping[str, Any]], str]] = {}
    for row in rows:
        item = row[0]
        full_name = str(item.get("full_name") or "").strip()
        short_name = _short_declaration_name(full_name)
        candidates = {full_name, short_name}
        if short_name.endswith("Spec"):
            candidates.add(short_name[: -len("Spec")])
        for candidate in candidates:
            if candidate:
                lookup[candidate] = row

    section_for_row: dict[str, str] = {}
    seen: set[str] = set()
    for raw in raw_sections:
        if not isinstance(raw, Mapping):
            raise ValueError("each presentation section must be an object")
        title = str(raw.get("title") or "").strip()
        names = raw.get("names")
        if (
            not title
            or not isinstance(names, list)
            or not names
            or not all(isinstance(name, str) and name.strip() for name in names)
        ):
            raise ValueError(
                "each presentation section needs a title and nonempty names"
            )
        for raw_name in names:
            name = str(raw_name).strip()
            row = lookup.get(name)
            if row is None:
                raise ValueError(
                    "presentation section references an unknown source card: " + name
                )
            full_name = str(row[0].get("full_name") or "").strip()
            if full_name in seen:
                raise ValueError(
                    "presentation sections repeat source card: " + name
                )
            seen.add(full_name)
            section_for_row[full_name] = title
    unassigned = [
        str(row[0].get("full_name") or "").strip()
        for row in rows
        if str(row[0].get("full_name") or "").strip() not in seen
    ]
    if unassigned:
        raise ValueError(
            "presentation sections must cover every source card; missing "
            + ", ".join(unassigned)
        )
    # `_claim_review_rows` has already read the approved intake's DAG
    # linearization.  Section metadata gives it headings only: it cannot move
    # a definition after a result which uses that definition.  A paper section
    # may therefore occur in more than one contiguous run when an earlier
    # prerequisite is needed by a claim in another paper section.
    grouped: list[
        tuple[str, list[tuple[dict[str, Any], list[Mapping[str, Any]], str]]]
    ] = []
    used_titles: dict[str, int] = {}
    for row in rows:
        full_name = str(row[0].get("full_name") or "").strip()
        configured_title = section_for_row[full_name]
        if grouped and grouped[-1][0].split(" (continued", 1)[0] == configured_title:
            grouped[-1][1].append(row)
            continue
        used_titles[configured_title] = used_titles.get(configured_title, 0) + 1
        occurrence = used_titles[configured_title]
        displayed_title = (
            configured_title
            if occurrence == 1
            else configured_title + " (continued" + ("" if occurrence == 2 else " " + str(occurrence - 1)) + ")"
        )
        grouped.append((displayed_title, [row]))
    return grouped


def _v11_packet_surface_error(
    status: Mapping[str, Any], source_map: Mapping[str, Any]
) -> str:
    """Return why an unmarked packet would misrepresent its review surface."""

    review_surface = status.get("review_surface")
    if not isinstance(review_surface, Mapping) or review_surface.get(
        "require_v11_raw_source_spec_screening"
    ) is not True:
        return "the paper has not explicitly activated the v11 raw-source-to-Spec review surface"
    if source_map.get("semantic_contract_schema") != 1:
        return "the source map has not prepared the v11 one-claim-to-one-Spec contract surface"
    return ""


def _review_readiness_notice(
    claim_rows: Iterable[Mapping[str, Any]],
    library_prerequisites: Iterable[Mapping[str, Any]],
) -> str:
    """Describe pending direct reviews once, before the packet cards.

    An activated v11 surface is enough to generate a human-review worksheet;
    it is not enough to imply that the current source-to-Spec and material
    library judgments have all been recorded.  Keep this summary in the front
    matter, rather than repeating a generic diagnostic disclaimer on each
    page.  Individual cards still expose their own recorded verdict.
    """

    categories = (
        ("source-claim screens", list(claim_rows), "llm_match_current"),
        ("library prerequisite screens", list(library_prerequisites), "semantic_current"),
    )
    pending = [
        f"{sum(bool(row.get(field)) for row in rows)}/{len(rows)} {label}"
        for label, rows, field in categories
        if rows and not all(bool(row.get(field)) for row in rows)
    ]
    if not pending:
        return ""
    return (
        "\\noindent\\fbox{\\parbox{0.96\\linewidth}{\\textbf{Review status:} "
        + _tex_escape("; ".join(pending))
        + ". This is a review worksheet while those direct checks remain pending; "
        "it is not a final validation receipt.}}\\par"
    )


def _contents_tex(
    paper_dir: Path,
    claim_sections: Iterable[
        tuple[str, list[tuple[dict[str, Any], list[Mapping[str, Any]], str]]]
    ],
    library_prerequisites: Iterable[Mapping[str, Any]],
) -> str:
    """Render a compact linked contents list for the packet's review order."""

    library_entries = _dependency_first_entries(
        library_prerequisites,
        name_field="lean_name",
        dependency_field="direct_library_declarations",
        normalize_dependency=review_dashboard.library_review_owner_declaration,
    )
    rendered = ["\\section*{Contents}", "\\begin{itemize}[leftmargin=1.2em]"]
    if library_entries:
        rendered.extend(
            [
                "\\item \\hyperlink{"
                + _packet_anchor("library-section", paper_dir.name)
                + "}{Semantic library prerequisites ("
                + str(len(library_entries))
                + "; not paper claims)}",
                "\\begin{itemize}[leftmargin=1.2em]",
            ]
        )
        for entry in library_entries:
            name = str(entry.get("label") or entry.get("lean_name") or "Library prerequisite")
            rendered.append(
                "\\item \\hyperlink{"
                + _packet_anchor("library-prerequisite", entry.get("lean_name"))
                + "}{"
                + _tex_escape(name)
                + "}"
            )
        rendered.append("\\end{itemize}")
    for raw_title, section_rows in claim_sections:
        title = raw_title or "Source claims"
        rendered.extend(
            [
                "\\item \\hyperlink{"
                + _packet_anchor("source-section", title)
                + "}{"
                + _tex_escape(title)
                + " ("
                + str(len(section_rows))
                + ")}",
                "\\begin{itemize}[leftmargin=1.2em]",
            ]
        )
        for item, records, _proof_endpoint in section_rows:
            record = records[0] if records else {}
            name = str(
                record.get("source_item")
                or record.get("title")
                or item.get("name")
                or "Source claim"
            )
            rendered.append(
                "\\item \\hyperlink{"
                + _packet_anchor(
                    "source-claim", item.get("full_name") or item.get("name")
                )
                + "}{"
                + _tex_escape(name)
                + "}"
            )
        rendered.append("\\end{itemize}")
    rendered.append("\\end{itemize}")
    return "\n".join(rendered)


def render_packet(
    paper: str,
    *,
    allow_draft: bool = False,
) -> str:
    """Return deterministic TeX for one current dashboard review surface."""

    paper_dir = ROOT / "papers" / paper
    if not paper_dir.is_dir():
        raise ValueError(f"unknown paper: {paper}")
    source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
    status = _read_json(paper_dir / "status.json")
    surface_error = _v11_packet_surface_error(status, source_map)
    if surface_error and not allow_draft:
        raise ValueError(
            "refusing to produce an unmarked human-review packet: "
            + surface_error
            + ". Complete the v11 preparation first, or pass --draft for a visibly incomplete diagnostic."
        )
    interface_items = _paperinterface_items(paper_dir)
    claim_rows = _claim_review_rows(paper_dir, source_map, interface_items)
    specifications = [
        str(item.get("full_name") or "") for item, _records, _proof in claim_rows
    ]
    packet_cache = _current_packet_lean_cache(paper_dir, specifications)
    if packet_cache is None:
        raise ValueError(
            "packet Lean displays are not cached for this exact paper Lean surface; "
            "run --prepare-lean-cache --stage specifications, then "
            "--stage paper-prerequisites, then --stage library"
        )
    semantic_targets = {
        str(name): dict(target)
        for name, target in packet_cache["semantic_targets"].items()
        if isinstance(target, Mapping)
    }
    if set(semantic_targets) != {name for name in specifications if name}:
        raise ValueError(
            "packet Lean-cache lacks a complete semantic Spec display set; "
            "rerun --prepare-lean-cache --stage specifications"
        )
    paper_prerequisite_targets = {
        str(name): dict(target)
        for name, target in packet_cache["paper_prerequisite_targets"].items()
        if isinstance(target, Mapping)
    }
    library_semantic_targets = {
        str(name): dict(target)
        for name, target in packet_cache["library_semantic_targets"].items()
        if isinstance(target, Mapping)
    }
    library_semantic_target_errors = {
        str(name): str(error)
        for name, error in packet_cache["library_semantic_target_errors"].items()
        if str(name).strip() and str(error).strip()
    }
    screenings = _v11_screening_rows(
        paper_dir, source_map, interface_items, semantic_targets
    )
    prepared_rows: list[tuple[dict[str, Any], list[Mapping[str, Any]], str]] = []
    for item, records, proof_endpoint in claim_rows:
        prepared = dict(item)
        target = semantic_targets.get(str(item.get("full_name") or ""), {})
        prepared["semantic_expanded_statement"] = str(target.get("display") or "")
        prepared["library_review_owner_declarations"] = list(
            target.get("library_declarations", ())
        )
        primary_record = records[0] if records else None
        if primary_record is not None:
            source_text, _source_digest, source_error = (
                review_dashboard.source_semantic_input_bundle(
                    primary_record, require_context_roles=True
                )
            )
            if not source_error:
                prepared["verbatim_source_input"] = source_text
            prepared["source_status"] = str(
                primary_record.get("source_status") or "not recorded"
            )
        screening = screenings.get(str(item.get("full_name") or ""), {})
        prepared.update(
            {
                "llm_match_judgment": screening.get("judgment", "not recorded"),
                "llm_match_reason": screening.get("reason", "not recorded"),
                "llm_match_validator": screening.get("validator", "not recorded"),
                "llm_match_validated_at": screening.get("validated_at", "not recorded"),
                "llm_match_current": bool(screening.get("current")),
            }
        )
        prepared_rows.append((prepared, records, proof_endpoint))
    rows: list[str] = []
    row_number = 0
    claim_sections = _claim_presentation_sections(status, prepared_rows)
    for section_title, section_rows in claim_sections:
        display_section_title = section_title or "Source claims"
        for section_index, (item, records, proof_endpoint) in enumerate(section_rows):
            row_number += 1
            rows.append(
                _row_tex(
                    item,
                    records,
                    proof_endpoint,
                    row_number,
                    presentation_section=(
                        display_section_title if section_index == 0 else ""
                    ),
                    presentation_section_anchor=(
                        _packet_anchor("source-section", display_section_title)
                        if section_index == 0
                        else ""
                    ),
                )
            )
    if not rows:
        raise ValueError(f"{paper} has no dashboard review rows")
    paper_prerequisites = paper_semantic_prerequisites(
        paper_dir,
        semantic_targets,
        semantic_targets_by_name_override=paper_prerequisite_targets,
    )
    library_review_inputs: list[Mapping[str, Any]] = [
        item for item, _records, _proof in prepared_rows
    ]
    library_review_inputs.extend(
        {
            "library_review_owner_declarations": prerequisite.get(
                "direct_library_declarations", ()
            )
        }
        for prerequisite in paper_prerequisites
    )
    library_prerequisites = review_dashboard.human_review_library_prerequisites(
        paper_dir,
        library_review_inputs,
        semantic_targets_override=library_semantic_targets,
        semantic_target_errors_override=library_semantic_target_errors,
    )
    template = TEMPLATE_PATH.read_text(encoding="utf-8")
    source_version = str(source_map.get("source_version") or "not recorded")
    source_url = str(source_map.get("source_url") or "")
    metadata = [
        "\\noindent\\textbf{Paper:} " + _tex_escape(paper) + "\\\\",
        "\\textbf{Paper id:} \\texttt{" + _tex_escape(paper) + "}\\\\",
        "\\textbf{Source version:} " + _tex_escape(source_version) + "\\\\",
        "\\textbf{Source record:} \\texttt{" + _tex_escape(SOURCE_MAP_NAME) + "}\\\\",
        "\\textbf{Rows:} " + str(len(rows)) + "\\\\",
        "\\textbf{Generated:} " + dt.date.today().isoformat()
        + ("\\\\" if source_url else ""),
    ]
    if source_url:
        primary_source_url = source_url.split(";", maxsplit=1)[0].strip()
        # The exact URL is a convenience link, not review evidence (the map's
        # byte-pinned anchors are).  Keep it compact enough that it cannot
        # create an overfull header in packets with an archival and TeX URL.
        metadata.append(
            "\\textbf{Source URL:} "
            + "\\href{"
            + primary_source_url.replace("%", r"\%")
            + "}{official source}"
        )
    draft_notice = (
        "\\noindent\\fbox{\\parbox{0.96\\linewidth}{\\textbf{Draft diagnostic only.} "
        + _tex_escape(surface_error)
        + ". This is not a complete v11 human-review packet or a closeout artifact.}}\\par"
        if surface_error
        else ""
    )
    review_readiness_notice = _review_readiness_notice(
        [item for item, _records, _proof in prepared_rows],
        library_prerequisites,
    )
    return (
        template.replace("@@PAPER_TITLE@@", _tex_escape(paper))
        .replace("@@PAPER_ID@@", _tex_escape(paper))
        .replace("@@METADATA@@", "\n".join(metadata))
        .replace("@@REVIEW_STATUS_NOTICE@@", review_readiness_notice)
        .replace("@@DRAFT_NOTICE@@", draft_notice)
        .replace(
            "@@CONTENTS@@",
            _contents_tex(
                paper_dir,
                claim_sections,
                library_prerequisites,
            ),
        )
        .replace(
            "@@PREREQUISITES@@",
            "\\clearpage\n".join(
                part
                for part in (
                    _prerequisites_tex(
                        paper_dir,
                        library_review_inputs,
                        semantic_targets_override=library_semantic_targets,
                        semantic_target_errors_override=library_semantic_target_errors,
                        entries_override=library_prerequisites,
                    ),
                )
                if part
            ),
        )
        .replace("@@ROWS@@", "\n".join(rows))
    )


def _resolve_output_dir(
    paper: str, raw_output: str
) -> Path:
    paper_dir = (ROOT / "papers" / paper).resolve()
    output_dir = Path(raw_output) if raw_output else paper_dir / "docs"
    if not output_dir.is_absolute():
        output_dir = (ROOT / output_dir).resolve()
    try:
        relative = output_dir.relative_to(paper_dir)
    except ValueError as exc:
        raise ValueError("--out-dir must remain inside the paper folder") from exc
    return output_dir


def _compile(tex_path: Path) -> None:
    completed = subprocess.run(
        [
            "latexmk",
            "-xelatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            tex_path.name,
        ],
        cwd=tex_path.parent,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(f"LaTeX compilation failed for {tex_path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder id")
    parser.add_argument(
        "--out-dir",
        default="",
        help="paper-local output directory (default: papers/<paper>/docs)",
    )
    parser.add_argument("--write", action="store_true", help="write the TeX packet")
    parser.add_argument("--compile", action="store_true", help="compile the written packet to PDF")
    parser.add_argument(
        "--prepare-lean-cache",
        action="store_true",
        help="prepare one bounded Lean-display stage for a later packet render",
    )
    parser.add_argument(
        "--stage",
        choices=("specifications", "paper-prerequisites", "library"),
        default="specifications",
        help="Lean-cache stage used with --prepare-lean-cache",
    )
    parser.add_argument(
        "--draft",
        action="store_true",
        help="allow a visibly incomplete diagnostic when v11 preparation is not active",
    )
    args = parser.parse_args()
    if args.compile and not args.write:
        parser.error("--compile requires --write")
    if args.prepare_lean_cache and (args.write or args.compile):
        parser.error("--prepare-lean-cache does not write or compile a packet")
    try:
        if args.prepare_lean_cache:
            print(prepare_packet_lean_cache(args.paper, stage=args.stage))
            return 0
        rendered = render_packet(args.paper, allow_draft=args.draft)
        if not args.write:
            print(rendered)
            return 0
        output_dir = _resolve_output_dir(
            args.paper,
            args.out_dir,
        )
        output_dir.mkdir(parents=True, exist_ok=True)
        tex_path = output_dir / f"{PACKET_NAME}.tex"
        tex_path.write_text(rendered, encoding="utf-8")
        print(f"wrote {tex_path.relative_to(ROOT)}")
        if args.compile:
            _compile(tex_path)
            print(f"wrote {tex_path.with_suffix('.pdf').relative_to(ROOT)}")
    except (OSError, RuntimeError, ValueError) as exc:
        print(f"review-dashboard-packet: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
