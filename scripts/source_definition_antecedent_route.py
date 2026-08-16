#!/usr/bin/env python3
"""Archived diagnostic for historical source-definition route artifacts.

This module is not imported by the canonical repository or conclusion audits,
and its output cannot grant source-record or conclusion credit. It is retained
only to inspect and migrate existing private artifacts while the general Lean
dependency-graph audit supersedes the old transport.

This is a deliberately narrow transport for a conclusion/input obligation that
is an expansion of a source definition used by a source theorem or lemma.  It
does not infer that relation from a Lean predicate, theorem, binder, or map
key.  Instead it requires all of the following current evidence:

* the generated raw input's fully expanded proposition and complete raw-member
  pin set;
* the direct source-result association and elaborated signature for the
  source theorem/lemma containing that input;
* a current v10 statement-match record for that source result and its input
  atom;
* a current v10 direct source-definition statement-match record whose exact
  IFF expansion has the same expanded proposition; and
* byte-checked source anchors for both the definition and the source result.

The output receipt is semantic and name-independent: identifiers remain only
as provenance/navigation data after the source content, formulas, signatures,
and associations have selected a unique route.  A materialization updates one
existing ordinary ``source_record_match_llm`` entry only.  It deliberately
does not restamp the sidecar root, so stale sibling judgments cannot inherit
current aggregate freshness.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package-style focused tests.
    from scripts.lean_signature_manifest import (
        HELPER_PATH as SIGNATURE_MANIFEST_HELPER_PATH,
        parse_signature_manifest_output,
    )
    from scripts.review_dashboard import signature_manifest_atom_digest
    from scripts.source_coverage_scope import source_item_coverage_sha256
    from scripts.source_record_differential_revalidation import _raw_item_groups
    from scripts.source_record_integrity import canonical_digest_payload
    from scripts.source_record_target_disposition import (
        project_source_record_response_association_pins,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from lean_signature_manifest import (
        HELPER_PATH as SIGNATURE_MANIFEST_HELPER_PATH,
        parse_signature_manifest_output,
    )
    from review_dashboard import signature_manifest_atom_digest
    from source_coverage_scope import source_item_coverage_sha256
    from source_record_differential_revalidation import _raw_item_groups
    from source_record_integrity import canonical_digest_payload
    from source_record_target_disposition import (
        project_source_record_response_association_pins,
    )


SCHEMA = 3
ARTIFACT_KIND = "source_definition_antecedent_route"
POLICY_VERSION = "source-definition-antecedent-route-v3-coherent-telescope-overlay"
RECEIPT_FILENAME = "source_definition_antecedent_route.json"
MATERIALIZATION_FIELD = "source_definition_antecedent_route"
MATERIALIZATION_SCHEMA = 3
SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
SOURCE_RECORD_ITEM_DIGEST_SCHEMA = 5
SOURCE_RESULT_KINDS = frozenset({"theorem", "lemma", "corollary", "proposition"})
LEAN_BRIDGE_TIMEOUT_SECONDS = 45
LEAN_INTERFACE_BUILD_TIMEOUT_SECONDS = 180
LEAN_META_HELPER_PATH = ROOT / "scripts" / "source_definition_antecedent_meta_helper.lean"
LEAN_META_BRIDGE_SENTINEL = "SOURCE_DEFINITION_ANTECEDENT_META:"
LEAN_META_BRIDGE_SCHEMA = 3
# This changes only when the Lean semantic interpretation of the bridge
# changes. It invalidates historical route evidence; fresh overlays are always
# required for current acceptance.
LEAN_META_BRIDGE_POLICY_VERSION = "parsed-semantic-formula-bridge-v2-coherent-telescope-map"
# This identifies the persisted evidence format. It is not a cache protocol:
# prior bridge output is provenance only until a hermetic module closure exists.
LEAN_META_BRIDGE_PROTOCOL_VERSION = "fresh-semantic-overlay-result-v1"
LEAN_META_BRIDGE_SEAL_SCHEMA = 1
LEAN_META_BRIDGE_METHOD = (
    "lean_meta_coherent_telescope_formula_bridge_and_signature_atoms_"
    "current_paper_interface_source_overlay"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LOCATION_RE = re.compile(r"^(?P<path>[^:]+):(?P<start>[1-9][0-9]*)-(?P<end>[1-9][0-9]*)$")
_QUALIFIED_LEAN_HEAD_RE = re.compile(
    r"^(?P<head>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)(?P<tail>(?:\s+.*)?)$"
)
_LEAN_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*)\s*(?:--.*)?$")
_LEAN_CHECKER_IDENTITY_CACHE: tuple[tuple[tuple[str, str], ...], dict[str, Any]] | None = None


class SourceDefinitionAntecedentRouteError(ValueError):
    """Raised when no exact, independently pinned definition route exists."""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    return candidate if _SHA256_RE.fullmatch(candidate) else ""


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _normalized_text(value: object) -> str:
    return re.sub(r"\s+", " ", str(value or "").strip())


def _statement_digest(value: object) -> str:
    return _sha256_text(_normalized_text(value))


def _formula(value: object) -> str:
    # Formula bytes are semantic input to Lean.  In particular, whitespace in
    # a string literal is not formatting, so never collapse internal
    # whitespace before pinning or elaborating it.  Outer trimming merely
    # removes transport indentation around the serialized field.
    text = str(value or "").strip()
    if not text:
        raise SourceDefinitionAntecedentRouteError(
            "an expanded proposition is missing or empty"
        )
    return text


def _formula_digest(value: object) -> str:
    return _sha256_text(_formula(value))


def _formula_equal(left: object, right: object) -> bool:
    return _formula(left) == _formula(right)


def _has_one_top_level_iff_shape(value: object) -> bool:
    """Cheap, non-accepting shape gate before an expensive Lean overlay.

    This only avoids running a source-overlay command for a review entry that
    cannot even present an outer IFF. It never selects a side, compares a
    formula, or contributes to acceptance; the schema-2 Lean helper later
    parses and elaborates the complete expression and is the sole authority.
    """

    text = _formula(value)
    depth = 0
    iff_count = 0
    for index, character in enumerate(text):
        if character in "([{⦃":
            depth += 1
        elif character in ")]}⦄":
            # A malformed expression cannot establish a source-definition route.
            if depth <= 0:
                raise SourceDefinitionAntecedentRouteError(
                    "definition IFF surface has unbalanced delimiters"
                )
            depth -= 1
        elif character == "↔" and depth == 0:
            iff_count += 1
    return depth == 0 and iff_count == 1


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceDefinitionAntecedentRouteError(f"{label} at {path} is not an object")
    return payload


def _safe_paper_path(paper_dir: Path, value: object, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceDefinitionAntecedentRouteError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    try:
        path.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"{label} escapes the paper directory"
        ) from exc
    return path


def _paper_relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
        mode="w",
        encoding="utf-8",
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _lean_overlay_temp_dir() -> Path:
    """Return an ignored runtime directory for short-lived Lean overlays.

    A cancelled audit must not leave a generated Lean source at the repository
    root, where it can look like a real paper artifact.  Respect an explicit
    ``TMPDIR`` for hermetic runners; otherwise use the repository's ignored
    runtime directory while retaining the project root as Lean's working
    directory for import resolution.
    """

    configured = os.environ.get("TMPDIR")
    directory = Path(configured) if configured else ROOT / ".scratch" / "runtime-tmp"
    if not directory.is_absolute():
        directory = ROOT / directory
    try:
        directory.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not create Lean overlay runtime directory {directory}: {exc}"
        ) from exc
    return directory


def _parse_location(value: object, *, label: str) -> tuple[str, int, int]:
    text = str(value or "").strip()
    match = _LOCATION_RE.fullmatch(text)
    if match is None:
        raise SourceDefinitionAntecedentRouteError(
            f"{label} must be an exact `path:start-end` source locator"
        )
    start = int(match.group("start"))
    end = int(match.group("end"))
    if end < start:
        raise SourceDefinitionAntecedentRouteError(f"{label} has an inverted line range")
    return match.group("path"), start, end


def _anchor_from_mapping(
    value: object,
    *,
    paper_dir: Path,
    source_artifact_sha256: str,
    label: str,
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise SourceDefinitionAntecedentRouteError(f"{label} is not an object")
    path_text = str(value.get("path") or "").strip()
    start = value.get("line_start")
    end = value.get("line_end")
    quote = value.get("quoted_text")
    quote_sha = _sha256(value.get("quoted_text_sha256"))
    if (
        not path_text
        or not isinstance(start, int)
        or isinstance(start, bool)
        or not isinstance(end, int)
        or isinstance(end, bool)
        or start < 1
        or end < start
        or not isinstance(quote, str)
        or not quote_sha
    ):
        raise SourceDefinitionAntecedentRouteError(f"{label} is malformed")
    path = _safe_paper_path(paper_dir, path_text, label=f"{label}.path")
    try:
        contents = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read {label} source artifact: {exc}"
        ) from exc
    # ``str.split('\n')`` deliberately preserves form-feed characters present in
    # text extractions, unlike ``splitlines``.
    lines = contents.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    if end > len(lines):
        raise SourceDefinitionAntecedentRouteError(f"{label} line range is outside source")
    observed = "\n".join(lines[start - 1 : end])
    if observed != quote or _sha256_text(quote) != quote_sha:
        raise SourceDefinitionAntecedentRouteError(
            f"{label} quoted source bytes do not match the current source artifact"
        )
    return {
        "path": _paper_relative_path(path, paper_dir),
        "line_start": start,
        "line_end": end,
        "quoted_text_sha256": quote_sha,
        "source_artifact_sha256": source_artifact_sha256,
    }


def _source_artifact_context(
    statement_map: Mapping[str, Any], *, paper_dir: Path
) -> tuple[str, str]:
    path_text = str(statement_map.get("source_artifact_path") or "").strip()
    expected_sha = _sha256(statement_map.get("source_artifact_sha256"))
    if not path_text or not expected_sha:
        raise SourceDefinitionAntecedentRouteError(
            "statement map has no pinned source artifact path and digest"
        )
    path = _safe_paper_path(paper_dir, path_text, label="source_artifact_path")
    try:
        actual_sha = hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read source artifact at {path}: {exc}"
        ) from exc
    if actual_sha != expected_sha:
        raise SourceDefinitionAntecedentRouteError(
            "current source artifact bytes do not match the statement-map pin"
        )
    return _paper_relative_path(path, paper_dir), expected_sha


def _root_relative_path(path: Path, *, label: str) -> str:
    """Return a repository-stable path for an environment pin."""

    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"{label} must remain inside the private repository"
        ) from exc


def _sha256_file(path: Path, *, label: str) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read {label} at {path}: {exc}"
        ) from exc


def _lean_import_modules(interface_text: str) -> list[str]:
    """Extract the source overlay's direct imports for provenance diagnostics.

    The overlay elaborates the current ``PaperInterface.lean`` source itself.
    Their source and olean pins make a receipt inspectable, but are not a
    complete transitive elaboration-closure fingerprint and therefore never
    authorize cache reuse.
    """

    modules: list[str] = []
    seen: set[str] = set()
    for line in interface_text.splitlines():
        match = _LEAN_IMPORT_RE.fullmatch(line)
        if match is None:
            continue
        for module in match.group(1).split():
            if module not in seen:
                modules.append(module)
                seen.add(module)
    if not modules:
        raise SourceDefinitionAntecedentRouteError(
            "PaperInterface source overlay has no direct imports"
        )
    return modules


def _module_source_path(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    candidates = [ROOT / relative, ROOT / "papers" / relative]
    packages = ROOT / ".lake" / "packages"
    if packages.is_dir():
        candidates.extend(
            child / relative
            for child in sorted(packages.iterdir(), key=lambda entry: entry.name)
            if child.is_dir()
        )
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def _module_olean_path(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".olean")
    candidates = [ROOT / ".lake" / "build" / "lib" / "lean" / relative]
    packages = ROOT / ".lake" / "packages"
    if packages.is_dir():
        candidates.extend(
            child / ".lake" / "build" / "lib" / "lean" / relative
            for child in sorted(packages.iterdir(), key=lambda entry: entry.name)
            if child.is_dir()
        )
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def _lean_checker_identity() -> dict[str, Any]:
    """Pin the actual Lake/Lean command that checks the source overlay."""

    global _LEAN_CHECKER_IDENTITY_CACHE
    file_pins: list[dict[str, str]] = []
    for relative in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = ROOT / relative
        if not path.is_file():
            raise SourceDefinitionAntecedentRouteError(
                f"Lean checker identity input is missing: {relative}"
            )
        file_pins.append(
            {
                "path": relative,
                "sha256": _sha256_file(path, label="Lean checker identity input"),
            }
        )
    cache_key = tuple((pin["path"], pin["sha256"]) for pin in file_pins)
    if (
        _LEAN_CHECKER_IDENTITY_CACHE is not None
        and _LEAN_CHECKER_IDENTITY_CACHE[0] == cache_key
    ):
        return copy.deepcopy(_LEAN_CHECKER_IDENTITY_CACHE[1])
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--version"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=LEAN_BRIDGE_TIMEOUT_SECONDS,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not identify the Lean checker: {exc}"
        ) from exc
    if completed.returncode != 0:
        raise SourceDefinitionAntecedentRouteError(
            "could not identify the Lean checker: `lake env lean --version` failed"
        )
    identity = {
        "schema": 1,
        "command": ["lake", "env", "lean", "--version"],
        "stdout_sha256": _sha256_text(completed.stdout),
        "stderr_sha256": _sha256_text(completed.stderr),
        "identity_file_pins": file_pins,
    }
    _LEAN_CHECKER_IDENTITY_CACHE = (cache_key, identity)
    return copy.deepcopy(identity)


def _source_overlay_environment(
    *, paper: str, paper_dir: Path
) -> tuple[Path, str, dict[str, Any]]:
    """Return the current source-overlay checker environment and its pins.

    ``PaperInterface.lean`` is intentionally elaborated from source in the
    temporary checker input.  The pre-existing interface olean remains pinned
    only as a current build artifact diagnostic; it is never substituted for
    that source elaboration.
    """

    interface_path = _safe_paper_path(
        paper_dir, "PaperInterface.lean", label="PaperInterface source overlay path"
    )
    interface_sha = _sha256_file(interface_path, label="PaperInterface source overlay")
    try:
        interface_text = interface_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read PaperInterface source overlay: {exc}"
        ) from exc
    helper_sha = _sha256_file(LEAN_META_HELPER_PATH, label="focused Lean Meta helper")
    manifest_helper_sha = _sha256_file(
        SIGNATURE_MANIFEST_HELPER_PATH, label="focused Lean signature-manifest helper"
    )
    imports: list[dict[str, Any]] = []
    for module in _lean_import_modules(interface_text):
        source_path = _module_source_path(module)
        olean_path = _module_olean_path(module)
        if olean_path is None:
            raise SourceDefinitionAntecedentRouteError(
                f"source-overlay import `{module}` has no current olean artifact"
            )
        entry: dict[str, Any] = {
            "module": module,
            "olean_path": _root_relative_path(
                olean_path, label="source-overlay import olean"
            ),
            "olean_sha256": _sha256_file(
                olean_path, label="source-overlay import olean"
            ),
        }
        if source_path is not None:
            entry["source_path"] = _root_relative_path(
                source_path, label="source-overlay import source"
            )
            entry["source_sha256"] = _sha256_file(
                source_path, label="source-overlay import source"
            )
        imports.append(entry)
    interface_module = f"{paper}.PaperInterface"
    interface_olean = _module_olean_path(interface_module)
    if interface_olean is None:
        raise SourceDefinitionAntecedentRouteError(
            "PaperInterface has no current build artifact for source-overlay diagnostics"
        )
    environment = {
        "schema": 1,
        "mode": "source_overlay_current_paper_interface_v1",
        "interface": {
            "paper_relative_path": _paper_relative_path(interface_path, paper_dir),
            "sha256": interface_sha,
            "module": interface_module,
            "current_olean_path": _root_relative_path(
                interface_olean, label="PaperInterface build artifact"
            ),
            "current_olean_sha256": _sha256_file(
                interface_olean, label="PaperInterface build artifact"
            ),
        },
        "direct_import_closure": imports,
        "focused_meta_helper": {
            "path": _root_relative_path(LEAN_META_HELPER_PATH, label="focused Lean Meta helper"),
            "sha256": helper_sha,
        },
        "signature_manifest_helper": {
            "path": _root_relative_path(
                SIGNATURE_MANIFEST_HELPER_PATH,
                label="focused Lean signature-manifest helper",
            ),
            "sha256": manifest_helper_sha,
        },
        "checker": _lean_checker_identity(),
    }
    return interface_path, interface_text, environment


def _fresh_paper_interface_build(paper: str) -> dict[str, Any]:
    """Build exactly the reviewed paper interface before its source overlay.

    The source overlay deliberately elaborates ``PaperInterface.lean`` from
    current text, but its imports are compiled artifacts.  A module-scoped
    Lake build refreshes that dependency closure without invoking a repository
    build or regenerating any raw-audit surface.
    """

    interface_module = _qualified_declaration_coordinate(
        f"{paper}.PaperInterface", label="PaperInterface build module"
    )
    try:
        completed = subprocess.run(
            ["lake", "build", interface_module],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=LEAN_INTERFACE_BUILD_TIMEOUT_SECONDS,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"paper-local PaperInterface build could not run: {exc}"
        ) from exc
    if completed.returncode != 0:
        diagnostic_lines = [
            line.strip()
            for line in (completed.stderr + "\n" + completed.stdout).splitlines()
            if "error:" in line.lower() or "failed" in line.lower()
        ]
        diagnostic = _normalized_text(
            " | ".join(diagnostic_lines[-4:])
            or completed.stderr
            or completed.stdout
        )
        raise SourceDefinitionAntecedentRouteError(
            "paper-local PaperInterface build failed"
            + (f": {diagnostic[:500]}" if diagnostic else "")
        )
    return {
        "schema": 1,
        "command": ["lake", "build", interface_module],
        # Lake's ordinary progress output can include nondeterministic timing
        # and temporary paths. The post-build source/olean pins are
        # reproducible provenance; the successful module command records how
        # the fresh overlay environment was obtained.
        "succeeded": True,
    }


def _qualified_declaration_coordinate(value: object, *, label: str) -> str:
    declaration = str(value or "").strip()
    match = _QUALIFIED_LEAN_HEAD_RE.fullmatch(declaration)
    if match is None or match.group("tail"):
        raise SourceDefinitionAntecedentRouteError(
            f"{label} is not a fully qualified Lean declaration coordinate"
        )
    return declaration


def _meta_verdict_from_output(
    payload: object,
    *,
    lemma_declaration: str,
    lemma_binder_index: int,
    definition_declaration: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
) -> dict[str, Any]:
    """Validate the focused helper's semantic source-overlay verdict.

    Lean parses the raw expansion only under the lemma telescope and the
    reviewed IFF only under the definition telescope. It must then establish
    one type-checked outer-binder coordinate bijection and compare every
    transported expression in the lemma context. Python supplies exact text
    only as source-review evidence; it never splits an IFF, matches variable
    names, or chooses a formula side.
    """

    if not isinstance(payload, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta helper did not emit an object verdict"
        )
    if str(payload.get("schema") or "") != str(LEAN_META_BRIDGE_SCHEMA):
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta helper emitted an unsupported verdict schema"
        )
    if (
        str(payload.get("lemma") or "") != lemma_declaration
        or str(payload.get("definition") or "") != definition_declaration
        or str(payload.get("lemma_binder_index") or "") != str(lemma_binder_index)
    ):
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta helper verdict coordinates do not match the current route"
        )
    formula_side = str(payload.get("review_formula_iff_side") or "").strip()
    if (
        payload.get("iff_is_syntactic") is not True
        or payload.get("raw_expansion_matches_lemma_binder") is not True
        or payload.get("review_surface_is_syntactic_iff") is not True
        or payload.get("review_surface_matches_actual_iff") is not True
        or formula_side not in {"left", "right"}
        or str(payload.get("review_formula_selection_method") or "")
        != "syntactic_alpha_under_unique_coordinate_bijection"
        or payload.get("review_formula_side_matches_actual") is not True
        or payload.get("opposite_actual_endpoint_matches_lemma_binder") is not True
        or payload.get("parameter_correspondence_established") is not True
        or str(payload.get("parameter_correspondence_method") or "")
        != "unique_type_checked_coordinate_bijection"
        or str(payload.get("failure_tag") or "")
    ):
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta helper did not establish the semantic IFF endpoint bridge"
        )
    # Alpha-normalized expression evidence is emitted by Lean. Python only
    # pins its hashes; it never compares an endpoint's pretty-printed text or
    # uses declaration/predicate spellings to choose the formula side.
    alpha_fields = (
        "parsed_raw_expansion_alpha",
        "review_left_iff_side_alpha",
        "review_right_iff_side_alpha",
        "actual_left_iff_side_alpha",
        "actual_right_iff_side_alpha",
    )
    alpha: dict[str, str] = {}
    for field in alpha_fields:
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise SourceDefinitionAntecedentRouteError(
                f"focused Lean Meta helper omitted `{field}`"
            )
        alpha[field] = value
    raw_correspondence = payload.get("parameter_correspondence")
    if not isinstance(raw_correspondence, list):
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta helper omitted its parameter correspondence"
        )
    correspondence: list[dict[str, int]] = []
    seen_definition_indices: set[int] = set()
    seen_lemma_indices: set[int] = set()
    for raw_pair in raw_correspondence:
        if not isinstance(raw_pair, Mapping):
            raise SourceDefinitionAntecedentRouteError(
                "focused Lean Meta helper emitted a malformed parameter correspondence"
            )
        try:
            definition_index = int(str(raw_pair.get("definition_binder_index")))
            lemma_index = int(str(raw_pair.get("lemma_binder_index")))
        except (TypeError, ValueError) as exc:
            raise SourceDefinitionAntecedentRouteError(
                "focused Lean Meta helper emitted a non-numeric parameter coordinate"
            ) from exc
        if (
            definition_index < 0
            or lemma_index < 0
            or definition_index in seen_definition_indices
            or lemma_index in seen_lemma_indices
        ):
            raise SourceDefinitionAntecedentRouteError(
                "focused Lean Meta helper emitted a non-bijective parameter correspondence"
            )
        seen_definition_indices.add(definition_index)
        seen_lemma_indices.add(lemma_index)
        correspondence.append(
            {
                "definition_binder_index": definition_index,
                "lemma_binder_index": lemma_index,
            }
        )
    result: dict[str, Any] = {
        "schema": LEAN_META_BRIDGE_SCHEMA,
        "lemma": lemma_declaration,
        "definition": definition_declaration,
        "lemma_binder_index": lemma_binder_index,
        "raw_expanded_proposition_sha256": _formula_digest(raw_expanded_proposition),
        "review_surface_expression_sha256": _formula_digest(review_surface_expression),
        "review_formula_iff_side": formula_side,
        "raw_expansion_matches_lemma_binder": True,
        "review_surface_is_syntactic_iff": True,
        "review_surface_matches_actual_iff": True,
        "review_formula_selection_method": (
            "syntactic_alpha_under_unique_coordinate_bijection"
        ),
        "review_formula_side_matches_actual": True,
        "opposite_actual_endpoint_matches_lemma_binder": True,
        "parameter_correspondence_method": (
            "unique_type_checked_coordinate_bijection"
        ),
        "parameter_correspondence": correspondence,
        "parameter_correspondence_sha256": _canonical_digest(correspondence),
        "parsed_raw_expansion_alpha_sha256": _sha256_text(
            alpha["parsed_raw_expansion_alpha"]
        ),
        "review_left_iff_side_alpha_sha256": _sha256_text(
            alpha["review_left_iff_side_alpha"]
        ),
        "review_right_iff_side_alpha_sha256": _sha256_text(
            alpha["review_right_iff_side_alpha"]
        ),
        "actual_left_iff_side_alpha_sha256": _sha256_text(
            alpha["actual_left_iff_side_alpha"]
        ),
        "actual_right_iff_side_alpha_sha256": _sha256_text(
            alpha["actual_right_iff_side_alpha"]
        ),
        # Pretty-printer output is a non-authoritative diagnostic only.
        "lemma_binder_display_sha256": _sha256_text(
            str(payload.get("lemma_binder_type") or "")
        ),
    }
    definition_iff_display = payload.get("definition_iff_display")
    if isinstance(definition_iff_display, str) and definition_iff_display.strip():
        result["definition_iff_display_sha256"] = _sha256_text(
            definition_iff_display
        )
    return result


def _manifest_atom_from_current_overlay(
    manifests: Mapping[str, Any],
    *,
    declaration: str,
    ref: str,
    expected_manifest_sha256: str,
    expected_atom_sha256: str,
    expected_role: str,
    label: str,
) -> dict[str, str]:
    """Require a current Lean manifest to reproduce one pinned v10 atom."""

    manifest = manifests.get(declaration)
    if not isinstance(manifest, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest omitted {label} declaration"
        )
    manifest_sha = _sha256(manifest.get("sha256"))
    expected_manifest = _sha256(expected_manifest_sha256)
    if not manifest_sha or not expected_manifest or manifest_sha != expected_manifest:
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest does not match the current {label} signature"
        )
    raw_atoms = manifest.get("atoms")
    if not isinstance(raw_atoms, list):
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest has no {label} atoms"
        )
    atoms = [
        atom
        for atom in raw_atoms
        if isinstance(atom, Mapping) and str(atom.get("ref") or "").strip() == ref
    ]
    if len(atoms) != 1:
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest has no unique {label} atom `{ref}`"
        )
    if str(atoms[0].get("role") or "").strip() != expected_role:
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest has the wrong {label} atom role"
        )
    atom_sha = _sha256(signature_manifest_atom_digest(dict(atoms[0])))
    expected_atom = _sha256(expected_atom_sha256)
    if not atom_sha or not expected_atom or atom_sha != expected_atom:
        raise SourceDefinitionAntecedentRouteError(
            f"source-overlay signature manifest does not match the current {label} atom"
        )
    return {
        "declaration_signature_sha256": manifest_sha,
        "signature_ref": ref,
        "role": expected_role,
        "signature_atom_sha256": atom_sha,
    }


def _overlay_signature_manifest_verification(
    stdout: str,
    *,
    lemma_declaration: str,
    lemma_binder_index: int,
    lemma_signature_sha256: str,
    lemma_input_atom_sha256: str,
    definition_declaration: str,
    definition_signature_sha256: str,
    definition_result_atom_sha256: str,
) -> dict[str, Any]:
    """Validate both v10 atom pins from the same source-overlay invocation."""

    manifests = parse_signature_manifest_output(stdout)
    expected_declarations = {lemma_declaration, definition_declaration}
    if set(manifests) != expected_declarations:
        raise SourceDefinitionAntecedentRouteError(
            "source-overlay signature manifest did not return exactly both reviewed declarations"
        )
    lemma = _manifest_atom_from_current_overlay(
        manifests,
        declaration=lemma_declaration,
        ref=f"b/{lemma_binder_index}",
        expected_manifest_sha256=lemma_signature_sha256,
        expected_atom_sha256=lemma_input_atom_sha256,
        expected_role="assumption",
        label="source-result",
    )
    definition = _manifest_atom_from_current_overlay(
        manifests,
        declaration=definition_declaration,
        ref="result",
        expected_manifest_sha256=definition_signature_sha256,
        expected_atom_sha256=definition_result_atom_sha256,
        expected_role="conclusion",
        label="source-definition",
    )
    # The parser has normalized the helper-owned canonical structures. Keep a
    # digest of the exact two-declaration output as a reproducible command
    # output pin, without treating declaration strings as semantic evidence.
    normalized_output = {
        declaration: manifests[declaration]
        for declaration in sorted(expected_declarations)
    }
    return {
        "schema": 1,
        "manifest_output_sha256": _canonical_digest(normalized_output),
        "lemma": lemma,
        "definition": definition,
    }


def _source_overlay_script(
    *,
    interface_text: str,
    manifest_helper_text: str,
    meta_helper_text: str,
    lemma_declaration: str,
    lemma_binder_index: int,
    definition_declaration: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
) -> str:
    """Build the deterministic single-invocation source-overlay command."""

    manifest_commands = (
        f'#signature_manifest {json.dumps(lemma_declaration)} ""\n'
        f'#signature_manifest {json.dumps(definition_declaration)} ""\n'
    )
    bridge_command = (
        "#source_definition_antecedent_semantic_bridge "
        f"{json.dumps(lemma_declaration, ensure_ascii=False)} "
        f"{json.dumps(str(lemma_binder_index), ensure_ascii=False)} "
        f"{json.dumps(definition_declaration, ensure_ascii=False)} "
        f"{json.dumps(raw_expanded_proposition, ensure_ascii=False)} "
        f"{json.dumps(review_surface_expression, ensure_ascii=False)}\n"
    )
    return (
        "import Lean\n\n"
        "-- Current PaperInterface source overlay; do not import its olean.\n"
        + interface_text
        + "\n\n-- Exact v10-compatible current signature atoms.\n"
        + manifest_helper_text
        + "\n\n-- Focused declaration-coordinate Meta bridge.\n"
        + meta_helper_text
        + "\n\n-- Current selected declaration coordinates.\n"
        + manifest_commands
        + bridge_command
    )


def _bridge_input_payload(
    *,
    paper: str,
    lemma_declaration: str,
    lemma_binder_index: int,
    lemma_signature_sha256: str,
    lemma_input_atom_sha256: str,
    definition_declaration: str,
    definition_signature_sha256: str,
    definition_result_atom_sha256: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
    source_overlay: str,
    environment: Mapping[str, Any],
) -> dict[str, Any]:
    """Return the exact fresh-overlay semantic input, excluding diagnostics."""

    return {
        "schema": LEAN_META_BRIDGE_SCHEMA,
        "bridge_policy_version": LEAN_META_BRIDGE_POLICY_VERSION,
        "bridge_protocol_version": LEAN_META_BRIDGE_PROTOCOL_VERSION,
        "paper": paper,
        "lemma_declaration": lemma_declaration,
        "lemma_binder_index": lemma_binder_index,
        "lemma_signature_sha256": lemma_signature_sha256,
        "lemma_input_signature_atom_sha256": lemma_input_atom_sha256,
        "definition_declaration": definition_declaration,
        "definition_signature_sha256": definition_signature_sha256,
        "definition_result_signature_atom_sha256": definition_result_atom_sha256,
        # The exact source-review texts are syntax-elaborated by Lean in the
        # overlay. Their hashes are semantic input pins, never a Python
        # formula-side heuristic.
        "raw_expanded_proposition_sha256": _formula_digest(raw_expanded_proposition),
        "review_surface_expression_sha256": _formula_digest(
            review_surface_expression
        ),
        "source_overlay_sha256": _sha256_text(source_overlay),
        "environment": environment,
    }


def _current_source_overlay_preflight(
    *,
    paper: str,
    paper_dir: Path,
    lemma_declaration: str,
    lemma_binder_index: int,
    lemma_signature_sha256: str,
    lemma_input_atom_sha256: str,
    definition_declaration: str,
    definition_signature_sha256: str,
    definition_result_atom_sha256: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
) -> dict[str, Any]:
    """Recompute all replay inputs without a Lake build or a Lean process."""

    _interface_path, interface_text, environment = _source_overlay_environment(
        paper=paper, paper_dir=paper_dir
    )
    try:
        meta_helper_text = LEAN_META_HELPER_PATH.read_text(encoding="utf-8")
        manifest_helper_text = SIGNATURE_MANIFEST_HELPER_PATH.read_text(
            encoding="utf-8"
        )
    except (OSError, UnicodeDecodeError) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"could not read focused Lean source-overlay helper: {exc}"
        ) from exc
    source_overlay = _source_overlay_script(
        interface_text=interface_text,
        manifest_helper_text=manifest_helper_text,
        meta_helper_text=meta_helper_text,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        definition_declaration=definition_declaration,
        raw_expanded_proposition=raw_expanded_proposition,
        review_surface_expression=review_surface_expression,
    )
    payload = _bridge_input_payload(
        paper=paper,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        lemma_signature_sha256=lemma_signature_sha256,
        lemma_input_atom_sha256=lemma_input_atom_sha256,
        definition_declaration=definition_declaration,
        definition_signature_sha256=definition_signature_sha256,
        definition_result_atom_sha256=definition_result_atom_sha256,
        raw_expanded_proposition=raw_expanded_proposition,
        review_surface_expression=review_surface_expression,
        source_overlay=source_overlay,
        environment=environment,
    )
    return {
        "bridge_input": payload,
        "bridge_input_sha256": _canonical_digest(payload),
        "source_overlay": source_overlay,
        "environment": environment,
    }


def _assert_source_overlay_preflight_stable(
    *,
    paper: str,
    paper_dir: Path,
    lemma_declaration: str,
    lemma_binder_index: int,
    lemma_signature_sha256: str,
    lemma_input_atom_sha256: str,
    definition_declaration: str,
    definition_signature_sha256: str,
    definition_result_atom_sha256: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
    expected_bridge_input: Mapping[str, Any],
    expected_bridge_input_sha256: str,
) -> None:
    """Fail closed if cheap replay inputs changed after a cache lookup."""

    replay_preflight = _current_source_overlay_preflight(
        paper=paper,
        paper_dir=paper_dir,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        lemma_signature_sha256=lemma_signature_sha256,
        lemma_input_atom_sha256=lemma_input_atom_sha256,
        definition_declaration=definition_declaration,
        definition_signature_sha256=definition_signature_sha256,
        definition_result_atom_sha256=definition_result_atom_sha256,
        raw_expanded_proposition=raw_expanded_proposition,
        review_surface_expression=review_surface_expression,
    )
    if (
        str(replay_preflight.get("bridge_input_sha256") or "")
        != expected_bridge_input_sha256
        or not _canonical_equal(
            replay_preflight.get("bridge_input"), expected_bridge_input
        )
    ):
        raise SourceDefinitionAntecedentRouteError(
            "source-overlay inputs changed during bridge cache reuse; retry"
        )


def _canonical_equal(left: object, right: object) -> bool:
    """Compare receipt payloads through the repository's stable JSON form."""

    return canonical_digest_payload(left) == canonical_digest_payload(right)


def _sealed_bridge_verdict_matches_input(
    verdict: object, *, bridge_input: Mapping[str, Any]
) -> bool:
    """Revalidate the stored Python-normalized Lean success evidence."""

    if not isinstance(verdict, Mapping):
        return False
    if (
        verdict.get("schema") != LEAN_META_BRIDGE_SCHEMA
        or str(verdict.get("lemma") or "")
        != str(bridge_input.get("lemma_declaration") or "")
        or str(verdict.get("definition") or "")
        != str(bridge_input.get("definition_declaration") or "")
        or verdict.get("lemma_binder_index") != bridge_input.get("lemma_binder_index")
        or _sha256(verdict.get("raw_expanded_proposition_sha256"))
        != _sha256(bridge_input.get("raw_expanded_proposition_sha256"))
        or _sha256(verdict.get("review_surface_expression_sha256"))
        != _sha256(bridge_input.get("review_surface_expression_sha256"))
        or str(verdict.get("review_formula_iff_side") or "") not in {"left", "right"}
        or str(verdict.get("review_formula_selection_method") or "")
        != "syntactic_alpha"
    ):
        return False
    for field in (
        "raw_expansion_matches_lemma_binder",
        "review_surface_is_syntactic_iff",
        "review_surface_matches_actual_iff",
        "review_formula_side_matches_actual",
        "opposite_actual_endpoint_matches_lemma_binder",
    ):
        if verdict.get(field) is not True:
            return False
    for field in (
        "parsed_raw_expansion_alpha_sha256",
        "review_left_iff_side_alpha_sha256",
        "review_right_iff_side_alpha_sha256",
        "actual_left_iff_side_alpha_sha256",
        "actual_right_iff_side_alpha_sha256",
        "lemma_binder_display_sha256",
    ):
        if not _sha256(verdict.get(field)):
            return False
    display_sha = verdict.get("definition_iff_display_sha256")
    return display_sha is None or bool(_sha256(display_sha))


def _sealed_manifest_verification_matches_input(
    value: object, *, bridge_input: Mapping[str, Any]
) -> bool:
    """Check the stored same-overlay manifest pins without re-running Lean."""

    if not isinstance(value, Mapping) or value.get("schema") != 1:
        return False
    if not _sha256(value.get("manifest_output_sha256")):
        return False
    lemma = value.get("lemma")
    definition = value.get("definition")
    if not isinstance(lemma, Mapping) or not isinstance(definition, Mapping):
        return False
    return (
        _sha256(lemma.get("declaration_signature_sha256"))
        == _sha256(bridge_input.get("lemma_signature_sha256"))
        and str(lemma.get("signature_ref") or "")
        == f"b/{bridge_input.get('lemma_binder_index')}"
        and str(lemma.get("role") or "") == "assumption"
        and _sha256(lemma.get("signature_atom_sha256"))
        == _sha256(bridge_input.get("lemma_input_signature_atom_sha256"))
        and _sha256(definition.get("declaration_signature_sha256"))
        == _sha256(bridge_input.get("definition_signature_sha256"))
        and str(definition.get("signature_ref") or "") == "result"
        and str(definition.get("role") or "") == "conclusion"
        and _sha256(definition.get("signature_atom_sha256"))
        == _sha256(bridge_input.get("definition_result_signature_atom_sha256"))
    )


def _sealed_bridge_result_if_current(
    value: object,
    *,
    bridge_input: Mapping[str, Any],
    bridge_input_sha256: str,
    source_overlay_sha256: str,
    environment: Mapping[str, Any],
    dependency_closure_build: Mapping[str, Any],
) -> dict[str, Any] | None:
    """Return a sealed prior result only when post-build inputs are exact.

    This function is intentionally a cache validator rather than a source of
    route truth. A failure is a cache miss: the caller performs the focused
    overlay and later receipt replay still compares the rebuilt semantic
    route to the supplied receipt.
    """

    if not isinstance(value, Mapping):
        return None
    stored_input = value.get("bridge_input")
    if not isinstance(stored_input, Mapping):
        return None
    if (
        value.get("schema") != LEAN_META_BRIDGE_SCHEMA
        or str(value.get("bridge_policy_version") or "")
        != LEAN_META_BRIDGE_POLICY_VERSION
        or str(value.get("bridge_protocol_version") or "")
        != LEAN_META_BRIDGE_PROTOCOL_VERSION
        or value.get("sealed_reuse_schema") != LEAN_META_BRIDGE_SEAL_SCHEMA
        or str(value.get("method") or "") != LEAN_META_BRIDGE_METHOD
        or _sha256(value.get("bridge_input_sha256")) != bridge_input_sha256
        or _canonical_digest(stored_input) != bridge_input_sha256
        or not _canonical_equal(stored_input, bridge_input)
        or _sha256(value.get("source_overlay_sha256")) != source_overlay_sha256
        or not _canonical_equal(value.get("environment"), environment)
        or not _canonical_equal(
            value.get("dependency_closure_build"), dependency_closure_build
        )
    ):
        return None
    if (
        str(stored_input.get("bridge_policy_version") or "")
        != LEAN_META_BRIDGE_POLICY_VERSION
        or str(stored_input.get("bridge_protocol_version") or "")
        != LEAN_META_BRIDGE_PROTOCOL_VERSION
    ):
        return None
    text_hashes = value.get("input_text_hashes")
    expected_text_hashes = {
        "raw_expanded_proposition_sha256": bridge_input.get(
            "raw_expanded_proposition_sha256"
        ),
        "review_surface_expression_sha256": bridge_input.get(
            "review_surface_expression_sha256"
        ),
    }
    if not _canonical_equal(text_hashes, expected_text_hashes):
        return None
    command = value.get("command")
    if (
        not isinstance(command, Mapping)
        or command.get("template") != ["lake", "env", "lean", "<source-overlay>"]
        or _sha256(command.get("input_sha256")) != source_overlay_sha256
        or not _sha256(command.get("machine_verdict_output_sha256"))
        or not _sha256(command.get("parsed_signature_manifest_output_sha256"))
    ):
        return None
    if not _sealed_manifest_verification_matches_input(
        value.get("signature_manifest_verification"), bridge_input=bridge_input
    ):
        return None
    if not _sealed_bridge_verdict_matches_input(
        value.get("verdict"), bridge_input=bridge_input
    ):
        return None
    return copy.deepcopy(dict(value))


def _receipt_has_valid_bridge_reuse_envelope(
    receipt: object, *, paper: str
) -> bool:
    if not isinstance(receipt, Mapping):
        return False
    if (
        receipt.get("schema") != SCHEMA
        or receipt.get("artifact_kind") != ARTIFACT_KIND
        or receipt.get("policy_version") != POLICY_VERSION
        or receipt.get("paper") != paper
    ):
        return False
    claimed = _sha256(receipt.get("receipt_sha256"))
    unsigned = {key: value for key, value in receipt.items() if key != "receipt_sha256"}
    return bool(claimed) and claimed == _canonical_digest(unsigned)


def _sealed_bridge_reuse_index_from_receipts(
    receipts: object, *, paper: str
) -> dict[str, dict[str, Any]]:
    """Extract only integrity-checked sealed bridge results from receipts.

    Current routes are never read from this index. It can merely save a
    source-overlay invocation after current raw/map/match evidence selects the
    same exact post-build bridge input.
    """

    if not isinstance(receipts, (list, tuple)):
        return {}
    indexed: dict[str, dict[str, Any]] = {}
    for receipt in receipts:
        if not _receipt_has_valid_bridge_reuse_envelope(receipt, paper=paper):
            continue
        raw_routes = receipt.get("routes") if isinstance(receipt, Mapping) else None
        if not isinstance(raw_routes, list):
            continue
        for route in raw_routes:
            definition = route.get("definition") if isinstance(route, Mapping) else None
            endpoint = definition.get("endpoint") if isinstance(definition, Mapping) else None
            bridge = (
                endpoint.get("current_elaborated_meta_bridge")
                if isinstance(endpoint, Mapping)
                else None
            )
            if not isinstance(bridge, Mapping):
                continue
            input_sha = _sha256(bridge.get("bridge_input_sha256"))
            stored_input = bridge.get("bridge_input")
            if (
                not input_sha
                or not isinstance(stored_input, Mapping)
                or _canonical_digest(stored_input) != input_sha
            ):
                continue
            normalized = copy.deepcopy(dict(bridge))
            prior = indexed.get(input_sha)
            if prior is not None and not _canonical_equal(prior, normalized):
                # Do not first-win conflicting claims for the same exact
                # input. A cache miss is appropriate for one malformed entry,
                # but two integrity-valid receipts asserting incompatible
                # results are an ambiguity that consumers must not ignore.
                raise SourceDefinitionAntecedentRouteError(
                    "sealed bridge reuse receipts conflict for one exact input"
                )
            indexed[input_sha] = normalized
    return indexed


def _semantic_source_identity_scope(value: object) -> dict[str, Any] | None:
    """Project a source identity for advisory cache navigation only.

    The full identity remains part of current route reconstruction.  This
    smaller projection deliberately drops storage keys, whole-map hashes, and
    declaration spellings so a sealed receipt can cheaply point at a likely
    current definition after administrative renames.  It must never be used
    as route acceptance evidence.
    """

    if not isinstance(value, Mapping):
        return None
    location = str(value.get("source_location") or "").strip()
    kind = str(value.get("source_kind") or "").strip()
    semantic_sha = _sha256(value.get("source_semantic_sha256"))
    contract = value.get("semantic_contract")
    try:
        normalized_contract = _semantic_contract(
            contract, label="sealed source identity scope"
        )
    except SourceDefinitionAntecedentRouteError:
        return None
    if not location or not kind or not semantic_sha:
        return None
    return {
        "schema": 1,
        "source_location": location,
        "source_kind": kind,
        "source_semantic_sha256": semantic_sha,
        "semantic_contract": {
            "evidence_mode": normalized_contract["evidence_mode"],
            "semantic_shape": normalized_contract["semantic_shape"],
        },
    }


def _input_atom_scope(value: object) -> dict[str, Any] | None:
    """Return the name-independent part of one current input atom."""

    if not isinstance(value, Mapping):
        return None
    signature_atom = _sha256(value.get("lean_signature_atom_sha256"))
    signature_ref = str(value.get("lean_signature_ref") or "").strip()
    binder_index = value.get("lean_binder_index")
    surface_sha = _sha256(value.get("surface_expression_sha256"))
    visible_sha = _sha256(value.get("qualified_visible_input_surface_sha256"))
    match = re.fullmatch(r"b/([0-9]+)", signature_ref)
    if (
        not signature_atom
        or match is None
        or not isinstance(binder_index, int)
        or isinstance(binder_index, bool)
        or binder_index != int(match.group(1))
        or not surface_sha
        or not visible_sha
    ):
        return None
    return {
        "schema": 1,
        "lean_signature_atom_sha256": signature_atom,
        "lean_signature_ref": signature_ref,
        "lean_binder_index": binder_index,
        "surface_expression_sha256": surface_sha,
        "qualified_visible_input_surface_sha256": visible_sha,
    }


def _raw_lemma_candidate_scope(
    raw: Mapping[str, Any], lemma: Mapping[str, Any]
) -> dict[str, Any] | None:
    """Project current raw/lemma semantics for an advisory definition scope.

    This contains semantic hashes and positional signature coordinates only.
    In particular it excludes raw storage IDs, map keys, source-record IDs,
    theorem/definition declaration strings, and binder display names.
    """

    raw_fields = {
        field: _sha256(raw.get(field))
        for field in (
            "raw_group_semantic_descriptor_sha256",
            "full_member_pins_sha256",
            "expanded_proposition_sha256",
            "qualified_visible_input_surface_sha256",
        )
    }
    alias_chain = raw.get("transparent_alias_chain_sha256s")
    association_sha = _sha256(
        raw.get("semantic_association_sha256")
        or lemma.get("semantic_association_sha256")
    )
    lemma_identity = _semantic_source_identity_scope(lemma.get("source_identity"))
    signature_sha = _sha256(lemma.get("elaborated_signature_sha256"))
    input_atom = _input_atom_scope(lemma.get("input_atom"))
    if (
        not all(raw_fields.values())
        or not isinstance(alias_chain, list)
        or not alias_chain
        or any(not _sha256(value) for value in alias_chain)
        or not association_sha
        or lemma_identity is None
        or not signature_sha
        or input_atom is None
    ):
        return None
    return {
        "schema": 1,
        "raw": {
            **raw_fields,
            "transparent_alias_chain_sha256s": sorted(
                _sha256(value) for value in alias_chain
            ),
            "semantic_association_sha256": association_sha,
        },
        "lemma": {
            "source_identity": lemma_identity,
            "elaborated_signature_sha256": signature_sha,
            "input_atom": input_atom,
        },
    }


def _definition_candidate_scope(definition: Mapping[str, Any]) -> dict[str, Any] | None:
    """Project semantic definition identity plus its current record signature."""

    identity = _semantic_source_identity_scope(definition.get("source_identity"))
    signature_sha = _sha256(definition.get("elaborated_signature_sha256"))
    if identity is None or not signature_sha:
        return None
    return {
        "schema": 1,
        "source_identity": identity,
        "elaborated_signature_sha256": signature_sha,
    }


def _sealed_definition_candidate_scopes_from_receipts(
    receipts: object, *, paper: str
) -> dict[str, tuple[dict[str, Any], ...]]:
    """Extract advisory semantic candidate scopes from sealed route receipts.

    Multiple distinct definition scopes for one raw/lemma context intentionally
    do not conflict: callers simply fall back to the ordinary all-candidate
    current reconstruction.  Unlike bridge-result conflicts, this information
    cannot establish a route and therefore never warrants first-wins behavior.
    """

    if not isinstance(receipts, (list, tuple)):
        return {}
    by_context: dict[str, dict[str, dict[str, Any]]] = {}
    for receipt in receipts:
        if not _receipt_has_valid_bridge_reuse_envelope(receipt, paper=paper):
            continue
        raw_routes = receipt.get("routes") if isinstance(receipt, Mapping) else None
        if not isinstance(raw_routes, list):
            continue
        for route in raw_routes:
            if not isinstance(route, Mapping):
                continue
            raw = route.get("raw_input")
            lemma = route.get("lemma")
            definition = route.get("definition")
            if (
                not isinstance(raw, Mapping)
                or not isinstance(lemma, Mapping)
                or not isinstance(definition, Mapping)
            ):
                continue
            context = _raw_lemma_candidate_scope(raw, lemma)
            definition_scope = _definition_candidate_scope(definition)
            if context is None or definition_scope is None:
                continue
            context_sha = _canonical_digest(context)
            scope_sha = _canonical_digest(definition_scope)
            by_context.setdefault(context_sha, {})[scope_sha] = definition_scope
    return {
        context_sha: tuple(scopes[key] for key in sorted(scopes))
        for context_sha, scopes in by_context.items()
    }


def _run_source_overlay_meta_bridge(
    *,
    paper: str,
    paper_dir: Path,
    lemma_declaration: str,
    lemma_binder_index: int,
    lemma_signature_sha256: str,
    definition_declaration: str,
    definition_signature_sha256: str,
    lemma_input_atom_sha256: str,
    definition_result_atom_sha256: str,
    raw_expanded_proposition: str,
    review_surface_expression: str,
    sealed_bridge_reuse: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run one fresh, source-overlay Lean Meta bridge verification.

    This is deliberately a focused compile, not a source-record audit rerun.
    It pastes the current ``PaperInterface.lean`` source into a temporary
    overlay with the canonical signature-manifest and small Meta helpers. One
    Lean invocation therefore both reproduces the exact v10 ``b/N``/``result``
    atom hashes and semantically binds both reviewed expression texts in Lean.
    No raw source-record audit is regenerated. Cross-process bridge reuse is
    intentionally disabled: a receipt cannot establish the complete
    transitive parser/elaborator environment of an arbitrary Lean overlay.
    """

    # Kept in the call signature while receipts from prior route versions are
    # migrated. It must never become accepting evidence without a hermetic
    # resolved-module closure fingerprint.
    del sealed_bridge_reuse

    lemma_declaration = _qualified_declaration_coordinate(
        lemma_declaration, label="raw source-result declaration"
    )
    definition_declaration = _qualified_declaration_coordinate(
        definition_declaration, label="source-definition evidence declaration"
    )
    if not isinstance(lemma_binder_index, int) or isinstance(lemma_binder_index, bool):
        raise SourceDefinitionAntecedentRouteError(
            "raw source-result binder coordinate is not an integer"
        )
    raw_expanded_proposition = _formula(raw_expanded_proposition)
    review_surface_expression = _formula(review_surface_expression)
    lemma_atom = _sha256(lemma_input_atom_sha256)
    definition_atom = _sha256(definition_result_atom_sha256)
    lemma_signature = _sha256(lemma_signature_sha256)
    definition_signature = _sha256(definition_signature_sha256)
    if not lemma_atom or not definition_atom or not lemma_signature or not definition_signature:
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta bridge lacks current declaration or signature-atom pins"
        )
    # Always run the incremental paper-local build before the fresh overlay.
    # This refreshes the reviewed module closure without invoking a repository
    # build or regenerating any raw-audit surface.
    dependency_closure_build = _fresh_paper_interface_build(paper)
    # Record the direct post-build overlay snapshot as provenance. It is not a
    # transitive cache seal; the temporary overlay below is always rerun.
    preflight = _current_source_overlay_preflight(
        paper=paper,
        paper_dir=paper_dir,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        lemma_signature_sha256=lemma_signature,
        lemma_input_atom_sha256=lemma_atom,
        definition_declaration=definition_declaration,
        definition_signature_sha256=definition_signature,
        definition_result_atom_sha256=definition_atom,
        raw_expanded_proposition=raw_expanded_proposition,
        review_surface_expression=review_surface_expression,
    )
    source_overlay = str(preflight["source_overlay"])
    source_overlay_sha = _sha256_text(source_overlay)
    bridge_input = preflight["bridge_input"]
    bridge_input_sha = str(preflight["bridge_input_sha256"])
    environment = preflight["environment"]
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=_lean_overlay_temp_dir(),
            prefix=".source_definition_antecedent_meta_",
            suffix=".lean",
            delete=False,
            mode="w",
            encoding="utf-8",
        ) as handle:
            handle.write(source_overlay)
            temporary = Path(handle.name)
        completed = subprocess.run(
            ["lake", "env", "lean", str(temporary)],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=LEAN_BRIDGE_TIMEOUT_SECONDS,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"focused Lean Meta bridge could not run: {exc}"
        ) from exc
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()
    stdout = completed.stdout
    stderr = completed.stderr
    if completed.returncode != 0:
        diagnostic_lines = [
            line.strip()
            for line in (stderr + "\n" + stdout).splitlines()
            if "error:" in line.lower() or "failed" in line.lower()
        ]
        diagnostic = _normalized_text(
            " | ".join(diagnostic_lines[-4:]) or stderr or stdout
        )
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta bridge source-overlay command failed"
            + (f": {diagnostic[:500]}" if diagnostic else "")
        )
    sentinel_lines = [
        line[len(LEAN_META_BRIDGE_SENTINEL) :]
        for line in stdout.splitlines()
        if line.startswith(LEAN_META_BRIDGE_SENTINEL)
    ]
    if len(sentinel_lines) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "focused Lean Meta bridge emitted no unique machine-readable verdict"
        )
    try:
        raw_verdict = json.loads(sentinel_lines[0])
    except json.JSONDecodeError as exc:
        raise SourceDefinitionAntecedentRouteError(
            f"focused Lean Meta bridge emitted malformed JSON: {exc}"
        ) from exc
    verdict = _meta_verdict_from_output(
        raw_verdict,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        definition_declaration=definition_declaration,
        raw_expanded_proposition=raw_expanded_proposition,
        review_surface_expression=review_surface_expression,
    )
    manifest_verification = _overlay_signature_manifest_verification(
        stdout,
        lemma_declaration=lemma_declaration,
        lemma_binder_index=lemma_binder_index,
        lemma_signature_sha256=lemma_signature,
        lemma_input_atom_sha256=lemma_atom,
        definition_declaration=definition_declaration,
        definition_signature_sha256=definition_signature,
        definition_result_atom_sha256=definition_atom,
    )
    result = {
        "schema": LEAN_META_BRIDGE_SCHEMA,
        "bridge_policy_version": LEAN_META_BRIDGE_POLICY_VERSION,
        "bridge_protocol_version": LEAN_META_BRIDGE_PROTOCOL_VERSION,
        "method": LEAN_META_BRIDGE_METHOD,
        # The full canonical input explains exactly what Lean elaborated in
        # this receipt. It is never reused as an accepting cache key.
        "bridge_input": copy.deepcopy(bridge_input),
        "bridge_input_sha256": bridge_input_sha,
        "source_overlay_sha256": source_overlay_sha,
        "environment": environment,
        "input_text_hashes": {
            "raw_expanded_proposition_sha256": bridge_input[
                "raw_expanded_proposition_sha256"
            ],
            "review_surface_expression_sha256": bridge_input[
                "review_surface_expression_sha256"
            ],
        },
        "dependency_closure_build": dependency_closure_build,
        "command": {
            "template": ["lake", "env", "lean", "<source-overlay>"],
            "input_sha256": source_overlay_sha,
            "machine_verdict_output_sha256": _sha256_text(sentinel_lines[0]),
            "parsed_signature_manifest_output_sha256": manifest_verification[
                "manifest_output_sha256"
            ],
        },
        "signature_manifest_verification": manifest_verification,
        "verdict": verdict,
    }
    return result


def _semantic_contract(value: object, *, label: str) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise SourceDefinitionAntecedentRouteError(f"{label} has no semantic contract")
    fields = {
        field: str(value.get(field) or "").strip()
        for field in (
            "evidence_declaration",
            "spec_declaration",
            "evidence_mode",
            "semantic_shape",
        )
    }
    if not all(fields.values()) or fields["evidence_declaration"] == fields["spec_declaration"]:
        raise SourceDefinitionAntecedentRouteError(f"{label} has an incomplete semantic contract")
    return fields


def _source_identity(source_key: str, item: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "source_key": source_key,
        "source_location": str(item.get("source_location") or "").strip(),
        "source_kind": str(item.get("source_kind") or "").strip(),
        "source_map_item_sha256": _canonical_digest(item),
        "source_semantic_sha256": source_item_coverage_sha256(dict(item), ""),
        "semantic_contract": _semantic_contract(
            item.get("semantic_contract"), label=f"source item `{source_key}`"
        ),
    }


def _source_items(statement_map: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    raw = statement_map.get("items")
    if not isinstance(raw, Mapping):
        raise SourceDefinitionAntecedentRouteError("statement map has no item ledger")
    items: dict[str, dict[str, Any]] = {}
    for raw_key, value in raw.items():
        key = str(raw_key).strip()
        if not key or not isinstance(value, Mapping):
            raise SourceDefinitionAntecedentRouteError("statement map has a malformed item")
        items[key] = dict(value)
    return items


def _map_item_from_raw_identity(
    source_items: Mapping[str, Mapping[str, Any]], identity: object
) -> tuple[str, dict[str, Any]]:
    if not isinstance(identity, Mapping):
        raise SourceDefinitionAntecedentRouteError("raw source identity is not an object")
    expected_map_sha = _sha256(identity.get("source_map_item_sha256"))
    expected_semantic_sha = _sha256(identity.get("source_semantic_sha256"))
    expected_location = str(identity.get("source_location") or "").strip()
    expected_kind = str(identity.get("source_kind") or "").strip()
    expected_contract = identity.get("semantic_contract")
    if not expected_map_sha or not expected_semantic_sha or not expected_location or not expected_kind:
        raise SourceDefinitionAntecedentRouteError("raw source identity is incomplete")
    candidates: list[tuple[str, dict[str, Any]]] = []
    for key, item in source_items.items():
        try:
            current = _source_identity(key, item)
        except SourceDefinitionAntecedentRouteError:
            continue
        if (
            current["source_map_item_sha256"] == expected_map_sha
            and current["source_semantic_sha256"] == expected_semantic_sha
            and current["source_location"] == expected_location
            and current["source_kind"] == expected_kind
            and canonical_digest_payload(current["semantic_contract"])
            == canonical_digest_payload(expected_contract)
        ):
            candidates.append((key, item))
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "raw source identity does not select exactly one current source-map item"
        )
    return candidates[0]


def _anchor_for_definition(
    item: Mapping[str, Any], *, paper_dir: Path, source_artifact_sha256: str
) -> dict[str, Any]:
    reconciliation = item.get("source_presentation_reconciliation")
    if not isinstance(reconciliation, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            "source definition lacks a current presentation-reconciliation anchor"
        )
    anchor = _anchor_from_mapping(
        reconciliation.get("core_anchor"),
        paper_dir=paper_dir,
        source_artifact_sha256=source_artifact_sha256,
        label="source definition core anchor",
    )
    path, start, end = _parse_location(
        item.get("source_location"), label="source definition source_location"
    )
    if anchor["path"] != path or not (start <= anchor["line_start"] <= anchor["line_end"] <= end):
        raise SourceDefinitionAntecedentRouteError(
            "source definition core anchor is outside its current source location"
        )
    return anchor


def _anchor_for_result(
    item: Mapping[str, Any], *, paper_dir: Path, source_artifact_sha256: str
) -> dict[str, Any]:
    path, start, end = _parse_location(
        item.get("source_location"), label="source result source_location"
    )
    raw_anchors = item.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list):
        raise SourceDefinitionAntecedentRouteError(
            "source result lacks source_anchor_evidence"
        )
    anchors = [
        _anchor_from_mapping(
            anchor,
            paper_dir=paper_dir,
            source_artifact_sha256=source_artifact_sha256,
            label="source result anchor",
        )
        for anchor in raw_anchors
    ]
    exact = [
        anchor
        for anchor in anchors
        if anchor["path"] == path
        and anchor["line_start"] == start
        and anchor["line_end"] == end
    ]
    if len(exact) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "source result must have exactly one byte-checked anchor at its source location"
        )
    return exact[0]


def _statement_match_items(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    prompt = str(payload.get("prompt_version") or "").strip()
    if not prompt.startswith("statement-match-v10-"):
        raise SourceDefinitionAntecedentRouteError(
            "statement-match payload is not a v10 statement-match record"
        )
    raw = payload.get("items")
    if not isinstance(raw, Mapping):
        raise SourceDefinitionAntecedentRouteError("statement-match payload has no item ledger")
    items: dict[str, dict[str, Any]] = {}
    for raw_key, value in raw.items():
        key = str(raw_key).strip()
        if key and isinstance(value, Mapping):
            items[key] = dict(value)
    if not items:
        raise SourceDefinitionAntecedentRouteError("statement-match payload has no records")
    return items


def _record_has_current_source_route(
    record: Mapping[str, Any], item: Mapping[str, Any]
) -> bool:
    statement_sha = _statement_digest(item.get("statement"))
    location = str(item.get("source_location") or "").strip()
    if (
        str(record.get("judgment") or "").strip() != "matches"
        or _sha256(record.get("paper_statement_sha256")) != statement_sha
        or not _sha256(record.get("lean_signature_sha256"))
    ):
        return False
    raw_routes = record.get("source_routes")
    if not isinstance(raw_routes, list):
        return False
    matched_routes = [
        route
        for route in raw_routes
        if isinstance(route, Mapping)
        and str(route.get("route_kind") or "").strip() == "direct"
        and str(route.get("semantic_relation") or "").strip()
        == "equivalent_source_statement"
        and _sha256(route.get("source_statement_sha256")) == statement_sha
        and str(route.get("source_location") or "").strip() == location
    ]
    if len(matched_routes) != 1:
        return False
    obligations = record.get("source_obligations")
    if not isinstance(obligations, list):
        return False
    return any(
        isinstance(obligation, Mapping)
        and str(obligation.get("kind") or "").strip() == "conclusion"
        and _sha256(obligation.get("source_statement_sha256")) == statement_sha
        and str(obligation.get("source_location") or "").strip() == location
        for obligation in obligations
    )


def _statement_match_for_result(
    records: Mapping[str, Mapping[str, Any]],
    item: Mapping[str, Any],
    *,
    expected_signature: str,
) -> tuple[str, dict[str, Any]]:
    candidates = [
        (key, dict(record))
        for key, record in records.items()
        if _record_has_current_source_route(record, item)
        and _sha256(record.get("lean_signature_sha256")) == expected_signature
    ]
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "source result does not select exactly one current v10 statement-match endpoint"
        )
    return candidates[0]


def _statement_match_for_definition(
    records: Mapping[str, Mapping[str, Any]], item: Mapping[str, Any]
) -> tuple[str, dict[str, Any]]:
    candidates = [
        (key, dict(record))
        for key, record in records.items()
        if _record_has_current_source_route(record, item)
    ]
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "source definition does not select exactly one current v10 statement-match endpoint"
        )
    return candidates[0]


def _obligation_index(record: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    raw = record.get("lean_obligations")
    if not isinstance(raw, list):
        raise SourceDefinitionAntecedentRouteError(
            "statement-match record has no lean_obligations list"
        )
    out: dict[str, Mapping[str, Any]] = {}
    for value in raw:
        if not isinstance(value, Mapping):
            raise SourceDefinitionAntecedentRouteError(
                "statement-match record has a malformed Lean obligation"
            )
        identifier = str(value.get("id") or "").strip()
        if not identifier or identifier in out or not _sha256(value.get("signature_atom_sha256")):
            raise SourceDefinitionAntecedentRouteError(
                "statement-match record has an unpinned Lean obligation"
            )
        out[identifier] = value
    return out


def _binder_index_from_signature_ref(value: object, *, label: str) -> int:
    """Parse the manifest's stable binder coordinate without using its label.

    The signature manifest emits ``b/N`` for each outer Pi binder.  That
    coordinate is the only positional datum passed to the focused Meta check;
    the displayed binder name remains non-authoritative diagnostics.
    """

    match = re.fullmatch(r"b/([0-9]+)", str(value or "").strip())
    if match is None:
        raise SourceDefinitionAntecedentRouteError(
            f"{label} has no outer-binder signature coordinate"
        )
    return int(match.group(1))


def _source_obligation_index(record: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    raw = record.get("source_obligations")
    if not isinstance(raw, list):
        raise SourceDefinitionAntecedentRouteError(
            "statement-match record has no source_obligations list"
        )
    out: dict[str, Mapping[str, Any]] = {}
    for value in raw:
        if not isinstance(value, Mapping):
            continue
        identifier = str(value.get("id") or "").strip()
        if identifier and identifier not in out:
            out[identifier] = value
    return out


def _definition_iff_endpoint(
    record: Mapping[str, Any],
    *,
    expanded_proposition: str,
    paper: str,
    paper_dir: Path,
    lemma_declaration: str,
    lemma_signature_sha256: str,
    lemma_input: Mapping[str, Any],
    definition_declaration: str,
    sealed_bridge_reuse: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Bind a reviewed source Definition IFF to an actual Lean Meta verdict.

    The full reviewed IFF and raw expanded proposition are elaborated in Lean
    under the current definition and lemma telescopes. Lean, not a Python
    string split or a declaration name, selects the unique alpha-structural
    formula side and checks both declaration bridges.
    """

    scope = record.get("semantic_scope_review")
    if not isinstance(scope, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            "definition statement-match record has no semantic scope review"
        )
    definition_review = scope.get("source_definition_semantics_review")
    if not isinstance(definition_review, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            "definition statement-match record has no source-definition semantics review"
        )
    for field in (
        "domain_relation",
        "operational_relation",
        "outside_domain_relation",
    ):
        if str(definition_review.get(field) or "").strip() != "equivalent":
            raise SourceDefinitionAntecedentRouteError(
                f"definition statement-match record has non-equivalent {field}"
            )
    raw_properties = definition_review.get("advertised_properties")
    if not isinstance(raw_properties, list) or not raw_properties:
        raise SourceDefinitionAntecedentRouteError(
            "definition statement-match record has no reviewed advertised property"
        )
    obligations = _obligation_index(record)
    named_review = scope.get("named_definition_review")
    raw_named = named_review.get("items") if isinstance(named_review, Mapping) else None
    if not isinstance(raw_named, list):
        raise SourceDefinitionAntecedentRouteError(
            "definition statement-match record has no named-definition expansion"
        )
    candidates: list[dict[str, Any]] = []
    for entry in raw_named:
        if not isinstance(entry, Mapping) or entry.get("used_as_source_conclusion_evidence") is not True:
            continue
        if entry.get("recursive_expansion_complete") is not True:
            continue
        raw_ids = entry.get("lean_obligation_ids")
        if not isinstance(raw_ids, list) or len(raw_ids) != 1:
            continue
        obligation_id = str(raw_ids[0]).strip()
        obligation = obligations.get(obligation_id)
        surface = entry.get("surface_expression")
        if (
            obligation is None
            or str(obligation.get("kind") or "").strip() != "conclusion"
            or not isinstance(surface, str)
        ):
            continue
        try:
            if not _has_one_top_level_iff_shape(surface):
                continue
        except SourceDefinitionAntecedentRouteError:
            continue
        try:
            reviewed_iff = _formula(surface)
            raw_expansion = _formula(expanded_proposition)
        except SourceDefinitionAntecedentRouteError:
            continue
        signature_atom = _sha256(obligation.get("signature_atom_sha256"))
        if (
            not signature_atom
            or str(obligation.get("signature_ref") or "").strip() != "result"
        ):
            continue
        try:
            endpoint_bridge = _run_source_overlay_meta_bridge(
                paper=paper,
                paper_dir=paper_dir,
                lemma_declaration=lemma_declaration,
                lemma_binder_index=int(lemma_input["lean_binder_index"]),
                lemma_signature_sha256=lemma_signature_sha256,
                definition_declaration=definition_declaration,
                definition_signature_sha256=_sha256(
                    record.get("lean_signature_sha256")
                ),
                lemma_input_atom_sha256=str(
                    lemma_input["lean_signature_atom_sha256"]
                ),
                definition_result_atom_sha256=signature_atom,
                raw_expanded_proposition=raw_expansion,
                review_surface_expression=reviewed_iff,
                sealed_bridge_reuse=sealed_bridge_reuse,
            )
        except SourceDefinitionAntecedentRouteError:
            continue
        bridge_verdict = endpoint_bridge.get("verdict")
        formula_side = (
            str(bridge_verdict.get("review_formula_iff_side") or "").strip()
            if isinstance(bridge_verdict, Mapping)
            else ""
        )
        if formula_side not in {"left", "right"}:
            continue
        if not any(
            isinstance(property_entry, Mapping)
            and str(property_entry.get("relation") or "").strip() == "equivalent"
            and str(property_entry.get("lean_evidence_conclusion_id") or "").strip()
            == obligation_id
            for property_entry in raw_properties
        ):
            continue
        candidates.append(
            {
                "lean_obligation_id": obligation_id,
                "lean_signature_atom_sha256": signature_atom,
                "lean_signature_ref": "result",
                "iff_surface_sha256": _formula_digest(reviewed_iff),
                "expanded_proposition_sha256": _formula_digest(raw_expansion),
                "formula_iff_side": formula_side,
                "current_elaborated_meta_bridge": endpoint_bridge,
            }
        )
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "definition endpoint has no unique exact IFF expansion for the raw input"
        )
    return candidates[0]


def _lemma_input_atom(
    record: Mapping[str, Any],
    *,
    qualified_visible_input_surface: str,
    lemma_location: str,
) -> dict[str, Any]:
    """Return the current theorem input atom after exact raw-chain binding.

    The source-result review names the elaborated input surface.  It must be
    exactly the final fully qualified expression emitted by the current raw
    transparent-alias chain, not merely an atom with a matching terminal
    spelling.  The separate definition IFF check establishes the actual
    mathematical expansion of that atom.
    """

    scope = record.get("semantic_scope_review")
    named_review = scope.get("named_definition_review") if isinstance(scope, Mapping) else None
    raw_named = named_review.get("items") if isinstance(named_review, Mapping) else None
    obligations = _obligation_index(record)
    source_obligations = _source_obligation_index(record)
    alignments = record.get("obligation_alignment")
    if not isinstance(raw_named, list) or not isinstance(alignments, list):
        raise SourceDefinitionAntecedentRouteError(
            "source result lacks current input-atom review evidence"
        )
    candidates: list[dict[str, Any]] = []
    for entry in raw_named:
        if not isinstance(entry, Mapping) or entry.get("used_as_source_conclusion_evidence") is True:
            continue
        if entry.get("recursive_expansion_complete") is not True:
            continue
        raw_ids = entry.get("lean_obligation_ids")
        if not isinstance(raw_ids, list) or len(raw_ids) != 1:
            continue
        obligation_id = str(raw_ids[0]).strip()
        obligation = obligations.get(obligation_id)
        surface = entry.get("surface_expression")
        if (
            obligation is None
            or str(obligation.get("kind") or "").strip() != "assumption"
            or not isinstance(surface, str)
            or not _formula_equal(surface, qualified_visible_input_surface)
        ):
            continue
        aligned_source_ids = [
            str(alignment.get("source_id") or "").strip()
            for alignment in alignments
            if isinstance(alignment, Mapping)
            and str(alignment.get("lean_id") or "").strip() == obligation_id
            and str(alignment.get("relation") or "").strip() == "equivalent"
        ]
        if len(aligned_source_ids) != 1:
            continue
        source_obligation = source_obligations.get(aligned_source_ids[0])
        if (
            source_obligation is None
            or str(source_obligation.get("kind") or "").strip() != "assumption"
            or str(source_obligation.get("source_location") or "").strip()
            != lemma_location
        ):
            continue
        candidates.append(
            {
                "lean_obligation_id": obligation_id,
                "lean_signature_atom_sha256": _sha256(
                    obligation.get("signature_atom_sha256")
                ),
                "lean_signature_ref": str(obligation.get("signature_ref") or "").strip(),
                "lean_binder_index": _binder_index_from_signature_ref(
                    obligation.get("signature_ref"),
                    label="source result input obligation",
                ),
                "source_obligation_id": aligned_source_ids[0],
                "surface_expression_sha256": _formula_digest(surface),
                "qualified_visible_input_surface_sha256": _formula_digest(
                    qualified_visible_input_surface
                ),
            }
        )
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "source result does not expose one current reviewed input atom for the raw input"
        )
    return candidates[0]


def _full_member_pins(raw_members: object) -> list[dict[str, Any]]:
    if not isinstance(raw_members, list) or not raw_members:
        raise SourceDefinitionAntecedentRouteError("raw group has no members")
    pins: list[dict[str, Any]] = []
    seen: set[tuple[str, str, str]] = set()
    for member in raw_members:
        if not isinstance(member, tuple) or len(member) != 2:
            raise SourceDefinitionAntecedentRouteError("raw group member has an invalid shape")
        section, item = member
        if not isinstance(section, str) or not isinstance(item, Mapping):
            raise SourceDefinitionAntecedentRouteError("raw group member is malformed")
        kind = str(item.get("kind") or "").strip()
        digest = _sha256(item.get("source_record_item_sha256"))
        schema = item.get("source_record_item_digest_schema")
        semantic_id = _sha256(item.get("source_record_item_semantic_id"))
        context_sha = _sha256(item.get("source_record_item_semantic_context_requirements_sha256"))
        if (
            not kind
            or not digest
            or schema != SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            or not semantic_id
            or not context_sha
        ):
            raise SourceDefinitionAntecedentRouteError(
                "raw group member lacks a complete schema-5 semantic pin"
            )
        identifier = (section, kind, digest)
        if identifier in seen:
            raise SourceDefinitionAntecedentRouteError("raw group has duplicate full member pins")
        seen.add(identifier)
        pins.append(
            {
                "section": section,
                "kind": kind,
                "source_record_item_digest_schema": schema,
                "source_record_item_sha256": digest,
                "source_record_item_semantic_id": semantic_id,
                "source_record_item_semantic_context_requirements_sha256": context_sha,
            }
        )
    return sorted(
        pins,
        key=lambda pin: (
            pin["section"],
            pin["kind"],
            pin["source_record_item_sha256"],
        ),
    )


def _qualified_visible_input_surface(
    item: Mapping[str, Any], *, expanded_proposition: str
) -> tuple[str, str]:
    """Recover one opaque input's exact final alias surface, fail closed.

    A direct-definition route has two distinct facts to establish.  The raw
    expansion gives the mathematical proposition.  Separately, the reviewed
    source-result input must be the *same current opaque Lean atom* that
    generated that expansion.  Comparing an unqualified terminal such as
    ``WellOrdered`` would permit unrelated namespaces to cross-select.

    The generator already records a transparent definition chain for this
    case.  We require its final fully qualified declaration and reconstruct
    the visible application exactly.  An unqualified raw head is permitted
    only as the presentation of that final chain endpoint; it is never used to
    select a statement-match record.  The statement-match surface must then
    equal the reconstructed qualified expression byte-for-normalized-byte.
    """

    visible_candidates: list[str] = []
    raw_input = item.get("input")
    if isinstance(raw_input, Mapping) and str(raw_input.get("type") or "").strip():
        visible_candidates.append(_formula(raw_input["type"]))
    if str(item.get("binder_type") or "").strip():
        visible_candidates.append(_formula(item["binder_type"]))
    if len(set(visible_candidates)) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "raw definition antecedent must expose one visible opaque input surface"
        )
    visible = visible_candidates[0]
    alias = item.get("proposition_alias_expansion")
    if not isinstance(alias, Mapping) or not _formula_equal(
        alias.get("expanded_type"), expanded_proposition
    ):
        raise SourceDefinitionAntecedentRouteError(
            "raw definition antecedent lacks an exact transparent expansion"
        )
    raw_steps = alias.get("transparent_steps")
    if not isinstance(raw_steps, list) or not raw_steps:
        raise SourceDefinitionAntecedentRouteError(
            "raw definition antecedent has no transparent alias chain"
        )
    terminal_step = raw_steps[-1]
    final_declaration = (
        str(terminal_step.get("declaration") or "").strip()
        if isinstance(terminal_step, Mapping)
        else ""
    )
    if (
        not final_declaration
        or "." not in final_declaration
        or any(not piece for piece in final_declaration.split("."))
    ):
        raise SourceDefinitionAntecedentRouteError(
            "raw transparent alias chain has no fully qualified final declaration"
        )
    match = _QUALIFIED_LEAN_HEAD_RE.fullmatch(visible)
    if match is None:
        raise SourceDefinitionAntecedentRouteError(
            "raw visible opaque input is not a simple predicate application"
        )
    raw_head = match.group("head")
    raw_tail = match.group("tail")
    if "." in raw_head:
        if raw_head != final_declaration:
            raise SourceDefinitionAntecedentRouteError(
                "raw visible opaque input names a different qualified declaration"
            )
    elif raw_head != final_declaration.rsplit(".", 1)[-1]:
        raise SourceDefinitionAntecedentRouteError(
            "raw alias chain endpoint cannot reconstruct the visible opaque input"
        )
    return _formula(final_declaration + raw_tail), _canonical_digest(dict(alias))


def _raw_route_candidates(
    raw_audit: Mapping[str, Any],
) -> list[dict[str, Any]]:
    groups, errors = _raw_item_groups(raw_audit)
    if errors:
        raise SourceDefinitionAntecedentRouteError(
            "raw audit has malformed generated groups: " + ", ".join(sorted(errors)[:5])
        )
    candidates: list[dict[str, Any]] = []
    for storage_key, group in groups.items():
        if not isinstance(group, Mapping):
            continue
        raw_members = group.get("raw_members")
        try:
            pins = _full_member_pins(raw_members)
        except SourceDefinitionAntecedentRouteError:
            continue
        assert isinstance(raw_members, list)
        expanded_types: set[str] = set()
        associations: list[Mapping[str, Any]] = []
        signature_identities: set[tuple[str, str]] = set()
        for _section, item in raw_members:
            for field in ("expanded_input_type", "expanded_binder_type"):
                if str(item.get(field) or "").strip():
                    expanded_types.add(_formula(item[field]))
            alias = item.get("proposition_alias_expansion")
            if isinstance(alias, Mapping) and str(alias.get("expanded_type") or "").strip():
                expanded_types.add(_formula(alias["expanded_type"]))
            association = item.get("source_contract_association")
            if isinstance(association, Mapping):
                associations.append(association)
            raw_signatures = item.get("reviewed_elaborated_signature_identities")
            if isinstance(raw_signatures, list):
                for identity in raw_signatures:
                    if not isinstance(identity, Mapping):
                        continue
                    signature = _sha256(identity.get("elaborated_signature_sha256"))
                    declaration = str(
                        identity.get("qualified_declaration") or ""
                    ).strip()
                    if signature and _QUALIFIED_LEAN_HEAD_RE.fullmatch(declaration):
                        signature_identities.add((signature, declaration))
        if len(expanded_types) != 1 or len(associations) != len(raw_members):
            continue
        expanded_proposition = next(iter(expanded_types))
        try:
            visible_inputs = [
                _qualified_visible_input_surface(
                    item, expanded_proposition=expanded_proposition
                )
                for _section, item in raw_members
            ]
        except SourceDefinitionAntecedentRouteError:
            continue
        qualified_input_surfaces = {surface for surface, _alias_sha in visible_inputs}
        alias_chain_sha256s = {alias_sha for _surface, alias_sha in visible_inputs}
        if len(qualified_input_surfaces) != 1 or not alias_chain_sha256s:
            continue
        association_digests = {_canonical_digest(association) for association in associations}
        if len(association_digests) != 1 or len(signature_identities) != 1:
            continue
        association = associations[0]
        if (
            association.get("schema") != 2
            or str(association.get("association_mode") or "").strip()
            != "semantic_contract_group_member"
            or str(association.get("semantic_contract_member_role") or "").strip()
            != "direct_evidence"
            or not _sha256(association.get("association_sha256"))
            or not _sha256(association.get("semantic_association_sha256"))
        ):
            continue
        source_identities = association.get("source_item_identities")
        if not isinstance(source_identities, list) or len(source_identities) != 1:
            continue
        descriptor = group.get("descriptor")
        descriptor_sha = _sha256(group.get("descriptor_sha256"))
        if not isinstance(descriptor, Mapping) or not descriptor_sha or _canonical_digest(descriptor) != descriptor_sha:
            continue
        lemma_signature, lemma_declaration = next(iter(signature_identities))
        candidates.append(
            {
                "storage_judgment_key": str(storage_key),
                "raw_group_semantic_descriptor_sha256": descriptor_sha,
                "raw_group_semantic_descriptor": copy.deepcopy(dict(descriptor)),
                "full_member_pins": pins,
                "full_member_pins_sha256": _canonical_digest(pins),
                "expanded_proposition": expanded_proposition,
                "expanded_proposition_sha256": _formula_digest(expanded_proposition),
                "qualified_visible_input_surface": next(iter(qualified_input_surfaces)),
                "qualified_visible_input_surface_sha256": _formula_digest(
                    next(iter(qualified_input_surfaces))
                ),
                "transparent_alias_chain_sha256s": sorted(alias_chain_sha256s),
                "source_contract_association_sha256": _sha256(
                    association.get("association_sha256")
                ),
                "semantic_association_sha256": _sha256(
                    association.get("semantic_association_sha256")
                ),
                "source_identity": copy.deepcopy(dict(source_identities[0])),
                "lemma_elaborated_signature_sha256": lemma_signature,
                "lemma_qualified_declaration": lemma_declaration,
                "raw_members": raw_members,
            }
        )
    return candidates


def _semantic_route_projection(route: Mapping[str, Any]) -> dict[str, Any]:
    """Drop storage/navigation coordinates from the identity used for acceptance.

    Full source-map and association records remain mandatory while rebuilding a
    current route.  They are not retained in the receipt's semantic identity,
    because a map-key or declaration-route rename should not invalidate an
    unchanged source formula, source anchor, association *semantics*, or Lean
    signature.  The current rebuild still rejects a stale full record before
    reaching this projection.
    """

    route_copy = copy.deepcopy(dict(route))
    route_copy.pop("route_identity_sha256", None)
    raw = route_copy.get("raw_input")
    if isinstance(raw, Mapping):
        raw = dict(raw)
        raw.pop("storage_judgment_key", None)
        route_copy["raw_input"] = raw
    for side in ("lemma", "definition"):
        value = route_copy.get(side)
        if isinstance(value, Mapping):
            value = dict(value)
            value.pop("source_key", None)
            value.pop("statement_match_id", None)
            value.pop("source_contract_association_sha256", None)
            source_identity = value.get("source_identity")
            if isinstance(source_identity, Mapping):
                source_identity = dict(source_identity)
                source_identity.pop("source_key", None)
                source_identity.pop("source_map_item_sha256", None)
                contract = source_identity.get("semantic_contract")
                if isinstance(contract, Mapping):
                    contract = dict(contract)
                    contract.pop("evidence_declaration", None)
                    contract.pop("spec_declaration", None)
                    source_identity["semantic_contract"] = contract
                value["source_identity"] = source_identity
            endpoint = value.get("endpoint")
            if isinstance(endpoint, Mapping):
                endpoint = dict(endpoint)
                endpoint.pop("declared_evidence_declaration", None)
                endpoint.pop("declared_spec_declaration", None)
                value["endpoint"] = endpoint
            route_copy[side] = value
    return route_copy


def _route_identity(route: Mapping[str, Any]) -> str:
    return _canonical_digest(_semantic_route_projection(route))


def _route_from_raw_candidate(
    raw: Mapping[str, Any],
    *,
    paper: str,
    source_items: Mapping[str, Mapping[str, Any]],
    statement_records: Mapping[str, Mapping[str, Any]],
    paper_dir: Path,
    source_artifact_sha256: str,
    sealed_bridge_reuse: Mapping[str, Mapping[str, Any]] | None = None,
    sealed_definition_candidate_scopes: Mapping[
        str, tuple[Mapping[str, Any], ...]
    ] | None = None,
) -> dict[str, Any] | None:
    # Receipt-derived scopes are archival provenance only. They cannot order,
    # filter, or establish the current semantic candidate set until a
    # hermetic overlay-cache boundary exists.
    del sealed_definition_candidate_scopes
    try:
        lemma_key, lemma_item = _map_item_from_raw_identity(
            source_items, raw["source_identity"]
        )
        if str(lemma_item.get("source_kind") or "").strip().lower() not in SOURCE_RESULT_KINDS:
            return None
        lemma_contract = _semantic_contract(
            lemma_item.get("semantic_contract"), label="source result"
        )
        lemma_declaration = _qualified_declaration_coordinate(
            raw.get("lemma_qualified_declaration"),
            label="raw source-result declaration",
        )
        if lemma_contract["evidence_declaration"] != lemma_declaration:
            return None
        lemma_anchor = _anchor_for_result(
            lemma_item,
            paper_dir=paper_dir,
            source_artifact_sha256=source_artifact_sha256,
        )
        lemma_record_key, lemma_record = _statement_match_for_result(
            statement_records,
            lemma_item,
            expected_signature=str(raw["lemma_elaborated_signature_sha256"]),
        )
        lemma_input = _lemma_input_atom(
            lemma_record,
            qualified_visible_input_surface=str(
                raw["qualified_visible_input_surface"]
            ),
            lemma_location=str(lemma_item["source_location"]),
        )
        lemma_identity = _source_identity(lemma_key, lemma_item)
    except SourceDefinitionAntecedentRouteError:
        return None

    # First gather exactly the same cheap current definition evidence the
    # ordinary loop needs.  A sealed receipt can prioritize one semantic
    # candidate, but it must never remove another current candidate from the
    # uniqueness check: a newly added, independently valid definition for the
    # same raw formula makes the route ambiguous.
    definition_contexts: list[
        tuple[str, dict[str, Any], str, dict[str, Any], dict[str, Any], dict[str, Any]]
    ] = []
    for definition_key, definition_item in source_items.items():
        if (
            str(definition_item.get("source_kind") or "").strip().lower()
            != "definition"
            or definition_item.get("claim_bearing") is not True
        ):
            continue
        try:
            definition_contract = _semantic_contract(
                definition_item.get("semantic_contract"), label="source definition"
            )
            definition_declaration = _qualified_declaration_coordinate(
                definition_contract["evidence_declaration"],
                label="source-definition evidence declaration",
            )
            definition_anchor = _anchor_for_definition(
                definition_item,
                paper_dir=paper_dir,
                source_artifact_sha256=source_artifact_sha256,
            )
            definition_record_key, definition_record = _statement_match_for_definition(
                statement_records, definition_item
            )
            definition_identity = _source_identity(definition_key, definition_item)
        except SourceDefinitionAntecedentRouteError:
            continue
        definition_contexts.append(
            (
                definition_key,
                definition_item,
                definition_record_key,
                definition_record,
                definition_anchor,
                {
                    "definition_declaration": definition_declaration,
                    "source_identity": definition_identity,
                    "elaborated_signature_sha256": _sha256(
                        definition_record.get("lean_signature_sha256")
                    ),
                },
            )
        )
    definition_candidates: list[
        tuple[str, dict[str, Any], str, dict[str, Any], dict[str, Any], dict[str, Any]]
    ] = []
    for (
        definition_key,
        definition_item,
        definition_record_key,
        definition_record,
        definition_anchor,
        context,
    ) in definition_contexts:
        try:
            endpoint = _definition_iff_endpoint(
                definition_record,
                expanded_proposition=str(raw["expanded_proposition"]),
                paper=paper,
                paper_dir=paper_dir,
                lemma_declaration=lemma_declaration,
                lemma_signature_sha256=str(raw["lemma_elaborated_signature_sha256"]),
                lemma_input=lemma_input,
                definition_declaration=str(context["definition_declaration"]),
                sealed_bridge_reuse=sealed_bridge_reuse,
            )
        except SourceDefinitionAntecedentRouteError:
            continue
        definition_candidates.append(
            (
                definition_key,
                definition_item,
                definition_record_key,
                definition_record,
                definition_anchor,
                endpoint,
            )
        )
    if len(definition_candidates) != 1:
        return None
    (
        definition_key,
        definition_item,
        definition_record_key,
        definition_record,
        definition_anchor,
        endpoint,
    ) = definition_candidates[0]
    definition_identity = _source_identity(definition_key, definition_item)
    definition_contract = _semantic_contract(
        definition_item.get("semantic_contract"), label="source definition"
    )
    route: dict[str, Any] = {
        "schema": SCHEMA,
        "semantic_relation": "exact_definition_iff_expansion_is_source_result_input",
        "raw_input": {
            "storage_judgment_key": raw["storage_judgment_key"],
            "raw_group_semantic_descriptor_sha256": raw[
                "raw_group_semantic_descriptor_sha256"
            ],
            "raw_group_semantic_descriptor": raw["raw_group_semantic_descriptor"],
            "full_member_pins": raw["full_member_pins"],
            "full_member_pins_sha256": raw["full_member_pins_sha256"],
            "expanded_proposition_sha256": raw["expanded_proposition_sha256"],
            "lemma_qualified_declaration": raw["lemma_qualified_declaration"],
            "qualified_visible_input_surface_sha256": raw[
                "qualified_visible_input_surface_sha256"
            ],
            "transparent_alias_chain_sha256s": raw[
                "transparent_alias_chain_sha256s"
            ],
        },
        "lemma": {
            "source_key": lemma_key,
            "source_identity": lemma_identity,
            "source_anchor": lemma_anchor,
            "source_contract_association_sha256": raw[
                "source_contract_association_sha256"
            ],
            "semantic_association_sha256": raw["semantic_association_sha256"],
            "statement_match_id": lemma_record_key,
            "statement_match_sha256": _canonical_digest(lemma_record),
            "current_elaborated_declaration": lemma_declaration,
            "elaborated_signature_sha256": raw["lemma_elaborated_signature_sha256"],
            "input_atom": lemma_input,
        },
        "definition": {
            "source_key": definition_key,
            "source_identity": definition_identity,
            "source_anchor": definition_anchor,
            "statement_match_id": definition_record_key,
            "statement_match_sha256": _canonical_digest(definition_record),
            "elaborated_signature_sha256": _sha256(
                definition_record.get("lean_signature_sha256")
            ),
            "endpoint": {
                "declared_evidence_declaration": definition_contract[
                    "evidence_declaration"
                ],
                "declared_spec_declaration": definition_contract["spec_declaration"],
                **endpoint,
            },
        },
    }
    route["route_identity_sha256"] = _route_identity(route)
    return route


def build_source_definition_antecedent_receipt(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    statement_matches: Mapping[str, Any],
    sealed_bridge_reuse: Mapping[str, Mapping[str, Any]] | None = None,
    sealed_definition_candidate_scopes: Mapping[
        str, tuple[Mapping[str, Any], ...]
    ] | None = None,
    sealed_receipts: tuple[Mapping[str, Any], ...] | list[Mapping[str, Any]] = (),
) -> dict[str, Any]:
    """Build a current, deterministic receipt for every exact definition route."""

    # Prior receipt data remains readable for provenance/migration, but no
    # bridge result or candidate scope is reusable across processes until the
    # entire Lean elaboration closure is hermetically pinned.
    del sealed_bridge_reuse, sealed_definition_candidate_scopes, sealed_receipts

    if raw_audit.get("paper") not in {None, paper}:
        raise SourceDefinitionAntecedentRouteError("raw audit belongs to another paper")
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if not raw_digest:
        raise SourceDefinitionAntecedentRouteError("raw audit has no current aggregate digest")
    prompt = str(raw_audit.get("prompt_version") or "").strip()
    if prompt != SOURCE_RECORD_V10_PROMPT_VERSION:
        raise SourceDefinitionAntecedentRouteError("raw audit does not use the v10 prompt")
    source_artifact_path, source_artifact_sha = _source_artifact_context(
        statement_map, paper_dir=paper_dir
    )
    source_items = _source_items(statement_map)
    statement_records = _statement_match_items(statement_matches)
    routes = [
        route
        for raw in _raw_route_candidates(raw_audit)
        if (
            route := _route_from_raw_candidate(
                raw,
                paper=paper,
                source_items=source_items,
                statement_records=statement_records,
                paper_dir=paper_dir,
                source_artifact_sha256=source_artifact_sha,
                sealed_bridge_reuse=None,
                sealed_definition_candidate_scopes=None,
            )
        )
        is not None
    ]
    by_identity: dict[str, dict[str, Any]] = {}
    for route in routes:
        identity = str(route["route_identity_sha256"])
        if identity in by_identity:
            raise SourceDefinitionAntecedentRouteError(
                "two current routes have the same semantic identity"
            )
        by_identity[identity] = route
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "artifact_kind": ARTIFACT_KIND,
        "policy_version": POLICY_VERSION,
        "paper": paper,
        "source_record_audit_sha256": raw_digest,
        "source_record_prompt_version": prompt,
        "source_artifact_path": source_artifact_path,
        "source_artifact_sha256": source_artifact_sha,
        "routes": [by_identity[key] for key in sorted(by_identity)],
    }
    payload["receipt_sha256"] = _canonical_digest(payload)
    return payload


def current_source_definition_antecedent_route_keys(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    statement_matches: Mapping[str, Any],
    sealed_receipts: tuple[Mapping[str, Any], ...] | list[Mapping[str, Any]] = (),
) -> set[str]:
    """Return only current raw groups that require this exact route receipt.

    Consumers use this to distinguish ordinary complete-pin reuse from a
    direct-definition antecedent reissue. The set is derived from the same
    semantic reconstruction as the receipt builder; no storage key, theorem
    name, or predicate suffix is used to discover a route.
    """

    if sealed_receipts:
        # A materialized sidecar names a receipt for provenance, but validation
        # reconstructs it through a fresh current Lean overlay. No prior bridge
        # result is an input to route discovery or acceptance.
        routes: list[Mapping[str, Any]] = []
        for sealed_receipt in sealed_receipts:
            if not isinstance(sealed_receipt, Mapping):
                raise SourceDefinitionAntecedentRouteError(
                    "sealed route receipt candidate is not an object"
                )
            routes.extend(
                validate_source_definition_antecedent_receipt(
                    sealed_receipt,
                    paper=paper,
                    paper_dir=paper_dir,
                    raw_audit=raw_audit,
                    statement_map=statement_map,
                    statement_matches=statement_matches,
                ).values()
            )
    else:
        rebuilt = build_source_definition_antecedent_receipt(
            paper=paper,
            paper_dir=paper_dir,
            raw_audit=raw_audit,
            statement_map=statement_map,
            statement_matches=statement_matches,
        )
        routes = rebuilt["routes"]
    keys: set[str] = set()
    for route in routes:
        raw_input = route.get("raw_input") if isinstance(route, Mapping) else None
        if not isinstance(raw_input, Mapping):
            raise SourceDefinitionAntecedentRouteError(
                "rebuilt route has no raw input identity"
            )
        key = str(raw_input.get("storage_judgment_key") or "").strip()
        if not key:
            raise SourceDefinitionAntecedentRouteError(
                "rebuilt route has no current raw storage group"
            )
        keys.add(key)
    return keys


def validate_source_definition_antecedent_receipt(
    receipt: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    statement_matches: Mapping[str, Any],
    sealed_bridge_reuse: Mapping[str, Mapping[str, Any]] | None = None,
    sealed_definition_candidate_scopes: Mapping[
        str, tuple[Mapping[str, Any], ...]
    ] | None = None,
) -> dict[str, dict[str, Any]]:
    """Replay receipt semantics and return current routes by semantic identity.

    Current source-map keys, statement-match storage IDs, and raw sidecar keys
    are intentionally not equality inputs.  They may change only after the
    exact current semantic route independently reconstructs.
    """

    del sealed_bridge_reuse, sealed_definition_candidate_scopes

    if (
        receipt.get("schema") != SCHEMA
        or receipt.get("artifact_kind") != ARTIFACT_KIND
        or receipt.get("policy_version") != POLICY_VERSION
        or receipt.get("paper") != paper
    ):
        raise SourceDefinitionAntecedentRouteError("receipt has an unsupported identity")
    claimed_digest = _sha256(receipt.get("receipt_sha256"))
    unsigned = {key: value for key, value in receipt.items() if key != "receipt_sha256"}
    if not claimed_digest or claimed_digest != _canonical_digest(unsigned):
        raise SourceDefinitionAntecedentRouteError("receipt integrity digest does not match")
    expected = build_source_definition_antecedent_receipt(
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        statement_map=statement_map,
        statement_matches=statement_matches,
    )
    for field in (
        "source_record_audit_sha256",
        "source_record_prompt_version",
        "source_artifact_path",
        "source_artifact_sha256",
    ):
        if receipt.get(field) != expected.get(field):
            raise SourceDefinitionAntecedentRouteError(
                f"receipt has a stale current `{field}` pin"
            )
    supplied_routes = receipt.get("routes")
    if not isinstance(supplied_routes, list) or not supplied_routes:
        raise SourceDefinitionAntecedentRouteError("receipt has no routes")
    current_by_identity = {
        str(route["route_identity_sha256"]): route for route in expected["routes"]
    }
    validated: dict[str, dict[str, Any]] = {}
    for supplied in supplied_routes:
        if not isinstance(supplied, Mapping):
            raise SourceDefinitionAntecedentRouteError("receipt has a malformed route")
        identity = _sha256(supplied.get("route_identity_sha256"))
        if not identity or identity in validated:
            raise SourceDefinitionAntecedentRouteError("receipt has duplicate or unpinned routes")
        current = current_by_identity.get(identity)
        if current is None:
            raise SourceDefinitionAntecedentRouteError(
                "receipt route no longer reconstructs from current semantic evidence"
            )
        if canonical_digest_payload(_semantic_route_projection(supplied)) != canonical_digest_payload(
            _semantic_route_projection(current)
        ):
            raise SourceDefinitionAntecedentRouteError(
                "receipt route semantic projection differs from current evidence"
            )
        validated[identity] = current
    return validated


def _current_response_from_route(
    route: Mapping[str, Any],
    *,
    receipt_sha256: str,
    receipt_path: Path,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    validator: str,
    validated_at: str,
) -> dict[str, Any]:
    raw_input = route.get("raw_input")
    if not isinstance(raw_input, Mapping):
        raise SourceDefinitionAntecedentRouteError("route has no raw input")
    pins = raw_input.get("full_member_pins")
    if not isinstance(pins, list) or len(pins) < 1:
        raise SourceDefinitionAntecedentRouteError("route has no complete current member pins")
    raw_groups, errors = _raw_item_groups(raw_audit)
    if errors:
        raise SourceDefinitionAntecedentRouteError("raw audit has malformed generated groups")
    target_descriptor = _sha256(raw_input.get("raw_group_semantic_descriptor_sha256"))
    candidates = [
        group
        for group in raw_groups.values()
        if isinstance(group, Mapping)
        and _sha256(group.get("descriptor_sha256")) == target_descriptor
        and canonical_digest_payload(group.get("descriptor"))
        == canonical_digest_payload(raw_input.get("raw_group_semantic_descriptor"))
    ]
    if len(candidates) != 1:
        raise SourceDefinitionAntecedentRouteError(
            "route does not select exactly one current raw semantic group"
        )
    group = candidates[0]
    current_pins = _full_member_pins(group.get("raw_members"))
    if canonical_digest_payload(current_pins) != canonical_digest_payload(pins):
        raise SourceDefinitionAntecedentRouteError(
            "route full member pins no longer match the current raw group"
        )
    lemma = route.get("lemma")
    definition = route.get("definition")
    if not isinstance(lemma, Mapping) or not isinstance(definition, Mapping):
        raise SourceDefinitionAntecedentRouteError("route lacks source anchors")
    definition_anchor = definition.get("source_anchor")
    lemma_anchor = lemma.get("source_anchor")
    if not isinstance(definition_anchor, Mapping) or not isinstance(lemma_anchor, Mapping):
        raise SourceDefinitionAntecedentRouteError("route source anchors are malformed")
    source_location = (
        f"{definition_anchor['path']}:{definition_anchor['line_start']}-{definition_anchor['line_end']}; "
        f"{lemma_anchor['path']}:{lemma_anchor['line_start']}-{lemma_anchor['line_end']}"
    )
    response: dict[str, Any] = {
        "classification": "validated_source_assumption",
        "source_target_disposition": "literal_source_match",
        "reason": (
            "The current source theorem/lemma has this premise, and the current "
            "source definition's exact IFF expansion is the same expanded proposition. "
            "Both source anchors, source identities, association pins, elaborated "
            "signatures, and every current raw member were replayed; no declaration "
            "or binder name establishes the match."
        ),
        "source_location": source_location,
    }
    projected, projection_error = project_source_record_response_association_pins(
        group.get("raw_members"),
        response,
        judgment_key=raw_input.get("storage_judgment_key"),
        reject_existing=True,
        statement_map=statement_map,
    )
    if projection_error or projected is None:
        raise SourceDefinitionAntecedentRouteError(
            "could not project current source association pins: "
            + (projection_error or "unknown error")
        )
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if not raw_digest:
        raise SourceDefinitionAntecedentRouteError("raw audit lacks an aggregate digest")
    projected.update(
        {
            "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
            "validator": validator,
            "validated_at": validated_at,
            "source_record_audit_sha256": raw_digest,
            # The legacy single pin stays only for backward-compatible readers.
            # The complete list is the authoritative current proof for a group
            # with a boundary and a conclusion-dependency surface.
            "source_record_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            "source_record_item_sha256": current_pins[0]["source_record_item_sha256"],
            "source_record_item_sha256s": copy.deepcopy(current_pins),
            MATERIALIZATION_FIELD: {
                "schema": MATERIALIZATION_SCHEMA,
                "receipt_path": _paper_relative_path(receipt_path, paper_dir),
                "receipt_sha256": receipt_sha256,
                "route_identity_sha256": route["route_identity_sha256"],
                "full_member_pins_sha256": raw_input["full_member_pins_sha256"],
            },
        }
    )
    return projected


def validate_current_source_definition_antecedent_reissue_item(
    value: Mapping[str, Any],
    *,
    judgment_key: object,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    statement_matches: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate one materialized reissue before a loader grants source credit.

    This is the consumer-side authority boundary for this narrow transport.
    A current aggregate source-record hash is deliberately insufficient here:
    the item must replay its receipt, reconstruct its route from current raw
    members/source anchors/v10 records, and equal the deterministic response
    for that route.  A caller should accept the returned mapping only after
    this function succeeds; it must not fall back to ordinary aggregate
    freshness for an item carrying :data:`MATERIALIZATION_FIELD`.
    """

    if not isinstance(value, Mapping):
        raise SourceDefinitionAntecedentRouteError("reissued source-record item is not an object")
    marker = value.get(MATERIALIZATION_FIELD)
    if not isinstance(marker, Mapping):
        raise SourceDefinitionAntecedentRouteError("reissued source-record item has no route receipt")
    if marker.get("schema") != MATERIALIZATION_SCHEMA:
        raise SourceDefinitionAntecedentRouteError("reissued source-record item has an unsupported route schema")
    receipt_path = _safe_paper_path(
        paper_dir, marker.get("receipt_path"), label="reissued route receipt_path"
    )
    receipt = _read_json_object(receipt_path, label="reissued route receipt")
    receipt_sha = _sha256(marker.get("receipt_sha256"))
    if not receipt_sha or receipt_sha != _sha256(receipt.get("receipt_sha256")):
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item receipt digest does not match its receipt"
        )
    route_identity = _sha256(marker.get("route_identity_sha256"))
    if not route_identity:
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item has no route identity"
        )
    routes = validate_source_definition_antecedent_receipt(
        receipt,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        statement_map=statement_map,
        statement_matches=statement_matches,
    )
    route = routes.get(route_identity)
    if route is None:
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item route is not current"
        )
    raw_input = route.get("raw_input")
    if not isinstance(raw_input, Mapping) or str(
        raw_input.get("storage_judgment_key") or ""
    ).strip() != str(judgment_key or "").strip():
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item does not address this current raw group"
        )
    if marker.get("full_member_pins_sha256") != raw_input.get("full_member_pins_sha256"):
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item does not pin every current raw member"
        )
    validator = str(value.get("validator") or "").strip()
    validated_at = str(value.get("validated_at") or "").strip()
    if not validator or not validated_at:
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item lacks validator/timestamp provenance"
        )
    expected = _current_response_from_route(
        route,
        receipt_sha256=receipt_sha,
        receipt_path=receipt_path,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        statement_map=statement_map,
        validator=validator,
        validated_at=validated_at,
    )
    if dict(value) != expected:
        raise SourceDefinitionAntecedentRouteError(
            "reissued source-record item differs from the exact current route response"
        )
    return expected


def materialize_source_definition_antecedent_route(
    receipt: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    receipt_path: Path,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    statement_matches: Mapping[str, Any],
    validator: str,
    validated_at: str,
    route_identity_sha256: str | None = None,
) -> dict[str, Any]:
    """Return a sidecar with exactly one independently reissued current item."""

    validator = str(validator or "").strip()
    validated_at = str(validated_at or "").strip()
    if not validator or not validated_at:
        raise SourceDefinitionAntecedentRouteError(
            "materialization requires nonempty validator and validated_at"
        )
    routes = validate_source_definition_antecedent_receipt(
        receipt,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        statement_map=statement_map,
        statement_matches=statement_matches,
    )
    selected_identity = _sha256(route_identity_sha256)
    if selected_identity:
        route = routes.get(selected_identity)
        if route is None:
            raise SourceDefinitionAntecedentRouteError(
                "requested route identity is not present in the validated receipt"
            )
    elif len(routes) == 1:
        route = next(iter(routes.values()))
        selected_identity = str(route["route_identity_sha256"])
    else:
        raise SourceDefinitionAntecedentRouteError(
            "receipt has multiple routes; materialization requires route_identity_sha256"
        )
    if sidecar.get("schema") != 1 or sidecar.get("paper") not in {None, paper}:
        raise SourceDefinitionAntecedentRouteError("ordinary source-record sidecar is invalid")
    if str(sidecar.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        raise SourceDefinitionAntecedentRouteError("ordinary sidecar does not use the v10 prompt")
    raw_items = sidecar.get("items")
    if not isinstance(raw_items, Mapping):
        raise SourceDefinitionAntecedentRouteError("ordinary sidecar has no item ledger")
    raw_input = route.get("raw_input")
    if not isinstance(raw_input, Mapping):
        raise SourceDefinitionAntecedentRouteError("route raw input is malformed")
    storage_key = str(raw_input.get("storage_judgment_key") or "").strip()
    existing = raw_items.get(storage_key)
    if not isinstance(existing, Mapping):
        raise SourceDefinitionAntecedentRouteError(
            "route does not address an existing ordinary source-record item"
        )
    if str(existing.get("classification") or "").strip() != "validated_source_assumption":
        raise SourceDefinitionAntecedentRouteError(
            "materialization only reissues an existing validated source assumption"
        )
    if str(existing.get("source_target_disposition") or "").strip() != "literal_source_match":
        raise SourceDefinitionAntecedentRouteError(
            "materialization only reissues an existing literal-source match"
        )
    receipt_sha = _sha256(receipt.get("receipt_sha256"))
    if not receipt_sha:
        raise SourceDefinitionAntecedentRouteError("receipt has no integrity digest")
    current_response = _current_response_from_route(
        route,
        receipt_sha256=receipt_sha,
        receipt_path=receipt_path,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        statement_map=statement_map,
        validator=validator,
        validated_at=validated_at,
    )
    output = copy.deepcopy(dict(sidecar))
    output_items = copy.deepcopy(dict(raw_items))
    output_items[storage_key] = current_response
    output["items"] = output_items
    # Do not update top-level aggregate provenance: a sidecar can contain many
    # stale entries, and only this one has been reconstructed from the route.
    return output


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build or materialize a semantic direct-definition source antecedent "
            "receipt without rerunning source/Lean audits."
        )
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    def common(command: argparse.ArgumentParser) -> None:
        command.add_argument("--root", type=Path, default=ROOT)
        command.add_argument("--paper", required=True)
        command.add_argument("--raw-audit", type=Path)
        command.add_argument("--statement-map", type=Path)
        command.add_argument("--statement-matches", type=Path)

    build = subparsers.add_parser("build", help="build a receipt")
    common(build)
    build.add_argument("--out", type=Path, required=True)
    build.add_argument("--write", action="store_true")

    materialize = subparsers.add_parser(
        "materialize", help="reissue one existing ordinary sidecar item"
    )
    common(materialize)
    materialize.add_argument("--receipt", type=Path, required=True)
    materialize.add_argument("--sidecar", type=Path)
    materialize.add_argument("--out", type=Path, required=True)
    materialize.add_argument("--route-identity-sha256")
    materialize.add_argument("--validator", default="source-definition-antecedent-route-v1")
    materialize.add_argument("--validated-at", required=True)
    materialize.add_argument("--write", action="store_true")
    return parser.parse_args()


def _cli_paths(args: argparse.Namespace) -> tuple[Path, Path, Path, Path]:
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    raw = _safe_paper_path(
        paper_dir,
        args.raw_audit or Path("audit/source_record_audit.json"),
        label="--raw-audit",
    )
    statement_map = _safe_paper_path(
        paper_dir,
        args.statement_map or Path("audit/paper_statement_map.json"),
        label="--statement-map",
    )
    statement_matches = _safe_paper_path(
        paper_dir,
        args.statement_matches or Path("audit/statement_match_llm.json"),
        label="--statement-matches",
    )
    return paper_dir, raw, statement_map, statement_matches


def main() -> int:
    args = _parse_args()
    try:
        paper_dir, raw_path, map_path, matches_path = _cli_paths(args)
        raw = _read_json_object(raw_path, label="raw audit")
        statement_map = _read_json_object(map_path, label="statement map")
        statement_matches = _read_json_object(matches_path, label="statement matches")
        if args.command == "build":
            output_path = _safe_paper_path(paper_dir, args.out, label="--out")
            sealed_receipts: tuple[Mapping[str, Any], ...] = tuple()
            if output_path.is_file():
                try:
                    sealed_receipts = (
                        _read_json_object(output_path, label="existing route receipt"),
                    )
                except SourceDefinitionAntecedentRouteError:
                    # An existing output is optional cache material, never a
                    # source of route truth. A malformed prior file simply
                    # cannot save the focused overlay.
                    sealed_receipts = tuple()
            receipt = build_source_definition_antecedent_receipt(
                paper=args.paper,
                paper_dir=paper_dir,
                raw_audit=raw,
                statement_map=statement_map,
                statement_matches=statement_matches,
                sealed_receipts=sealed_receipts,
            )
            if args.write:
                _atomic_write(output_path, json.dumps(receipt, indent=2, sort_keys=True) + "\n")
                print(f"{args.paper}: wrote {len(receipt['routes'])} definition-antecedent routes to {output_path}")
            else:
                print(
                    f"{args.paper}: definition-antecedent receipt validates "
                    f"({len(receipt['routes'])} routes); rerun with --write"
                )
            return 0
        receipt_path = _safe_paper_path(paper_dir, args.receipt, label="--receipt")
        sidecar_path = _safe_paper_path(
            paper_dir,
            args.sidecar or Path("audit/source_record_match_llm.json"),
            label="--sidecar",
        )
        output_path = _safe_paper_path(paper_dir, args.out, label="--out")
        materialized = materialize_source_definition_antecedent_route(
            _read_json_object(receipt_path, label="receipt"),
            _read_json_object(sidecar_path, label="ordinary sidecar"),
            paper=args.paper,
            paper_dir=paper_dir,
            receipt_path=receipt_path,
            raw_audit=raw,
            statement_map=statement_map,
            statement_matches=statement_matches,
            validator=args.validator,
            validated_at=args.validated_at,
            route_identity_sha256=args.route_identity_sha256,
        )
        if args.write:
            _atomic_write(output_path, json.dumps(materialized, indent=2, sort_keys=True) + "\n")
            print(f"{args.paper}: wrote one reissued source-record item to {output_path}")
        else:
            print(
                f"{args.paper}: source-definition antecedent materialization validates; "
                "rerun with --write"
            )
        return 0
    except SourceDefinitionAntecedentRouteError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
