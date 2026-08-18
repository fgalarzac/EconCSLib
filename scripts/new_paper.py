#!/usr/bin/env python3
"""Create the standard EconCSLib paper-formalization scaffold.

The script performs the deterministic intake step for a new source paper:
create the citation-specific folder, cache the source PDF when possible,
extract a text cache with `pdftotext` when available, and write the required
README/DAG/MainTheorems/PaperInterface/status/formalization-plan/.gitignore files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import date
from pathlib import Path

try:
    from source_coverage_scope import SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_coverage_scope import SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
FOLDER_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
LEAN_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_NAMESPACE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
PLACEHOLDER_RE = re.compile(
    r"(?:\bTODO\b|\bTBD\b|\bplaceholder\b|\bto be (?:filled|refined|replaced)\b|"
    r"\[paper|\[source|<paper|<source)",
    re.IGNORECASE,
)
SOURCE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
SOURCE_TEXT_NORMALIZATION = "utf8-lf-v1"
INTAKE_SOURCE_IDENTITY = "source-location+normalized-statement-sha256-v1"
EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.IGNORECASE,
)
SOURCE_KINDS = {
    "lemma",
    "theorem",
    "proposition",
    "corollary",
    "claim",
    "runtime_claim",
}
LEAN_BREAKOUT_LINE_RE = re.compile(
    r"(?m)^\s*(?:#|@\[|import\b|namespace\b|section\b|end\b|open\b|export\b|"
    r"universe\b|variable\b|include\b|omit\b|attribute\b|set_option\b|"
    r"private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|abbrev\b|"
    r"axiom\b|opaque\b|constant\b|structure\b|class\b|inductive\b|instance\b|"
    r"example\b|where\b|deriving\b)",
)
LEAN_RENDERED_DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|opaque|constant|structure|class|inductive|"
    r"instance|example)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
SCAFFOLD_META_SENTINEL = "ECONCS_SCAFFOLD_TARGET_OK:"
SOURCE_RECORD_PROMPT_VERSION = "source-record-v10-semantic-conclusion-boundary-contract"
OPERATIONAL_COMPLEXITY_REVIEW_VERSION = (
    "operational-complexity-review-v1-transitive-work-accounting"
)
LEGACY_FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v2-shape-action-witness-count-execution"
)
FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v3-shape-action-witness-count-generic-execution"
)
FIDELITY_EXECUTION_SCOPE_FIELDS = (
    "source_input_scope",
    "lean_input_scope",
    "source_state_transition_scope",
    "lean_state_transition_scope",
    "source_termination_scope",
    "lean_termination_scope",
    "source_numeric_representation",
    "lean_numeric_representation",
    "source_cost_scope",
    "lean_cost_scope",
    "global_claim_bridge_basis",
)
FIDELITY_RISK_DIMENSIONS = {
    "output_shape",
    "adversarial_action_space",
    "coherent_extrema_witness",
    "cardinality_fibers",
    "execution_claim_scope",
}
FIDELITY_RISK_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
    "uncertain",
}
SEMANTIC_MODEL_DIMENSION_ORDER = (
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
)
SEMANTIC_MODEL_REVIEW_SCHEMA = 2
COHERENT_EXTREMA_WITNESS_STATUSES = {
    "not_required",
    "same_coherent_witness",
    "proved_jointly_realizable",
    "separate_witnesses_only",
    "missing",
}
COUNTING_SEMANTICS = {
    "syntactic_family_cardinality",
    "nonempty_realized_fibers",
    "other",
}
SURJECTIVITY_STATUSES = {
    "not_required",
    "definitionally_surjective",
    "proved_surjective",
    "missing",
}


@dataclass(frozen=True)
class StatementTarget:
    """One source-pinned proposition transcription to seed as an honest proof hole."""

    source_item: str
    source_location: str
    source_statement: str
    lean_name: str
    lean_type: str
    source_kind: str
    kind: str = "theorem"


@dataclass(frozen=True)
class StatementSpec:
    """Pinned source artifact plus exact source-to-Lean target routing."""

    targets: list[StatementTarget]
    source_artifact_path: Path
    source_artifact_sha256: str
    source_version: str


def statement_spec_name(target: StatementTarget) -> str:
    """Return the transparent proposition name paired with one proof target."""

    return f"{target.lean_name}Spec"


def statement_first_review_names(targets: list[StatementTarget]) -> list[str]:
    """Return one expanded semantic target per source claim, in source order."""

    return [statement_spec_name(target) for target in targets]


def statement_first_spec_proof_routes(targets: list[StatementTarget]) -> dict[str, str]:
    """Return the exact Prop-spec to theorem/lemma routes for later Meta checks."""

    return {statement_spec_name(target): target.lean_name for target in targets}


def statement_first_semantic_contract_template(
    target: StatementTarget,
) -> dict[str, str]:
    """Return an inactive exact-contract route for one audited source target.

    This is deliberately *not* named ``semantic_contract``.  The source text
    still needs an independent source-atom inventory, and the theorem body is
    still a proof hole. At closeout the route must also satisfy the v11
    source-to-Spec correspondence and full Lean-closure audit; these four
    routing fields never supply that evidence themselves.
    """

    return {
        "spec_declaration": statement_spec_name(target),
        "evidence_declaration": target.lean_name,
        "evidence_mode": "proves",
        "semantic_shape": "plain",
    }


def _required_target_text(raw: object, field: str, index: int) -> str:
    value = raw.strip() if isinstance(raw, str) else ""
    if not value:
        raise ValueError(f"statement target {index} has no `{field}`")
    if PLACEHOLDER_RE.search(value):
        raise ValueError(
            f"statement target {index} `{field}` is still placeholder text"
        )
    return value


def load_statement_spec(path: Path) -> StatementSpec:
    """Load targets only after verifying their pinned source artifact bytes."""

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ValueError(
            f"could not read statement target spec `{path}`: {exc}"
        ) from exc
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"invalid JSON in statement target spec `{path}`: {exc}"
        ) from exc
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise ValueError("statement target spec must be an object with `schema: 1`")
    source_artifact_raw = _required_target_text(
        payload.get("source_artifact_path"), "source_artifact_path", 0
    )
    source_artifact_path = Path(source_artifact_raw).expanduser()
    if not source_artifact_path.is_absolute():
        source_artifact_path = (path.parent / source_artifact_path).resolve()
    if not source_artifact_path.is_file():
        raise ValueError(
            f"statement target spec source artifact does not exist: `{source_artifact_path}`"
        )
    recorded_source_sha256 = (
        str(payload.get("source_artifact_sha256") or "").strip().lower()
    )
    if not SOURCE_SHA256_RE.fullmatch(recorded_source_sha256):
        raise ValueError(
            "statement target spec needs a 64-hex `source_artifact_sha256`"
        )
    actual_source_sha256 = hashlib.sha256(source_artifact_path.read_bytes()).hexdigest()
    if recorded_source_sha256 != actual_source_sha256:
        raise ValueError(
            "statement target spec source_artifact_sha256 does not match source artifact bytes"
        )
    source_version = _required_target_text(
        payload.get("source_version"), "source_version", 0
    )
    raw_targets = payload.get("targets")
    if not isinstance(raw_targets, list) or not raw_targets:
        raise ValueError("statement target spec must contain a nonempty `targets` list")

    targets: list[StatementTarget] = []
    seen_names: set[str] = set()
    for index, raw in enumerate(raw_targets, start=1):
        if not isinstance(raw, dict):
            raise ValueError(f"statement target {index} is not an object")
        kind = str(raw.get("kind") or "theorem").strip()
        if kind not in {"theorem", "lemma"}:
            raise ValueError(
                f"statement target {index} has unsupported kind `{kind}`; use theorem or lemma"
            )
        lean_name = _required_target_text(raw.get("lean_name"), "lean_name", index)
        if not LEAN_NAME_RE.fullmatch(lean_name):
            raise ValueError(
                f"statement target {index} has unsafe Lean name `{lean_name}`; "
                "use an unqualified identifier"
            )
        if lean_name in seen_names:
            raise ValueError(f"duplicate statement target Lean name `{lean_name}`")
        seen_names.add(lean_name)
        lean_type = _required_target_text(raw.get("lean_type"), "lean_type", index)
        if lean_type in {"True", "Prop"}:
            raise ValueError(
                f"statement target {index} uses the bare placeholder type `{lean_type}`"
            )
        _validate_lean_type_fragment(lean_type, index)
        source_statement = _required_target_text(
            raw.get("source_statement"), "source_statement", index
        )
        if "/-" in source_statement or "-/" in source_statement:
            raise ValueError(
                f"statement target {index} source statement contains a Lean comment delimiter"
            )
        source_item = _required_target_text(
            raw.get("source_item"), "source_item", index
        )
        source_location = _required_target_text(
            raw.get("source_location"), "source_location", index
        )
        if any(
            token in value
            for value in (source_item, source_location)
            for token in ("/-", "-/")
        ):
            raise ValueError(
                f"statement target {index} source metadata contains a Lean comment delimiter"
            )
        if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
            raise ValueError(f"statement target {index} has no exact source locator")
        source_kind = _required_target_text(
            raw.get("source_kind"), "source_kind", index
        ).lower()
        if source_kind not in SOURCE_KINDS:
            raise ValueError(
                f"statement target {index} has unsupported source_kind `{source_kind}`"
            )
        targets.append(
            StatementTarget(
                source_item=source_item,
                source_location=source_location,
                source_statement=source_statement,
                lean_name=lean_name,
                lean_type=lean_type,
                source_kind=source_kind,
                kind=kind,
            )
        )
    generated_names: dict[str, str] = {}
    for target in targets:
        for declaration_name, role in (
            (statement_spec_name(target), "generated proposition specification"),
            (target.lean_name, "proof declaration"),
        ):
            previous = generated_names.get(declaration_name)
            if previous is not None:
                raise ValueError(
                    "statement target names collide after generating `...Spec`: "
                    f"`{declaration_name}` would be both {previous} and {role}"
                )
            generated_names[declaration_name] = role

    return StatementSpec(
        targets=targets,
        source_artifact_path=source_artifact_path,
        source_artifact_sha256=actual_source_sha256,
        source_version=source_version,
    )


def load_statement_targets(path: Path) -> list[StatementTarget]:
    """Compatibility wrapper for callers that only need target declarations."""

    return load_statement_spec(path).targets


def title_case_slug(text: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", text) if part]
    if not parts:
        return "Paper"
    return "".join(part[:1].upper() + part[1:] for part in parts)


def derive_folder(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    stem = Path(parsed.path).stem or parsed.netloc or "paper"
    stem = re.sub(r"^abs$", "", stem)
    slug = title_case_slug(stem)
    return f"Draft{date.today().year % 100:02d}{slug}"


def lean_namespace(folder: str) -> str:
    namespace = re.sub(r"[^A-Za-z0-9_]", "", folder)
    if not namespace or namespace[0].isdigit():
        namespace = f"Paper{namespace}"
    return namespace


def validate_scaffold_cli_inputs(
    args: argparse.Namespace, folder: str, namespace: str
) -> None:
    """Reject path and Lean-source injection through scaffold CLI metadata."""

    if Path(folder).name != folder or not FOLDER_RE.fullmatch(folder):
        raise ValueError(
            "--folder must be one safe path component matching "
            "[AuthorInitials][2DigitYear][Descriptor]"
        )
    if not LEAN_NAMESPACE_RE.fullmatch(namespace):
        raise ValueError("--namespace must be a qualified Lean identifier")
    title = str(args.title or "")
    if any(token in title for token in ("\n", "\r", "/-", "-/")):
        raise ValueError(
            "--title must be one line and may not contain Lean comment delimiters"
        )


def normalize_pdf_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    if parsed.netloc.endswith("arxiv.org"):
        if parsed.path.startswith("/abs/"):
            arxiv_id = parsed.path.removeprefix("/abs/")
            return urllib.parse.urlunparse(
                parsed._replace(path=f"/pdf/{arxiv_id}.pdf", query="")
            )
        if parsed.path.startswith("/pdf/") and not parsed.path.endswith(".pdf"):
            return urllib.parse.urlunparse(
                parsed._replace(path=f"{parsed.path}.pdf", query="")
            )
    return url


def audited_source_filename(source: Path) -> str:
    """Return a stable paper-local name while preserving the artifact format."""

    suffixes = "".join(source.suffixes).lower()
    if not suffixes or not re.fullmatch(r"(?:\.[a-z0-9]+)+", suffixes):
        suffixes = ".bin"
    return f"source-audited{suffixes}"


def _validate_lean_type_fragment(value: str, index: int) -> None:
    """Reject syntax that can escape the generated theorem's type position."""

    if any(token in value for token in ("--", "/-", "-/")):
        raise ValueError(
            f"statement target {index} Lean type may not contain Lean comments"
        )
    if LEAN_BREAKOUT_LINE_RE.search(value):
        raise ValueError(
            f"statement target {index} Lean type contains a top-level command or declaration"
        )

    stack: list[str] = []
    matching = {")": "(", "]": "[", "}": "{"}
    in_string = False
    escaped = False
    line_start = 0
    cursor = 0
    while cursor < len(value):
        char = value[cursor]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            cursor += 1
            continue
        if char == '"':
            in_string = True
            cursor += 1
            continue
        if char in "([{":
            stack.append(char)
        elif char in ")]}":
            if not stack or stack.pop() != matching[char]:
                raise ValueError(
                    f"statement target {index} Lean type has unbalanced delimiters"
                )
        elif char == "\n":
            line_start = cursor + 1
        elif value.startswith(":=", cursor) and not stack:
            line_prefix = value[line_start:cursor].strip()
            if not re.match(r"^let(?:\s+rec)?\b", line_prefix):
                raise ValueError(
                    f"statement target {index} Lean type contains a top-level `:=` breakout"
                )
            cursor += 1
        cursor += 1
    if in_string or stack:
        raise ValueError(
            f"statement target {index} Lean type has an unterminated literal or delimiter"
        )


def _mask_lean_comments_and_strings(source: str) -> str:
    """Mask non-code while preserving offsets/newlines for scaffold assertions."""

    out = list(source)
    cursor = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while cursor < len(source):
        if in_line_comment:
            if source[cursor] == "\n":
                in_line_comment = False
            else:
                out[cursor] = " "
            cursor += 1
            continue
        if block_depth:
            if source.startswith("/-", cursor):
                out[cursor] = out[cursor + 1] = " "
                block_depth += 1
                cursor += 2
                continue
            if source.startswith("-/", cursor):
                out[cursor] = out[cursor + 1] = " "
                block_depth -= 1
                cursor += 2
                continue
            if source[cursor] != "\n":
                out[cursor] = " "
            cursor += 1
            continue
        if in_string:
            if source[cursor] != "\n":
                out[cursor] = " "
            if escaped:
                escaped = False
            elif source[cursor] == "\\":
                escaped = True
            elif source[cursor] == '"':
                in_string = False
            cursor += 1
            continue
        if source.startswith("--", cursor):
            out[cursor] = out[cursor + 1] = " "
            in_line_comment = True
            cursor += 2
            continue
        if source.startswith("/-", cursor):
            out[cursor] = out[cursor + 1] = " "
            block_depth = 1
            cursor += 2
            continue
        if source[cursor] == '"':
            out[cursor] = " "
            in_string = True
        cursor += 1
    if block_depth or in_string:
        raise ValueError(
            "rendered statement interface has an unterminated comment or string"
        )
    return "".join(out)


def validate_rendered_statement_interface(
    namespace: str,
    targets: list[StatementTarget],
    rendered: str,
    timeout_seconds: int = 120,
) -> None:
    """Statically partition, then Lean-check the human semantic surface."""

    masked = _mask_lean_comments_and_strings(rendered)
    declarations = list(LEAN_RENDERED_DECL_RE.finditer(masked))
    actual = [(match.group(1), match.group(2)) for match in declarations]
    expected = [("def", statement_spec_name(target)) for target in targets]
    if actual != expected:
        raise ValueError(
            "rendered statement interface contains declarations outside the requested targets"
        )
    end_marker = f"\n\nend {namespace}"
    namespace_end = masked.rfind(end_marker)
    if namespace_end < 0:
        raise ValueError(
            "rendered statement interface has no expected namespace terminator"
        )

    def normalized_code(text: str) -> str:
        return re.sub(r"\s+", " ", text).strip()

    for target_index, target in enumerate(targets):
        spec_declaration = declarations[target_index]
        spec_end = (
            declarations[target_index + 1].start()
            if target_index + 1 < len(declarations)
            else namespace_end
        )
        spec_block = masked[spec_declaration.start() : spec_end].strip()
        expected_spec = (
            f"def {statement_spec_name(target)} : Prop := {target.lean_type}"
        )
        if normalized_code(spec_block) != normalized_code(expected_spec):
            raise ValueError(
                f"rendered target `{target.lean_name}` does not have the exact generated "
                "transparent `...Spec : Prop` declaration"
            )

    start_marker = f"namespace {namespace}\n\n"
    payload_start = rendered.find(start_marker)
    payload_end = rendered.rfind(end_marker)
    if payload_start < 0 or payload_end < 0:
        raise ValueError("could not isolate rendered statement declarations")
    declarations_source = rendered[payload_start + len(start_marker) : payload_end]
    meta_helper = r"""
open Lean Meta Elab Command
    syntax "#assert_scaffold_spec " str : command
    elab_rules : command
  | `(#assert_scaffold_spec $spec:str) => do
      let specName := spec.getString.toName
      let specInfo ← liftTermElabM (getConstInfo specName)
      match specInfo with
      | .defnInfo definitionInfo =>
          let isProposition ← liftTermElabM (isProp definitionInfo.value)
          unless isProposition do
            throwError "scaffold specification is not Prop-valued"
          if definitionInfo.value.hasSorry then
            throwError "scaffold specification contains sorryAx"
      | _ =>
          throwError "scaffold specification is not a transparent definition"
      IO.println s!"ECONCS_SCAFFOLD_TARGET_OK:{specName}"
"""
    commands = "\n".join(
        "#assert_scaffold_spec "
        f"{json.dumps(f'{namespace}.{statement_spec_name(target)}')}"
        for target in targets
    )
    validation_import = "import EconCSLib\n\n" if targets else "import Lean\n\n"
    validation_source = (
        validation_import
        + f"namespace {namespace}\n\n{declarations_source}\n\nend {namespace}\n\n"
        f"{meta_helper}\n{commands}\n"
    )
    project_root = Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory() as temp_dir:
        validation_path = Path(temp_dir) / "statement_scaffold_validation.lean"
        validation_path.write_text(validation_source, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(validation_path)],
                cwd=project_root,
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise ValueError(
                f"Lean could not validate rendered statement targets: {exc}"
            ) from exc
    if proc.returncode != 0:
        details = (proc.stdout or proc.stderr).strip().splitlines()
        excerpt = " ".join(details[:4])[:800]
        raise ValueError(
            "Lean rejected the rendered statement targets"
            + (f": {excerpt}" if excerpt else "")
        )
    reported = {
        line.split(SCAFFOLD_META_SENTINEL, 1)[1].strip()
        for line in proc.stdout.splitlines()
        if SCAFFOLD_META_SENTINEL in line
    }
    expected_names = {f"{namespace}.{statement_spec_name(target)}" for target in targets}
    if reported != expected_names:
        raise ValueError(
            "Lean did not validate exactly the requested statement targets"
        )


def validate_rendered_proof_interface(
    namespace: str,
    targets: list[StatementTarget],
    rendered: str,
) -> None:
    """Require one exact-type draft proof endpoint outside the human interface."""

    masked = _mask_lean_comments_and_strings(rendered)
    declarations = list(LEAN_RENDERED_DECL_RE.finditer(masked))
    actual = [(match.group(1), match.group(2)) for match in declarations]
    expected = [(target.kind, target.lean_name) for target in targets]
    if actual != expected:
        raise ValueError(
            "rendered proof interface contains declarations outside the requested targets"
        )
    end_marker = f"\n\nend {namespace}"
    namespace_end = masked.rfind(end_marker)
    if namespace_end < 0:
        raise ValueError("rendered proof interface has no expected namespace terminator")

    def normalized_code(text: str) -> str:
        return re.sub(r"\s+", " ", text).strip()

    for index, target in enumerate(targets):
        declaration = declarations[index]
        declaration_end = (
            declarations[index + 1].start()
            if index + 1 < len(declarations)
            else namespace_end
        )
        block = masked[declaration.start() : declaration_end].strip()
        expected_block = (
            f"{target.kind} {target.lean_name} : "
            f"{statement_spec_name(target)} := by sorry"
        )
        if normalized_code(block) != normalized_code(expected_block):
            raise ValueError(
                f"rendered proof endpoint `{target.lean_name}` does not have the generated "
                "`...Spec := by sorry` proof body"
            )


def write_file(path: Path, contents: str, force: bool) -> None:
    if path.exists() and not force:
        print(f"skip existing {path.relative_to(ROOT)}")
        return
    path.write_text(contents, encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


def refresh_review_cache(folder: str) -> None:
    """Run the review metadata bootstrap for a fresh paper scaffold."""

    cmd = [
        "python3",
        str(ROOT / "scripts" / "review_dashboard.py"),
        "--paper",
        folder,
        "--refresh-cache",
    ]
    try:
        proc = subprocess.run(
            cmd, cwd=str(ROOT), check=False, capture_output=True, text=True
        )
    except OSError as exc:
        print(f"warning: could not refresh review cache for {folder}: {exc}")
        return
    if proc.returncode != 0:
        if proc.stdout:
            print(proc.stdout.strip())
        if proc.stderr:
            print(proc.stderr.strip())
        print(f"warning: review cache refresh failed for {folder}")


def synchronize_scaffold_readme(folder: str) -> bool:
    """Render the fresh README through the canonical paper-status projection."""

    cmd = [
        sys.executable,
        str(Path(__file__).resolve().with_name("sync_paper_status.py")),
        "--repo",
        str(ROOT),
        "--paper",
        folder,
    ]
    try:
        proc = subprocess.run(
            cmd, cwd=str(ROOT), check=False, capture_output=True, text=True
        )
    except OSError as exc:
        print(f"error: could not synchronize scaffold README for {folder}: {exc}", file=sys.stderr)
        return False
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        print(
            f"error: could not synchronize scaffold README for {folder}: {detail}",
            file=sys.stderr,
        )
        return False
    if proc.stdout:
        print(proc.stdout.strip())
    return True


def download_pdf(url: str, target: Path, force: bool) -> bool:
    if target.exists() and not force:
        print(f"skip existing {target.relative_to(ROOT)}")
        return True
    try:
        request = urllib.request.Request(
            normalize_pdf_url(url),
            headers={"User-Agent": "EconCSLib paper intake"},
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
        target.write_bytes(data)
        print(f"downloaded {target.relative_to(ROOT)}")
        return True
    except Exception as exc:  # noqa: BLE001 - intake should report and continue
        print(f"warning: could not download PDF from {url}: {exc}", file=sys.stderr)
        return False


def extract_text(pdf: Path, txt: Path, force: bool) -> bool:
    """Run pdftotext and report whether this call wrote the text artifact."""

    if txt.exists() and not force:
        print(f"skip existing {txt.relative_to(ROOT)}")
        return False
    if not pdf.exists():
        print(
            f"warning: no PDF at {pdf.relative_to(ROOT)}; skipping text extraction",
            file=sys.stderr,
        )
        return False
    if shutil.which("pdftotext") is None:
        print(
            "warning: `pdftotext` not found; skipping text extraction", file=sys.stderr
        )
        return False
    subprocess.run(["pdftotext", str(pdf), str(txt)], cwd=ROOT, check=True)
    print(f"extracted {txt.relative_to(ROOT)}")
    return True


def normalized_source_text_receipt(
    txt: Path,
    *,
    source_artifact_path: str,
    source_artifact_sha256: str,
) -> dict[str, object] | None:
    """Normalize extracted PDF text and bind it to its exact source artifact."""

    try:
        raw = txt.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        print(
            f"warning: could not normalize extracted source text at {txt}: {exc}",
            file=sys.stderr,
        )
        return None
    normalized = text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
    try:
        if raw != normalized:
            txt.write_bytes(normalized)
    except OSError as exc:
        print(
            f"warning: could not write normalized source text at {txt}: {exc}",
            file=sys.stderr,
        )
        return None
    return {
        "schema": 1,
        "path": str(txt.relative_to(ROOT)),
        "sha256": hashlib.sha256(normalized).hexdigest(),
        "normalization": SOURCE_TEXT_NORMALIZATION,
        "extraction": {
            "schema": 1,
            "source_artifact_path": source_artifact_path,
            "source_artifact_sha256": source_artifact_sha256,
            "tool": "pdftotext",
            "options": [],
        },
    }


def readme_text(
    args: argparse.Namespace,
    folder: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    official_url = args.official_url or args.url
    pdf_url = normalize_pdf_url(args.pdf_url or args.url)
    theorem_rows = "\n".join(
        f"| {target.source_item} ({target.source_location}) | "
        f"`{statement_spec_name(target)}` -> `{target.lean_name}` | "
        f"statement specification + proof stub | `PaperInterface.lean` | "
        "The transparent `...Spec : Prop` is the statement-audit target; the proof "
        "body is `by sorry`; raw-source-to-expanded-Spec judgment and premise provenance pending |"
        for target in targets
    )
    if not theorem_rows:
        theorem_rows = (
            "| No source-pinned targets supplied | `none` | not started | `none` | "
            "Do not add a generic `True` theorem; extract exact source statements first |"
        )
    return f"""# {title}

## Source Version

- Paper: *{title}*
- Authors: {authors}
- Version formalized: {version}
- Official URL: {official_url}
- Public PDF: {pdf_url}

Without a statement spec, a downloaded PDF is cached as `source.pdf` and ignored
by Git. A statement spec's SHA-256-verified source bytes are copied to a stable
paper-local `source-audited.*` path recorded in `audit/paper_statement_map.json`.
These artifacts are ignored by default. Unignore one only after an explicit
redistribution-rights review; machines without the private bytes must leave the
source-evidence gate unresolved rather than accepting the digest alone.
The extracted text cache is `source.txt` when `pdftotext` succeeds, and is also
ignored by Git in public workspaces unless redistribution rights have been
checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `{folder}/MainTheorems.lean`
- Human-facing theorem file: `{folder}/PaperInterface.lean`
- Machine-readable status source: `{folder}/status.json`
- Private outside-Lean proof plan: `{folder}/docs/FORMALIZATION_PLAN.md`
- Final validation report: `{folder}/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `{folder}/docs/DependencyDAG.tex`
- Rendered DAG: `{folder}/docs/DependencyDAG.pdf`
- LLM/source audit sidecars: `{folder}/audit/*.json`

`PaperInterface.lean` should be readable on its own: expose source formulas,
transparent statement specifications, and theorem/lemma proof routes there,
with short closed proofs that call into `MainTheorems.lean`. Do not mark a row
`formalized` unless the Lean declaration is closed and the remaining assumptions
cell is `None`.
Keep the dashboard surface curated but complete for source-labelled formal
material: definitions, formulas, propositions, theorems/corollaries, named
claims, and main-text lemmas that a reviewer or LLM-as-judge should inspect.
Do not omit source-visible named material merely to keep the dashboard compact.
Appendix theorems/corollaries should be represented; appendix lemmas are a
judgment call, but if they carry paper-facing mathematical content needed for
the formalized claim, expose review-legible rows rather than hiding them in a
broad support bundle. Catalog unnumbered prose assertions separately. They are
claim-bearing but, under the standing user-approved scope policy, are not
independent theorem targets unless explicitly opted in; retain exact source
anchors and a `user_approved_scope_exclusion` record rather than silently
omitting them or using Lean declaration names to decide scope.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that still depend on an
external theorem, certificate, or proof boundary, and should name that boundary
in the final column rather than using `conditional` as a separate status label.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the target-relevant part of
`docs/FORMALIZATION_PLAN.md`'s `Initial Outside-Lean Paper Audit` section. Read
the source closely enough to establish the current source-shaped target,
visible assumptions, formula risks, and likely proof seam. This is a compact
source-target setup gate, not a reason to delay an actionable proof for a full
DAG, status/report refresh, or exploratory work. Alert the user early about a
material source defect or missing assumption.
Before drafting Lean, independently inventory every material source atom from
the exact pinned source quote bytes. The inventory is source-side work: do not
derive it from theorem, binder, field, function, or source-map names. After that
inventory and the first compact `PaperInterface.lean` statement skeleton exist,
give every in-scope theorem/formula claim one transparent
`<name>Spec : Prop := <complete source-shaped statement>` in
`PaperInterface.lean`, with its separate
`theorem/lemma <name> : <name>Spec := by sorry` endpoint in
`ProofInterface.lean`. Audit the specification, not the theorem name; Lean
Meta must later confirm that the proof declaration has exactly that type. Do
not put a desired conclusion in `Assumptions.lean`, a record field, or a
helper theorem to avoid the hole. `scripts/new_paper.py` accepts these targets
through `--statement-spec`; without that source-pinned input it intentionally
generates an empty interface rather than a fake `True` target. Audit each
skeleton row's statement and premise provenance before
treating it as a source-faithful target; perform broader source-record and
report work at the next material audit boundary. Then run the statement
target-setting pass:
populate
`audit/lean_to_tex_llm.json`, populate `audit/statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper {folder} --statement-precheck`.
Also populate `audit/paper_statement_map.json` for the normal source surface,
then run the paper-level coverage pass and save `audit/paper_coverage_llm.json`.
Normal scope is source-named theory: visibly numbered or named definitions,
results, claims, formulas/equations, algorithms, assumptions/model conditions,
and named appendix items. Figures, captions, tables, numerical examples,
simulations, empirical material, and ordinary prose need an explicit deep-paper
audit; map keys and Lean names never decide scope. This source-to-row accounting
is separate from the row-local statement judge.
For a source-game theorem with a best-response/equilibrium comparison over
feasible actions and a posterior, conditional expectation, belief, or
observation-contingent payoff, add a byte-pinned
`semantic_context_requirements` entry of kind
`strategic_observation_totality`. The v10 audit will then require a
source/signature-bound review of zero-probability/off-path observation branches,
the source conditioning population, any selected sequential action history, event
measurability/null handling, and every declared conditionalization mode, including
any a.e. RCD/disintegration fibre/base scope.
Do not call a Lean default conditional value source-faithful unless the source
itself totalizes it or explicitly removes that branch/action from the
equilibrium comparison.
For any source row that asserts a conditional expectation, Bayesian/PBO belief,
or conditional law, add a byte-pinned `semantic_context_requirements` entry of
kind `conditioning_information`. Its contract must enumerate the source
observed components, ordered action-selection stages, raw-vs-selected law
population, and positive-event/pointwise/a.e. conditionalization scope. The
source-record review will require an exact source/signature-bound Lean-side
comparison for each component and stage; a raw posterior, coarser observed map,
or pointwise reading of an a.e. RCD is not a direct source match.
For a source model whose stated primitives are meant to imply a process, cycle,
execution trace, or conditional-law conclusion, add a byte-pinned
`semantic_context_requirements` entry of kind `source_model_derivation`. Its
schema-2 contract must enumerate the source primitive components and the derived
conclusion, with a separate exact `source_location` and byte-pinned
`source_anchor_evidence` for every component and for the conclusion itself. The
source-record review will require a current source/signature-bound mapping for
every primitive and a checked Lean derivation route. If the generated expanded
surface structurally detects a caller-supplied model-construction package, the
current generic auditor is deliberately fail-closed: record only
`documented_partial_boundary`; a declaration name or free-text derivation route
cannot restore a direct match. Recovering that direct route requires a separate
machine-generated primitive-level Lean derivation receipt with a clean expanded
input surface. A record field that merely supplies the process/cycle/trace/law
is an open partial-formalization boundary, not a source-faithful direct match.
If a source item is represented using a reusable library definition/theorem,
do not point the inventory directly at the reusable declaration as evidence.
Add a paper-local bridge/equivalence declaration, put that declaration on the
reviewed or assumption surface, add a `Source status:` line to its
paper-facing comment, and list it in the inventory under
`semantic_bridge_declarations`, `paper_equivalence_declarations`,
`source_equivalence_declarations`, or `library_bridge_declarations`. The
repository audit rejects hidden bridge helpers and name-only matches.
Then run `python3 scripts/review_dashboard.py --paper {folder}
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran. Freeze the current v11 Lean declaration manifest/digest for
every matched specification/proof route in the plan before proof work. Replace
each `sorry` without changing the elaborated specification or its paired proof
type; any signature change invalidates the statement audit and must repeat this
phase. Draft `sorry`s are never permitted at closeout. At formalized closeout,
enable the v11 source-to-Spec correspondence: bind every source atom to the
current elaborated Spec surface, inspect the entire Lean closure including proof
and instance arguments, and give every material closure terminal a source atom,
approved source correction/additional assumption, checked Lean derivation, or
version-pinned foundation disposition. There are no automatic data, container,
or name-based exemptions. Reuse this evidence only per unchanged item identity:
source atoms, Spec closure, narrow closure environment, and exact theorem type;
legacy v10 evidence remains readable but is not a v11 credential.

At review boundaries, populate `audit/statement_match_llm.json` with one
judgment per source claim. The only source-side input is the exact ordered
bundle of byte-pinned `source_anchor_evidence` quotes plus any separately
byte-pinned `semantic_context_requirements` quotes. The only Lean-side input is
the fully expanded transparent `...Spec : Prop`. Do not give the judge a
source-map summary, source-claim paraphrase, theorem label, Lean-to-TeX
translation, explanation, or thin proof wrapper. The receipt records
`source_input_protocol: verbatim_source_anchor_bundle_v1`, its bundle digest,
`lean_target_protocol: expanded_paperinterface_spec_v1`, the semantic Spec
declaration, and the expanded-Spec digest. A row may be judged `matches` only
if those exact raw inputs are semantically equivalent, including all
hypotheses, subparts, quantifiers, domains, constants, normalizations, signs,
inequality directions, conclusions, and visible inputs. Every input premise
must be accounted for as a paper primitive/source assumption, a Lean-derived
consequence of those primitives, or an explicit conditional boundary. Inspect
named Lean predicates/wrappers semantically; never approve from labels or
phrase overlap. A Lean-to-TeX rendering is optional display metadata, never an
input to or prerequisite for this semantic judgment. If the expanded Spec is a
conditional wrapper, source-row package,
certificate/replay/process/bridge package, omitted subclaim,
weakened/strengthened statement, hidden strengthening inside a named predicate,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include raw-source-input and expanded-Spec digests
plus the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch
   or uncertainty, iterate on the Lean statement before treating it as the paper
   theorem target. At an active statement-review handoff, use
`python3 scripts/review_dashboard.py --paper {folder} --precheck` only to
diagnose missing/stale statement-audit rows. It is not a frozen-closeout
predecessor: after report, status, map, and DAG inputs are frozen, start with
`python3 scripts/closeout_reuse_plan.py --paper {folder}` and execute only its
current `next_action`.
For every `source_routes` entry, pin the canonical source item, current source
statement digest, and exact locator, then record semantic scope/evidence in the
obligation ledger. Use `direct` only for an exact equivalent paper-facing
endpoint with an exact source-conclusion/Lean-conclusion equivalence. List each
scoped composite component as `source_component`; it needs semantic evidence
and a Lean conclusion, not a fabricated full-theorem equivalence.
`source_model_convention` is only for an explicit model reading, and
`defect_or_remark_support` only for a quarantined defect or support-only prose.
Use `proof_support` only with a substantive source-support scope; it never
supplies endpoint coverage. Names are navigation only, not route evidence.
All audit sidecars are fail-closed. Blank scaffolded files, missing prompt
versions, stale prompt versions, missing current digests, missing
validator/model identity, missing timestamps, unrecognized judgments, failed
judge runs, and items without explicit success verdicts remain audit alarms
until rerun against the current Lean/source inputs.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`audit/assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
When a source proof route is used, maintain `audit/source_proof_fidelity.json`.
Inventory every discovered proof-text defect by source locator, mathematical
claim, repair obligation, and acceptance condition. A corrected proof line is
never a source assumption: prove its replacement derivation or leave an
explicit proof boundary. This ledger is semantic evidence, not a Lean-name map.
If a defective printed result is quarantined and a Lean counterexample or
refutation is used as support, populate `audit/defect_support_match_llm.json`
with an independent semantic judgment. It must freeze the exact defect record,
source statement, Lean statement, elaborated signature, and every signature
atom; a theorem name, theorem kind, or tautology such as `True` is not defect
support. Rerun the source-to-Lean precheck after either source or Lean changes.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `audit/review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 120 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.
For public-facing closeout, populate a current `audit/review_surface_llm.json` even
when the dashboard has 30 or fewer rows; the row threshold is an early review
prompt, not a final-audit exemption. During active source-map repair, use
`python3 scripts/review_dashboard.py --paper {folder} --paper-coverage-precheck`
to diagnose missing, stale, partial, or uncertain coverage. Do not rerun that
precheck as a frozen-closeout precursor: the planner determines whether an
unchanged coverage receipt is reusable or which current item needs repair.
For efficiency, run `--source-inventory-check` first after a source-map change;
when the cache is current, use targeted `--statement-check` and
`--paper-coverage-check` before rebuilding manifests. Once the source map,
interface, and status surface are stable, refresh the target-paper cache once
during active review, or let the planner schedule it at frozen closeout. Let the
manifest tool use its bounded chunk retry and per-row fallback; do not restart a
whole-surface manifest extraction for a few failing declarations.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
{theorem_rows}

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `docs/FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Record the shared-library reuse checkpoint: mathlib, cslib, optlib,
      potential upstream Lean sources, and `EconCSLib` modules/declarations
      inspected; API chosen; near-misses.
- [ ] For every source-defined object represented by a reusable library
      definition/theorem, plan a paper-local semantic bridge/equivalence row;
      do not rely on matching Lean/library names as source evidence.
- [ ] Cite upstream material used or ported: repository URL, file/module path,
      commit or release when available, license status, and what was reused.
- [ ] Record the formal target map: rows to prove, empirical/out-of-scope rows,
      and any explicit boundary that would remain if the paper cannot close now.
- [ ] Replace the initial placeholder with one transparent exact source-shaped
      `<name>Spec : Prop` plus one theorem/lemma `<name> : <name>Spec` per
      in-scope paper-facing claim, using `by sorry` only as the temporary private
      proof body.
- [ ] Independently inventory every material source atom against exact pinned
      source quote bytes before consulting Lean; do not use identifiers or type
      shape as a substitute for source semantics.
- [ ] Run source-record/conclusion-provenance on the complete skeleton before
      any proof implementation; resolve circular or conclusion-bearing inputs.
- [ ] Run the raw-source-to-expanded-Spec statement target-setting pass and fix
      mismatched theorem targets before serious proof work. Review one
      transparent `Spec` per source claim, retain the paired theorem only as
      the proof endpoint, and record/freeze every canonical signature digest.
- [ ] Complete the five fidelity-risk dimensions semantically; bind each
      applicable match to a Lean conclusion, and never use declaration or
      function names as the evidence.
- [ ] Run the assumption/hidden-premise precheck before proof work; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Run the source-record/boundary-input audit if any reviewed theorem uses a
      record, certificate, replay, process, bridge, source-row, or broad package
      premise.
- [ ] Audit each source proof route used and update
      `audit/source_proof_fidelity.json`; never normalize a proof-text defect
      into a source assumption.
- [ ] Confirm `scripts/audit_conclusion_provenance.py --paper {folder}` reports
      no circular constructor, missing configured row, recursion failure, or
      unclassified conclusion-bearing input for the frozen skeleton. The full
      repository closeout audit is intentionally deferred while `sorry`s remain.
- [ ] Before a full status, complete v11 source-to-Spec correspondence: each
      atom binds to the elaborated Spec surface; the theorem type is exactly the
      transparent Spec; the closure includes proof/instance arguments; and every
      material terminal has a source, approved correction/additional assumption,
      checked derivation, or version-pinned foundation disposition.
- [ ] Create or update `docs/DependencyDAG.tex` at a paper milestone or
      closeout; do not rerender it for every proof-row edit.
- [ ] Replace the `PaperInterface.lean` placeholder before adding review rows;
      add `MainTheorems.lean` proof implementations only after the statement
      signatures are audited and frozen.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [ ] Run the byte-pinned raw-source-to-expanded-Spec semantic judgment before
      asking for human dashboard review. A Lean-to-TeX translation may be kept
      as optional display metadata but must not be used as semantic evidence.
- [ ] Update `status.json`, then run `python3 scripts/sync_paper_status.py
      --paper {folder}`. Defer the unscoped aggregate/site sync to integration
      or release.
- [ ] Rebuild `docs/DependencyDAG.pdf` and verify visually at a paper milestone
      or closeout when the DAG changed.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [ ] Update `docs/DependencyDAG.tex`, rerender `docs/DependencyDAG.pdf`, inspect the
      rendered diagram, and record the DAG audit evidence in both
      `FINAL_VALIDATION_REPORT.md` and `docs/POST_FORMALIZATION_AUDIT.md`.
- [ ] After the report/DAG/status updates, run
      `python3 scripts/closeout_reuse_plan.py --paper {folder}`, follow its
      dependency-ordered actions through any explicit replan, and execute its
      exact `strict_closeout` argv.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [ ] Do not run a second repository-wide provenance audit after a passing
      consolidated closeout. Use a standalone provenance command only to
      diagnose the named failing lane or at an explicit integration/release
      boundary.
"""


def status_text(
    args: argparse.Namespace,
    folder: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    review_names = statement_first_review_names(targets)
    spec_proof_routes = statement_first_spec_proof_routes(targets)
    title = args.title or "[Paper Title]"
    authors = args.authors or "[Authors]"
    version = args.version or "[Conference/Journal/arXiv version]"
    return (
        json.dumps(
            {
                "schema": 1,
                "id": folder,
                "title": title,
                "authors": authors,
                "source_version": version,
                # Presence opts a newly scaffolded paper into the prospective intake
                # seal. Historical status files omit it and remain grandfathered.
                "intake_freeze_required": True,
                # New work is private until a separate reviewed export explicitly
                # changes this release authorization.
                "repository_visibility": "private_only",
                "build_target": f"lake build {folder}",
                "status": "not started",
                "main_caveat": "Replace with the public caveat or state that no caveat is known.",
                "human_summary": "Replace with a concise public-facing note; leave empty for formalized papers unless a source-version or proof-route note matters.",
                "human_summary_review": {
                    "status": "draft",
                    "note": (
                        "Set to human_approved only after a human has written or explicitly approved this "
                        "summary; do not rewrite a human_approved summary without explicit human instruction."
                    ),
                },
                "review_entrypoint": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
                "human_review": {
                    "reviewed_rows": 0,
                    "total_rows": 0,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                    "source": "paper-local status.json review_surface; human entries come from dashboard logs",
                },
                "paper_interface": {
                    "path": f"papers/{folder}/PaperInterface.lean",
                    "line_count": 0,
                    "declaration_rows": len(review_names),
                    "review_rows": len(review_names),
                    "oversized": False,
                    "maintainability_issue": None,
                },
                "artifacts": {
                    "paper_interface": f"papers/{folder}/PaperInterface.lean",
                    "proof_interface": f"papers/{folder}/ProofInterface.lean",
                    "assumptions": f"papers/{folder}/Assumptions.lean",
                    "final_validation_report": f"papers/{folder}/FINAL_VALIDATION_REPORT.md",
                    "dependency_dag_tex": f"papers/{folder}/docs/DependencyDAG.tex",
                    "dependency_dag_pdf": f"papers/{folder}/docs/DependencyDAG.pdf",
                    "source_proof_fidelity": f"papers/{folder}/audit/source_proof_fidelity.json",
                    "defect_support_match": f"papers/{folder}/audit/defect_support_match_llm.json",
                    "library_semantic_review": f"papers/{folder}/audit/library_semantic_review.json",
                    "v11_raw_source_spec_screening": f"papers/{folder}/audit/v11_raw_source_spec_screening.json",
                },
                "review_surface": {
                    "source_file": f"papers/{folder}/PaperInterface.lean",
                    "proof_module": folder,
                    "assumption_source_file": f"papers/{folder}/Assumptions.lean",
                    # This is a closeout requirement. A `not started` scaffold has
                    # no atom inventory or closure receipt yet, so the v11 lane
                    # remains pending until the paper reaches a full status.
                    "require_source_spec_correspondence": True,
                    "llm_statement_review": {
                        "lean_to_tex_file": f"papers/{folder}/audit/lean_to_tex_llm.json",
                        "match_judgment_file": f"papers/{folder}/audit/statement_match_llm.json",
                        "library_semantic_review_file": f"papers/{folder}/audit/library_semantic_review.json",
                        "v11_screening_file": f"papers/{folder}/audit/v11_raw_source_spec_screening.json",
                        "review_surface_audit_file": f"papers/{folder}/audit/review_surface_llm.json",
                        "paper_coverage_audit_file": f"papers/{folder}/audit/paper_coverage_llm.json",
                        "defect_support_judgment_file": f"papers/{folder}/audit/defect_support_match_llm.json",
                        "assumption_judgment_file": f"papers/{folder}/audit/assumption_match_llm.json",
                        "surface_audit_threshold": 30,
                        "surface_warning_threshold": 120,
                        "require_explicit_source_routes": True,
                        "require_source_claim_atoms": True,
                        "require_direct_expression_semantics_review": "v1",
                        "required_prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2",
                        "policy": (
                            "For one source claim, give the LLM only the ordered byte-pinned source "
                            "anchor bundle plus any byte-pinned semantic context, and the fully "
                            "expanded transparent `...Spec : Prop`. Never compare a source-map "
                            "summary, curator paraphrase, theorem label, Lean-to-TeX translation, "
                            "or proof wrapper. Record the raw source-input bundle digest and the "
                            "expanded-Spec digest under the v11 protocols. The paired theorem/lemma "
                            "lives in ProofInterface.lean and receives only Lean-Meta exact-type "
                            "proof credit through the configured proposition_spec_proofs route. "
                            "For every material reused EconCSLib definition that appears in a source-facing "
                            "Spec, separately register an exact bounded library declaration and source-map "
                            "item in library_semantic_review.json; compare the raw source bundle with that "
                            "actual library code, never with its name or a glossary. "
                            "For formalized closeout, independently inventory every material source "
                            "atom from exact pinned source quote bytes before consulting Lean, then "
                            "bind the atoms to the elaborated Spec and account for the complete Lean "
                            "closure, including proof and instance arguments. Every material closure "
                            "terminal needs an explicit source, approved correction/additional "
                            "assumption, checked Lean derivation, or version-pinned foundation basis; "
                            "there are no automatic data, container, or name-based exemptions. "
                            "Boolean check equals true remains proof debt when the check decides a "
                            "result-bearing proposition; reflection makes that debt visible but does "
                            "not discharge it. A total data selector may support an unconditional "
                            "theorem only about its actual internally selected output; the review must "
                            "expose its success/fallback equations and nontriviality and must not infer "
                            "that a proposed nonfallback output is accepted. A result-level dependent "
                            "if remains conditional proof debt, and a noncomputable decision receives "
                            "no executable or runtime credit. Extra replay, "
                            "certificate, process, bridge, source-row, or broad package assumptions "
                            "must be judged "
                            "`mismatch` or `uncertain`. Record the model/agent validator metadata "
                            "and an atom-by-atom obligation ledger with exact source locators, explicit "
                            "mathematical bridge statements, every source conclusion, and every Lean "
                            "assumption. For every source route, pin the canonical source-item key, "
                            "statement digest, exact locator, route kind, and semantic scope/evidence. "
                            "Use direct only for an exact equivalent paper-facing endpoint with an exact "
                            "source-conclusion/Lean-conclusion equivalence. Composite rows list every scoped "
                            "source component as source_component with semantic evidence and a Lean conclusion, "
                            "not a fabricated full-theorem equivalence. source_model_convention routes only an "
                            "explicit source model reading, defect_or_remark_support only a quarantined defect or "
                            "support-only remark, and proof_support only a substantive source-support scope that "
                            "never supplies endpoint credit. Declaration "
                            "links are only a cross-check, never semantic evidence. Conditional boundaries may account for extra Lean assumptions "
                            "but cannot excuse unmatched source conclusions. "
                            "Iterate on PaperInterface.lean until the full statement matches. "
                            "If the dashboard has more than 30 rows, run a no-paper-context LLM "
                            "audit that checks whether every row is paper-facing; at 120 or more "
                            "rows, curate the surface before broad human review."
                        ),
                    },
                    "llm_paper_coverage_review": {
                        "paper_coverage_audit_file": f"papers/{folder}/audit/paper_coverage_llm.json",
                        "defect_support_judgment_file": f"papers/{folder}/audit/defect_support_match_llm.json",
                        "policy": (
                            "Maintain an audit/paper_statement_map.json inventory of source definitions, "
                            "formulas, and named statements, then use a separate LLM pass to judge "
                            "whether each source item is covered by one or more dashboard rows. "
                            "If coverage uses a reusable library declaration, it must route through "
                            "an audited paper-local semantic bridge/equivalence row; matching by "
                            "Lean/library/source names is not semantic evidence. "
                            "Quarantined source defects require a separate exact-hash semantic "
                            "judgment binding each candidate counterexample/refutation theorem to "
                            "the validated defect record and every elaborated signature atom. "
                            "This paper-level accounting is required before calling a full-paper "
                            "formalization closed and is separate from row-local statement matching."
                        ),
                    },
                    "llm_assumption_review": {
                        "assumption_judgment_file": f"papers/{folder}/audit/assumption_match_llm.json",
                        "policy": (
                            "Every paper-facing theorem premise not derived from prior Lean declarations "
                            "must be declared in Assumptions.lean, listed in assumption_names, "
                            "and judged by an independent LLM as a true paper/source model assumption rather "
                            "than a proof assumption."
                        ),
                    },
                    "llm_source_record_review": {
                        "source_record_audit_file": f"papers/{folder}/audit/source_record_audit.json",
                        "source_record_judgment_file": f"papers/{folder}/audit/source_record_match_llm.json",
                        "policy": (
                            "Run the code-backed recursive source-record audit for any visible "
                            "record, certificate, replay, process, bridge, source-row, or broad "
                            "package premise. The LLM judge must classify each boundary-shaped "
                            "input and recursive field by source evidence, Lean derivation, "
                            "approved external boundary, or unresolved proof debt."
                        ),
                    },
                    "semantic_model_review": {
                        "schema": SEMANTIC_MODEL_REVIEW_SCHEMA,
                        "required_dimensions": list(SEMANTIC_MODEL_DIMENSION_ORDER),
                        "policy": (
                            "For every reviewed row, preserve an alpha-normalized expanded "
                            "binder/domain surface, including transparent local type aliases, "
                            "record parameter domains, and model records reached only in result "
                            "quantifiers. An unexpanded local opaque/constant type requires a "
                            "checked carrier/refinement bridge rather than being silently treated "
                            "as an ordinary carrier. When an expanded finite carrier uses index "
                            "arithmetic such as Fin (n + c), record the source cardinal parameter, "
                            "the expanded Lean expression, and a proved parameter translation; "
                            "then explicitly compare it with pinned source text. "
                            "Review endpoint support/cutoffs, product or iid laws versus "
                            "source state evolution, conditioning/calibration semantics, expectation "
                            "definedness, null-cell totalization and finite/countable/arbitrary "
                            "partition scope, and Real versus extended-rate codomains when the "
                            "expanded model makes them relevant. For a probability-law surface, "
                            "state whether conditioning is pointwise, a.e., positive-fiber, or "
                            "event-calibrated; state measurability/integrability or extended-value "
                            "conventions for every expectation; and expose every zero-mass-cell "
                            "branch. Local declaration and binder names are routing only; detected "
                            "probability/rate shapes need a checked bridge from source primitives. "
                            "Because this scaffold enables explicit v10 source routes, every full "
                            "closeout requires current source-record semantic-model judgments for "
                            "every generated row; an unresolved model dimension blocks both full statuses."
                        ),
                    },
                    "source_proof_fidelity_review": {
                        "ledger_file": f"papers/{folder}/audit/source_proof_fidelity.json",
                        "policy": (
                            "Audit source proof steps by source locator and mathematical claim, not by Lean declaration name. "
                            "Completed papers use ledger schema 2. Every defect records status_impact as formalized_note, "
                            "formalized_with_caveat, or partially_formalized plus a semantic rationale. Minor repairs with "
                            "an unchanged substantive endpoint are notes; formalized with caveat is reserved for a substantial "
                            "central source-paper error with a fully proved corrected endpoint; weaker Lean targets and added "
                            "non-source assumptions are partial. Keep this configured ledger whenever "
                            "explicit source routes or source-defect links are present; a formalized note "
                            "cannot waive an added non-source assumption or a partial boundary."
                        ),
                    },
                    "assumption_policy": "strict",
                    "assumption_names": [],
                    "source_definition_names": [],
                    "proposition_spec_proofs": spec_proof_routes,
                    "paper_coverage_required": False,
                    "include_names": review_names,
                    "slices": [
                        {
                            "id": "all",
                            "title": "All source-facing review rows",
                            "names": review_names,
                        }
                    ],
                },
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def paper_statement_map_text(
    args: argparse.Namespace,
    folder: str,
    spec: StatementSpec,
    source_artifact_path: str,
) -> str:
    """Seed pinned source routing without claiming independent source curation."""

    source_url = args.official_url or args.url
    items = {
        target.lean_name: {
            "statement": target.source_statement,
            "source_item": target.source_item,
            "source_kind": target.source_kind,
            "source_location": target.source_location,
            "source_url": source_url,
            "source_status": (
                "pinned statement-spec transcription; independent source audit pending"
            ),
            "spec_lean_declarations": [statement_spec_name(target)],
            "proof_lean_declarations": [target.lean_name],
            "semantic_contract_template": statement_first_semantic_contract_template(
                target
            ),
        }
        for target in spec.targets
    }
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "source_url": source_url,
                "source_version": spec.source_version,
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": spec.source_artifact_sha256,
                "source_inventory_kind": "pinned_statement_target_scaffold",
                "source_curated": False,
                "seed_scaffold": True,
                "source_coverage_mode": "named_theoretical_statements",
                "semantic_contract_policy": {
                    "schema": 1,
                    "activation": (
                        "Before Lean drafting, independently inventory every material source atom "
                        "against exact pinned source quote bytes; do not infer that inventory from "
                        "declaration, binder, field, or function names. After a source item has an "
                        "audited paper-local specification and a theorem/lemma proving or refuting "
                        "it, add top-level semantic_contract_schema: 1, classify every item with "
                        "an explicit claim_bearing Boolean, and record semantic_contract for each "
                        "true item. At formalized closeout, also add source_claim_atoms_schema: 1 "
                        "and source_spec_correspondence_schema: 1. Bind each atom to an elaborated "
                        "Spec component and account for every material Lean-closure terminal, "
                        "including proof and instance arguments, by source atom, approved source "
                        "correction/additional assumption, checked Lean derivation, or version-pinned "
                        "foundation basis. "
                        "Each statement-first row supplies an inactive "
                        "semantic_contract_template pairing its transparent `...Spec : Prop` "
                        "with its theorem/lemma. Promote that exact template only after the "
                        "independent source audit passes, the theorem has exactly the transparent "
                        "Spec type, the closure record passes, and the proof hole is replaced. Do "
                        "not manufacture a contract from the temporary by-sorry statement skeleton "
                        "alone. Legacy v10 evidence remains readable but is not a v11 realization "
                        "credential. For a source-game result whose feasible-action "
                        "equilibrium comparison uses a conditional/posterior or "
                        "observation-contingent value, add the separately byte-pinned "
                        "`semantic_context_requirements` kind "
                        "`strategic_observation_totality`; it requires an explicit "
                        "off-path/zero-probability totality audit and cannot be satisfied "
                        "by a Lean-only default value."
                    ),
                    "required_fields": [
                        "spec_declaration",
                        "evidence_declaration",
                        "evidence_mode",
                        "semantic_shape",
                    ],
                    "evidence_modes": ["proves", "refutes"],
                    "semantic_shapes": ["plain"],
                    "shape_policy": (
                        "Only plain exact-proposition contracts are currently enforced. "
                        "Do not record a specialized runtime, preprocessing, or refinement "
                        "shape until the audit implements its structural check."
                    ),
                    "source_defect_routing": (
                        "Every repaired_in_lean source-proof defect must be linked from a "
                        "successfully checked contract item through source_defect_ids."
                    ),
                },
                "items": items,
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def intake_freeze_text(
    folder: str,
    spec: StatementSpec | None,
    source_artifact_path: str,
    source_text_artifact: dict[str, object] | None = None,
) -> str:
    """Seed a future-paper-only, machine-checkable intake completion boundary."""

    items = []
    for dependency_order, target in enumerate(
        spec.targets if spec is not None else (), start=1
    ):
        items.append(
            {
                "source_item": target.source_item,
                "source_location": target.source_location,
                "source_statement_sha256": hashlib.sha256(
                    re.sub(r"\s+", " ", target.source_statement.strip()).encode("utf-8")
                ).hexdigest(),
                "source_kind": target.source_kind,
                "spec_declaration": statement_spec_name(target),
                "proof_declaration": target.lean_name,
                "dependency_order": dependency_order,
                "depends_on_source_items": [],
                "owner": "unassigned",
                "source_atoms": [],
                "acceptance_conditions": [
                    "all exact source atoms are byte-pinned and semantically complete",
                    "the transparent Spec is equivalent to the full source target",
                    "every visible premise has source or checked derivation provenance",
                    "the proof closes without paper-local placeholders",
                ],
            }
        )
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "acceptance_credential": False,
                "future_paper_intake_only": True,
                "state": "draft",
                "inventory_scope": "complete named theoretical source surface",
                "inventory_complete": False,
                "source_item_identity": INTAKE_SOURCE_IDENTITY,
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": (
                    spec.source_artifact_sha256 if spec is not None else ""
                ),
                "source_version": spec.source_version if spec is not None else "",
                "source_text_artifact": source_text_artifact,
                "items": items,
                "seal_requirements": {
                    "state": "sealed",
                    "inventory_complete": True,
                    "every_item_has_owner": True,
                    "dependency_order_is_total": True,
                    "every_source_atom_has_locator_exact_byte_slice_quote_and_sha256": True,
                    "pdf_atoms_use_pinned_normalized_source_text_receipt": True,
                },
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def lean_to_tex_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "lean-to-tex-v3-strict-context-free-semantic-inputs",
                "translator": "",
                "translator_type": "",
                "translated_at": "",
                "prompt_summary": [
                    "Translate each Lean declaration from the Lean statement alone, with no paper context.",
                    "Preserve every visible variable, binder, hypothesis, domain condition, named predicate/wrapper application, equivalence or implication direction, and conclusion.",
                    "Do not replace formulas or named premises with theorem labels, source-like phrases, informal endpoints, or proof-route summaries.",
                    "If a statement contains a predicate such as a certificate/replay/process/bridge/source-row/bounds condition, keep that premise explicit with its arguments so the statement-match judge can inspect it semantically.",
                ],
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def statement_match_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2",
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Compare verbatim byte-pinned source-anchor text against the fully expanded transparent Lean Spec. The source-map statement is navigation metadata only and must not be used as semantic-review input.",
                "prompt_summary": [
                    "A matches verdict requires semantic equivalence of the full source statement and Lean statement: same hypotheses, subparts, quantifiers, domains, constants, normalizations, signs, inequality directions, conclusions, and visible inputs.",
                    "The only permitted source-side semantic input is the exact concatenation of the source map item's byte-pinned source_anchor_evidence quoted_text slices followed by its semantic_context_requirements source_anchor_evidence slices, all in declared order. Do not use or rewrite the source-map statement, source_claim_atoms.semantic_claim, a curator summary, a theorem label, context explanation, or inferred surrounding context. If the displayed theorem needs surrounding assumptions, add those exact source slices as semantic_context_requirements before judging; otherwise return uncertain rather than reconstructing them.",
                    "Set source_input_protocol to verbatim_source_anchor_bundle_v1 and source_input_bundle_sha256 to the canonical digest of that exact quote sequence. Set paper_statement_sha256 equal to that source_input_bundle_sha256: it is the source-side semantic target, not the map statement digest. For every source_routes entry and every direct endpoint source_obligation, record source_anchor_quote_identity_sha256 for the cited item's displayed source anchor; direct endpoint obligations also record source_input_bundle_sha256. The auditor must be able to reconstruct the LLM source input solely from that digest and the byte-pinned source map.",
                    "The only permitted Lean-side semantic input is the exact expanded transparent Spec declaration. Set lean_target_protocol to expanded_paperinterface_spec_v1 and semantic_target_declaration to that Spec's fully qualified PaperInterface declaration. Set lean_statement_sha256 to the exact expanded Spec text digest. Do not use a Lean-to-TeX draft, agent paraphrase, declaration label, or thin proof wrapper as source or Lean semantic input.",
                    "When a source item has a transparent Spec plus a paired theorem/lemma, compare the verbatim source text only to the fully expanded Spec. Do not issue an independent semantic match for a thin proof wrapper of the form theorem T : TSpec; Lean Meta's exact proof-to-Spec check is the proof credential for that endpoint.",
                    "Do not approve by theorem label, phrase overlap, or source-looking Lean names. Expand or otherwise semantically inspect every named predicate/wrapper appearing as a Lean hypothesis or conclusion.",
                    "Every input premise must be one of: a paper primitive/source assumption, a Lean-derived consequence of paper primitives, an approved external boundary, or an explicit conditional boundary.",
                    "For a composite source result, audit premise scope atom by atom: map each source conclusion atom to the exact Lean implication or conjunction branch that proves it. A witness, endpoint, cardinality, typeclass, or other premise needed only by one sibling atom must not gate an independent atom. Treat an unseparated or unnecessarily narrowed atom as mismatch or partial coverage even when the composite theorem is otherwise true.",
                    "Mark mismatch or uncertain for omitted source subclaims, added non-source conditions, hidden strengthening inside named predicates, conditional wrappers, broad aggregate rows, source-row packages, certificate/replay/process/bridge packages, or weakened/strengthened statements.",
                    "A replay/certificate/process/bridge premise is an extra assumption unless the source statement explicitly assumes that object or the Lean statement also includes a checked derivation from source primitives.",
                    "Treat `check input = true` as caller-supplied proof debt when the check unfolds to `decide` over a result-bearing proposition, even if a reflection theorem exists. A total Option/match/dependent-if success/failure statement avoids a caller proof only as a conditional checker specification; expand the branch semantics, and never credit a noncomputable decision as executable or polynomial.",
                    "For formula-bearing rows, check the exact formula rather than only the theorem label or qualitative interpretation.",
                    "For every row, complete numeric_semantics_review and partition every source/Lean obligation between reviewed numeric items and the explicit nonnumeric lists. For each source/Lean formula pair, separately record both value domains, coercions, division convention, rounding or truncation, normalization, strictness, zero-denominator behavior, and the exact relation. Natural floor division is not rational or real division. A proved or witness-specific equivalence must point to an explicit equality/iff Lean conclusion and state that conclusion; a matching function name is never evidence.",
                    "For every row, enumerate source_obligations and lean_obligations as semantic parameter/assumption/conclusion atoms. Every Lean obligation must reference exactly one atom in the machine-generated elaborated declaration manifest through signature_ref and signature_atom_sha256, and all manifest atoms must be covered exactly once. Record the current lean_signature_sha256, give every alignment an explicit mathematical bridge_statement, and record exact unmatched_source_conclusions, unmatched_source_inputs, unjustified_lean_inputs, and unmatched_lean_conclusions lists. Names are routing, not evidence.",
                    "For every source_routes entry, pin source_item, source_statement_sha256, source_location, source_anchor_quote_identity_sha256, and route_kind. These route fields are locators and integrity pins only: their map statement digest or explanation must never be semantic LLM input. direct is only an exact equivalent paper-facing endpoint with an exact source-conclusion/Lean-conclusion equivalence. A source-map item marked corrected_source_statement is different: retain its archival statement, compare Lean only with corrected_target.statement, use route_kind approved_corrected_target and resolution approved_corrected_target, and pin the archival statement digest, corrected_target_sha256, governing_defect_ids, approval artifact hash, and archival_equivalence_claimed=false. It must never use direct or certify the archival statement. A corrected target has exactly one complete PaperInterface endpoint in lean_declarations; use one explicit conjunction when it has several clauses. Aliases, proof helpers, support declarations, and semantic bridges never receive corrected-target text, source-route credit, or coverage credit. Composite rows use source_component for each scoped source component and a Lean conclusion as evidence, not a fabricated full-theorem endpoint. source_model_convention is only an explicit model reading; defect_or_remark_support is only quarantined-defect or support-only prose; proof_support needs a substantive source_support_scope and never provides endpoint credit.",
                    "For each direct or approved-corrected-target route whose pinned source item is a definition or predicate vocabulary item, complete source_definition_semantics_review. When status.json review_surface.llm_statement_review.require_direct_expression_semantics_review is exactly v1, apply that same review to formula, equation, and algorithmic_formula items. Expand the source and Lean legal domains, their behavior outside the source domain (including any Lean totalization), and the actual operational object rather than relying on a source-looking function name. Explicitly classify every advertised definition property: for example, that revenue counts only winners, a formula defines a normalized probability law on its stated support, or a selected threshold attains the advertised optimum. A total Lean function, an unnormalised formula, or a bare selector is not equivalent merely because it has a convenient name. If the source definition has no additional advertised property, say why in no_advertised_properties_basis. A full source-definition endpoint cannot be routed only as a source_component to skip this review.",
                    "For every row, complete semantic_scope_review from expanded definitions. Record fixed-profile versus all-profile quantification; do not infer scope from generic parameters or declaration names.",
                    "For every row, complete the versioned fidelity_risk_review. Its five dimensions are semantic checks, not declaration-name heuristics: source output arity/shape and terminal projection; adversarial action-space carrier, capacity, nonvacuity, and duplicate interactions; coherent realization of candidatewise extrema with actual-runner/refinement evidence; syntactic-family cardinality versus nonempty realized fibers with surjectivity for equality; and execution scope across input domains, state transitions, termination, numeric representation, cost claims, and any bridge from local execution to the advertised global claim.",
                    "A matches verdict must bind each applicable fidelity dimension to source and elaborated-Lean obligation ids, record equivalent expanded semantics, and cite a Lean conclusion that exposes the evidence. An algorithmic row may not classify execution_claim_scope as absent.",
                    "For every named predicate, wrapper, structure, or inductive certificate, cite the definition or constructor expansion basis, bind it to the Lean obligations where it occurs, and enumerate the transitive result-bearing field/constructor dependencies. Put every other Lean obligation in non_definition_lean_obligation_ids. A matches verdict requires recursive_expansion_complete=true; describing a type by its name is not semantic review.",
                    "Complete discrete_semantics_review and partition every source/Lean obligation between reviewed discrete-operation items and the explicit nondiscrete lists. Immediate list successor, next active choice, eventual occurrence, support under a restricted carrier, and first occurrence are different operations unless an explicit equality/iff Lean conclusion proves equivalence on the reviewed domain.",
                    "Unfold every result-bearing predicate or iff. If an output, feasibility, or optimality characterization unfolds to the same fact about an independently supplied object, classify it self_characterizing and never use it as source-conclusion evidence.",
                    "For an algorithmic row, distinguish existence, noncomputable existence, executable output, and polynomial time. The advertised result must be derived from the formalized source runner or connected across distinct semantic worlds by an exposed refinement/preservation proposition; conjoining runner success with an independent characterization is not such a bridge.",
                    "A polynomial-time match requires an explicit complexity conclusion and arithmetic/representation model. A generic selector, termination fact, or finite enumeration does not establish the source runtime claim.",
                    "Audit complexity from the transitive semantic operational dependency graph over every reachable branch in the stated input domain, not from one trace or from function/declaration names. Extensional equality, refinement, simulation, or result preservation establishes correctness, not runtime; a cached or memoized recursive executor must not evaluate the old semantic closure or oracle after materialization.",
                    "For each matches polynomial-time row, complete operational_complexity_review as a row-level sibling of semantic_scope_review. Give a worst-case recurrence and bound. Charge traversal and enumeration length (including duplicates), materialization and rebuilding, representation/container primitives, and exact-rational bit growth. A missing or excluded_by_claim item cannot support a matches polynomial-time verdict. When closure elimination is material, pin the evidence artifact and audited source by SHA-256 and bind the generated IR/C call graph or cost-threaded executor to the eliminated dependency semantically; symbol names are routing only.",
                ],
                "semantic_scope_review_schema": {
                    "required": [
                        "source_quantification",
                        "lean_quantification",
                        "quantification_relation",
                        "source_quantification_basis",
                        "lean_quantification_basis",
                        "named_definition_review",
                        "numeric_semantics_review",
                        "discrete_semantics_review",
                        "algorithm_review",
                        "fidelity_risk_review",
                        "semantic_worlds",
                        "world_bridges",
                    ],
                    "profile_quantification_values": [
                        "not_profile_based",
                        "fixed_profile",
                        "all_profiles",
                        "existential_profile",
                        "mixed_profile_scope",
                    ],
                    "named_definition_item_required": [
                        "lean_obligation_ids",
                        "surface_expression",
                        "unfolded_semantics",
                        "expansion_basis",
                        "recursive_result_dependencies",
                        "recursive_expansion_complete",
                        "classification",
                        "used_as_source_conclusion_evidence",
                    ],
                    "named_definition_coverage_required": [
                        "non_definition_lean_obligation_ids",
                    ],
                    "recursive_named_definition_dependency_required": [
                        "surface_expression",
                        "unfolded_semantics",
                        "expansion_basis",
                    ],
                    "named_definition_recursive_rule": (
                        "recursive_result_dependencies is the transitive result-bearing "
                        "constructor/field/definition closure. A matches verdict requires "
                        "recursive_expansion_complete=true."
                    ),
                    "named_definition_absence_rule": (
                        "When definitions_present is false, items must be empty and "
                        "absence_basis must explain why no result-bearing wrapper occurs. "
                        "Every Lean obligation must occur in one item or in the explicit "
                        "non_definition_lean_obligation_ids list."
                    ),
                    "named_definition_classification_values": [
                        "substantive",
                        "self_characterizing",
                        "routing_only",
                    ],
                    "source_definition_semantics_review_required_when": (
                        "A direct or approved-corrected-target source route pins an item "
                        "whose source_kind is definition or predicate_vocabulary; when "
                        "status.json review_surface.llm_statement_review."
                        "require_direct_expression_semantics_review is exactly v1, this "
                        "also includes formula, equation, and algorithmic_formula."
                    ),
                    "source_definition_semantics_review_required": [
                        "source_obligation_ids",
                        "lean_obligation_ids",
                        "source_legal_domain",
                        "lean_legal_domain",
                        "domain_relation",
                        "source_outside_domain_behavior",
                        "lean_outside_domain_behavior",
                        "outside_domain_relation",
                        "source_operational_semantics",
                        "lean_operational_semantics",
                        "operational_relation",
                        "advertised_property_status",
                        "advertised_properties",
                    ],
                    "source_definition_semantic_relation_values": [
                        "equivalent",
                        "source_stronger",
                        "lean_stronger",
                        "incomparable",
                        "uncertain",
                    ],
                    "source_definition_advertised_property_status_values": [
                        "properties_reviewed",
                        "no_advertised_properties",
                    ],
                    "source_definition_property_required": [
                        "id",
                        "source_property",
                        "lean_realization",
                        "source_obligation_ids",
                        "lean_obligation_ids",
                        "relation",
                        "lean_evidence_kind",
                        "evidence_basis",
                    ],
                    "source_definition_property_evidence_kind_values": [
                        "expanded_definition_body",
                        "paper_interface_equivalence",
                        "paper_interface_conclusion",
                        "missing",
                    ],
                    "source_definition_semantics_rule": (
                        "The review covers every visible source and Lean obligation. "
                        "For a matches verdict, legal domain, outside-domain/totalization "
                        "behavior, operational meaning, and every advertised property are "
                        "equivalent. A paper_interface_equivalence property must cite a "
                        "Lean equality or iff conclusion; paper_interface_conclusion must "
                        "cite its exact audited conclusion; expanded_definition_body evidence "
                        "must bind a definition-valued Lean conclusion."
                    ),
                    "numeric_semantics_item_required": [
                        "id",
                        "source_obligation_ids",
                        "lean_obligation_ids",
                        "source_expression",
                        "lean_expression",
                        "source_domain",
                        "lean_domain",
                        "source_operations",
                        "lean_operations",
                        "source_coercions",
                        "lean_coercions",
                        "source_division",
                        "lean_division",
                        "source_rounding",
                        "lean_rounding",
                        "source_normalization",
                        "lean_normalization",
                        "source_strictness",
                        "lean_strictness",
                        "source_zero_denominator",
                        "lean_zero_denominator",
                        "relation",
                        "relation_basis",
                    ],
                    "numeric_semantics_coverage_required": [
                        "non_numeric_source_obligation_ids",
                        "non_numeric_lean_obligation_ids",
                    ],
                    "numeric_semantics_equivalence_rule": (
                        "proved_equivalent and witness_specific_equivalent items must name a "
                        "Lean conclusion containing equality or iff in "
                        "lean_equivalence_conclusion_id and state it in "
                        "lean_equivalence_statement. A matches verdict "
                        "allows only definitionally_equal or proved_equivalent numeric relations."
                    ),
                    "numeric_semantics_relation_values": [
                        "definitionally_equal",
                        "proved_equivalent",
                        "witness_specific_equivalent",
                        "different",
                        "uncertain",
                    ],
                    "discrete_semantics_item_required": [
                        "id",
                        "source_obligation_ids",
                        "lean_obligation_ids",
                        "source_expression",
                        "lean_expression",
                        "source_domain",
                        "lean_domain",
                        "source_operation",
                        "lean_operation",
                        "source_order_sensitivity",
                        "lean_order_sensitivity",
                        "relation",
                        "relation_basis",
                    ],
                    "discrete_semantics_coverage_required": [
                        "non_discrete_source_obligation_ids",
                        "non_discrete_lean_obligation_ids",
                    ],
                    "discrete_semantics_equivalence_rule": (
                        "proved_equivalent and witness_specific_equivalent items must name a "
                        "Lean conclusion containing equality or iff in "
                        "lean_equivalence_conclusion_id and state it in "
                        "lean_equivalence_statement. A matches verdict allows only "
                        "definitionally_equal or proved_equivalent discrete relations."
                    ),
                    "discrete_semantics_relation_values": [
                        "definitionally_equal",
                        "proved_equivalent",
                        "witness_specific_equivalent",
                        "different",
                        "uncertain",
                    ],
                    "source_claim_level_values": [
                        "not_algorithmic",
                        "existence",
                        "executable",
                        "polynomial_time",
                    ],
                    "algorithm_review_basis_required": [
                        "source_claim_basis",
                        "lean_claim_basis",
                    ],
                    "lean_claim_level_values": [
                        "not_algorithmic",
                        "existence",
                        "noncomputable_existence",
                        "executable",
                        "polynomial_time",
                    ],
                    "runner_provenance_values": [
                        "not_applicable",
                        "same_formalized_runner",
                        "proved_refinement",
                        "independent_characterization",
                        "missing",
                    ],
                    "result_provenance_values": [
                        "not_applicable",
                        "runner_derived",
                        "preservation_bridge",
                        "independent_characterization",
                        "missing",
                    ],
                    "world_bridge_relation_values": [
                        "definitionally_equal",
                        "equivalent",
                        "refines",
                        "simulates",
                        "preserves_result",
                    ],
                    "note": (
                        "World ids and surface expressions are routing only. Give each world "
                        "expanded mathematical semantics and expose every required bridge through "
                        "a Lean conclusion obligation."
                    ),
                },
                "fidelity_risk_review_schema": {
                    "version": FIDELITY_RISK_REVIEW_VERSION,
                    "placement": (
                        "Every row stores fidelity_risk_review inside semantic_scope_review."
                    ),
                    "required_dimensions": sorted(FIDELITY_RISK_DIMENSIONS),
                    "common_applicable_fields": [
                        "applicable",
                        "source_obligation_ids",
                        "lean_obligation_ids",
                        "source_semantics",
                        "lean_semantics",
                        "relation",
                        "relation_basis",
                        "lean_evidence_statement",
                        "lean_evidence_conclusion_id",
                    ],
                    "nonapplicable_fields": ["applicable", "absence_basis"],
                    "relation_values": sorted(FIDELITY_RISK_RELATIONS),
                    "matches_rule": (
                        "Every applicable dimension must have relation=equivalent and bind "
                        "its semantic evidence to a Lean conclusion obligation included in "
                        "that dimension's lean_obligation_ids."
                    ),
                    "output_shape_fields": [
                        "source_output_shape",
                        "lean_output_shape",
                        "projection_terminal_policy",
                        "arity_basis",
                    ],
                    "adversarial_action_space_fields": [
                        "source_action_space",
                        "lean_action_space",
                        "carrier_capacity_basis",
                        "duplicate_interaction_basis",
                        "nonvacuity_basis",
                        "source_nonvacuous",
                        "lean_nonvacuous",
                    ],
                    "coherent_extrema_witness_fields": [
                        "source_extrema_semantics",
                        "lean_extrema_semantics",
                        "coherent_witness_basis",
                        "runner_refinement_basis",
                        "source_combines_candidatewise_extrema",
                        "lean_combines_candidatewise_extrema",
                        "coherent_witness_status",
                    ],
                    "coherent_witness_status_values": sorted(
                        COHERENT_EXTREMA_WITNESS_STATUSES
                    ),
                    "cardinality_fibers_fields": [
                        "source_counted_object",
                        "lean_counted_object",
                        "realized_fiber_semantics",
                        "surjectivity_basis",
                        "source_counting_semantics",
                        "lean_counting_semantics",
                        "source_claims_exact_cardinality",
                        "lean_claims_exact_cardinality",
                        "claims_syntactic_family_equals_realized_fibers",
                        "surjectivity_status",
                    ],
                    "counting_semantics_values": sorted(COUNTING_SEMANTICS),
                    "surjectivity_status_values": sorted(SURJECTIVITY_STATUSES),
                    "surjectivity_rule": (
                        "Exact equality between a syntactic-family count and nonempty "
                        "realized fibers requires surjectivity recorded as definitionally_surjective or "
                        "proved_surjective evidence bound to a Lean conclusion."
                    ),
                    "execution_claim_scope_fields": list(
                        FIDELITY_EXECUTION_SCOPE_FIELDS
                    ),
                    "algorithmic_rule": (
                        "Every algorithmic source row must mark execution_claim_scope applicable. "
                        "A local transition, partial execution, incompatible termination rule, "
                        "or local cost count does not match an advertised complete or polynomial "
                        "execution claim without a checked global bridge."
                    ),
                    "legacy_compatibility_rule": (
                        "Existing fidelity-risk-review-v2 records remain valid under their "
                        "original execution-scope field set. New reviews must use this v3 "
                        "domain-neutral field set."
                    ),
                    "name_independence_rule": (
                        "Dimension, declaration, and function names plus obligation ids only "
                        "route evidence. Expanded source/Lean semantics and checked conclusions "
                        "determine the verdict."
                    ),
                },
                "operational_complexity_review_schema": {
                    "version": OPERATIONAL_COMPLEXITY_REVIEW_VERSION,
                    "required_when": (
                        "judgment=matches and source_claim_level=polynomial_time and "
                        "lean_claim_level=polynomial_time"
                    ),
                    "placement": (
                        "Each matching row stores operational_complexity_review as a "
                        "sibling of semantic_scope_review."
                    ),
                    "required": [
                        "schema_version",
                        "executor_semantics",
                        "input_domain",
                        "input_size_measure",
                        "dependency_graph",
                        "worst_case_recurrence",
                        "worst_case_bound",
                        "complexity_lean_conclusion_id",
                        "complexity_statement_binding",
                        "work_accounting",
                        "closure_elimination",
                    ],
                    "dependency_graph_required": [
                        "nodes",
                        "edges",
                        "root_node_ids",
                        "transitive_closure_complete",
                        "all_reachable_branches_complete",
                        "coverage_basis",
                    ],
                    "dependency_node_required": [
                        "id",
                        "operation_semantics",
                        "reachable_branch_domain",
                        "work_accounting_categories",
                    ],
                    "dependency_edge_required": [
                        "from_node_id",
                        "to_node_id",
                        "invocation_semantics",
                        "branch_condition",
                    ],
                    "work_accounting_required_categories": [
                        "traversal_enumeration_length",
                        "duplicate_multiplicity",
                        "materialization_rebuilding",
                        "representation_container_primitives",
                        "exact_rational_bit_growth",
                    ],
                    "work_accounting_item_required": [
                        "category",
                        "status",
                        "operation_semantics",
                        "worst_case_charge_or_absence_basis",
                        "evidence_basis",
                    ],
                    "work_accounting_status_values": [
                        "charged",
                        "proved_absent",
                        "not_applicable",
                        "missing",
                        "excluded_by_claim",
                    ],
                    "full_runtime_match_status_values": [
                        "charged",
                        "proved_absent",
                        "not_applicable",
                    ],
                    "charged_category_rule": (
                        "Every charged category must occur in at least one dependency node's "
                        "work_accounting_categories; proved_absent and not_applicable items "
                        "must instead give their substantive absence basis."
                    ),
                    "closure_elimination_required": [
                        "material",
                    ],
                    "non_material_closure_elimination_required": [
                        "non_material_basis",
                    ],
                    "material_closure_elimination_required": [
                        "evidence_kind",
                        "evidence_artifact_sha256",
                        "audited_source_sha256",
                        "evidence_locator",
                        "old_dependency_semantics",
                        "semantic_binding",
                        "elimination_basis",
                        "symbol_names_used_as_evidence",
                    ],
                    "closure_evidence_kind_values": [
                        "generated_ir_call_graph",
                        "cost_threaded_executor",
                    ],
                    "note": (
                        "Node ids, edge endpoints, declaration names, and generated symbols are routing "
                        "only. A full runtime match requires semantic coverage of every reachable "
                        "operation and branch, a worst-case bound, and complete work accounting."
                    ),
                },
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def library_semantic_review_text(folder: str) -> str:
    """Scaffold the source-to-library semantic-review lane for a new paper."""

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "library-statement-match-v1-verbatim-source-anchor-expanded-definition",
                "target_protocol": "expanded_library_definition_v1",
                "comment": (
                    "For every material reusable EconCSLib definition used by a source-facing "
                    "Spec, record the exact declaration and a source-map item. Compare only that "
                    "item's byte-pinned verbatim source bundle with the exact bounded library Lean "
                    "definition. A name, docstring, glossary, Lean-to-TeX prose, or theorem label "
                    "is not semantic input. Leave a primitive absent until an exact source connection "
                    "is identified; do not manufacture a matches judgment."
                ),
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def v11_raw_source_spec_screening_text(folder: str) -> str:
    """Scaffold the canonical raw-source-to-expanded-Spec screening ledger."""

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "audit_kind": "raw_source_to_expanded_spec_screening",
                "prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2",
                "validator": "",
                "validated_at": "",
                "comment": (
                    "Each row must compare only the exact byte-pinned source-anchor bundle "
                    "and required source context with one direct expanded PaperInterface "
                    "Spec. The paired proof endpoint is separate Lean evidence. Reissue with "
                    "scripts/reissue_v11_raw_source_spec_screening.py after an explicit "
                    "reviewer decision; do not enter a map summary, theorem name, wrapper, "
                    "or Lean-to-TeX paraphrase as semantic input."
                ),
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def review_surface_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "prompt_version": "review-surface-v2-semantic-paper-facing",
                "comment": "",
                "prompt_summary": [
                    "Judge whether each dashboard row is genuinely paper-facing, not just source-sounding.",
                    "Rows should expose source definitions, formulas, named statements, explicit source conditions, or documented boundaries.",
                    "Reject or mark needs_curation for rows that are merely proof plumbing, broad packages, replay/certificate/process/bridge internals, or theorem-label paraphrases without source-facing mathematical content.",
                    "Do not approve by Lean declaration name, phrase overlap, or source-looking terminology.",
                ],
                "judgment": "",
                "reason": "",
                "review_rows": 0,
                "review_surface_sha256": "",
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def paper_coverage_llm_text(
    folder: str,
    *,
    source_artifact_path: str = "",
    source_artifact_sha256: str = "",
) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "paper-coverage-v6-verbatim-source-anchor-proof-row-signature-pins",
                "audit_kind": "source_to_dashboard_llm",
                "source_grounded": True,
                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                "seed_scaffold": False,
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Judge whether each canonical source-paper statement is semantically covered by one or more dashboard rows. This is separate from row-local statement matching; phrase overlap or matching theorem names are not enough.",
                "source_coverage_mode": "named_theoretical_statements",
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": source_artifact_sha256,
                "prompt_summary": [
                    "For each source inventory item, identify the exact dashboard row(s) that cover the mathematical content.",
                    "Set source_input_protocol to verbatim_source_anchor_bundle_v1. Read the exact byte-pinned source_anchor_evidence quote bundle plus semantic_context_requirements quotes, never a source-map statement/paraphrase, as the source-side input. Record source_anchor_quote_identity_sha256 for each item. If the result depends on surrounding source context, that context must be included as exact anchors before coverage is judged.",
                    "The default coverage surface is source-labelled named theory only: named definitions, theorem-like results, and explicitly numbered formulas, algorithms, or assumptions. Figures, captions, numerical examples, simulations, empirical observations, and general prose belong only to an explicit deep_paper_with_all_prose_claims audit. A source-map key, claim_bearing flag, or Lean declaration/function name cannot suppress a labelled source result.",
                    "A covered verdict requires semantic coverage of the source hypotheses, objects, quantifiers, constants, formulas, and conclusions, not just a matching title or phrase.",
                    "Do not mark source-labelled formal results (definitions, propositions, theorems/corollaries, named claims, or main-text lemmas) out of scope for compactness. Expose dashboard rows so the row-local statement judge can inspect them. An unnumbered prose assertion may instead use the dedicated user_approved_scope_exclusion lane only with a byte-pinned source anchor and an explicit user instruction; it remains claim-bearing and receives no Lean proof credit. Appendix lemmas are a judgment call, but appendix theorem/corollary targets should be covered.",
                    "If a linked Lean row has extra replay/certificate/process/bridge/source-row premises, mark the source item covered_with_boundary or partially_covered unless those premises are separately derived from source primitives.",
                    "A theorem, proposition, lemma, corollary, named claim, runtime claim, or opted-in claim-bearing item receives direct coverage only through a reviewed Lean theorem/lemma row. A matching def/abbrev is specification vocabulary, not proof evidence; inspect declaration manifests rather than declaration names. A user_approved_scope_exclusion is the separate non-proof disposition for an unnumbered prose assertion, not direct coverage.",
                    "For every direct or conditional coverage link, record review_row_signature_sha256 as an exact object from each linked review-row name to that row's current elaborated, normalized Lean signature digest. Row names and source routes only locate the row; they do not bind the coverage judgment after its theorem type changes. The map keys must be exactly review_rows and every digest must be current.",
                    "For a corrected_source_statement inventory item, use coverage covered_corrected_target, target_kind approved_corrected_target, the corrected target statement digest, archival_statement_sha256, corrected_target_sha256, the exact governing_defect_ids, and archival_equivalence_claimed=false. The linked row must be exactly the sole complete endpoint in lean_declarations, and its reviewed paper statement must be the corrected target, not the archival wording. Aliases and support helpers cannot carry this coverage. Ordinary covered or a direct route is prohibited for that item.",
                    "A source_status quarantined_source_defect item is never directly covered as proved. Use support_only only with validated source_defect_ids and reviewed theorem/lemma counterexample or refutation routes, which are counted separately as defect support.",
                    "Every quarantined support route also needs an independent current audit/defect_support_match_llm.json judgment that exact-hash pins the source item, full validated defect record, Lean statement, and elaborated signature; declaration names and theorem kind are navigation, not semantic evidence.",
                    "Include source_evidence from the paper and dashboard_evidence from the row; exact-key or theorem-name matching is only a scaffold.",
                ],
                "paper_statement_inventory_sha256": "",
                "review_surface_sha256": "",
                "item_schema": {
                    "direct_coverage_required": [
                        "review_rows",
                        "review_row_signature_sha256",
                        "reason",
                        "source_evidence",
                        "source_anchor_quote_identity_sha256",
                        "statement_sha256",
                        "source_item_coverage_digest_schema",
                        "source_item_coverage_sha256",
                    ],
                    "review_row_signature_sha256": {
                        "<review_row_name>": "<current_elaborated_normalized_lean_signature_sha256>"
                    },
                    "source_item_coverage_digest_schema": SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
                    "source_item_coverage_sha256": "<current_source_semantic_item_digest>",
                },
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def defect_support_match_llm_text(folder: str) -> str:
    """Create the independent exact-hash defect-to-Lean judgment scaffold."""

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "defect-support-v1-exact-source-defect-to-lean-semantic",
                "audit_kind": "source_defect_to_lean_llm",
                "source_grounded": True,
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Judge whether each proposed Lean theorem is mathematically a counterexample to or refutation of the exact validated source defect. Names and declaration kind are never sufficient evidence.",
                "prompt_summary": [
                    "Read the exact source span and all semantic fields of the cited audit/source_proof_fidelity.json defect, then inspect the elaborated Lean signature rather than relying on the declaration name.",
                    "Copy the exact canonical source item key, source statement digest, complete source_defect snapshot, source defect digest, Lean statement text/digest, and lean_signature_sha256. Any source or Lean change must make the judgment stale.",
                    "List every elaborated signature atom exactly once in lean_obligations using signature_ref, role, signature_atom_sha256, defect_relevance, and a substantive semantic_explanation. Do not insert unpinned Lean prose in place of signature atoms.",
                    "Align every Lean atom to a semantic source_defect field. For the conclusion, use counterexample_to or refutes and explicitly align it to source_claim. For each parameter or assumption, explain the concrete witness, source-model condition, or checked derivation that prevents a hidden premise.",
                    "Reject True, reflexive equality/equivalence, vacuous implications, and statements that only share names or terminology with the defect. A theorem proof is support only when its actual conclusion and inputs establish the recorded counterexample/refutation.",
                    "Use a validator independent of the formalizer, source curator, coverage classifier, and statement judge.",
                ],
                "item_schema": {
                    "required": [
                        "source_item",
                        "source_statement_sha256",
                        "defect_id",
                        "source_defect",
                        "source_defect_sha256",
                        "support_declaration",
                        "lean_statement",
                        "lean_statement_sha256",
                        "lean_signature_sha256",
                        "judgment",
                        "reason",
                        "lean_obligations",
                        "obligation_alignment",
                    ],
                    "judgment_values": [
                        "valid_counterexample",
                        "valid_refutation",
                        "does_not_support",
                        "uncertain",
                    ],
                    "source_defect_fields": [
                        "id",
                        "source_locator",
                        "source_claim",
                        "defect_kind",
                        "affected_source_locators",
                        "statement_impact",
                        "status_impact",
                        "status_impact_rationale",
                        "repair_obligation",
                        "acceptance_condition",
                        "resolution",
                        "resolution_evidence",
                    ],
                    "lean_obligation_required": [
                        "signature_ref",
                        "role",
                        "signature_atom_sha256",
                        "defect_relevance",
                        "semantic_explanation",
                    ],
                    "alignment_required": [
                        "source_defect_field",
                        "lean_signature_ref",
                        "relation",
                        "semantic_basis",
                        "witness_or_derivation",
                    ],
                },
                "items": {},
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def assumption_match_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": "assumption-provenance-v4-verbatim-source-anchor-exact-premise",
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "comment": "Validate every assumption declaration and every exact audit-premise against source text or a Lean derivation.",
                "prompt_summary": [
                    "For each Assumptions.lean declaration, decide semantically whether it is an explicit paper/model assumption, a source theorem condition, a documented caveat, a partial-formalization boundary, not a paper assumption, or uncertain.",
                    "For every exact -- audit-premise entry, give an independent premise_judgments entry. Group-level approval is insufficient.",
                    "Scrutinize each premise against the source model, not by declaration name, theorem label, or phrase overlap. Expand named predicates/wrappers enough to identify the actual mathematical assumption.",
                    "Certificate, replay, process, bridge, source-row, or broad package premises need a specific source primitive or a Lean-checked instantiation path from paper primitives; otherwise mark partial_boundary/not_paper_assumption.",
                    "Use source_text_model_primitive, source_text, or paper_condition only for premises explicitly stated by the source. Supply the exact byte-pinned source-anchor quote bundle, cite source_location, and record source_anchor_quote_identity_sha256; do not use a paraphrase, map statement, or reconstructed context as source evidence.",
                    "Use derived_from_source_primitives only when the Lean development derives the premise from prior source primitives.",
                    "Displayed formulas, capacity equations, threshold identities, density/mass rows, source-row packages, certificates, and proof conveniences are not paper assumptions unless the source explicitly assumes them; otherwise mark partial_boundary or not_paper_assumption.",
                ],
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def source_record_match_llm_text(folder: str) -> str:
    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "prompt_version": SOURCE_RECORD_PROMPT_VERSION,
                "source_record_policy_version": SOURCE_RECORD_PROMPT_VERSION,
                "validator": "",
                "validator_type": "",
                "validated_at": "",
                "source_record_audit_sha256": "",
                "comment": "Classify every boundary-shaped theorem input and recursive source-record field semantically against the paper source and Lean derivation path.",
                "prompt_summary": [
                    "Do not approve by theorem label, phrase overlap, final theorem name, or source-looking Lean names.",
                    "Each replay/certificate/process/bridge/source-row/package input needs a specific source primitive, a Lean-checked constructor from paper primitives, an approved external boundary, or unresolved_assumed_math.",
                    "Use validated_source_assumption only with a source key/location/evidence; use proved_from_primitives only with a Lean constructor/derivation.",
                    "For every semantic_model_comparison item, set classification to semantic_model_review and provide semantic_model_dimensions for every requested dimension. Each dimension needs an exact source_locator, concrete semantic_comparison, lean_evidence, and verdict matches_source_model/not_applicable/mismatch_or_open/documented_partial_boundary. Every detected dimension marked requires_checked_bridge_when_detected, including endpoint-support, joint-law/state-evolution, conditioning/calibration, expectation-definedness, null-cell/partition, extended-rate, and opaque-carrier surfaces, also needs a checked lean_bridge; not_applicable is invalid for a detected shape. When carrier_and_domain requests requires_cardinality_boundary_analysis_when_detected, add cardinality_boundary_analysis with a verdict plus source_cardinality_domain, lean_cardinality_domain, boundary_cases_checked, strictness_witness_or_reason, and lean_boundary_evidence. When joint_law_and_state_evolution requests requires_transformed_law_analysis_when_detected, add transformed_law_analysis with a verdict plus source_operation, lean_operation, parameter_domain_and_endpoints, law_normalization_or_pushforward_evidence, outcome_equivariance_or_no_relabeling_evidence, and lean_semantic_bridge. Do not use theorem, declaration, wrapper, field, binder, or function names as semantic evidence.",
                    "When a generated source_model_derivation dimension is present, reproduce every byte-pinned source primitive component in order, map each to an expanded Lean primitive role, and give non-name-only evidence for the checked Lean derivation of the declared source consequence. Every source primitive and the source conclusion needs its own exact source anchor in the schema-2 source contract; the enclosing context quote is not enough. The only direct-match route is checked_lean_derivation_from_source_primitives. When its generated caller_supplied_model_construction_basis is nonempty, the current generic receipt is fail-closed: use documented_partial_boundary with an open route. A declaration name or free-text derivation narrative cannot restore matches_source_model; a future direct route needs a separate machine-generated primitive-level Lean derivation receipt with a clean expanded input surface.",
                    "Compare expanded binder domains, transparent type aliases, record parameter restrictions, and records reached only in result quantifiers with source quantification. A local opaque/constant/axiom type surface needs a checked carrier/refinement bridge before it can be treated as ordinary model data. For finite ordered laws, distinguish strict adjacent tails from terminal cutoffs and endpoint support. Do not replace a source state process with iid/product sampling without a checked bridge, and do not treat a Real rate as an extended WithTop rate without handling infinite/eventually-zero and boundary cases. For each expanded probability-law surface, distinguish pointwise, a.e., positive-fiber, and measurable-event conditioning/calibration; give the exact joint-event formula and a bridge for any change of convention. Identify the law/integrand and measurability plus integrability or extended-value convention for each expectation. Distinguish finite, countable, and arbitrary partition scope, and expose measurable cover/disjointness and every zero-mass-cell denominator branch. A finite positive-mass calculation does not establish an arbitrary-partition statement.",
                    "Use visible_boundary_component only for recursive fields exactly unpacked from visible theorem premises; use derived_from_visible_boundary only for recursive fields Lean derives from visible theorem premises.",
                    "Do not use visible_boundary_component or derived_from_visible_boundary for theorem inputs themselves; boundary inputs remain visible proof debt unless source-validated or Lean-derived from paper primitives.",
                    "Use approved_external_boundary only for declared partial/conditional boundaries, not for a paper marked fully formalized.",
                    "Do not classify a theorem input as container_recursively_audited or nonpropositional_witness_data.",
                    "For algorithmic or optimization rows, inspect the literal legal action space and whether profiles are ordered tuples, multisets, or bounded stocks; do not infer either from names.",
                    "Audit the recurrent fidelity hazards explicitly from expanded semantics: source output arity/shape and terminal projection; nonvacuous adversarial carrier/capacity and duplicate interactions; one coherent witness for any combined candidatewise extrema plus actual-runner/refinement evidence; syntactic-family cardinality versus nonempty realized fibers with surjectivity before equality; and source/Lean input scope, state transitions, termination, numeric representation, cost scope, and local-to-global bridge basis for execution claims.",
                    "Check that the actual source executor evaluates every advertised input and output branch under the stated input domain, transition relation, and termination condition. A noncomputable finite selector is neither an executable refinement nor a runtime theorem.",
                    "Unfold result-bearing definitions and iff predicates. A characterization that reduces to the advertised membership/feasibility fact on an independently supplied object is self-characterizing, not evidence that the algorithm produced or preserved that object.",
                    "Track the source runner, Lean runner, input profile, returned profile, and independently characterized profile as distinct semantic worlds until a checked equality, simulation, refinement, or result-preservation proposition connects them. A conjunction of facts from different worlds is not a bridge.",
                    "Compare fixed-profile claims with all-profile claims explicitly. A theorem about one supplied or constructed profile does not validate a source theorem quantified over every legal profile.",
                    "Compare every visible proposition premise structurally with the advertised result. A premise equivalent to, providing, or logically composing the advertised feasibility, cost, runtime, or optimality result is conclusion-bearing proof debt, not a validated source assumption for that result; source-facing coverage must derive it from paper primitives.",
                    "A true-result premise for a Boolean wrapper over `decide` is still conclusion-bearing proof debt; an iff/reflection row does not discharge it. If the Lean interface instead gives an internally selected total success/failure branch, classify it only as a conditional checker contract, inspect the branch predicate semantically, and deny executable/runtime credit to a noncomputable classical decision.",
                    "Separately require evidence for any complexity claim, arithmetic representation, and claimed refinement to external code. Record noncomputable existence, executable output, and polynomial time as different capabilities.",
                    "For a cached or memoized complexity claim, inspect the transitive semantic operational dependency graph over every reachable branch in the stated input domain: extensional/refinement correctness does not establish runtime, and the executor must not evaluate an old semantic closure or oracle after materialization. Function and declaration names are not operational evidence.",
                    "Require a worst-case recurrence and bound, and charge traversal/enumeration length and duplicates, all materialization/rebuilding, representation/container primitives, and exact-rational bit growth. Missing or excluded_by_claim work cannot support a full runtime match. If closure elimination is material, require artifact/source SHA-256 pins and a semantic binding to the generated IR/C call graph or cost-threaded executor; symbol names alone are not evidence.",
                ],
                "items": {},
            },
            indent=2,
        )
        + "\n"
    )


def source_proof_fidelity_text(
    folder: str,
    source_artifact_path: str = "",
    source_artifact_sha256: str = "",
) -> str:
    """Create the source-proof fidelity ledger required for new paper closeout.

    The ledger is intentionally about source proof mathematics rather than Lean
    declaration names.  It gives a later proof agent a source-located repair
    obligation and prevents a broken proof line from being relabeled as a
    paper assumption.
    """

    return (
        json.dumps(
            {
                "schema": 1,
                "paper": folder,
                "source_artifact_path": source_artifact_path,
                "source_artifact_sha256": source_artifact_sha256,
                "review_status": "not_started",
                "reviewed_proof_scopes": [],
                "model_conventions": [],
                "checked_proof_steps": [],
                "model_convention_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "classification",
                        "formal_meaning",
                        "why_needed",
                        "checked_scope",
                    ],
                    "optional": ["unresolved_relation_to_literal_source"],
                },
                "checked_proof_step_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "source_step",
                        "checked_conclusion",
                        "scope",
                    ]
                },
                "defects": [],
                "defect_entry_schema": {
                    "required": [
                        "id",
                        "source_locator",
                        "source_claim",
                        "defect_kind",
                        "affected_source_locators",
                        "statement_impact",
                        "repair_obligation",
                        "acceptance_condition",
                        "resolution",
                        "resolution_evidence",
                    ],
                    "defect_kind_values": [
                        "algebra_or_sign",
                        "inequality_direction",
                        "quantifier_or_uniformity",
                        "domain_or_endpoint",
                        "index_or_integrality",
                        "event_or_measure",
                        "normalization_or_scaling",
                        "logical_dependency",
                        "other",
                    ],
                    "statement_impact_values": [
                        "proof_only",
                        "source_statement",
                        "uncertain",
                    ],
                    "status_impact_values": [
                        "formalized_note",
                        "formalized_with_caveat",
                        "partially_formalized",
                    ],
                    "resolution_values": [
                        "repaired_in_lean",
                        "open_proof_obligation",
                        "corrected_source_statement",
                        "resolved_in_current_source",
                    ],
                },
                "policy": [
                    "Review source proof text by exact source locator and mathematical claim; Lean declaration names are navigation only and are not evidence.",
                    "Give every defect a stable unique id using letters, digits, dot, underscore, or hyphen so source-map contracts can route its repair without depending on Lean names.",
                    "A source proof defect is not a paper/model assumption. Do not classify its repaired conclusion as validated_source_assumption.",
                    "Record every explicit formalization convention that resolves a source-model ambiguity in model_conventions, with the literal source relation and checked scope. A convention is not a literal source theorem without a source-side semantic bridge.",
                    "Record every source proof step independently checked by Lean in checked_proof_steps, including its exact source step, checked conclusion, and scope. A finite/event-level step does not silently establish an arbitrary-space, pointwise-conditioning, or arbitrary-partition claim.",
                    "For every defect, record the mathematical repair obligation and acceptance condition. Resolve it by a Lean derivation, leave it as an explicit open proof obligation, or record an explicit corrected source statement.",
                    "For every defect, separately record status_impact and status_impact_rationale. statement_impact says which source text changed; status_impact says whether the issue is a formalized note, a substantial source-paper caveat with a fully proved correction, or a partial-formalization boundary.",
                    "A proof-only defect may coexist with a source-faithful final theorem only after the replacement derivation is proved. A minor source-statement repair may also be formalized_note when the substantive advertised endpoint is unchanged. Only a substantial central source-paper error with a fully proved corrected endpoint justifies formalized_with_caveat.",
                ],
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    )


def dag_text() -> str:
    return r"""\documentclass[tikz,border=10pt]{standalone}
\input{../../../docs/tikz/dag_preamble.tex}

\begin{document}

% Agent visual validation loop:
% 1. Compile this file to PDF after every substantive DAG edit.
% 2. Inspect the PDF or a rendered PNG, not just the TeX source.
% 3. Increase spacing or reroute arrows until no box, legend, note, edge, or label overlaps.
%
% Intended lifecycle:
% - During paper intake, replace the scaffold below with every named result in the
%   paper and the dependency arrows between them.
% - After intake, treat this as a stable topology: update node styles/status/text
%   as proofs close, but avoid adding boxes or arrows unless the original named
%   result inventory or dependency map was actually incomplete.
%
% Arrow direction rule:
% Draw edges from prerequisite/source node to dependent/target node.  The
% `dag_arrow` and `dag_dashed_arrow` styles use an explicit end-arrow (`->`),
% so the arrowhead should always land on the node that consumes the dependency.
% Do not reverse the coordinate order just to make routing easier; use anchors
% or an orthogonal route through empty space instead.

\begin{tikzpicture}[
  x=1cm,
  y=1cm,
  every node/.append style={outer sep=4pt}
]

\dagPaperMetadata{[Paper Title]}{[Authors]}{[Publication Venue]}{[Year]}{[Formalized PDF link]}

% --- Legend: README status vocabulary plus formalized node-type styles. ---
\dagPaperLegendRightOfMetadata{
\node[dag_result, dag_template_legend] (legRes) at (0,0) {formalized\\result};
\node[dag_lemma, dag_template_legend] (legLem) at (4.2,0) {formalized\\lemma};
\node[dag_model, dag_template_legend] (legDef) at (8.4,0) {formalized\\definition};
\node[dag_caveat_legend] (legCav) at (12.6,0) {formalized\\with caveat};
\node[dag_partial, dag_template_legend] (legPart) at (0,-2.6) {partially\\formalized};
\node[dag_conditional, dag_template_legend] (legCond) at (4.2,-2.6) {conditional};
\node[dag_scaffold, dag_template_legend] (legScaf) at (8.4,-2.6) {scaffold};
\node[dag_unformalized, dag_template_legend] (legNot) at (12.6,-2.6) {not started /\\not formalized};
}
\daglegend{(legRes)(legLem)(legDef)(legCav)(legPart)(legCond)(legScaf)(legNot)}{Legend}

\begin{dagPaperBody}

% --- Layout guidance for future agents. ---
\node[dag_template_note] (Guide) at (6.4,0) {
  Replace these scaffold nodes with the paper's named definitions, lemmas,
  propositions, theorems, and corollaries. Keep nodes on the grid below:
  columns are spaced by 6.4cm and rows by 3.2cm, which is wide enough for the
  default 5cm node text widths. Prefer straight or orthogonal arrows (`--`,
  `|-`, `-|`) and route through empty grid cells when a dependency skips a row.
  Draw from prerequisite to dependent result so the arrowhead points at the
  consumer.  For short horizontal gaps, use explicit anchors like `(A.east) --
  (B.west)` and increase spacing if the arrowhead visually merges with a node.
  After every layout change, render and inspect the PDF; if anything overlaps,
  increase row or column spacing before adding complicated curves. Once the
  initial named-result map is complete, prefer README-status style updates over
  adding new boxes or arrows.
};

% --- Non-overlapping proof graph scaffold. ---
% Status update pattern:
% - Change the leading style only, e.g. dag_unformalized -> dag_conditional ->
%   dag_lemma/dag_result, and update the short text if the remaining assumption changed.
% - Keep node names and arrows stable after the initial intake map is complete.
\node[dag_model] (Model) at (0,-4.2) {
  \textbf{Definitions / Model} \\
  Source primitives
};
\node[dag_lemma] (LemmaA) at (6.4,-4.2) {
  \textbf{Lemma A} \\
  First reusable step
};
\node[dag_lemma] (LemmaB) at (12.8,-4.2) {
  \textbf{Lemma B} \\
  Second reusable step
};

\node[dag_conditional] (Bridge) at (6.4,-7.4) {
  \textbf{Bridge Theorem} \\
  Boundary-dependent paper-facing reduction
};
\node[dag_unformalized] (Open) at (12.8,-7.4) {
  \textbf{Open Source Result} \\
  Name exact remaining gap
};

\node[dag_result] (Main) at (6.4,-10.6) {
  \textbf{Main Theorem} \\
  Closed paper-facing endpoint
};

\draw[dag_arrow] (Model) -- (LemmaA);
\draw[dag_arrow] (LemmaA) -- (LemmaB);
\draw[dag_arrow] (LemmaA) -- (Bridge);
\draw[dag_dashed_arrow] (LemmaB) -- (Open);
\draw[dag_arrow] (Bridge) -- (Main);
\draw[dag_dashed_arrow] (Open) |- (Main);
\end{dagPaperBody}
\end{tikzpicture}
\end{document}
"""


def main_theorems_text(title: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import Mathlib

/-!
# Paper-Facing Theorems: {display_title}

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace {namespace}

end {namespace}
"""


def assumption_source_text(title: str, folder: str, namespace: str) -> str:
    display_title = title or "[Paper Title]"
    return f"""import {folder}.MainTheorems

/-!
# Paper Assumptions: {display_title}

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`audit/assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

Start empty. Add a proposition here only after locating it as a literal source
antecedent. Never move an unproved lemma or target conclusion here merely to
make a statement skeleton compile.
-/

namespace {namespace}

end {namespace}
"""


def paper_interface_text(
    title: str,
    folder: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    targets = targets or []
    display_title = title or "[Paper Title]"
    inventory = "\n".join(
        f"- `{statement_spec_name(target)}` -> `{target.lean_name}`: "
        f"{target.source_item}, {target.source_location}."
        for target in targets
    )
    if not inventory:
        inventory = (
            "- None yet. This interface is intentionally empty because no "
            "source-pinned statement spec was supplied."
        )

    declarations: list[str] = []
    for target in targets:
        lean_type = "\n  ".join(target.lean_type.splitlines())
        declarations.append(
            f"""/--
{target.source_item}

Paper statement: {target.source_statement}

Source location: {target.source_location}
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def {statement_spec_name(target)} : Prop :=
  {lean_type}"""
        )
    declaration_text = "\n\n".join(declarations)
    if not declaration_text:
        declaration_text = (
            "-- Intentionally no theorem placeholder: extract and audit the exact "
            "source targets first."
        )
    return f"""import {folder}.MainTheorems
import {folder}.Assumptions

/-!
# Human-Facing Paper Interface: {display_title}

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `EconCSLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; its temporary
  proof body may be `by sorry` only in a private draft. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus recursive
  premise/conclusion provenance on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace the `ProofInterface.lean` `sorry` with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

{inventory}
-/

namespace {namespace}

{declaration_text}

end {namespace}
"""


def proof_interface_text(
    title: str,
    folder: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
) -> str:
    """Render the non-human proof endpoints paired with PaperInterface Specs."""

    targets = targets or []
    display_title = title or "[Paper Title]"
    declarations = "\n\n".join(
        f"""/--
Lean proof endpoint for `{statement_spec_name(target)}`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
{target.kind} {target.lean_name} :
  {statement_spec_name(target)} := by
  sorry"""
        for target in targets
    )
    if not declarations:
        declarations = "-- No proof endpoint until a source-pinned Spec is added."
    return f"""import {folder}.PaperInterface

/-!
# Proof Interface: {display_title}

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace {namespace}

{declarations}

end {namespace}
"""


def gitignore_text() -> str:
    return """source-audited*
*.pdf
!docs/DependencyDAG.pdf
*.aux
*.log
*.fls
*.fdb_latexmk
*.synctex.gz
"""


def review_launcher_text() -> str:
    return """#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)"
ROOT_DIR="$(cd \"${SCRIPT_DIR}/../..\" && pwd)"
PAPER_DIR=\"$(basename \"$SCRIPT_DIR\")\"

exec \"${ROOT_DIR}/scripts/launch_review_dashboard.sh\" --paper \"$PAPER_DIR\" \"$@\"
"""


def root_import_text(folder: str) -> str:
    return f"""import {folder}.ProofInterface
"""


def notes_text(title: str, namespace: str, args: argparse.Namespace) -> str:
    official_url = args.official_url or args.url
    title_text = title or "[Paper Title]"
    return f"""# {title_text} Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `{namespace}`
- Official URL: {official_url}
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Recursive provenance is clear in the consolidated paper closeout. Run a
      standalone repository-wide provenance audit only for a named diagnostic
      failure or at an explicit integration/release boundary.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed:
- Last theorem row formalized:
- Outstanding assumptions / caveats:
- Reusable library elevation candidates:

"""


def formalization_plan_text(
    title: str,
    namespace: str,
    targets: list[StatementTarget] | None = None,
    paper_root: str | None = None,
) -> str:
    targets = targets or []
    paper_root = paper_root or namespace
    title_text = title or "[Paper Title]"
    skeleton_rows = "\n".join(
        f"| {target.source_item} / {target.source_location} | "
        f"`{statement_spec_name(target)}` -> `{target.lean_name}` | "
        "pending | pending | pending | `by sorry` |"
        for target in targets
    )
    if not skeleton_rows:
        skeleton_rows = (
            "| No source-pinned target supplied | `none` | | pending | pending | none |"
        )
    return f"""# Formalization Plan: {title_text}

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report. Once the current source-shaped
target and audited `PaperInterface.lean` skeleton are present, prioritize the
next proof obligation; update this document at material boundaries rather than
after routine proof steps.

- Namespace: `{namespace}`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
- Source/version mismatch notes:
- Complete named-result ledger status:
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains:
  - Density vs mass / likelihood-kernel representation issues:
  - Dependency map between named source results:
  - Formula-bearing displayed claims that need derivation, not source-row assumptions:
- Named result sanity check:
  - Results that look correct as stated:
  - Suspected bugs, missing assumptions, or ambiguous wording:
- Source-proof fidelity ledger (`audit/source_proof_fidelity.json`):
  - Proof scopes reviewed by source locator and mathematical claim:
  - Source proof defects, if any, with repair obligation and acceptance condition:
  - Proof-only defects kept out of `Assumptions.lean`:
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected:
  - Cslib declarations/modules inspected:
  - Optlib declarations/modules inspected:
  - Other potential upstream sources inspected:
  - Upstream sources used or ported, with citation/provenance:
  - Existing `EconCSLib` declarations/modules inspected:
  - API chosen and near-misses:
  - Source-defined objects that will use reusable library definitions, and the
    planned paper-local semantic bridge/equivalence rows:
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:
- Algorithmic complexity audit, when applicable:
  - Transitive operational dependency graph over every reachable branch and old semantic closure/oracle dependencies:
  - Worst-case recurrence and bound over the stated input-size measure:
  - Traversal/enumeration lengths, duplicates, and materialization/rebuild charges:
  - Representation/container primitives and rational bit-growth work accounting; missing/excluded work withholds a runtime match:
  - Pinned evidence when closure elimination is material: artifact/source hashes and semantic binding to generated IR/C or a cost-threaded executor:

## Source Inventory

- Definitions / formatted paper objects:
- Named lemmas / propositions / theorems / corollaries:
- Named assumptions / model conditions used by those results:
- Deep-only prose, standalone formulas, algorithms, figures, simulations, and
  computational examples (record scope disposition; do not create normal-mode
  proof targets merely because they are numbered or displayed):

## Intake Freeze Boundary

Do not begin the main proof campaign until this boundary is complete. The
purpose is to discover missing conclusions and hidden premises while changing
the statement skeleton is still cheap, rather than during final closeout.

- [ ] Exact source version and every source artifact used by the normal-scope
      inventory are byte-pinned.
- [ ] The independent normal-scope inventory contains every named theoretical
      definition, result, and source assumption, with explicit dispositions for
      exclusions. Navigation names are not coverage evidence.
- [ ] Every selected result has source-first premise/conclusion atoms, exact
      anchors, and one complete transparent `Spec : Prop` in `PaperInterface`.
- [ ] The proof-obligation dependency order below is acyclic and assigns one
      owning module to each result; concurrent agents do not share an item.
- [ ] One focused manifest/statement/source-record review has frozen the exact
      statement identities. After this point, a proof-body-only edit reopens
      proof closure and compilation, not the human statement judgment.
- [ ] That fully current initial review has written entry-local reuse pins with
      `semantic_audit_reuse.py --bootstrap-current --write`; this is a one-time
      identity seal, not a stale-evidence override or a new human judgment.
- [ ] The dashboard cache is created once after this freeze, never during bare
      scaffold creation.

### Proof-obligation order

| Order | Source-semantic item | Dependencies | Owning module / agent | Statement frozen | Proof status |
|---:|---|---|---|---|---|
| 1 | Fill from the independent source inventory | none | | no | pending |

## Initial Proof Strategy

- Main theorem chain:
- Likely reusable `EconCSLib` seams:
- Paper steps that look underspecified or analytically hard:
- Formal target map:
  - Rows to fully prove now:
  - Empirical/descriptive rows out of formal theorem scope:
  - Explicit assumption/certificate boundaries, if any:
- Planned fallback route if the source proof is too informal:

## Audited Statement Skeleton

Before drafting Lean, independently inventory every material source atom against
the exact pinned source quote bytes. Then replace the generated placeholder with
every in-scope paper-facing theorem/formula statement as a transparent
`<name>Spec : Prop`, followed by `theorem/lemma <name> : <name>Spec := by sorry`.
Audit and freeze the specification's canonical declaration-manifest digest; Lean
Meta must confirm the paired proof route has exactly that elaborated proposition.
The inactive source-map `semantic_contract_template` records only the
spec/proof pairing to promote after source review and proof completion. Never
treat the `by sorry` route, an identifier, or a type/container label as active
semantic contract or proof evidence.

At formalized closeout, complete v11 source-to-Spec correspondence. Bind every
source atom to the current elaborated Spec surface, traverse the full Lean
closure including proof and instance arguments, and give every material closure
terminal a source atom, approved source correction/additional assumption,
checked Lean derivation, or version-pinned foundation disposition. Reuse a
receipt only when that item's source-atom content, Spec closure, narrow closure
environment, and exact theorem type are unchanged. Legacy v10 evidence remains
readable but does not satisfy this v11 credential.

Partition every source and Lean obligation through both the numeric and
discrete semantics reviews. Record coercion, division, rounding, normalization,
strictness, and zero-denominator behavior separately. Distinguish immediate
successor, next active choice, eventual occurrence, restricted support, and
first occurrence literally. Bind any proved equivalence to an explicit
equality/iff Lean conclusion on the reviewed obligations.

For every `source_routes` entry, pin the source item, current statement digest,
exact locator, route kind, and semantic scope/evidence. `direct` is only for an
exact equivalent paper-facing endpoint with an exact source-conclusion/Lean-
conclusion equivalence. A `corrected_source_statement` retains archival text
and has exactly one complete PaperInterface endpoint in `lean_declarations`;
state all repaired clauses as one explicit conjunction there. Aliases, proof
helpers, support declarations, and semantic bridges cannot carry the repaired
target, source-route credit, or coverage credit. A composite row lists each scoped component as
`source_component`, using a Lean conclusion as evidence without claiming a
full-theorem equivalence. `source_model_convention` is for an explicit model
reading, `defect_or_remark_support` for quarantined/support-only material, and
`proof_support` only for a substantive support scope that never gives endpoint
credit. Names route review but never establish it.

| Source item / locator | Spec -> proof route | v10 declaration-manifest SHA-256 | Statement verdict | Premise provenance | Proof body |
|---|---|---|---|---|---|
{skeleton_rows}

Signature changes after a `matches` verdict invalidate the row and require a
fresh audit. Replacing `sorry` without changing the type does not.

## Planned Verification And Invalidation

Use these boundaries throughout the paper so closeout is execution of a plan,
not a new discovery pass.

| Material change | Reopen |
|---|---|
| One source item's semantic content or byte anchor | That item's source, coverage, statement, and dependent proof obligations |
| One `Spec` type or elaborated semantic dependency | That statement item and its dependent proof closure |
| Proof body only, theorem type unchanged | Focused compilation and proof closure only |
| Report, README, status prose, or DAG only | Presentation/status consistency only |
| Audit producer or protocol | Only lanes whose pinned producer/protocol identity changed; first run the reuse planner |

Planned commands, in order:

1. Intake seal, once the complete statement review is current: `python3
   scripts/semantic_audit_reuse.py --paper {paper_root} --bootstrap-current
   --write`.
2. Proof loop: `lake build {paper_root}.PaperInterface` or the narrower touched
   proof module.
3. Freeze closeout presentation inputs once: final report, status, source map,
   and Dependency DAG source/PDF. Run `python3 scripts/sync_paper_status.py
   --paper {paper_root}`; defer aggregate/site status to integration or release.
4. Closeout readiness: `python3 scripts/closeout_reuse_plan.py --paper {paper_root}`.
   Execute its `next_action`. If the frozen plan gives that action an explicit
   state-qualified successor, continue through that successor to its required
   replan boundary; do not rerun the planner between a cache-miss build and its
   one manifest refresh. A cache miss never erases unchanged semantic judgments.
   An exact current compiled cache skips a redundant standalone build, while a
   rebuilt artifact must be replanned before strict closeout.
5. Consolidated closeout, once the planner exposes it: run the exact
   `strict_closeout` argv/command printed by the plan. It carries a
   non-authoritative operational plan identity, preventing an accidental
   duplicate of the same completed execution. Do not invoke
   `run_paper_closeout.py` from a handwritten command: its planner-issued
   identity and any `--new-run` disposition are required.
   This command records ignored operational state under `.review_traces`; if
   the terminal stream disappears, inspect that state instead of starting a
   duplicate run.
6. Run a repository-wide status/site refresh only at an integration or release
   boundary, not as part of every paper proof closeout.

## Reusable-Library TODO

- Library APIs to use directly:
- Small reusable lemmas to add now:
- Larger reusable components to defer:
- Library-audit risks:

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [ ] Complete the normal named-theory inventory and record deep-only
      dispositions separately.
- [ ] During active source-map repair, run `--source-inventory-check` before a
      necessary manifest refresh. With a current cache, use targeted
      statement/coverage checks; after the source map, interface, and status
      surface are stable, refresh once and let bounded manifest retry/fallback
      handle outliers. At frozen closeout, do not repeat those commands by
      default: let the planner schedule the required delta.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [ ] Build or select reusable library APIs before adding paper-local wrappers.
- [ ] Replace the paper scaffold with complete source-facing Lean definitions,
      transparent `<name>Spec : Prop` statements, and theorem/lemma routes typed
      exactly by those specifications; use `by sorry` only for temporary private
      proof bodies.
- [ ] Independently inventory every material source atom from exact pinned quote
      bytes before Lean review. At full closeout, bind those atoms to the
      elaborated Spec and account for every material closure terminal, including
      proof and instance arguments; no declaration, data, or container category
      is an automatic exemption.
- [ ] Run recursive source-record/conclusion-provenance checks and raw
      byte-pinned-source-to-expanded-Spec matching on every skeleton claim;
      record and freeze each signature digest. The paired theorem is only proof
      evidence, not a second semantic match.
- [ ] Complete numeric and discrete obligation partitions; do not claim absence
      when the elaborated manifest exposes arithmetic or list operations.
- [ ] Complete the applicable fidelity-risk dimensions from expanded semantics:
      output/conclusion shape, action or input space, witness/optimization
      semantics, cardinality/quantification, and, for executable results,
      input scope, state transitions, termination, numeric representation, cost,
      and the global-claim bridge.
- [ ] For every runtime claim, audit the transitive operational dependency graph
      over every reachable branch; refinement alone is not cost evidence. Give a
      worst-case recurrence and bound, and completely account for traversal,
      duplicates, materialization, representation primitives, and rational bit
      growth. Missing or excluded work withholds a runtime match; materially
      eliminated closure dependencies need artifact/source hashes and semantic
      binding to generated IR/C or a cost-threaded executor.
- [ ] Review every source proof route used; record source proof defects as
      mathematical repair obligations, never as source assumptions.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Replace every skeleton `sorry` without changing its audited specification
      or theorem type; rerun statement audit whenever either changes.
- [ ] At closeout, update README, status, DAG, and validation report from the
      same row list.
- [ ] At closeout, freeze the paper inputs and run the reuse planner. Let its
      ordered actions own the targeted paper build, audits,
      placeholder/provenance checks, and DAG validation; do not pre-run those
      gates just to recreate an intermediate receipt.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
- Validation/audit checks that must inspect these assumptions:
"""


def final_validation_report_text(title: str, folder: str) -> str:
    title_text = title or "[Paper Short Name]"
    template = (PAPERS / "TEMPLATE" / "FINAL_VALIDATION_REPORT.md").read_text(
        encoding="utf-8"
    )
    return template.replace(
        "# Final Validation Report: [Paper Short Name]",
        f"# Final Validation Report: {title_text}",
        1,
    ).replace("papers/TEMPLATE", f"papers/{folder}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "url", help="paper URL; arXiv abs URLs are converted to PDF URLs"
    )
    parser.add_argument(
        "--folder", help="citation-style folder name, e.g. ABC24ShortTitle"
    )
    parser.add_argument("--title", help="paper title for README and theorem ledger")
    parser.add_argument("--authors", help="paper authors for README")
    parser.add_argument(
        "--version", help="source version, conference, journal, or arXiv version"
    )
    parser.add_argument(
        "--official-url", help="canonical paper URL if different from input URL"
    )
    parser.add_argument("--pdf-url", help="direct PDF URL if different from input URL")
    parser.add_argument(
        "--namespace", help="Lean namespace; defaults to sanitized folder name"
    )
    parser.add_argument(
        "--statement-spec",
        type=Path,
        help=(
            "JSON file containing exact theorem targets plus a verified local source artifact; "
            "target types are validated against the imported EconCSLib surface; without it "
            "PaperInterface.lean is intentionally empty"
        ),
    )
    parser.add_argument(
        "--no-download",
        action="store_true",
        help="scaffold files without downloading the PDF",
    )
    parser.add_argument(
        "--force", action="store_true", help="overwrite existing scaffold files"
    )
    parser.add_argument(
        "--with-notes",
        action="store_true",
        help="generate PAPER_NOTES.md handoff checklist",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help=(
            "build the dashboard cache immediately; normally defer this until the "
            "source inventory and PaperInterface statement skeleton are frozen"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    folder = args.folder or derive_folder(args.url)
    namespace = args.namespace or lean_namespace(folder)
    try:
        validate_scaffold_cli_inputs(args, folder, namespace)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    statement_spec: StatementSpec | None = None
    if args.statement_spec is not None:
        try:
            statement_spec = load_statement_spec(args.statement_spec)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        if not args.version or PLACEHOLDER_RE.search(args.version):
            print("error: --version is required with --statement-spec", file=sys.stderr)
            return 2
        if args.version.strip() != statement_spec.source_version:
            print(
                "error: --version does not match statement spec source_version",
                file=sys.stderr,
            )
            return 2
    targets = statement_spec.targets if statement_spec is not None else []

    paper_dir = PAPERS / folder
    paper_dir.mkdir(parents=True, exist_ok=True)
    docs_dir = paper_dir / "docs"
    audit_dir = paper_dir / "audit"
    docs_dir.mkdir(exist_ok=True)
    audit_dir.mkdir(exist_ok=True)

    pdf = paper_dir / "source.pdf"
    txt = paper_dir / "source.txt"
    audited_source: Path | None = None

    if statement_spec is not None:
        audited_source = paper_dir / audited_source_filename(
            statement_spec.source_artifact_path
        )
        if audited_source.exists() and not args.force:
            existing_sha256 = hashlib.sha256(audited_source.read_bytes()).hexdigest()
            if existing_sha256 != statement_spec.source_artifact_sha256:
                print(
                    f"error: existing {audited_source.relative_to(ROOT)} does not match statement spec artifact",
                    file=sys.stderr,
                )
                return 2
        elif statement_spec.source_artifact_path.resolve() != audited_source.resolve():
            shutil.copyfile(statement_spec.source_artifact_path, audited_source)
            print(
                f"copied verified source artifact to {audited_source.relative_to(ROOT)}"
            )
        copied_sha256 = hashlib.sha256(audited_source.read_bytes()).hexdigest()
        if copied_sha256 != statement_spec.source_artifact_sha256:
            print(
                "error: copied source artifact failed SHA-256 verification",
                file=sys.stderr,
            )
            return 2

    source_proof_artifact_path = ""
    source_proof_artifact_sha256 = ""
    source_text_artifact: dict[str, object] | None = None
    if audited_source is not None and statement_spec is not None:
        source_proof_artifact_path = str(audited_source.relative_to(ROOT))
        source_proof_artifact_sha256 = statement_spec.source_artifact_sha256
        if audited_source.suffix.lower() == ".pdf":
            if extract_text(audited_source, txt, True):
                source_text_artifact = normalized_source_text_receipt(
                    txt,
                    source_artifact_path=source_proof_artifact_path,
                    source_artifact_sha256=source_proof_artifact_sha256,
                )

    rendered_interface = paper_interface_text(
        args.title or "", folder, namespace, targets
    )
    rendered_proof_interface = proof_interface_text(
        args.title or "", folder, namespace, targets
    )
    try:
        validate_rendered_statement_interface(namespace, targets, rendered_interface)
        validate_rendered_proof_interface(
            namespace, targets, rendered_proof_interface
        )
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    write_file(paper_dir / ".gitignore", gitignore_text(), args.force)
    write_file(paper_dir / "README.md", readme_text(args, folder, targets), args.force)
    write_file(
        paper_dir / "status.json", status_text(args, folder, targets), args.force
    )
    write_file(
        audit_dir / "lean_to_tex_llm.json", lean_to_tex_llm_text(folder), args.force
    )
    write_file(
        audit_dir / "statement_match_llm.json",
        statement_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "library_semantic_review.json",
        library_semantic_review_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "v11_raw_source_spec_screening.json",
        v11_raw_source_spec_screening_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "review_surface_llm.json",
        review_surface_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "paper_coverage_llm.json",
        paper_coverage_llm_text(
            folder,
            source_artifact_path=source_proof_artifact_path,
            source_artifact_sha256=source_proof_artifact_sha256,
        ),
        args.force,
    )
    write_file(
        audit_dir / "defect_support_match_llm.json",
        defect_support_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "assumption_match_llm.json",
        assumption_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "source_record_match_llm.json",
        source_record_match_llm_text(folder),
        args.force,
    )
    write_file(
        audit_dir / "source_proof_fidelity.json",
        source_proof_fidelity_text(
            folder,
            source_proof_artifact_path,
            source_proof_artifact_sha256,
        ),
        args.force,
    )
    if statement_spec is not None:
        copied_source_path = str(audited_source.relative_to(ROOT))
        write_file(
            audit_dir / "paper_statement_map.json",
            paper_statement_map_text(
                args,
                folder,
                statement_spec,
                copied_source_path,
            ),
            args.force,
        )
        write_file(
            audit_dir / "intake_freeze.json",
            intake_freeze_text(
                folder,
                statement_spec,
                copied_source_path,
                source_text_artifact,
            ),
            args.force,
        )
    else:
        write_file(
            audit_dir / "intake_freeze.json",
            intake_freeze_text(folder, None, ""),
            args.force,
        )
    launch_script = paper_dir / "review-dashboard.sh"
    write_file(
        launch_script,
        review_launcher_text(),
        args.force,
    )
    launch_script.chmod(0o755)
    write_file(
        paper_dir / "FINAL_VALIDATION_REPORT.md",
        final_validation_report_text(args.title or "", folder),
        args.force,
    )
    write_file(docs_dir / "DependencyDAG.tex", dag_text(), args.force)
    write_file(
        docs_dir / "FORMALIZATION_PLAN.md",
        formalization_plan_text(
            args.title or "", namespace, targets, paper_root=folder
        ),
        args.force,
    )
    write_file(
        paper_dir / "MainTheorems.lean",
        main_theorems_text(args.title or "", namespace),
        args.force,
    )
    write_file(
        paper_dir / "Assumptions.lean",
        assumption_source_text(args.title or "", folder, namespace),
        args.force,
    )
    write_file(
        paper_dir / "PaperInterface.lean",
        rendered_interface,
        args.force,
    )
    write_file(
        paper_dir / "ProofInterface.lean",
        rendered_proof_interface,
        args.force,
    )
    write_file(PAPERS / f"{folder}.lean", root_import_text(folder), args.force)
    if args.with_notes:
        write_file(
            paper_dir / "PAPER_NOTES.md",
            notes_text(args.title or "", namespace, args),
            args.force,
        )

    if statement_spec is None and not args.no_download:
        downloaded = download_pdf(args.pdf_url or args.url, pdf, args.force)
        if downloaded:
            extract_text(pdf, txt, args.force)
    elif statement_spec is None:
        print("skipped PDF download")

    if statement_spec is None:
        print(
            "no --statement-spec supplied; PaperInterface.lean contains no theorem placeholder"
        )

    if not synchronize_scaffold_readme(folder):
        return 2

    if getattr(args, "refresh_cache", False):
        refresh_review_cache(folder)
    else:
        print(
            "deferred dashboard cache: freeze the source inventory and "
            "PaperInterface first, then run `python3 scripts/review_dashboard.py "
            f"--paper {folder} --refresh-cache` once"
        )

    print(f"paper scaffold ready: {paper_dir.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
