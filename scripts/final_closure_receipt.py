#!/usr/bin/env python3
"""Issue and validate the canonical final paper-closure receipt.

The final receipt deliberately has two evidence lanes.  A current raw
source-record audit is the ordinary lane.  A deliberately selected,
source-anchor-based direct-row review is the compatibility lane for a paper
whose current closeout was completed without regenerating a historical raw
machine receipt.  Both lanes bind the same current source, source map,
transitive Lean interface closure, review ledger, focused build declaration,
and semantic review protocol.

This module is intentionally independent of ``audit_evidence_integrity`` so
the main evidence gate can use it without a circular import.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Mapping

try:
    from scripts.formalization_protocol import formalization_review_protocol_digest
    from scripts.lean_import_closure import WorktreeImportClosureProvider
    from scripts.source_archive_surface import source_archive_surface_validation_issues
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:  # pragma: no cover - direct script invocation.
    from formalization_protocol import formalization_review_protocol_digest
    from lean_import_closure import WorktreeImportClosureProvider
    from source_archive_surface import source_archive_surface_validation_issues
    from tomllib_compat import tomllib


ROOT = Path(
    os.environ.get("ECONCSLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
RECEIPT_NAME = "FINAL_CLOSURE_RECEIPT.md"
RECEIPT_SCHEMA = 3
LEGACY_RECEIPT_SCHEMAS = frozenset({2, RECEIPT_SCHEMA})
FOCUSED_BUILD_RECEIPT_NAME = "FOCUSED_BUILD_RECEIPT.json"
FOCUSED_BUILD_RECEIPT_SCHEMA = 1
RAW_SOURCE_RECORD_LANE = "raw-source-record"
DIRECT_SOURCE_ROW_REVIEW_LANE = "direct-source-row-review"
EVIDENCE_LANES = frozenset({RAW_SOURCE_RECORD_LANE, DIRECT_SOURCE_ROW_REVIEW_LANE})
V11_SCREENING_LEDGER_RELATIVE = Path("audit") / "v11_raw_source_spec_screening.json"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")
REPORT_EVIDENCE_START_MARKER = "## 12. Detailed Formalization Evidence"


class FinalClosureReceiptError(ValueError):
    """A final closure receipt is missing, malformed, or no longer current."""


@dataclass(frozen=True)
class FinalClosureReceipt:
    """Parsed canonical receipt payload and its source path."""

    path: Path
    payload: Mapping[str, Any]


def final_closure_receipt_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / RECEIPT_NAME


def focused_build_receipt_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / "audit" / FOCUSED_BUILD_RECEIPT_NAME


def _sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_file(path: Path) -> str:
    try:
        return _sha256_bytes(path.read_bytes())
    except OSError as exc:
        raise FinalClosureReceiptError(f"could not read `{path}`: {exc}") from exc


def _required_string(payload: Mapping[str, Any], field: str) -> str:
    value = payload.get(field)
    if not isinstance(value, str) or not value.strip():
        raise FinalClosureReceiptError(f"`{field}` must be a nonempty string")
    return value.strip()


def _required_sha256(payload: Mapping[str, Any], field: str) -> str:
    value = _required_string(payload, field).lower()
    if not SHA256_RE.fullmatch(value):
        raise FinalClosureReceiptError(f"`{field}` must be a lowercase SHA-256")
    return value


def _mapping(payload: Mapping[str, Any], field: str) -> Mapping[str, Any]:
    value = payload.get(field)
    if not isinstance(value, Mapping):
        raise FinalClosureReceiptError(f"`{field}` must be a table")
    return value


def _repository_path(root: Path, raw: str, *, field: str) -> Path:
    path = PurePosixPath(raw)
    if (
        not raw
        or path.is_absolute()
        or "\\" in raw
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be a repository-relative path without `..`"
        )
    candidate = root / Path(*path.parts)
    try:
        candidate.resolve(strict=False).relative_to(root.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError(
            f"`{field}.path` resolves outside the repository"
        ) from exc
    return candidate


def _paper_local_path(root: Path, paper: str, raw: str, *, field: str) -> Path:
    normalized = str(raw).strip()
    path = PurePosixPath(normalized)
    if (
        not normalized
        or path.is_absolute()
        or "\\" in normalized
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be a paper-local or repository-relative path without `..`"
        )
    paper_dir = root / "papers" / paper
    candidate = (
        _repository_path(root, normalized, field=field)
        if path.parts[:1] == ("papers",)
        else paper_dir.joinpath(*path.parts)
    )
    try:
        candidate.resolve(strict=False).relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError(
            f"`{field}.path` must stay within papers/{paper}"
        ) from exc
    return candidate


def _source_artifact_path_from_map(root: Path, paper: str, raw: str) -> Path:
    """Resolve either accepted map spelling while enforcing paper locality."""

    return _paper_local_path(root, paper, str(raw).strip(), field="source_artifact")


def _read_toml_front_matter(path: Path) -> Mapping[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise FinalClosureReceiptError(f"could not read final closure receipt: {exc}") from exc
    lines = text.splitlines(keepends=True)
    if not lines or lines[0].strip() != "+++":
        raise FinalClosureReceiptError("receipt must start with TOML `+++` front matter")
    closing = next(
        (index for index, line in enumerate(lines[1:], start=1) if line.strip() == "+++"),
        None,
    )
    if closing is None:
        raise FinalClosureReceiptError("receipt TOML front matter has no closing `+++`")
    try:
        payload = tomllib.loads("".join(lines[1:closing]))
    except (TypeError, tomllib.TOMLDecodeError) as exc:
        raise FinalClosureReceiptError(f"receipt TOML front matter is invalid: {exc}") from exc
    if not isinstance(payload, Mapping):  # Defensive for alternate TOML backends.
        raise FinalClosureReceiptError("receipt TOML front matter must be an object")
    return payload


def load_final_closure_receipt(root: Path, paper: str) -> FinalClosureReceipt:
    if not PAPER_RE.fullmatch(paper):
        raise FinalClosureReceiptError("paper identifier is malformed")
    path = final_closure_receipt_path(root, paper)
    if not path.is_file():
        raise FinalClosureReceiptError(f"missing canonical receipt `{path.relative_to(root)}`")
    return FinalClosureReceipt(path=path, payload=_read_toml_front_matter(path))


def _expect_exact_keys(
    value: Mapping[str, Any], *, field: str, required: set[str]
) -> None:
    actual = set(value)
    if actual != required:
        missing = sorted(required - actual)
        extra = sorted(actual - required)
        parts: list[str] = []
        if missing:
            parts.append("missing " + ", ".join(missing))
        if extra:
            parts.append("unexpected " + ", ".join(extra))
        raise FinalClosureReceiptError(f"`{field}` has " + "; ".join(parts))


def _validate_file_pin(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
    *,
    field: str,
    expected_path: Path | None = None,
    paper_local: bool = True,
) -> Path:
    pin = _mapping(payload, field)
    _expect_exact_keys(pin, field=field, required={"path", "sha256"})
    raw_path = _required_string(pin, "path")
    candidate = (
        _paper_local_path(root, paper, raw_path, field=field)
        if paper_local
        else _repository_path(root, raw_path, field=field)
    )
    if expected_path is not None and candidate.resolve(strict=False) != expected_path.resolve(
        strict=False
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be `{expected_path.relative_to(root).as_posix()}`"
        )
    expected_hash = _required_sha256(pin, "sha256")
    actual_hash = _sha256_file(candidate)
    if actual_hash != expected_hash:
        raise FinalClosureReceiptError(
            f"`{field}` SHA-256 is stale for `{candidate.relative_to(root)}`"
        )
    return candidate


def _review_ledger_selected_bytes(path: Path, *, content_start: str | None) -> bytes:
    """Return the evidence-bearing bytes of a review ledger.

    A final validation report has a deliberately editable paper-facing front
    section.  Its detailed evidence begins at a stable heading, so bind that
    evidence section rather than making a prose clarification in Sections 1--11
    invalidate the paper's canonical closure.  A standalone row-review ledger
    remains byte-pinned in full.
    """

    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise FinalClosureReceiptError(f"could not read `{path}`: {exc}") from exc
    if content_start is None:
        return raw
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise FinalClosureReceiptError(
            f"review ledger `{path}` cannot use a text evidence boundary"
        ) from exc
    matches = [
        match.start()
        for match in re.finditer(
            rf"(?m)^{re.escape(content_start)}\s*$",
            text,
        )
    ]
    if len(matches) != 1:
        raise FinalClosureReceiptError(
            f"review ledger evidence boundary `{content_start}` must occur exactly once"
        )
    return text[matches[0] :].encode("utf-8")


def _review_ledger_pin(root: Path, path: Path) -> dict[str, str]:
    """Create the lane-specific immutable review-evidence pin for ``path``."""

    content_start = (
        REPORT_EVIDENCE_START_MARKER
        if path.name == "FINAL_VALIDATION_REPORT.md"
        else None
    )
    pin = {
        "path": path.relative_to(root).as_posix(),
        "sha256": _sha256_bytes(
            _review_ledger_selected_bytes(path, content_start=content_start)
        ),
    }
    if content_start is not None:
        pin["content_start"] = content_start
    return pin


def _validate_review_ledger_pin(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
) -> Path:
    """Validate the source-review bytes without hashing report front matter."""

    pin = _mapping(payload, "review_ledger")
    allowed = {"path", "sha256", "content_start"}
    unexpected = set(pin) - allowed
    if unexpected:
        raise FinalClosureReceiptError(
            "`review_ledger` has unexpected " + ", ".join(sorted(unexpected))
        )
    required = {"path", "sha256"}
    missing = required - set(pin)
    if missing:
        raise FinalClosureReceiptError(
            "`review_ledger` missing " + ", ".join(sorted(missing))
        )
    raw_path = _required_string(pin, "path")
    path = _repository_path(root, raw_path, field="review_ledger")
    try:
        path.resolve(strict=False).relative_to((root / "papers" / paper).resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError("`review_ledger.path` must stay within this paper") from exc
    raw_boundary = pin.get("content_start")
    if raw_boundary is not None and (
        not isinstance(raw_boundary, str) or not raw_boundary.strip()
    ):
        raise FinalClosureReceiptError("`review_ledger.content_start` must be a nonempty string")
    content_start = raw_boundary.strip() if isinstance(raw_boundary, str) else None
    if path.name == "FINAL_VALIDATION_REPORT.md" and content_start != REPORT_EVIDENCE_START_MARKER:
        raise FinalClosureReceiptError(
            "`review_ledger` must bind the detailed-evidence section of FINAL_VALIDATION_REPORT.md"
        )
    expected_hash = _required_sha256(pin, "sha256")
    actual_hash = _sha256_bytes(
        _review_ledger_selected_bytes(path, content_start=content_start)
    )
    if actual_hash != expected_hash:
        raise FinalClosureReceiptError(
            f"`review_ledger` SHA-256 is stale for `{path.relative_to(root)}`"
        )
    return path


def _current_interface_closure(
    root: Path,
    paper: str,
    *,
    closure_provider_factory: Callable[[Path], Any] = WorktreeImportClosureProvider,
) -> str:
    provider = closure_provider_factory(root)
    entrypoint = f"papers/{paper}/PaperInterface.lean"
    identity, problem = provider.identity_for_entrypoint(entrypoint)
    if identity is None or problem is not None:
        raise FinalClosureReceiptError(
            "could not establish current transitive PaperInterface closure: "
            + str(problem or "unknown closure failure")
        )
    problems = provider.finalization_problems()
    if problems:
        raise FinalClosureReceiptError(
            "PaperInterface closure changed while validated: " + str(problems[0])
        )
    return identity


def validate_final_closure_receipt(
    root: Path,
    paper: str,
    *,
    required_lane: str | None = None,
    allow_missing_source_bytes: bool = False,
    closure_provider_factory: Callable[[Path], Any] = WorktreeImportClosureProvider,
) -> FinalClosureReceipt:
    """Fail closed unless the one paper-local receipt binds every current input.

    A public structural checkout may intentionally omit licensed source bytes.
    In that mode, retain the exact path and statement-map hash checks, but use
    the receipt's immutable source pin instead of trying to read absent bytes.
    This is validation of an already-issued receipt, never permission to issue
    a new one without the canonical source artifact.
    """

    receipt = load_final_closure_receipt(root, paper)
    payload = receipt.payload
    schema = payload.get("schema")
    if schema not in LEGACY_RECEIPT_SCHEMAS:
        expected = ", ".join(str(value) for value in sorted(LEGACY_RECEIPT_SCHEMAS))
        raise FinalClosureReceiptError(f"`schema` must equal one of {expected}")
    if _required_string(payload, "paper") != paper:
        raise FinalClosureReceiptError("receipt `paper` does not match its folder")
    if _required_string(payload, "closure_status") != "current":
        raise FinalClosureReceiptError("receipt `closure_status` must be `current`")
    lane = _required_string(payload, "evidence_lane")
    if lane not in EVIDENCE_LANES:
        raise FinalClosureReceiptError("receipt `evidence_lane` is unsupported")
    if required_lane is not None and lane != required_lane:
        raise FinalClosureReceiptError(
            f"receipt evidence lane is `{lane}`, expected `{required_lane}`"
        )

    allowed = {
        "schema",
        "paper",
        "closure_status",
        "evidence_lane",
        "source_artifact",
        "statement_map",
        "paper_interface_closure",
        "review_ledger",
        "focused_build",
        "protocol",
        "closed_at",
    }
    if lane == RAW_SOURCE_RECORD_LANE:
        allowed.add("raw_source_record")
    if schema == RECEIPT_SCHEMA:
        allowed.add("focused_build_receipt")
    _expect_exact_keys(payload, field="receipt", required=allowed)

    paper_dir = root / "papers" / paper
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    map_pin = _mapping(payload, "statement_map")
    _expect_exact_keys(map_pin, field="statement_map", required={"path", "sha256"})
    expected_map_path = map_path.relative_to(root).as_posix()
    if _required_string(map_pin, "path") != expected_map_path:
        raise FinalClosureReceiptError(
            f"`statement_map.path` must be `{expected_map_path}`"
        )
    _validate_file_pin(
        root,
        paper,
        payload,
        field="statement_map",
        expected_path=map_path,
        paper_local=False,
    )
    try:
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(f"current statement map is unreadable: {exc}") from exc
    if not isinstance(source_map, Mapping):
        raise FinalClosureReceiptError("current statement map must be an object")
    archive_surface_issues = source_archive_surface_validation_issues(
        paper_dir,
        source_map,
        repository_root=root,
        require_source_bytes=not allow_missing_source_bytes,
    )
    if archive_surface_issues:
        raise FinalClosureReceiptError(
            "current archive-source provenance is invalid: "
            + "; ".join(issue.message for issue in archive_surface_issues)
        )
    source_relative = _required_string(source_map, "source_artifact_path")
    expected_source = _source_artifact_path_from_map(root, paper, source_relative)
    source_pin = _mapping(payload, "source_artifact")
    _expect_exact_keys(source_pin, field="source_artifact", required={"path", "sha256"})
    source_pin = _mapping(payload, "source_artifact")
    _expect_exact_keys(source_pin, field="source_artifact", required={"path", "sha256"})
    source_path = _repository_path(
        root, _required_string(source_pin, "path"), field="source_artifact"
    )
    if source_path.resolve(strict=False) != expected_source.resolve(strict=False):
        raise FinalClosureReceiptError(
            "`source_artifact.path` must be "
            f"`{expected_source.relative_to(root).as_posix()}`"
        )
    map_source_hash = _required_sha256(source_map, "source_artifact_sha256")
    receipt_source_hash = _required_sha256(source_pin, "sha256")
    if receipt_source_hash != map_source_hash:
        raise FinalClosureReceiptError(
            "source-artifact pin does not agree with current paper_statement_map.json"
        )
    if source_path.exists():
        if not source_path.is_file() or _sha256_file(source_path) != map_source_hash:
            raise FinalClosureReceiptError(
                "source-artifact pin does not agree with current paper_statement_map.json"
            )
    elif not allow_missing_source_bytes:
        raise FinalClosureReceiptError(
            f"could not read `{source_path}`: canonical source bytes are unavailable"
        )

    closure = _mapping(payload, "paper_interface_closure")
    _expect_exact_keys(closure, field="paper_interface_closure", required={"root", "sha256"})
    if _required_string(closure, "root") != "PaperInterface.lean":
        raise FinalClosureReceiptError(
            "`paper_interface_closure.root` must be `PaperInterface.lean`"
        )
    if _required_sha256(closure, "sha256") != _current_interface_closure(
        root, paper, closure_provider_factory=closure_provider_factory
    ):
        raise FinalClosureReceiptError(
            "PaperInterface transitive import-closure SHA-256 is stale"
        )

    ledger_path = _validate_review_ledger_pin(root, paper, payload)

    focused_build = _mapping(payload, "focused_build")
    _expect_exact_keys(
        focused_build, field="focused_build", required={"command", "target", "result", "commit"}
    )
    status_path = paper_dir / "status.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(f"current status file is unreadable: {exc}") from exc
    expected_command = _required_string(status, "build_target")
    if (
        lane == DIRECT_SOURCE_ROW_REVIEW_LANE
        and _status_requires_v11_source_spec_screening(status)
        and ledger_path.resolve() != (paper_dir / V11_SCREENING_LEDGER_RELATIVE).resolve()
    ):
        raise FinalClosureReceiptError(
            "a v11 source-spec closeout using direct-source-row-review must bind "
            f"`{V11_SCREENING_LEDGER_RELATIVE.as_posix()}` as its review ledger"
        )
    if _required_string(focused_build, "command") != expected_command:
        raise FinalClosureReceiptError(
            "focused build command does not match current status build_target"
        )
    if _required_string(focused_build, "target") != paper:
        raise FinalClosureReceiptError("focused build target does not match the paper")
    if _required_string(focused_build, "result") != "passed":
        raise FinalClosureReceiptError("focused build result must be `passed`")
    commit = _required_string(focused_build, "commit").lower()
    if not GIT_COMMIT_RE.fullmatch(commit):
        raise FinalClosureReceiptError("focused build commit must be a lowercase Git commit")
    if schema == RECEIPT_SCHEMA:
        build_receipt_path = _validate_file_pin(
            root,
            paper,
            payload,
            field="focused_build_receipt",
            expected_path=focused_build_receipt_path(root, paper),
            paper_local=False,
        )
        if build_receipt_path != focused_build_receipt_path(root, paper):
            raise FinalClosureReceiptError("focused build receipt path is invalid")
        build_receipt = validate_focused_build_receipt(root, paper)
        if _required_string(build_receipt, "commit").lower() != commit:
            raise FinalClosureReceiptError(
                "focused build receipt commit disagrees with final receipt"
            )

    protocol = _mapping(payload, "protocol")
    _expect_exact_keys(
        protocol,
        field="protocol",
        required={"formalization_review_protocol_sha256"},
    )
    if _required_sha256(protocol, "formalization_review_protocol_sha256") != (
        formalization_review_protocol_digest()
    ):
        raise FinalClosureReceiptError("formalization review protocol digest is stale")
    closed_at = _required_string(payload, "closed_at")
    try:
        date.fromisoformat(closed_at)
    except ValueError as exc:
        raise FinalClosureReceiptError("`closed_at` must be YYYY-MM-DD") from exc

    if lane == RAW_SOURCE_RECORD_LANE:
        _validate_file_pin(
            root,
            paper,
            payload,
            field="raw_source_record",
            expected_path=paper_dir / "audit" / "source_record_audit.json",
            paper_local=False,
        )
    return receipt


def final_closure_receipt_error(
    root: Path,
    paper: str,
    *,
    required_lane: str | None = None,
    allow_missing_source_bytes: bool = False,
) -> str:
    """Return one concise error instead of raising for audit-gate composition."""

    try:
        validate_final_closure_receipt(
            root,
            paper,
            required_lane=required_lane,
            allow_missing_source_bytes=allow_missing_source_bytes,
        )
    except FinalClosureReceiptError as exc:
        return str(exc)
    return ""


def direct_source_row_review_receipt_error(
    root: Path, paper: str, *, allow_missing_source_bytes: bool = False
) -> str:
    """Validate the explicit direct-review lane; never infer it from a report."""

    return final_closure_receipt_error(
        root,
        paper,
        required_lane=DIRECT_SOURCE_ROW_REVIEW_LANE,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )


def _toml_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    head = result.stdout.strip().lower()
    if result.returncode != 0 or not GIT_COMMIT_RE.fullmatch(head):
        raise FinalClosureReceiptError(
            "could not determine the current Git commit for receipt issuance"
        )
    return head


def _focused_build(root: Path, command: str) -> None:
    try:
        argv = shlex.split(command)
    except ValueError as exc:
        raise FinalClosureReceiptError(f"focused build command cannot be parsed: {exc}") from exc
    if not argv:
        raise FinalClosureReceiptError("focused build command is empty")
    completed = subprocess.run(argv, cwd=root, check=False)
    if completed.returncode != 0:
        raise FinalClosureReceiptError(
            f"focused build failed with exit code {completed.returncode}"
        )


def _current_focused_build_inputs(
    root: Path, paper: str
) -> tuple[Mapping[str, Any], Mapping[str, Any], Path, Path, Path, Path]:
    """Return the source/code inputs a focused build is allowed to certify."""

    paper_dir = root / "papers" / paper
    status_path = paper_dir / "status.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    interface_path = paper_dir / "PaperInterface.lean"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(
            f"cannot read focused-build inputs: {exc}"
        ) from exc
    if not isinstance(status, Mapping) or not isinstance(source_map, Mapping):
        raise FinalClosureReceiptError("focused-build inputs must be JSON objects")
    source_relative = _required_string(source_map, "source_artifact_path")
    source_path = _source_artifact_path_from_map(root, paper, source_relative)
    if not interface_path.is_file():
        raise FinalClosureReceiptError("PaperInterface.lean is unavailable")
    return status, source_map, source_path, status_path, map_path, interface_path


def record_focused_build_receipt(root: Path, paper: str) -> Path:
    """Run the focused build and preserve a reusable, input-pinned result.

    This is operational evidence only.  The canonical final-closeout authority
    remains ``FINAL_CLOSURE_RECEIPT.md``; it can reuse this record only while
    its source, interface, map, and protocol pins are still current.
    """

    status, _source_map, source_path, status_path, map_path, interface_path = (
        _current_focused_build_inputs(root, paper)
    )
    command = _required_string(status, "build_target")
    _focused_build(root, command)
    payload = {
        "schema": FOCUSED_BUILD_RECEIPT_SCHEMA,
        "paper": paper,
        "command": command,
        "target": paper,
        "result": "passed",
        "commit": _git_head(root),
        "status_sha256": _sha256_file(status_path),
        "statement_map_sha256": _sha256_file(map_path),
        "source_artifact_sha256": _sha256_file(source_path),
        "paper_interface_sha256": _sha256_file(interface_path),
        "formalization_review_protocol_sha256": formalization_review_protocol_digest(),
    }
    path = focused_build_receipt_path(root, paper)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    validate_focused_build_receipt(root, paper, require_current_head=True)
    return path


def validate_focused_build_receipt(
    root: Path, paper: str, *, require_current_head: bool = False
) -> Mapping[str, Any]:
    """Check a recorded focused build without treating it as final closure."""

    path = focused_build_receipt_path(root, paper)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(
            f"could not read focused build receipt: {exc}"
        ) from exc
    required = {
        "schema",
        "paper",
        "command",
        "target",
        "result",
        "commit",
        "status_sha256",
        "statement_map_sha256",
        "source_artifact_sha256",
        "paper_interface_sha256",
        "formalization_review_protocol_sha256",
    }
    if not isinstance(payload, Mapping) or set(payload) != required:
        raise FinalClosureReceiptError("focused build receipt fields are malformed")
    if payload.get("schema") != FOCUSED_BUILD_RECEIPT_SCHEMA:
        raise FinalClosureReceiptError("focused build receipt schema is unsupported")
    if _required_string(payload, "paper") != paper:
        raise FinalClosureReceiptError("focused build receipt paper does not match")
    status, _source_map, source_path, status_path, map_path, interface_path = (
        _current_focused_build_inputs(root, paper)
    )
    if _required_string(payload, "command") != _required_string(status, "build_target"):
        raise FinalClosureReceiptError("focused build receipt command is stale")
    if _required_string(payload, "target") != paper:
        raise FinalClosureReceiptError("focused build receipt target is stale")
    if _required_string(payload, "result") != "passed":
        raise FinalClosureReceiptError("focused build receipt did not pass")
    commit = _required_string(payload, "commit").lower()
    if not GIT_COMMIT_RE.fullmatch(commit):
        raise FinalClosureReceiptError("focused build receipt commit is malformed")
    if require_current_head and commit != _git_head(root):
        raise FinalClosureReceiptError(
            "focused build receipt was issued for a different Git commit"
        )
    expected_pins = {
        "status_sha256": status_path,
        "statement_map_sha256": map_path,
        "source_artifact_sha256": source_path,
        "paper_interface_sha256": interface_path,
    }
    for field, current_path in expected_pins.items():
        if _required_sha256(payload, field) != _sha256_file(current_path):
            raise FinalClosureReceiptError(f"focused build receipt `{field}` is stale")
    if _required_sha256(
        payload, "formalization_review_protocol_sha256"
    ) != formalization_review_protocol_digest():
        raise FinalClosureReceiptError("focused build receipt protocol is stale")
    return payload


def _status_requires_v11_source_spec_screening(status: Mapping[str, Any]) -> bool:
    review_surface = status.get("review_surface")
    return isinstance(review_surface, Mapping) and review_surface.get(
        "require_source_spec_correspondence"
    ) is True


def issue_final_closure_receipt(
    root: Path,
    paper: str,
    *,
    evidence_lane: str,
    review_ledger_path: str,
    run_build: bool,
    reuse_focused_build_receipt: bool = False,
) -> Path:
    """Run the focused build and write a newly current canonical receipt."""

    if evidence_lane not in EVIDENCE_LANES:
        raise FinalClosureReceiptError("unsupported evidence lane")
    if run_build == reuse_focused_build_receipt:
        raise FinalClosureReceiptError(
            "issue exactly one focused-build proof: `--run-focused-build` or a current focused build receipt"
        )
    paper_dir = root / "papers" / paper
    status_path = paper_dir / "status.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(f"cannot issue receipt from unreadable input: {exc}") from exc
    if not isinstance(status, Mapping) or not isinstance(source_map, Mapping):
        raise FinalClosureReceiptError("status and source map must be JSON objects")
    build_command = _required_string(status, "build_target")
    source_relative = _required_string(source_map, "source_artifact_path")
    source_path = _source_artifact_path_from_map(root, paper, source_relative)
    ledger_path = _paper_local_path(root, paper, review_ledger_path, field="review_ledger")
    if not ledger_path.is_file():
        raise FinalClosureReceiptError("review ledger does not exist")
    if (
        evidence_lane == DIRECT_SOURCE_ROW_REVIEW_LANE
        and _status_requires_v11_source_spec_screening(status)
        and ledger_path.resolve() != (paper_dir / V11_SCREENING_LEDGER_RELATIVE).resolve()
    ):
        raise FinalClosureReceiptError(
            "a v11 source-spec closeout using direct-source-row-review must bind "
            f"`{V11_SCREENING_LEDGER_RELATIVE.as_posix()}` as its review ledger"
        )
    build_receipt: Mapping[str, Any] | None = None
    if run_build:
        _focused_build(root, build_command)
        focused_build_commit = _git_head(root)
    else:
        build_receipt = validate_focused_build_receipt(
            root, paper, require_current_head=True
        )
        focused_build_commit = _required_string(build_receipt, "commit")
    closure_digest = _current_interface_closure(root, paper)
    payload: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA if build_receipt is not None else 2,
        "paper": paper,
        "closure_status": "current",
        "evidence_lane": evidence_lane,
        "source_artifact": {
            "path": source_path.relative_to(root).as_posix(),
            "sha256": _sha256_file(source_path),
        },
        "statement_map": {
            "path": map_path.relative_to(root).as_posix(),
            "sha256": _sha256_file(map_path),
        },
        "paper_interface_closure": {
            "root": "PaperInterface.lean",
            "sha256": closure_digest,
        },
        "review_ledger": _review_ledger_pin(root, ledger_path),
        "focused_build": {
            "command": build_command,
            "target": paper,
            "result": "passed",
            "commit": focused_build_commit,
        },
        "protocol": {
            "formalization_review_protocol_sha256": formalization_review_protocol_digest(),
        },
        "closed_at": date.today().isoformat(),
    }
    if evidence_lane == RAW_SOURCE_RECORD_LANE:
        raw_path = paper_dir / "audit" / "source_record_audit.json"
        payload["raw_source_record"] = {
            "path": raw_path.relative_to(root).as_posix(),
            "sha256": _sha256_file(raw_path),
        }
    if build_receipt is not None:
        build_receipt_path = focused_build_receipt_path(root, paper)
        payload["focused_build_receipt"] = {
            "path": build_receipt_path.relative_to(root).as_posix(),
            "sha256": _sha256_file(build_receipt_path),
        }
    text = _render_receipt(payload)
    receipt_path = final_closure_receipt_path(root, paper)
    receipt_path.write_text(text, encoding="utf-8")
    validate_final_closure_receipt(root, paper, required_lane=evidence_lane)
    return receipt_path


def _render_table(name: str, value: Mapping[str, Any]) -> list[str]:
    lines = [f"[{name}]"]
    for key, scalar in value.items():
        lines.append(f"{key} = {_toml_string(str(scalar))}")
    lines.append("")
    return lines


def _render_receipt(payload: Mapping[str, Any]) -> str:
    lines = ["+++"]
    for key in ("schema", "paper", "closure_status", "evidence_lane", "closed_at"):
        value = payload[key]
        lines.append(
            f"{key} = {value}" if isinstance(value, int) else f"{key} = {_toml_string(str(value))}"
        )
    lines.append("")
    for key in (
        "source_artifact",
        "statement_map",
        "paper_interface_closure",
        "review_ledger",
        "raw_source_record",
        "focused_build",
        "focused_build_receipt",
        "protocol",
    ):
        value = payload.get(key)
        if isinstance(value, Mapping):
            lines.extend(_render_table(key, value))
    lines.extend(
        [
            "+++",
            "",
            "# Final Closure Receipt",
            "",
            "This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.",
            "",
        ]
    )
    return "\n".join(lines)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument(
        "--record-focused-build",
        action="store_true",
        help=(
            "run the focused build and write its input-pinned operational receipt; "
            "the canonical final closure receipt may reuse it at the same commit"
        ),
    )
    parser.add_argument("--evidence-lane", choices=sorted(EVIDENCE_LANES))
    parser.add_argument("--review-ledger")
    parser.add_argument("--run-focused-build", action="store_true")
    parser.add_argument(
        "--reuse-focused-build-receipt",
        action="store_true",
        help=(
            "with --write, reuse audit/FOCUSED_BUILD_RECEIPT.json only when its "
            "current input pins and Git commit match"
        ),
    )
    parser.add_argument("--allow-missing-source-bytes", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    selected_actions = sum(
        bool(value) for value in (args.check, args.write, args.record_focused_build)
    )
    if selected_actions != 1:
        raise SystemExit("choose exactly one of --check, --write, or --record-focused-build")
    if args.record_focused_build and (
        args.evidence_lane
        or args.review_ledger
        or args.run_focused_build
        or args.reuse_focused_build_receipt
    ):
        raise SystemExit("--record-focused-build cannot be combined with receipt-issue options")
    if args.reuse_focused_build_receipt and not args.write:
        raise SystemExit("--reuse-focused-build-receipt requires --write")
    if args.write and args.run_focused_build == args.reuse_focused_build_receipt:
        raise SystemExit(
            "--write requires exactly one of --run-focused-build or --reuse-focused-build-receipt"
        )
    try:
        if args.record_focused_build:
            path = record_focused_build_receipt(ROOT, args.paper)
            print(f"wrote {path.relative_to(ROOT)}")
        elif args.check:
            validate_final_closure_receipt(
                ROOT,
                args.paper,
                allow_missing_source_bytes=args.allow_missing_source_bytes,
            )
            print(f"final closure receipt is current: {args.paper}")
        else:
            if not args.evidence_lane or not args.review_ledger:
                raise FinalClosureReceiptError(
                    "--write requires --evidence-lane and --review-ledger"
                )
            path = issue_final_closure_receipt(
                ROOT,
                args.paper,
                evidence_lane=args.evidence_lane,
                review_ledger_path=args.review_ledger,
                run_build=args.run_focused_build,
                reuse_focused_build_receipt=args.reuse_focused_build_receipt,
            )
            print(f"wrote {path.relative_to(ROOT)}")
    except FinalClosureReceiptError as exc:
        print(f"final-closure-receipt: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI wrapper.
    raise SystemExit(main())
