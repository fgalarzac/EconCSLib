#!/usr/bin/env python3
"""Recover a missing historical authenticated manifest store without guessing.

This is a narrow evidence-recovery tool for the case where a historical
statement sidecar remains available but the carrier and authority that backed
its Lean signatures were not archived.  It checks that the surviving sidecar
is byte-identical to a blob in one immutable Git commit, checks out that exact
commit in a temporary detached worktree, and runs the *current* signature
manifest producer against the archived ``PaperInterface.lean`` review surface.

The tool deliberately reconstructs the complete configured review surface.  A
sidecar row, declaration name, source-map key, or function name never selects
or pairs a recovered entry.  Lean declaration names are only transient routing
coordinates needed to ask Lean for the archived roots' elaborated types.  A
later historical-replay bridge must perform its own name-free content pairing.

The public API is :func:`recover_historical_manifest_store`.  It is pure with
respect to the live paper until :func:`write_recovered_manifest_store` is
explicitly called.  The CLI performs the recovery and prints a receipt preview
by default; ``--write`` is required to create its three explicitly supplied
``papers/<paper>/audit/*.json`` artifacts.

This command is not a cache refresh, a statement audit, or a reissue command.
It never writes the normal mutable manifest carrier, the normal tracked
authority, a paper interface, a source sidecar, or a Git ref.  The temporary
worktree is removed before an output receipt is made available.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterable, Mapping, Sequence

try:  # Supports package imports and direct focused-test imports.
    from scripts import authenticated_manifest_store as manifest_store
    from scripts import lean_signature_manifest as manifest_tools
    from scripts import review_dashboard
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import authenticated_manifest_store as manifest_store
    import lean_signature_manifest as manifest_tools
    import review_dashboard


HISTORICAL_MANIFEST_STORE_RECOVERY_SCHEMA = 1
HISTORICAL_MANIFEST_STORE_RECOVERY_ARTIFACT_KIND = (
    "historical_authenticated_manifest_store_recovery"
)
HISTORICAL_MANIFEST_STORE_RECOVERY_POLICY_VERSION = (
    "historical-authenticated-manifest-store-recovery-v1"
)
HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD = (
    "historical_manifest_store_recovery_sha256"
)
HISTORICAL_SEMANTIC_REPLAY_INPUTS_SCHEMA = 1
# These are the historical paper-local artifacts needed to reconstruct the
# content identities consumed by ``semantic_audit_reuse``.  They are optional
# for a generic manifest-store recovery because some archived papers predate
# the relevant lanes; a replay consumer requires the exact subset it needs.
HISTORICAL_SEMANTIC_REPLAY_INPUT_PATHS = (
    "audit/paper_statement_map.json",
    "audit/lean_to_tex_llm.json",
    "audit/source_proof_fidelity.json",
)
CANONICAL_REVIEW_SOURCE = "PaperInterface.lean"
DEFAULT_TIMEOUT_SECONDS = 120
DEFAULT_BUILD_TIMEOUT_SECONDS = 600
DETERMINISTIC_GZIP_POLICY_VERSION = "gzip-mtime0-level1-v1"
MAX_DECOMPRESSED_CARRIER_BYTES = 1024 * 1024 * 1024

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_GIT_OBJECT_ID_RE = re.compile(r"^[0-9a-f]{40}(?:[0-9a-f]{24})?$", re.IGNORECASE)
_PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")


class HistoricalManifestStoreRecoveryError(RuntimeError):
    """Raised when immutable historical-store reconstruction is inadmissible."""


CommandRunner = Callable[[Sequence[str], Path], subprocess.CompletedProcess[bytes]]
ManifestContextProducer = Callable[..., Mapping[str, Any] | None]
ManifestProducer = Callable[..., Mapping[str, Mapping[str, Any]]]
StorePayloadBuilder = Callable[
    [str, Iterable[Mapping[str, Any]]],
    tuple[dict[str, Any], dict[str, Any], set[str]],
]


@dataclass(frozen=True)
class HistoricalReviewDeclaration:
    """One exact archived Lean coordinate used only to request a manifest."""

    qualified_declaration: str
    source_file: str
    lean_source_declaration: str
    line_number: int
    declaration_kind: str


@dataclass(frozen=True)
class HistoricalReviewSource:
    """One archived source/configuration file that selected the review roots."""

    paper_relative_path: str
    content: bytes


@dataclass(frozen=True)
class HistoricalReviewSurface:
    """The archived, configured PaperInterface review surface."""

    import_module: str
    declarations: tuple[HistoricalReviewDeclaration, ...]
    source_files: tuple[HistoricalReviewSource, ...]


@dataclass(frozen=True)
class HistoricalManifestStoreRecoveryConfig:
    """Exact inputs and output locations for one recovery attempt.

    All paths are paper-relative and must live below ``audit/``.  The input
    sidecar is read from the live worktree but has to match the separate
    ``historical_sidecar_git_path`` blob at ``historical_commit`` byte for
    byte.  Use a different Git path only when a surviving archival copy was
    renamed without changing its bytes.
    """

    root: Path
    paper: str
    historical_commit: str
    historical_sidecar_path: str | Path
    authority_output_path: str | Path
    carrier_output_path: str | Path
    receipt_output_path: str | Path
    historical_sidecar_git_path: str | Path | None = None
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS
    build_timeout_seconds: int = DEFAULT_BUILD_TIMEOUT_SECONDS


@dataclass(frozen=True)
class RecoveredHistoricalManifestStore:
    """In-memory recovery result; call the explicit writer to publish it."""

    authority: Mapping[str, Any]
    carrier: Mapping[str, Any]
    receipt: Mapping[str, Any]
    authority_bytes: bytes
    carrier_compressed_bytes: bytes
    carrier_uncompressed_bytes: bytes
    receipt_bytes: bytes
    accepted_declarations: tuple[str, ...]


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def _pretty_json_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _canonical_digest(value: object) -> str:
    return _sha256_bytes(_canonical_json_bytes(value))


def deterministic_gzip_compress(raw: bytes) -> bytes:
    """Return the one permitted compressed representation of a carrier.

    ``gzip.compress`` can expose host-specific header behavior on some Python
    versions.  ``GzipFile`` with an empty filename and a fixed timestamp keeps
    the carrier representation byte-stable across normal recovery runs.
    """

    if not isinstance(raw, bytes):
        raise HistoricalManifestStoreRecoveryError(
            "deterministic gzip input must be bytes"
        )
    output = io.BytesIO()
    with gzip.GzipFile(
        fileobj=output, mode="wb", filename="", compresslevel=1, mtime=0
    ) as handle:
        handle.write(raw)
    return output.getvalue()


def verified_deterministic_gzip_decompress(
    compressed: bytes,
    *,
    expected_compressed_sha256: str,
    expected_uncompressed_sha256: str,
    expected_uncompressed_byte_length: int | None = None,
) -> bytes:
    """Verify and decode one canonical compressed historical carrier.

    Consumers must first obtain the *raw compressed bytes* from a separately
    byte-pinned artifact/receipt.  This helper verifies both compressed and
    decompressed digests, an optional exact raw length, and canonical
    recompression before returning JSON bytes to an existing store validator.
    It therefore does not turn a transparent decompressor into an authority.
    """

    if not isinstance(compressed, bytes):
        raise HistoricalManifestStoreRecoveryError("compressed carrier must be bytes")
    compressed_sha256 = str(expected_compressed_sha256 or "").strip().lower()
    uncompressed_sha256 = str(expected_uncompressed_sha256 or "").strip().lower()
    if not _SHA256_RE.fullmatch(compressed_sha256) or not _SHA256_RE.fullmatch(
        uncompressed_sha256
    ):
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier requires valid compressed and uncompressed SHA-256 pins"
        )
    if _sha256_bytes(compressed) != compressed_sha256:
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier bytes do not match their receipt pin"
        )
    if expected_uncompressed_byte_length is not None and (
        isinstance(expected_uncompressed_byte_length, bool)
        or not isinstance(expected_uncompressed_byte_length, int)
        or expected_uncompressed_byte_length < 0
        or expected_uncompressed_byte_length > MAX_DECOMPRESSED_CARRIER_BYTES
    ):
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier has an invalid uncompressed byte-length pin"
        )
    limit = (
        expected_uncompressed_byte_length
        if expected_uncompressed_byte_length is not None
        else MAX_DECOMPRESSED_CARRIER_BYTES
    )
    chunks: list[bytes] = []
    total = 0
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode="rb") as handle:
            while True:
                chunk = handle.read(min(1024 * 1024, max(limit - total + 1, 1)))
                if not chunk:
                    break
                total += len(chunk)
                if total > limit:
                    raise HistoricalManifestStoreRecoveryError(
                        "compressed carrier exceeds its permitted uncompressed length"
                    )
                chunks.append(chunk)
    except HistoricalManifestStoreRecoveryError:
        raise
    except (EOFError, OSError) as exc:
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier is not valid gzip data"
        ) from exc
    raw = b"".join(chunks)
    if (
        expected_uncompressed_byte_length is not None
        and len(raw) != expected_uncompressed_byte_length
    ):
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier length does not match its receipt pin"
        )
    if _sha256_bytes(raw) != uncompressed_sha256:
        raise HistoricalManifestStoreRecoveryError(
            "decompressed carrier bytes do not match their receipt pin"
        )
    if deterministic_gzip_compress(raw) != compressed:
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier does not use the canonical gzip representation"
        )
    return raw


def historical_manifest_store_recovery_digest(payload: Mapping[str, Any]) -> str:
    """Return the receipt digest after excluding its self-integrity field."""

    body = dict(payload)
    body.pop(HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD, None)
    return _canonical_digest(body)


def _required_paper(value: object) -> str:
    paper = str(value or "").strip()
    if not _PAPER_RE.fullmatch(paper):
        raise HistoricalManifestStoreRecoveryError(
            "paper must be one normalized paper-directory name"
        )
    return paper


def _required_git_commit(value: object) -> str:
    commit = str(value or "").strip().lower()
    if not _GIT_OBJECT_ID_RE.fullmatch(commit):
        raise HistoricalManifestStoreRecoveryError(
            "historical_commit must be an exact 40- or 64-hex Git object id"
        )
    return commit


def _normalized_paper_relative_path(
    value: str | Path,
    *,
    label: str,
    require_audit: bool,
    suffix: str | None = None,
) -> str:
    text = str(value).strip().replace("\\", "/")
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise HistoricalManifestStoreRecoveryError(
            f"{label} must be a normalized paper-relative path"
        )
    normalized = pure.as_posix()
    if require_audit and (not pure.parts or pure.parts[0] != "audit"):
        raise HistoricalManifestStoreRecoveryError(f"{label} must live below audit/")
    if suffix is not None and not normalized.endswith(suffix):
        raise HistoricalManifestStoreRecoveryError(f"{label} must end in {suffix}")
    return normalized


def _paper_dir(root: Path, paper: str) -> Path:
    resolved_root = root.resolve()
    folder = (resolved_root / "papers" / paper).resolve()
    try:
        folder.relative_to(resolved_root / "papers")
    except ValueError as exc:  # pragma: no cover - defensive after paper regex.
        raise HistoricalManifestStoreRecoveryError(
            "paper directory escapes papers/"
        ) from exc
    return folder


def _configured_paper_path(
    root: Path, paper: str, relative: str, *, label: str
) -> Path:
    folder = _paper_dir(root, paper)
    path = (folder / relative).resolve()
    try:
        path.relative_to(folder)
    except ValueError as exc:
        raise HistoricalManifestStoreRecoveryError(
            f"{label} escapes the paper directory"
        ) from exc
    return path


def _default_command_runner(
    argv: Sequence[str], cwd: Path
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        list(argv),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


class _Git:
    """Small fail-closed Git boundary with no shell interpolation."""

    def __init__(self, root: Path, command_runner: CommandRunner) -> None:
        self.root = root
        self._command_runner = command_runner

    def _output(self, argv: Sequence[str], *, label: str) -> bytes:
        try:
            completed = self._command_runner(tuple(argv), self.root)
        except Exception as exc:  # pragma: no cover - defensive injection seam.
            raise HistoricalManifestStoreRecoveryError(f"{label} could not start") from exc
        if not isinstance(completed, subprocess.CompletedProcess):
            raise HistoricalManifestStoreRecoveryError(
                f"{label} runner did not return a completed process"
            )
        if completed.returncode != 0:
            raise HistoricalManifestStoreRecoveryError(f"{label} failed")
        if isinstance(completed.stdout, bytes):
            return completed.stdout
        if isinstance(completed.stdout, str):
            return completed.stdout.encode("utf-8")
        raise HistoricalManifestStoreRecoveryError(f"{label} had non-byte output")

    def text(self, argv: Sequence[str], *, label: str) -> str:
        raw = self._output(argv, label=label)
        try:
            text = raw.decode("ascii").strip().lower()
        except UnicodeDecodeError as exc:
            raise HistoricalManifestStoreRecoveryError(
                f"{label} had non-ASCII Git output"
            ) from exc
        if not text or "\n" in text:
            raise HistoricalManifestStoreRecoveryError(f"{label} had malformed Git output")
        return text

    def resolve_commit(self, requested: str) -> str:
        resolved = self.text(
            ("git", "rev-parse", "--verify", f"{requested}^{{commit}}"),
            label="historical Git commit resolution",
        )
        if not _GIT_OBJECT_ID_RE.fullmatch(resolved):
            raise HistoricalManifestStoreRecoveryError(
                "historical Git commit resolution returned a malformed object id"
            )
        return resolved

    def blob_id(self, commit: str, git_path: str, *, label: str) -> str:
        blob = self.text(
            ("git", "rev-parse", "--verify", f"{commit}:{git_path}"),
            label=f"{label} Git blob resolution",
        )
        if not _GIT_OBJECT_ID_RE.fullmatch(blob):
            raise HistoricalManifestStoreRecoveryError(
                f"{label} Git blob resolution returned a malformed object id"
            )
        return blob

    def blob_bytes(self, blob: str, *, label: str) -> bytes:
        return self._output(("git", "cat-file", "blob", blob), label=label)

    def verify_blob_bytes(
        self, commit: str, git_path: str, expected: bytes, *, label: str
    ) -> str:
        blob = self.blob_id(commit, git_path, label=label)
        actual = self.blob_bytes(blob, label=f"{label} Git blob read")
        if actual != expected:
            raise HistoricalManifestStoreRecoveryError(
                f"{label} bytes do not match its immutable Git blob"
            )
        return blob

    def worktree_add(self, path: Path, commit: str) -> None:
        self._output(
            ("git", "worktree", "add", "--detach", str(path), commit),
            label="temporary detached worktree creation",
        )

    def worktree_remove(self, path: Path) -> None:
        self._output(
            ("git", "worktree", "remove", "--force", str(path)),
            label="temporary detached worktree cleanup",
        )

    def worktree_head(self, path: Path) -> str:
        head = self.text(
            ("git", "-C", str(path), "rev-parse", "HEAD"),
            label="temporary detached worktree HEAD check",
        )
        if not _GIT_OBJECT_ID_RE.fullmatch(head):
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree HEAD check returned a malformed object id"
            )
        return head

    def worktree_is_clean(self, path: Path) -> bool:
        output = self._output(
            ("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"),
            label="temporary detached worktree cleanliness check",
        )
        try:
            return not output.decode("utf-8").strip()
        except UnicodeDecodeError as exc:
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree cleanliness check had non-UTF-8 output"
            ) from exc


def _read_json_object(path: Path, *, label: str) -> tuple[bytes, Mapping[str, Any]]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise HistoricalManifestStoreRecoveryError(f"could not read {label}") from exc
    try:
        decoded = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HistoricalManifestStoreRecoveryError(f"{label} is not a JSON object") from exc
    if not isinstance(decoded, Mapping):
        raise HistoricalManifestStoreRecoveryError(f"{label} is not a JSON object")
    return raw, decoded


def _validate_surviving_sidecar(
    path: Path, *, paper: str
) -> tuple[bytes, Mapping[str, Any]]:
    raw, payload = _read_json_object(path, label="surviving historical statement sidecar")
    if str(payload.get("paper") or "").strip() != paper:
        raise HistoricalManifestStoreRecoveryError(
            "surviving historical statement sidecar belongs to a different paper"
        )
    return raw, payload


def _source_file_bytes(path: Path, *, label: str) -> bytes:
    try:
        return path.read_bytes()
    except OSError as exc:
        raise HistoricalManifestStoreRecoveryError(f"could not read {label}") from exc


@contextmanager
def _historical_dashboard_root(worktree_root: Path) -> Iterable[None]:
    """Run the shared review-surface parser against the detached checkout.

    ``review_dashboard`` intentionally permits a status file to spell the
    canonical source as a repository-relative path.  Its parser uses ``ROOT``
    for that conversion, so isolate that one module-global setting for the
    duration of source-coordinate extraction.  No audit data is written and
    the value is restored even if parsing fails.
    """

    prior_root = review_dashboard.ROOT
    review_dashboard.ROOT = worktree_root
    try:
        yield
    finally:
        review_dashboard.ROOT = prior_root


def _default_historical_review_surface(
    worktree_root: Path, paper: str
) -> HistoricalReviewSurface:
    """Extract the complete configured historical PaperInterface surface.

    This shares the current dashboard's source parser and filter semantics.
    The archive's own ``status.json`` selects the review surface; sidecar data
    is intentionally not read here.
    """

    folder = _paper_dir(worktree_root, paper)
    expected_interface = (folder / CANONICAL_REVIEW_SOURCE).resolve()
    status_path = (folder / "status.json").resolve()
    if not status_path.is_file():
        raise HistoricalManifestStoreRecoveryError(
            "historical review-surface status.json is missing"
        )
    if not expected_interface.is_file():
        raise HistoricalManifestStoreRecoveryError(
            "historical canonical PaperInterface.lean is missing"
        )

    try:
        with _historical_dashboard_root(worktree_root):
            review_source = review_dashboard.review_source_file(folder).resolve()
            coordinates, duplicates = (
                review_dashboard.current_review_signature_manifest_source_coordinates(
                    folder
                )
            )
    except (OSError, RuntimeError, ValueError, FileNotFoundError) as exc:
        raise HistoricalManifestStoreRecoveryError(
            "could not extract the historical PaperInterface review surface"
        ) from exc
    if review_source != expected_interface:
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface is not canonical PaperInterface.lean"
        )
    if duplicates:
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface has duplicate declaration coordinates"
        )
    if not coordinates:
        raise HistoricalManifestStoreRecoveryError(
            "historical PaperInterface review surface has no selected declarations"
        )

    declarations: list[HistoricalReviewDeclaration] = []
    source_paths: set[str] = {"status.json", CANONICAL_REVIEW_SOURCE}
    for qualified, raw in sorted(coordinates.items()):
        if not isinstance(raw, Mapping):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface has a malformed declaration coordinate"
            )
        source_file = _normalized_paper_relative_path(
            str(raw.get("source_file") or ""),
            label="historical declaration source_file",
            require_audit=False,
            suffix=".lean",
        )
        declaration = HistoricalReviewDeclaration(
            qualified_declaration=str(qualified or "").strip(),
            source_file=source_file,
            lean_source_declaration=str(raw.get("lean_source_declaration") or ""),
            line_number=int(raw.get("line_number") or 0),
            declaration_kind=str(raw.get("declaration_kind") or "").strip(),
        )
        if (
            not declaration.qualified_declaration
            or not declaration.lean_source_declaration
            or declaration.line_number <= 0
            or declaration.declaration_kind not in review_dashboard.REVIEW_DECL_KINDS
        ):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface has an incomplete declaration coordinate"
            )
        source_paths.add(source_file)
        declarations.append(declaration)
    names = [item.qualified_declaration for item in declarations]
    if len(set(names)) != len(names):
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface has non-unique declaration coordinates"
        )

    sources: list[HistoricalReviewSource] = []
    for relative in sorted(source_paths):
        source_path = _configured_paper_path(
            worktree_root, paper, relative, label="historical review source"
        )
        sources.append(
            HistoricalReviewSource(
                paper_relative_path=relative,
                content=_source_file_bytes(source_path, label=f"historical {relative}"),
            )
        )
    return HistoricalReviewSurface(
        import_module=f"{paper}.PaperInterface",
        declarations=tuple(declarations),
        source_files=tuple(sources),
    )


def _validated_surface(surface: HistoricalReviewSurface, *, paper: str) -> HistoricalReviewSurface:
    """Validate custom or default extraction output before Lean is invoked."""

    expected_module = f"{paper}.PaperInterface"
    if surface.import_module != expected_module:
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface has a noncanonical import module"
        )
    if not surface.declarations:
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface has no declarations"
        )
    names: set[str] = set()
    for declaration in surface.declarations:
        if not isinstance(declaration, HistoricalReviewDeclaration):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface returned an invalid declaration record"
            )
        if (
            not declaration.qualified_declaration
            or declaration.qualified_declaration in names
            or not declaration.lean_source_declaration
            or declaration.line_number <= 0
            or declaration.declaration_kind not in review_dashboard.REVIEW_DECL_KINDS
        ):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface returned an incomplete declaration record"
            )
        _normalized_paper_relative_path(
            declaration.source_file,
            label="historical declaration source_file",
            require_audit=False,
            suffix=".lean",
        )
        names.add(declaration.qualified_declaration)
    source_paths: set[str] = set()
    for source in surface.source_files:
        if not isinstance(source, HistoricalReviewSource):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface returned an invalid source record"
            )
        relative = _normalized_paper_relative_path(
            source.paper_relative_path,
            label="historical review source path",
            require_audit=False,
        )
        if relative in source_paths or not isinstance(source.content, bytes):
            raise HistoricalManifestStoreRecoveryError(
                "historical review surface has duplicate or malformed source inputs"
            )
        source_paths.add(relative)
    required_sources = {"status.json", CANONICAL_REVIEW_SOURCE} | {
        declaration.source_file for declaration in surface.declarations
    }
    if source_paths != required_sources:
        raise HistoricalManifestStoreRecoveryError(
            "historical review surface did not pin exactly its selection inputs"
        )
    return surface


def _source_coordinate_payload(
    declarations: Sequence[HistoricalReviewDeclaration],
) -> list[dict[str, Any]]:
    return [
        {
            "qualified_declaration": declaration.qualified_declaration,
            "source_file": declaration.source_file,
            "lean_source_declaration": declaration.lean_source_declaration,
            "line_number": declaration.line_number,
            "declaration_kind": declaration.declaration_kind,
        }
        for declaration in sorted(
            declarations, key=lambda item: item.qualified_declaration
        )
    ]


def _snapshot_current_producers(root: Path) -> dict[str, dict[str, Any]]:
    """Return exact live producer byte identities and reject path escapes."""

    paths = (
        "scripts/historical_manifest_store_recovery.py",
        "scripts/lean_signature_manifest.py",
        "scripts/lean_signature_manifest_helper.lean",
        "scripts/authenticated_manifest_store.py",
        "scripts/review_dashboard.py",
    )
    resolved_root = root.resolve()
    snapshot: dict[str, dict[str, Any]] = {}
    for relative in paths:
        path = (resolved_root / relative).resolve()
        try:
            path.relative_to(resolved_root)
        except ValueError as exc:  # pragma: no cover - literal paths.
            raise HistoricalManifestStoreRecoveryError(
                "current producer path escapes the repository"
            ) from exc
        content = _source_file_bytes(path, label=f"current producer {relative}")
        snapshot[relative] = {
            "path": relative,
            "bytes_sha256": _sha256_bytes(content),
            "byte_length": len(content),
        }
    return snapshot


def _assert_current_producers_unchanged(
    root: Path, expected: Mapping[str, Mapping[str, Any]]
) -> None:
    actual = _snapshot_current_producers(root)
    if actual != dict(expected):
        raise HistoricalManifestStoreRecoveryError(
            "current manifest-store recovery producers changed during extraction"
        )


def _output_paths(
    config: HistoricalManifestStoreRecoveryConfig, *, paper: str
) -> tuple[str, str, str]:
    authority = _normalized_paper_relative_path(
        config.authority_output_path,
        label="authority_output_path",
        require_audit=True,
        suffix=".json",
    )
    carrier = _normalized_paper_relative_path(
        config.carrier_output_path,
        label="carrier_output_path",
        require_audit=True,
        suffix=".json.gz",
    )
    receipt = _normalized_paper_relative_path(
        config.receipt_output_path,
        label="receipt_output_path",
        require_audit=True,
        suffix=".json",
    )
    paths = (authority, carrier, receipt)
    if len(set(paths)) != len(paths):
        raise HistoricalManifestStoreRecoveryError(
            "authority, carrier, and receipt output paths must be distinct"
        )
    if "audit/lean_signature_manifest_cache_authority.json" in paths:
        raise HistoricalManifestStoreRecoveryError(
            "recovery may not overwrite the ordinary manifest-store authority"
        )
    sidecar = _normalized_paper_relative_path(
        config.historical_sidecar_path,
        label="historical_sidecar_path",
        require_audit=True,
        suffix=".json",
    )
    if sidecar in paths:
        raise HistoricalManifestStoreRecoveryError(
            "recovery output may not overwrite the surviving statement sidecar"
        )
    del paper  # Retained in this private helper's symmetric call site.
    return paths


def _assert_outputs_absent(root: Path, paper: str, paths: Sequence[str]) -> None:
    for relative in paths:
        path = _configured_paper_path(root, paper, relative, label="recovery output")
        if path.exists() or path.is_symlink():
            raise HistoricalManifestStoreRecoveryError(
                f"recovery output already exists: {relative}"
            )


def _context_modules(context: Mapping[str, Any], *, import_module: str) -> tuple[str, ...]:
    raw_modules = context.get("audit_modules")
    if not isinstance(raw_modules, list):
        raise HistoricalManifestStoreRecoveryError(
            "current signature-manifest context has no audit module list"
        )
    modules = tuple(str(module).strip() for module in raw_modules)
    if (
        not modules
        or any(not module for module in modules)
        or tuple(sorted(set(modules))) != modules
        or import_module not in modules
    ):
        raise HistoricalManifestStoreRecoveryError(
            "current signature-manifest context has an invalid audit module list"
        )
    return modules


def _manifest_candidates(
    *,
    surface: HistoricalReviewSurface,
    manifests: Mapping[str, Mapping[str, Any]],
    context: Mapping[str, Any],
) -> list[dict[str, Any]]:
    expected = {item.qualified_declaration for item in surface.declarations}
    observed = {str(name).strip() for name in manifests}
    if observed != expected:
        raise HistoricalManifestStoreRecoveryError(
            "historical manifest producer did not return exactly the configured review surface"
        )
    candidates: list[dict[str, Any]] = []
    for declaration in sorted(
        surface.declarations, key=lambda item: item.qualified_declaration
    ):
        manifest = manifests.get(declaration.qualified_declaration)
        if not isinstance(manifest, Mapping):
            raise HistoricalManifestStoreRecoveryError(
                "historical manifest producer returned a malformed declaration manifest"
            )
        signature = manifest_tools.signature_manifest_digest(dict(manifest))
        proposition_graph_sha256 = manifest_store.elaborated_proposition_graph_sha256(
            manifest.get("elaborated_proposition_graph")
        )
        if not _SHA256_RE.fullmatch(signature) or not _SHA256_RE.fullmatch(
            proposition_graph_sha256
        ):
            raise HistoricalManifestStoreRecoveryError(
                "historical manifest producer returned an incomplete Lean manifest"
            )
        candidates.append(
            {
                "qualified_declaration": declaration.qualified_declaration,
                "manifest": dict(manifest),
                "context": dict(context),
                "authority_binding": review_dashboard.review_signature_manifest_authority_binding(
                    qualified_declaration=declaration.qualified_declaration,
                    source_file=declaration.source_file,
                    lean_source_declaration=declaration.lean_source_declaration,
                    line_number=declaration.line_number,
                    declaration_kind=declaration.declaration_kind,
                    elaborated_signature_sha256=signature,
                    elaborated_proposition_graph_sha256=proposition_graph_sha256,
                ),
            }
        )
    return candidates


def _store_payload_builder_adapter(
    paper: str, candidates: Iterable[Mapping[str, Any]]
) -> tuple[dict[str, Any], dict[str, Any], set[str]]:
    return manifest_store.build_authenticated_manifest_store_payloads(
        paper=paper, candidates=candidates
    )


def _historical_source_receipt_entries(
    *,
    git: _Git,
    commit: str,
    paper: str,
    surface: HistoricalReviewSurface,
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for source in sorted(surface.source_files, key=lambda item: item.paper_relative_path):
        relative = _normalized_paper_relative_path(
            source.paper_relative_path,
            label="historical review source path",
            require_audit=False,
        )
        git_path = f"papers/{paper}/{relative}"
        blob = git.verify_blob_bytes(
            commit,
            git_path,
            source.content,
            label=f"historical review source {relative}",
        )
        entries.append(
            {
                "paper_relative_path": relative,
                "git_path": git_path,
                "git_blob": blob,
                "bytes_sha256": _sha256_bytes(source.content),
                "byte_length": len(source.content),
            }
        )
    return entries


def _historical_semantic_replay_input_entries(
    *,
    git: _Git,
    commit: str,
    paper: str,
    worktree: Path,
) -> list[dict[str, Any]]:
    """Pin optional historical sidecars usable by a later semantic replay.

    The recovery itself only needs a statement sidecar and the configured Lean
    review surface.  A later reuse bridge additionally needs source-map and
    text-translation bytes.  Record every available canonical artifact by its
    immutable Git blob now, rather than letting that later bridge read a live
    stale copy or infer a historical filename.
    """

    entries: list[dict[str, Any]] = []
    for relative in HISTORICAL_SEMANTIC_REPLAY_INPUT_PATHS:
        path = _configured_paper_path(
            worktree, paper, relative, label="historical semantic replay input"
        )
        if not path.is_file():
            continue
        content = _source_file_bytes(path, label=f"historical {relative}")
        git_path = f"papers/{paper}/{relative}"
        blob = git.verify_blob_bytes(
            commit,
            git_path,
            content,
            label=f"historical semantic replay input {relative}",
        )
        entries.append(
            {
                "paper_relative_path": relative,
                "git_path": git_path,
                "git_blob": blob,
                "bytes_sha256": _sha256_bytes(content),
                "byte_length": len(content),
            }
        )
    return entries


def _assert_historical_sources_unchanged(
    *, root: Path, paper: str, sources: Sequence[HistoricalReviewSource]
) -> None:
    for source in sources:
        path = _configured_paper_path(
            root,
            paper,
            _normalized_paper_relative_path(
                source.paper_relative_path,
                label="historical review source path",
                require_audit=False,
            ),
            label="historical review source",
        )
        if _source_file_bytes(path, label=f"historical {source.paper_relative_path}") != source.content:
            raise HistoricalManifestStoreRecoveryError(
                "historical review source changed during manifest extraction"
            )


def _prepare_detached_lake_environment(*, live_root: Path, worktree: Path) -> None:
    """Expose immutable package dependencies without sharing root build output.

    A detached Git worktree deliberately excludes ignored ``.lake`` files.  A
    historical manifest recovery nevertheless needs the package sources and
    their already-built dependency artifacts.  The root project's package
    directory is immutable for an ordinary ``lake build`` of the historical
    root target, whereas the root project's own ``.lake/build`` must never be
    shared: it would let an archived source build overwrite live artifacts.

    Link only ``.lake/packages`` into the detached worktree.  The historical
    root receives a fresh local ``.lake/build``; package versions remain pinned
    by the historical ``lake-manifest.json`` and the manifest context records
    the dependency environment.  No package refresh or network operation is
    performed here.
    """

    package_cache = (live_root / ".lake" / "packages").resolve()
    if not package_cache.is_dir():
        # Fixture tests and intentionally minimal repositories can provide
        # their own manifest producer.  The normal Lean producer will fail
        # closed later if its package environment is unavailable.
        return
    lake_dir = worktree / ".lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    link = lake_dir / "packages"
    if link.exists() or link.is_symlink():
        raise HistoricalManifestStoreRecoveryError(
            "detached historical worktree unexpectedly already has a package cache"
        )
    try:
        os.symlink(package_cache, link, target_is_directory=True)
    except OSError as exc:
        raise HistoricalManifestStoreRecoveryError(
            "could not expose the local immutable Lake package cache to the detached worktree"
        ) from exc


@contextmanager
def _temporary_detached_worktree(
    git: _Git, commit: str, *, live_root: Path
) -> Iterable[Path]:
    """Yield one detached checkout and make cleanup a hard completion gate."""

    with tempfile.TemporaryDirectory(prefix="econcs-historical-manifest-") as temp:
        worktree = Path(temp) / "worktree"
        added = False
        add_attempted = False
        primary_error: BaseException | None = None
        try:
            add_attempted = True
            git.worktree_add(worktree, commit)
            added = True
            _prepare_detached_lake_environment(live_root=live_root, worktree=worktree)
            yield worktree
        except BaseException as exc:  # Preserve the original extraction error.
            primary_error = exc
            raise
        finally:
            # A failed ``git worktree add`` can still leave a checkout
            # directory behind.  Remove that exact target when it exists;
            # never prune or otherwise touch an unrelated user worktree.
            if added or (add_attempted and worktree.exists()):
                try:
                    git.worktree_remove(worktree)
                except HistoricalManifestStoreRecoveryError as cleanup_error:
                    if primary_error is None:
                        raise
                    raise HistoricalManifestStoreRecoveryError(
                        "temporary detached worktree cleanup failed after recovery failure"
                    ) from cleanup_error


def _receipt_payload(
    *,
    paper: str,
    commit: str,
    sidecar_path: str,
    sidecar_git_path: str,
    sidecar_blob: str,
    sidecar_bytes: bytes,
    source_entries: Sequence[Mapping[str, Any]],
    semantic_replay_inputs: Sequence[Mapping[str, Any]],
    surface: HistoricalReviewSurface,
    producer_snapshot: Mapping[str, Mapping[str, Any]],
    authority_path: str,
    authority: Mapping[str, Any],
    authority_bytes: bytes,
    carrier_path: str,
    carrier: Mapping[str, Any],
    carrier_compressed_bytes: bytes,
    carrier_uncompressed_bytes: bytes,
    receipt_path: str,
    accepted_declarations: Sequence[str],
) -> dict[str, Any]:
    coordinates = _source_coordinate_payload(surface.declarations)
    source_entries_payload = [dict(entry) for entry in source_entries]
    semantic_replay_payload = [dict(entry) for entry in semantic_replay_inputs]
    payload: dict[str, Any] = {
        "schema": HISTORICAL_MANIFEST_STORE_RECOVERY_SCHEMA,
        "artifact_kind": HISTORICAL_MANIFEST_STORE_RECOVERY_ARTIFACT_KIND,
        "policy_version": HISTORICAL_MANIFEST_STORE_RECOVERY_POLICY_VERSION,
        "paper": paper,
        "historical_git_commit": commit,
        "historical_statement_sidecar": {
            "paper_relative_path": sidecar_path,
            "git_path": f"papers/{paper}/{sidecar_git_path}",
            "git_blob": sidecar_blob,
            "bytes_sha256": _sha256_bytes(sidecar_bytes),
            "byte_length": len(sidecar_bytes),
        },
        "historical_review_surface": {
            "import_module": surface.import_module,
            "review_source": CANONICAL_REVIEW_SOURCE,
            "source_files": source_entries_payload,
            "source_files_sha256": _canonical_digest(source_entries_payload),
            "selected_declaration_count": len(coordinates),
            # Coordinates are trace/provenance only.  The recovery tool never
            # matches them to an old sidecar or treats their spellings as a
            # semantic identity.
            "selected_declaration_coordinates": coordinates,
            "selected_declaration_coordinates_sha256": _canonical_digest(coordinates),
        },
        "historical_semantic_replay_inputs": {
            "schema": HISTORICAL_SEMANTIC_REPLAY_INPUTS_SCHEMA,
            "files": semantic_replay_payload,
            "files_sha256": _canonical_digest(semantic_replay_payload),
        },
        "current_producers": {
            "files": [
                dict(producer_snapshot[key]) for key in sorted(producer_snapshot)
            ],
            "files_sha256": _canonical_digest(
                [dict(producer_snapshot[key]) for key in sorted(producer_snapshot)]
            ),
        },
        "recovered_store": {
            "authority": {
                "paper_relative_path": authority_path,
                "bytes_sha256": _sha256_bytes(authority_bytes),
                "byte_length": len(authority_bytes),
                "canonical_payload_sha256": manifest_store.canonical_json_sha256(
                    authority
                ),
                "schema": authority.get("schema"),
                "entries_sha256": authority.get("entries_sha256"),
                "contexts_sha256": authority.get("contexts_sha256"),
            },
            "carrier": {
                "paper_relative_path": carrier_path,
                "encoding": "gzip",
                "compression_policy": DETERMINISTIC_GZIP_POLICY_VERSION,
                "compressed_bytes_sha256": _sha256_bytes(carrier_compressed_bytes),
                "compressed_byte_length": len(carrier_compressed_bytes),
                "uncompressed_bytes_sha256": _sha256_bytes(
                    carrier_uncompressed_bytes
                ),
                "uncompressed_byte_length": len(carrier_uncompressed_bytes),
                "uncompressed_canonical_payload_sha256": (
                    manifest_store.canonical_json_sha256(carrier)
                ),
                "schema": carrier.get("schema"),
            },
            "receipt_paper_relative_path": receipt_path,
            "accepted_declaration_count": len(accepted_declarations),
            "accepted_declarations_sha256": _canonical_digest(
                list(sorted(accepted_declarations))
            ),
        },
    }
    payload[HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD] = (
        historical_manifest_store_recovery_digest(payload)
    )
    return payload


def _receipt_bytes_fixed_point(payload: Mapping[str, Any]) -> bytes:
    """Encode and independently recheck the self-attesting recovery receipt."""

    actual = historical_manifest_store_recovery_digest(payload)
    recorded = str(payload.get(HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD) or "")
    if not _SHA256_RE.fullmatch(recorded) or actual != recorded:
        raise HistoricalManifestStoreRecoveryError(
            "historical manifest-store recovery receipt integrity is invalid"
        )
    return _pretty_json_bytes(dict(payload))


def _json_object_from_exact_bytes(value: bytes, *, label: str) -> dict[str, Any]:
    try:
        decoded = json.loads(value.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HistoricalManifestStoreRecoveryError(f"{label} is not a JSON object") from exc
    if not isinstance(decoded, dict):
        raise HistoricalManifestStoreRecoveryError(f"{label} is not a JSON object")
    return decoded


def _required_digest(value: object, *, label: str) -> str:
    digest = str(value or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        raise HistoricalManifestStoreRecoveryError(f"{label} must be a SHA-256 digest")
    return digest


def _required_nonnegative_int(value: object, *, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise HistoricalManifestStoreRecoveryError(
            f"{label} must be a nonnegative integer"
        )
    return value


def verified_recovered_manifest_store_artifacts(
    *,
    paper: str,
    receipt: Mapping[str, Any],
    receipt_bytes: bytes,
    authority_bytes: bytes,
    carrier_compressed_bytes: bytes,
) -> tuple[dict[str, Any], dict[str, Any], bytes]:
    """Verify recovery artifacts and return authority, carrier, and raw carrier bytes.

    This is the read-side companion to :func:`write_recovered_manifest_store`.
    It receives the raw bytes of all three artifacts, checks that the receipt
    exactly encodes its supplied object, checks its self-integrity field and
    every authority/carrier byte pin, verifies canonical deterministic gzip,
    and returns the uncompressed carrier JSON bytes unchanged.  It does *not*
    authenticate a Git checkout, replay a historical serializer, or establish
    a semantic match to a current paper; those remain separate evidence gates.
    """

    expected_paper = _required_paper(paper)
    if not isinstance(receipt, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovery receipt must be a mapping")
    parsed_receipt = _json_object_from_exact_bytes(receipt_bytes, label="recovery receipt")
    if parsed_receipt != dict(receipt):
        raise HistoricalManifestStoreRecoveryError(
            "recovery receipt object differs from its exact bytes"
        )
    if (
        receipt.get("schema") != HISTORICAL_MANIFEST_STORE_RECOVERY_SCHEMA
        or receipt.get("artifact_kind")
        != HISTORICAL_MANIFEST_STORE_RECOVERY_ARTIFACT_KIND
        or receipt.get("policy_version")
        != HISTORICAL_MANIFEST_STORE_RECOVERY_POLICY_VERSION
        or str(receipt.get("paper") or "").strip() != expected_paper
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovery receipt has the wrong schema, policy, or paper"
        )
    if _required_digest(
        receipt.get(HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD),
        label="recovery receipt integrity",
    ) != historical_manifest_store_recovery_digest(receipt):
        raise HistoricalManifestStoreRecoveryError("recovery receipt integrity is stale")

    recovered_store = receipt.get("recovered_store")
    if not isinstance(recovered_store, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovery receipt has no recovered store")
    authority_metadata = recovered_store.get("authority")
    carrier_metadata = recovered_store.get("carrier")
    if not isinstance(authority_metadata, Mapping) or not isinstance(
        carrier_metadata, Mapping
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovery receipt has malformed store metadata"
        )
    _normalized_paper_relative_path(
        str(authority_metadata.get("paper_relative_path") or ""),
        label="recovered authority path",
        require_audit=True,
        suffix=".json",
    )
    _normalized_paper_relative_path(
        str(carrier_metadata.get("paper_relative_path") or ""),
        label="recovered compressed carrier path",
        require_audit=True,
        suffix=".json.gz",
    )
    _normalized_paper_relative_path(
        str(recovered_store.get("receipt_paper_relative_path") or ""),
        label="recovered receipt path",
        require_audit=True,
        suffix=".json",
    )
    if (
        str(carrier_metadata.get("encoding") or "") != "gzip"
        or str(carrier_metadata.get("compression_policy") or "")
        != DETERMINISTIC_GZIP_POLICY_VERSION
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovery receipt has an unsupported carrier compression policy"
        )
    if (
        _sha256_bytes(authority_bytes)
        != _required_digest(
            authority_metadata.get("bytes_sha256"), label="authority bytes"
        )
        or len(authority_bytes)
        != _required_nonnegative_int(
            authority_metadata.get("byte_length"), label="authority byte_length"
        )
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered authority bytes do not match their receipt pin"
        )
    authority = _json_object_from_exact_bytes(
        authority_bytes, label="recovered authority"
    )
    if (
        authority.get("schema")
        != manifest_store.AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA
        or authority_metadata.get("schema")
        != manifest_store.AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA
        or authority.get("paper") != expected_paper
        or manifest_store.canonical_json_sha256(authority)
        != _required_digest(
            authority_metadata.get("canonical_payload_sha256"),
            label="authority canonical payload",
        )
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered authority has the wrong schema, paper, or canonical digest"
        )
    raw_carrier = verified_deterministic_gzip_decompress(
        carrier_compressed_bytes,
        expected_compressed_sha256=_required_digest(
            carrier_metadata.get("compressed_bytes_sha256"),
            label="compressed carrier bytes",
        ),
        expected_uncompressed_sha256=_required_digest(
            carrier_metadata.get("uncompressed_bytes_sha256"),
            label="uncompressed carrier bytes",
        ),
        expected_uncompressed_byte_length=_required_nonnegative_int(
            carrier_metadata.get("uncompressed_byte_length"),
            label="uncompressed carrier byte_length",
        ),
    )
    if len(carrier_compressed_bytes) != _required_nonnegative_int(
        carrier_metadata.get("compressed_byte_length"),
        label="compressed carrier byte_length",
    ):
        raise HistoricalManifestStoreRecoveryError(
            "compressed carrier length does not match its receipt pin"
        )
    carrier = _json_object_from_exact_bytes(raw_carrier, label="recovered carrier")
    if (
        carrier.get("schema") != manifest_store.AUTHENTICATED_MANIFEST_CARRIER_SCHEMA
        or carrier_metadata.get("schema")
        != manifest_store.AUTHENTICATED_MANIFEST_CARRIER_SCHEMA
        or carrier.get("paper") != expected_paper
        or manifest_store.canonical_json_sha256(carrier)
        != _required_digest(
            carrier_metadata.get("uncompressed_canonical_payload_sha256"),
            label="uncompressed carrier canonical payload",
        )
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered carrier has the wrong schema, paper, or canonical digest"
        )
    return authority, carrier, raw_carrier


def recover_historical_manifest_store(
    config: HistoricalManifestStoreRecoveryConfig,
    *,
    command_runner: CommandRunner = _default_command_runner,
    review_surface_extractor: Callable[[Path, str], HistoricalReviewSurface] = (
        _default_historical_review_surface
    ),
    manifest_context_producer: ManifestContextProducer = (
        manifest_tools.signature_manifest_cache_context
    ),
    manifest_producer: ManifestProducer = manifest_tools.run_lean_signature_manifests,
    store_payload_builder: StorePayloadBuilder = _store_payload_builder_adapter,
) -> RecoveredHistoricalManifestStore:
    """Reconstruct one historical store in memory from immutable Git sources.

    This function validates all input/output paths and rejects existing output
    paths before invoking Git or Lean.  It uses a detached temporary worktree,
    verifies every review-surface input against the requested commit before and
    after extraction, and removes that worktree before returning.  No live
    filesystem write occurs here.
    """

    paper = _required_paper(config.paper)
    requested_commit = _required_git_commit(config.historical_commit)
    if config.timeout_seconds <= 0 or config.build_timeout_seconds <= 0:
        raise HistoricalManifestStoreRecoveryError(
            "manifest and build timeouts must be positive"
        )
    root = config.root.resolve()
    if not (root / ".git").exists():
        raise HistoricalManifestStoreRecoveryError(
            "recovery root is not a Git worktree"
        )
    paper_dir = _paper_dir(root, paper)
    if not paper_dir.is_dir():
        raise HistoricalManifestStoreRecoveryError("paper directory does not exist")

    sidecar_path = _normalized_paper_relative_path(
        config.historical_sidecar_path,
        label="historical_sidecar_path",
        require_audit=True,
        suffix=".json",
    )
    sidecar_git_path = _normalized_paper_relative_path(
        config.historical_sidecar_git_path or sidecar_path,
        label="historical_sidecar_git_path",
        require_audit=True,
        suffix=".json",
    )
    authority_path, carrier_path, receipt_path = _output_paths(config, paper=paper)
    _assert_outputs_absent(root, paper, (authority_path, carrier_path, receipt_path))

    sidecar_bytes, _sidecar_payload = _validate_surviving_sidecar(
        _configured_paper_path(root, paper, sidecar_path, label="historical sidecar"),
        paper=paper,
    )
    producer_snapshot = _snapshot_current_producers(root)
    git = _Git(root, command_runner)
    commit = git.resolve_commit(requested_commit)
    sidecar_blob = git.verify_blob_bytes(
        commit,
        f"papers/{paper}/{sidecar_git_path}",
        sidecar_bytes,
        label="surviving historical statement sidecar",
    )

    authority: dict[str, Any]
    carrier: dict[str, Any]
    accepted: set[str]
    source_entries: list[dict[str, Any]]
    semantic_replay_inputs: list[dict[str, Any]]
    surface: HistoricalReviewSurface
    with _temporary_detached_worktree(git, commit, live_root=root) as worktree:
        if git.worktree_head(worktree) != commit:
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree is not at the requested commit"
            )
        if not git.worktree_is_clean(worktree):
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree is not clean before extraction"
            )
        try:
            surface = _validated_surface(
                review_surface_extractor(worktree, paper), paper=paper
            )
        except HistoricalManifestStoreRecoveryError:
            raise
        except Exception as exc:  # pragma: no cover - injection/producer boundary.
            raise HistoricalManifestStoreRecoveryError(
                "could not extract the historical PaperInterface review surface"
            ) from exc
        source_entries = _historical_source_receipt_entries(
            git=git,
            commit=commit,
            paper=paper,
            surface=surface,
        )
        semantic_replay_inputs = _historical_semantic_replay_input_entries(
            git=git,
            commit=commit,
            paper=paper,
            worktree=worktree,
        )
        names = [item.qualified_declaration for item in surface.declarations]
        checkpoint_context: dict[str, Any] | None = None
        checkpoint_context_conflict = False

        def capture_context(
            raw_context: Mapping[str, Any], _raw_manifests: Mapping[str, Mapping[str, Any]]
        ) -> None:
            """Retain the producer's one compiled context without persisting it."""

            nonlocal checkpoint_context, checkpoint_context_conflict
            if not isinstance(raw_context, Mapping):
                checkpoint_context_conflict = True
                return
            candidate = dict(raw_context)
            if checkpoint_context is None:
                checkpoint_context = candidate
            elif _canonical_json_bytes(checkpoint_context) != _canonical_json_bytes(
                candidate
            ):
                checkpoint_context_conflict = True

        try:
            manifests = manifest_producer(
                worktree,
                surface.import_module,
                names,
                timeout_seconds=config.timeout_seconds,
                build_timeout_seconds=config.build_timeout_seconds,
                manifest_checkpoint=capture_context,
            )
        except Exception as exc:  # pragma: no cover - current producer boundary.
            raise HistoricalManifestStoreRecoveryError(
                "current signature-manifest producer failed"
            ) from exc
        if not isinstance(manifests, Mapping):
            raise HistoricalManifestStoreRecoveryError(
                "current signature-manifest producer returned a malformed result"
            )
        if checkpoint_context_conflict:
            raise HistoricalManifestStoreRecoveryError(
                "current signature-manifest producer emitted inconsistent contexts"
            )
        context: Mapping[str, Any] | None = checkpoint_context
        if context is None:
            # A process-local manifest cache can satisfy a request without
            # calling the checkpoint hook.  This should not normally occur in
            # a unique temporary worktree, but rebuild a context rather than
            # guessing which environment supplied the cached manifest.
            try:
                context = manifest_context_producer(
                    worktree,
                    surface.import_module,
                    build_timeout_seconds=config.build_timeout_seconds,
                )
            except Exception as exc:  # pragma: no cover - producer boundary.
                raise HistoricalManifestStoreRecoveryError(
                    "current signature-manifest context producer failed"
                ) from exc
        if not isinstance(context, Mapping):
            raise HistoricalManifestStoreRecoveryError(
                "current signature-manifest context producer returned no context"
            )
        _context_modules(context, import_module=surface.import_module)
        candidates = _manifest_candidates(
            surface=surface, manifests=manifests, context=context
        )
        try:
            authority, carrier, accepted = store_payload_builder(paper, candidates)
        except Exception as exc:  # pragma: no cover - builder injection boundary.
            raise HistoricalManifestStoreRecoveryError(
                "authenticated manifest-store payload producer failed"
            ) from exc
        if not isinstance(authority, dict) or not isinstance(carrier, dict):
            raise HistoricalManifestStoreRecoveryError(
                "authenticated manifest-store payload producer returned malformed payloads"
            )
        expected = set(names)
        if set(accepted) != expected:
            raise HistoricalManifestStoreRecoveryError(
                "authenticated manifest-store payload producer rejected part of the historical review surface"
            )
        _assert_historical_sources_unchanged(
            root=worktree, paper=paper, sources=surface.source_files
        )
        if git.worktree_head(worktree) != commit:
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree HEAD changed during extraction"
            )
        if not git.worktree_is_clean(worktree):
            raise HistoricalManifestStoreRecoveryError(
                "temporary detached worktree modified tracked files during extraction"
            )
        _assert_current_producers_unchanged(root, producer_snapshot)

    authority_bytes = _pretty_json_bytes(authority)
    carrier_uncompressed_bytes = _pretty_json_bytes(carrier)
    carrier_compressed_bytes = deterministic_gzip_compress(carrier_uncompressed_bytes)
    # Catch a future compression-policy implementation change before an
    # artifact can be returned to a caller or written to a paper audit folder.
    if (
        verified_deterministic_gzip_decompress(
            carrier_compressed_bytes,
            expected_compressed_sha256=_sha256_bytes(carrier_compressed_bytes),
            expected_uncompressed_sha256=_sha256_bytes(carrier_uncompressed_bytes),
            expected_uncompressed_byte_length=len(carrier_uncompressed_bytes),
        )
        != carrier_uncompressed_bytes
    ):
        raise HistoricalManifestStoreRecoveryError(
            "canonical compressed carrier failed its own round-trip verification"
        )
    receipt = _receipt_payload(
        paper=paper,
        commit=commit,
        sidecar_path=sidecar_path,
        sidecar_git_path=sidecar_git_path,
        sidecar_blob=sidecar_blob,
        sidecar_bytes=sidecar_bytes,
        source_entries=source_entries,
        semantic_replay_inputs=semantic_replay_inputs,
        surface=surface,
        producer_snapshot=producer_snapshot,
        authority_path=authority_path,
        authority=authority,
        authority_bytes=authority_bytes,
        carrier_path=carrier_path,
        carrier=carrier,
        carrier_compressed_bytes=carrier_compressed_bytes,
        carrier_uncompressed_bytes=carrier_uncompressed_bytes,
        receipt_path=receipt_path,
        accepted_declarations=sorted(accepted),
    )
    receipt_bytes = _receipt_bytes_fixed_point(receipt)
    return RecoveredHistoricalManifestStore(
        authority=authority,
        carrier=carrier,
        receipt=receipt,
        authority_bytes=authority_bytes,
        carrier_compressed_bytes=carrier_compressed_bytes,
        carrier_uncompressed_bytes=carrier_uncompressed_bytes,
        receipt_bytes=receipt_bytes,
        accepted_declarations=tuple(sorted(accepted)),
    )


def _atomic_create_bytes(path: Path, content: bytes) -> None:
    """Create one new file atomically without replacing a pre-existing path."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError as exc:
            raise HistoricalManifestStoreRecoveryError(
                f"recovery output already exists: {path}"
            ) from exc
        try:
            directory_descriptor = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
            try:
                os.fsync(directory_descriptor)
            finally:
                os.close(directory_descriptor)
        except OSError:
            pass
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def write_recovered_manifest_store(
    config: HistoricalManifestStoreRecoveryConfig,
    recovered: RecoveredHistoricalManifestStore,
) -> None:
    """Publish a completed in-memory recovery to its three explicit paths.

    Carrier and authority are written before the receipt.  A partial write has
    no valid receipt and therefore must not be used as recovery evidence.  The
    writer never replaces a file and rechecks the output paths immediately
    before publication.
    """

    paper = _required_paper(config.paper)
    root = config.root.resolve()
    authority_path, carrier_path, receipt_path = _output_paths(config, paper=paper)
    _assert_outputs_absent(root, paper, (authority_path, carrier_path, receipt_path))
    if not isinstance(recovered, RecoveredHistoricalManifestStore):
        raise HistoricalManifestStoreRecoveryError("recovery result has the wrong type")
    if _pretty_json_bytes(dict(recovered.authority)) != recovered.authority_bytes:
        raise HistoricalManifestStoreRecoveryError("recovered authority bytes are stale")
    if (
        _pretty_json_bytes(dict(recovered.carrier))
        != recovered.carrier_uncompressed_bytes
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered uncompressed carrier bytes are stale"
        )
    carrier_metadata = recovered.receipt.get("recovered_store", {})
    if not isinstance(carrier_metadata, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovered receipt has no store metadata")
    carrier_metadata = carrier_metadata.get("carrier", {})
    if not isinstance(carrier_metadata, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovered receipt has no carrier metadata")
    authority_metadata = recovered.receipt.get("recovered_store", {})
    if not isinstance(authority_metadata, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovered receipt has no store metadata")
    authority_metadata = authority_metadata.get("authority", {})
    if not isinstance(authority_metadata, Mapping):
        raise HistoricalManifestStoreRecoveryError("recovered receipt has no authority metadata")
    recovered_store = recovered.receipt.get("recovered_store", {})
    if (
        str(authority_metadata.get("paper_relative_path") or "") != authority_path
        or str(carrier_metadata.get("paper_relative_path") or "") != carrier_path
        or not isinstance(recovered_store, Mapping)
        or str(recovered_store.get("receipt_paper_relative_path") or "")
        != receipt_path
        or str(carrier_metadata.get("encoding") or "") != "gzip"
        or str(carrier_metadata.get("compression_policy") or "")
        != DETERMINISTIC_GZIP_POLICY_VERSION
        or str(authority_metadata.get("bytes_sha256") or "")
        != _sha256_bytes(recovered.authority_bytes)
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered receipt does not bind the requested output artifacts"
        )
    if (
        verified_deterministic_gzip_decompress(
            recovered.carrier_compressed_bytes,
            expected_compressed_sha256=str(
                carrier_metadata.get("compressed_bytes_sha256") or ""
            ),
            expected_uncompressed_sha256=str(
                carrier_metadata.get("uncompressed_bytes_sha256") or ""
            ),
            expected_uncompressed_byte_length=carrier_metadata.get(
                "uncompressed_byte_length"
            ),
        )
        != recovered.carrier_uncompressed_bytes
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered compressed carrier does not reproduce the raw carrier"
        )
    if _receipt_bytes_fixed_point(recovered.receipt) != recovered.receipt_bytes:
        raise HistoricalManifestStoreRecoveryError("recovered receipt bytes are stale")
    verified_authority, verified_carrier, verified_raw_carrier = (
        verified_recovered_manifest_store_artifacts(
            paper=paper,
            receipt=recovered.receipt,
            receipt_bytes=recovered.receipt_bytes,
            authority_bytes=recovered.authority_bytes,
            carrier_compressed_bytes=recovered.carrier_compressed_bytes,
        )
    )
    if (
        verified_authority != dict(recovered.authority)
        or verified_carrier != dict(recovered.carrier)
        or verified_raw_carrier != recovered.carrier_uncompressed_bytes
    ):
        raise HistoricalManifestStoreRecoveryError(
            "recovered receipt does not reproduce its store payloads"
        )
    _atomic_create_bytes(
        _configured_paper_path(root, paper, carrier_path, label="carrier output"),
        recovered.carrier_compressed_bytes,
    )
    _atomic_create_bytes(
        _configured_paper_path(root, paper, authority_path, label="authority output"),
        recovered.authority_bytes,
    )
    _atomic_create_bytes(
        _configured_paper_path(root, paper, receipt_path, label="receipt output"),
        recovered.receipt_bytes,
    )


def _cli_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Recover a missing historical authenticated manifest store from an "
            "immutable Git commit. The command is dry-run unless --write is set."
        )
    )
    parser.add_argument("--paper", required=True, help="paper directory name")
    parser.add_argument(
        "--historical-commit",
        required=True,
        help="exact 40- or 64-hex immutable commit object id",
    )
    parser.add_argument(
        "--historical-sidecar",
        required=True,
        help="surviving audit/*.json path, relative to the paper directory",
    )
    parser.add_argument(
        "--historical-sidecar-git-path",
        help=(
            "audit/*.json path at the historical commit; defaults to "
            "--historical-sidecar"
        ),
    )
    parser.add_argument(
        "--authority-output",
        required=True,
        help="new audit/*.json authority artifact path, relative to the paper",
    )
    parser.add_argument(
        "--carrier-output",
        required=True,
        help="new audit/*.json.gz compressed carrier artifact path, relative to the paper",
    )
    parser.add_argument(
        "--receipt-output",
        required=True,
        help="new audit/*.json recovery receipt path, relative to the paper",
    )
    parser.add_argument(
        "--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS
    )
    parser.add_argument(
        "--build-timeout-seconds", type=int, default=DEFAULT_BUILD_TIMEOUT_SECONDS
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="create the three explicit output artifacts after a successful recovery",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _cli_parser().parse_args(argv)
    config = HistoricalManifestStoreRecoveryConfig(
        root=Path(__file__).resolve().parents[1],
        paper=args.paper,
        historical_commit=args.historical_commit,
        historical_sidecar_path=args.historical_sidecar,
        historical_sidecar_git_path=args.historical_sidecar_git_path,
        authority_output_path=args.authority_output,
        carrier_output_path=args.carrier_output,
        receipt_output_path=args.receipt_output,
        timeout_seconds=args.timeout_seconds,
        build_timeout_seconds=args.build_timeout_seconds,
    )
    try:
        recovered = recover_historical_manifest_store(config)
        if args.write:
            write_recovered_manifest_store(config, recovered)
        print(
            json.dumps(
                {
                    "status": "written" if args.write else "dry_run",
                    "paper": config.paper,
                    "accepted_declaration_count": len(recovered.accepted_declarations),
                    "receipt_sha256": recovered.receipt[
                        HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD
                    ],
                    "authority_bytes_sha256": _sha256_bytes(recovered.authority_bytes),
                    "carrier_compressed_bytes_sha256": _sha256_bytes(
                        recovered.carrier_compressed_bytes
                    ),
                    "carrier_uncompressed_bytes_sha256": _sha256_bytes(
                        recovered.carrier_uncompressed_bytes
                    ),
                },
                ensure_ascii=True,
                sort_keys=True,
            )
        )
    except HistoricalManifestStoreRecoveryError as exc:
        print(f"historical-manifest-store-recovery: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry point.
    raise SystemExit(main())
