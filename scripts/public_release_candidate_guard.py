#!/usr/bin/env python3
"""Validate a clean, allowlisted public release candidate without publishing it."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pwd
import re
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
try:
    from lean_import_closure import dependency_closure_issues
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.lean_import_closure import dependency_closure_issues
try:
    from public_release_artifact_policy import public_release_artifact_issues
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.public_release_artifact_policy import public_release_artifact_issues


ROOT = Path(__file__).resolve().parents[1]
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PUBLIC_REMOTE = "origin"
PUBLIC_BASE_REF = "origin/main"
PUBLIC_BRANCH_PREFIX = "release/"
PRIVATE_REMOTE = "origin"
PRIVATE_BASE_REF = "origin/main"
REVIEWER_APPROVAL_PATH = (
    Path(pwd.getpwuid(os.getuid()).pw_dir)
    / ".config"
    / "econcslib"
    / "public-release-approval.json"
)
PUBLIC_REMOTE_RE = re.compile(
    r"^(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
    r"nikhgarg/EconCSLib(?:\.git)?$",
    re.IGNORECASE,
)
PRIVATE_REMOTE_RE = re.compile(
    r"^(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
    r"nikhgarg/EconCSLib-private(?:\.git)?$",
    re.IGNORECASE,
)
FORBIDDEN_PUBLIC_PATH_RE = re.compile(
    r"(?:^|/)(?:\.review_traces|\.audit_source|sources|source_tex)(?:/|$)|"
    r"(?:^|/)(?:source(?:[._-][^/]*)?\.(?:txt|pdf|tex|tar|tgz|zip|gz)|"
    r"arxiv_source\.(?:tar|tgz|zip|gz))$|"
    r"(?:^|/)(?:PRIVATE_[^/]*|[^/]*_HANDOFF_[^/]*)$",
    re.IGNORECASE,
)
GENERATED_PUBLIC_STATUS_PATHS = frozenset(
    {
        "papers/status.json",
        "papers/human_status.json",
        "docs/PAPER_STATUS.md",
        "site/index.html",
    }
)
PUBLIC_STATUS_GENERATOR = "python3 scripts/sync_paper_status.py"
TRUSTED_STATUS_SYNC = Path(__file__).resolve().with_name("sync_paper_status.py")
SOURCE_TEXT_COMPANION_PATH_FIELDS = frozenset(
    {"canonical_text", "visual_primary_scan", "transcript_input_scan"}
)
PAPERS_NON_NAMESPACE_PATHS = frozenset(
    {
        "papers/audit_config.json",
        "papers/catalog.json",
        "papers/human_status.json",
        "papers/status.json",
    }
)


@dataclass(frozen=True)
class AllowlistEntry:
    path: str
    kind: str
    provenance: str
    source_commit: str | None
    reason: str
    generator: str | None
    public_base_blob_sha256: str | None = None
    candidate_blob_sha256: str | None = None


@dataclass(frozen=True)
class CandidateChange:
    status: str
    path: str


@dataclass(frozen=True)
class CandidateCommit:
    commit: str
    parent: str
    changes: tuple[CandidateChange, ...]


@dataclass(frozen=True)
class GitTreeEntry:
    mode: str
    object_type: str
    object_id: str


@dataclass(frozen=True)
class ReleaseApproval:
    candidate_commit: str
    public_base_commit: str
    allowlist_sha256: str
    guard_sha256: str
    trusted_tooling_sha256: str
    private_source_commits: tuple[str, ...]


def _git_environment() -> dict[str, str]:
    environment = os.environ.copy()
    for key in list(environment):
        if key.startswith("GIT_CONFIG_") or key in {
            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_COMMON_DIR",
            "GIT_DIR",
            "GIT_INDEX_FILE",
            "GIT_NAMESPACE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_WORK_TREE",
        }:
            environment.pop(key, None)
    environment["GIT_NO_REPLACE_OBJECTS"] = "1"
    return environment


def _git(repo: Path, args: list[str], *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed: {result.stderr.strip() or result.stdout.strip()}"
        )
    return result.stdout


def _git_bytes(repo: Path, args: list[str]) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed: "
            + result.stderr.decode("utf-8", errors="replace").strip()
        )
    return result.stdout


def is_git_repository(path: Path) -> bool:
    """Return whether ``path`` names a usable Git repository/worktree."""

    if not path.is_dir():
        return False
    result = subprocess.run(
        ["git", "rev-parse", "--git-dir"],
        cwd=path,
        env=_git_environment(),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def resolved_commit(repo: Path, ref: str) -> str:
    return _git(repo, ["rev-parse", "--verify", f"{ref}^{{commit}}"]).strip()


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _guard_sha256() -> str:
    return _sha256_bytes(Path(__file__).resolve().read_bytes())


def _trusted_tooling_sha256(scripts_dir: Path | None = None) -> str:
    """Digest every private production helper that release validation may load.

    The release guard imports and executes helpers from its sibling ``scripts``
    directory.  Pinning only this file would leave those transitive authorities
    mutable after review.  Hash the complete production-tooling directory,
    excluding tests and interpreter caches, so newly introduced local helpers
    are covered without maintaining a fragile hand-written import list.
    """

    scripts_dir = (
        Path(__file__).resolve().parent
        if scripts_dir is None
        else scripts_dir.resolve()
    )
    root = scripts_dir.parent
    records: list[dict[str, object]] = []
    for path in sorted(scripts_dir.rglob("*"), key=lambda item: item.as_posix()):
        relative_to_scripts = path.relative_to(scripts_dir)
        if any(part in {"__pycache__", "tests"} for part in relative_to_scripts.parts):
            continue
        try:
            metadata = path.lstat()
        except OSError as exc:
            raise RuntimeError(f"cannot inspect trusted tooling path {path}: {exc}") from exc
        if stat.S_ISDIR(metadata.st_mode):
            continue
        if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
            raise RuntimeError(
                f"trusted tooling contains a non-regular path: {path.relative_to(root)}"
            )
        if path.suffix in {".pyc", ".pyo"}:
            continue
        try:
            payload = path.read_bytes()
        except OSError as exc:
            raise RuntimeError(f"cannot read trusted tooling path {path}: {exc}") from exc
        records.append(
            {
                "path": path.relative_to(root).as_posix(),
                "executable": bool(metadata.st_mode & 0o111),
                "byte_length": len(payload),
                "sha256": _sha256_bytes(payload),
            }
        )
    if not records:
        raise RuntimeError("trusted release-tooling bundle is empty")
    encoded = json.dumps(
        {
            "schema": "econcslib.public-release-trusted-tooling/v1",
            "files": records,
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return _sha256_bytes(encoded)


def _path_is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def load_release_approval(path: Path) -> ReleaseApproval:
    """Load one fixed-path, reviewer-owned approval without following symlinks."""

    try:
        parent_metadata = path.parent.lstat()
    except OSError as exc:
        raise ValueError(f"cannot inspect reviewer approval directory {path.parent}: {exc}") from exc
    if (
        path.parent.is_symlink()
        or not stat.S_ISDIR(parent_metadata.st_mode)
        or parent_metadata.st_uid != os.getuid()
        or parent_metadata.st_mode & (stat.S_IWGRP | stat.S_IWOTH)
    ):
        raise ValueError(
            "reviewer approval directory must be reviewer-owned, non-symlink, and "
            f"not group/world writable: {path.parent}"
        )
    try:
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError as exc:
        raise ValueError(f"cannot read reviewer approval {path}: {exc}") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & (stat.S_IWGRP | stat.S_IWOTH)
        ):
            raise ValueError(
                "reviewer approval must be one reviewer-owned regular file that is "
                f"not group/world writable: {path}"
            )
        with os.fdopen(descriptor, "r", encoding="utf-8") as handle:
            descriptor = -1
            payload = json.load(handle)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read reviewer approval {path}: {exc}") from exc
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    required_fields = {
        "schema",
        "candidate_commit",
        "public_base_commit",
        "allowlist_sha256",
        "guard_sha256",
        "trusted_tooling_sha256",
        "private_source_commits",
    }
    if not isinstance(payload, dict) or set(payload) != required_fields:
        raise ValueError(
            "reviewer approval must be a schema-2 object with exactly: "
            + ", ".join(sorted(required_fields))
        )
    if payload.get("schema") != 2:
        raise ValueError("reviewer approval must use schema 2")
    candidate_commit = str(payload.get("candidate_commit") or "").strip().lower()
    public_base_commit = str(payload.get("public_base_commit") or "").strip().lower()
    allowlist_sha256 = str(payload.get("allowlist_sha256") or "").strip().lower()
    guard_sha256 = str(payload.get("guard_sha256") or "").strip().lower()
    trusted_tooling_sha256 = (
        str(payload.get("trusted_tooling_sha256") or "").strip().lower()
    )
    raw_source_commits = payload.get("private_source_commits")
    if not SHA1_RE.fullmatch(candidate_commit):
        raise ValueError("reviewer approval candidate_commit must be 40 lowercase hex")
    if not SHA1_RE.fullmatch(public_base_commit):
        raise ValueError("reviewer approval public_base_commit must be 40 lowercase hex")
    if not SHA256_RE.fullmatch(allowlist_sha256):
        raise ValueError("reviewer approval allowlist_sha256 must be 64 lowercase hex")
    if not SHA256_RE.fullmatch(guard_sha256):
        raise ValueError("reviewer approval guard_sha256 must be 64 lowercase hex")
    if not SHA256_RE.fullmatch(trusted_tooling_sha256):
        raise ValueError(
            "reviewer approval trusted_tooling_sha256 must be 64 lowercase hex"
        )
    if not isinstance(raw_source_commits, list):
        raise ValueError("reviewer approval private_source_commits must be a list")
    source_commits = tuple(
        str(commit).strip().lower() for commit in raw_source_commits
    )
    if any(not SHA1_RE.fullmatch(commit) for commit in source_commits):
        raise ValueError(
            "reviewer approval private_source_commits entries must be 40 lowercase hex"
        )
    if tuple(sorted(set(source_commits))) != source_commits:
        raise ValueError(
            "reviewer approval private_source_commits must be sorted and duplicate-free"
        )
    return ReleaseApproval(
        candidate_commit=candidate_commit,
        public_base_commit=public_base_commit,
        allowlist_sha256=allowlist_sha256,
        guard_sha256=guard_sha256,
        trusted_tooling_sha256=trusted_tooling_sha256,
        private_source_commits=source_commits,
    )


def canonical_remote_issues(
    repo: Path,
    *,
    remote: str,
    expected: re.Pattern[str],
    label: str,
) -> list[str]:
    """Require one canonical URL for both fetch and every push operation."""

    issues: list[str] = []
    fetch_urls = [
        value.strip()
        for value in _git(
            repo, ["remote", "get-url", "--all", remote], check=False
        ).splitlines()
        if value.strip()
    ]
    push_urls = [
        value.strip()
        for value in _git(
            repo, ["remote", "get-url", "--push", "--all", remote], check=False
        ).splitlines()
        if value.strip()
    ]
    for direction, urls in (("fetch", fetch_urls), ("push", push_urls)):
        if len(urls) != 1 or expected.fullmatch(urls[0]) is None:
            issues.append(
                f"{label} remote {remote!r} must have exactly one canonical {direction} "
                f"URL; got {urls!r}"
            )
    return issues


def _git_storage_path(repo: Path, arguments: list[str]) -> Path:
    return Path(
        _git(
            repo,
            ["rev-parse", "--path-format=absolute", *arguments],
        ).strip()
    ).resolve()


def shared_git_storage_issues(candidate_repo: Path, private_repo: Path) -> list[str]:
    """Reject worktrees or repositories that expose the same Git object store."""

    issues: list[str] = []
    for arguments, label in (
        (["--git-common-dir"], "Git common directory"),
        (["--git-path", "objects"], "Git object directory"),
    ):
        candidate_path = _git_storage_path(candidate_repo, arguments)
        private_path = _git_storage_path(private_repo, arguments)
        if candidate_path == private_path:
            issues.append(
                f"public candidate and private repository share the same {label}: "
                f"{candidate_path}"
            )
    candidate_objects = _git_storage_path(
        candidate_repo, ["--git-path", "objects"]
    )
    alternates = candidate_objects / "info" / "alternates"
    if alternates.exists():
        try:
            configured = [
                line.strip()
                for line in alternates.read_text(encoding="utf-8").splitlines()
                if line.strip()
            ]
        except (OSError, UnicodeDecodeError) as exc:
            issues.append(f"cannot inspect public candidate object alternates: {exc}")
        else:
            if configured:
                issues.append(
                    "public candidate must use a standalone Git object database; "
                    f"found alternates in {alternates}"
                )
    return issues


def _tree_entry(repo: Path, ref: str, path: str) -> GitTreeEntry | None:
    """Read one exact tree entry without treating ``path`` as a pathspec."""

    raw = _git_bytes(repo, ["ls-tree", "-z", ref, "--", f":(literal){path}"])
    records = [record for record in raw.split(b"\0") if record]
    if not records:
        return None
    if len(records) != 1 or b"\t" not in records[0]:
        raise RuntimeError(f"cannot resolve one exact tree entry for {ref}:{path}")
    metadata, raw_path = records[0].split(b"\t", 1)
    if raw_path.decode("utf-8", errors="surrogateescape") != path:
        raise RuntimeError(f"Git returned an unexpected tree path for {ref}:{path}")
    fields = metadata.split()
    if len(fields) != 3:
        raise RuntimeError(f"Git returned malformed tree metadata for {ref}:{path}")
    return GitTreeEntry(
        mode=fields[0].decode("ascii"),
        object_type=fields[1].decode("ascii"),
        object_id=fields[2].decode("ascii"),
    )


def _safe_relative_path(value: object) -> str | None:
    if not isinstance(value, str) or not value.strip():
        return None
    path = PurePosixPath(value.strip())
    if path.is_absolute() or ".." in path.parts or str(path) in {"", "."}:
        return None
    return str(path)


def load_allowlist(path: Path) -> list[AllowlistEntry]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise ValueError(f"cannot read public export allowlist {path}: {exc}") from exc
    return parse_allowlist(raw, source=str(path))


def parse_allowlist(raw: bytes, *, source: str) -> list[AllowlistEntry]:
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read public export allowlist {source}: {exc}") from exc
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise ValueError("public export allowlist must be a schema-1 object")
    raw_entries = payload.get("entries")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise ValueError("public export allowlist entries must be a nonempty list")
    entries: list[AllowlistEntry] = []
    seen: set[str] = set()
    for index, raw in enumerate(raw_entries):
        if not isinstance(raw, dict):
            raise ValueError(f"allowlist entry {index} must be an object")
        candidate = _safe_relative_path(raw.get("path"))
        kind = raw.get("kind")
        provenance = str(raw.get("provenance") or "").strip()
        raw_source_commit = raw.get("source_commit")
        source_commit = (
            str(raw_source_commit).strip().lower()
            if raw_source_commit is not None
            else None
        )
        reason = str(raw.get("reason") or "").strip()
        raw_generator = raw.get("generator")
        generator = str(raw_generator).strip() if raw_generator is not None else None
        raw_public_base_blob_sha256 = raw.get("public_base_blob_sha256")
        public_base_blob_sha256 = (
            str(raw_public_base_blob_sha256).strip().lower()
            if raw_public_base_blob_sha256 is not None
            else None
        )
        raw_candidate_blob_sha256 = raw.get("candidate_blob_sha256")
        candidate_blob_sha256 = (
            str(raw_candidate_blob_sha256).strip().lower()
            if raw_candidate_blob_sha256 is not None
            else None
        )
        if candidate is None:
            raise ValueError(f"allowlist entry {index} has an unsafe path")
        if candidate in seen:
            raise ValueError(f"allowlist path is duplicated: {candidate}")
        if kind != "file":
            raise ValueError(
                f"allowlist entry {candidate} kind must be file; directory entries "
                "cannot authorize an unreviewed descendant"
            )
        if provenance not in {
            "private_blob",
            "public_generated",
            "public_base_deletion",
            "public_base_edit",
            "public_base_addition",
        }:
            raise ValueError(
                f"allowlist entry {candidate} provenance must be private_blob, "
                "public_generated, public_base_deletion, public_base_edit, or "
                "public_base_addition"
            )
        if provenance == "private_blob":
            if source_commit is None or not SHA1_RE.fullmatch(source_commit):
                raise ValueError(
                    f"allowlist entry {candidate} needs a 40-hex source_commit"
                )
            if generator is not None:
                raise ValueError(
                    f"private_blob allowlist entry {candidate} cannot declare a generator"
                )
            if (
                public_base_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"private_blob allowlist entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "public_generated":
            if kind != "file" or candidate not in GENERATED_PUBLIC_STATUS_PATHS:
                raise ValueError(
                    f"public_generated entry {candidate} must be one exact generated status path"
                )
            if source_commit is not None:
                raise ValueError(
                    f"public_generated entry {candidate} must not claim a source_commit"
                )
            if generator != PUBLIC_STATUS_GENERATOR:
                raise ValueError(
                    f"public_generated entry {candidate} must declare generator "
                    f"{PUBLIC_STATUS_GENERATOR!r}"
                )
            if (
                public_base_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_generated entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "public_base_deletion":
            if source_commit is not None or generator is not None:
                raise ValueError(
                    f"public_base_deletion entry {candidate} cannot declare source_commit or generator"
                )
            if (
                public_base_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_base_deletion entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "public_base_edit":
            if source_commit is not None or generator is not None:
                raise ValueError(
                    f"public_base_edit entry {candidate} cannot declare source_commit or generator"
                )
            if not SHA256_RE.fullmatch(public_base_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_edit entry {candidate} needs a 64-hex "
                    "public_base_blob_sha256"
                )
            if not SHA256_RE.fullmatch(candidate_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_edit entry {candidate} needs a 64-hex "
                    "candidate_blob_sha256"
                )
            if public_base_blob_sha256 == candidate_blob_sha256:
                raise ValueError(
                    f"public_base_edit entry {candidate} must pin distinct base and "
                    "candidate blob digests"
                )
        else:
            if source_commit is not None or generator is not None:
                raise ValueError(
                    f"public_base_addition entry {candidate} cannot declare "
                    "source_commit or generator"
                )
            if public_base_blob_sha256 is not None:
                raise ValueError(
                    f"public_base_addition entry {candidate} cannot declare a "
                    "public_base_blob_sha256"
                )
            if not SHA256_RE.fullmatch(candidate_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_addition entry {candidate} needs a 64-hex "
                    "candidate_blob_sha256"
                )
        if not reason:
            raise ValueError(f"allowlist entry {candidate} needs a review reason")
        if raw.get("public_safety_reviewed") is not True:
            raise ValueError(
                f"allowlist entry {candidate} must set public_safety_reviewed=true"
            )
        seen.add(candidate)
        entries.append(
            AllowlistEntry(
                candidate,
                str(kind),
                provenance,
                source_commit,
                reason,
                generator,
                public_base_blob_sha256,
                candidate_blob_sha256,
            )
        )
    return entries


def path_is_allowlisted(path: str, entries: list[AllowlistEntry]) -> bool:
    return matching_allowlist_entry(path, entries) is not None


def matching_allowlist_entry(
    path: str, entries: list[AllowlistEntry]
) -> AllowlistEntry | None:
    return next((entry for entry in entries if path == entry.path), None)


def unused_allowlist_issues(
    entries: list[AllowlistEntry], used_entries: set[AllowlistEntry]
) -> list[str]:
    return [
        f"allowlist entry is unused by candidate history: {entry.path}"
        for entry in entries
        if entry not in used_entries
    ]


def status_visibility_issues(repo: Path, candidate_ref: str = "HEAD") -> list[str]:
    """Require explicit public visibility for every candidate paper namespace."""

    paths = _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    paper_names: set[str] = set()
    status_paths: dict[str, str] = {}
    for path in paths:
        if path in PAPERS_NON_NAMESPACE_PATHS or not path.startswith("papers/"):
            continue
        pure = PurePosixPath(path)
        if len(pure.parts) >= 3:
            paper_name = pure.parts[1]
        elif len(pure.parts) == 2 and pure.suffix == ".lean":
            paper_name = pure.stem
        else:
            continue
        if paper_name == "TEMPLATE":
            continue
        paper_names.add(paper_name)
        expected_status = f"papers/{paper_name}/status.json"
        if path == expected_status:
            status_paths[paper_name] = path

    issues: list[str] = []
    for paper_name in sorted(paper_names):
        path = status_paths.get(paper_name)
        if path is None:
            issues.append(
                f"papers/{paper_name}: public candidate paper namespace requires "
                f"papers/{paper_name}/status.json with repository_visibility=`public`"
            )
            continue
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{path}: cannot read candidate status: {exc}")
            continue
        visibility = payload.get("repository_visibility") if isinstance(payload, dict) else None
        if visibility != "public":
            issues.append(
                f"{path}: public candidate requires repository_visibility=`public`, "
                f"got {visibility!r}"
            )
    return issues


def _paper_local_candidate_path(
    *, paper_dir: PurePosixPath, raw_path: object
) -> str | None:
    """Resolve the source-map path convention without touching the worktree."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    raw = raw_path.strip()
    candidate = PurePosixPath(raw)
    if candidate.is_absolute() or ".." in candidate.parts:
        return None
    resolved = candidate if candidate.parts[:1] == ("papers",) else paper_dir / candidate
    try:
        resolved.relative_to(paper_dir)
    except ValueError:
        return None
    return str(resolved)


def _artifact_present(candidate_paths: set[str], artifact_path: str) -> bool:
    prefix = artifact_path.rstrip("/") + "/"
    return artifact_path in candidate_paths or any(
        path.startswith(prefix) for path in candidate_paths
    )


def source_artifact_leakage_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Reject source bytes declared by candidate source maps and companions."""

    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    map_paths = sorted(
        path
        for path in candidate_paths
        if path.startswith("papers/")
        and path.endswith("/audit/paper_statement_map.json")
    )
    issues: list[str] = []
    for map_path in map_paths:
        paper_dir = PurePosixPath(map_path).parents[1]
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{map_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{map_path}: cannot inspect declared source artifacts: {exc}")
            continue
        if not isinstance(payload, dict):
            issues.append(f"{map_path}: source map must be a JSON object")
            continue
        descriptors: list[tuple[str, object]] = []

        def collect_item_source_paths(value: object, location: str = "$") -> None:
            """Collect schema-declared source-byte paths without guessing by filename."""

            if isinstance(value, dict):
                for field in ("source_artifact_path", "source_text_file"):
                    if field in value:
                        descriptors.append((f"{location}.{field}", value.get(field)))
                anchors = value.get("source_anchor_evidence")
                if isinstance(anchors, list):
                    for index, anchor in enumerate(anchors):
                        if isinstance(anchor, dict) and "path" in anchor:
                            descriptors.append(
                                (
                                    f"{location}.source_anchor_evidence[{index}].path",
                                    anchor.get("path"),
                                )
                            )
                for field, child in value.items():
                    if field == "source_anchor_evidence":
                        continue
                    collect_item_source_paths(child, f"{location}.{field}")
            elif isinstance(value, list):
                for index, child in enumerate(value):
                    collect_item_source_paths(child, f"{location}[{index}]")

        collect_item_source_paths(payload)
        companion = payload.get("source_text_companion")
        if isinstance(companion, dict):
            for field in sorted(SOURCE_TEXT_COMPANION_PATH_FIELDS):
                descriptor = companion.get(field)
                raw_path = descriptor.get("path") if isinstance(descriptor, dict) else None
                descriptors.append((f"source_text_companion.{field}.path", raw_path))
        archive_surface = payload.get("source_archive_surface")
        if isinstance(archive_surface, dict):
            archive = archive_surface.get("archive")
            raw_path = archive.get("path") if isinstance(archive, dict) else None
            descriptors.append(("source_archive_surface.archive.path", raw_path))
        reported_artifacts: set[str] = set()
        for field, raw_path in descriptors:
            artifact = _paper_local_candidate_path(
                paper_dir=paper_dir, raw_path=raw_path
            )
            if artifact is None:
                if isinstance(raw_path, str) and raw_path.strip():
                    issues.append(
                        f"{map_path}: declared private source artifact path is unsafe "
                        f"or leaves its paper directory ({field} -> {raw_path.strip()})"
                    )
                continue
            if artifact not in reported_artifacts and _artifact_present(
                candidate_paths, artifact
            ):
                reported_artifacts.add(artifact)
                issues.append(
                    f"{map_path}: declared private source artifact is present in the "
                    f"public candidate ({field} -> {artifact})"
                )
    return issues


def forbidden_candidate_path_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    return [
        f"forbidden private/source artifact path in public candidate: {path}"
        for path in sorted(
            _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
        )
        if FORBIDDEN_PUBLIC_PATH_RE.search(path)
    ]


def _status_string_leaves(
    value: object,
    route: tuple[str, ...] = (),
) -> list[tuple[tuple[str, ...], str]]:
    leaves: list[tuple[tuple[str, ...], str]] = []
    if isinstance(value, dict):
        for key, child in value.items():
            leaves.extend(_status_string_leaves(child, (*route, str(key))))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            leaves.extend(_status_string_leaves(child, (*route, str(index))))
    elif isinstance(value, str):
        leaves.append((route, value))
    return leaves


def _candidate_current_audit_artifacts(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Read present supplemental current-audit paths from candidate status fields.

    ``review_surface`` file fields are configured destinations.  Some lanes are
    conditional (for example, defect-support evidence is needed only when a
    quarantined defect is used as support), so a safe paper-local destination
    may legitimately be absent.  ``artifacts`` entries instead declare current
    outputs and remain required to exist.  In both sections, validate the path
    before testing presence so an absent unsafe or cross-paper route cannot be
    used to weaken the public artifact policy.
    """

    current: set[str] = set()
    issues: list[str] = []
    status_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 3
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2] == "status.json"
    )
    for status_path in status_paths:
        paper = PurePosixPath(status_path).parts[1]
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{status_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(
                f"{status_path}: cannot derive current public audit artifacts: {exc}"
            )
            continue
        if not isinstance(payload, dict):
            issues.append(
                f"{status_path}: cannot derive current public audit artifacts from "
                "a non-object status"
            )
            continue
        expected_prefix = f"papers/{paper}/audit/"
        for section_name in ("artifacts", "review_surface"):
            section = payload.get(section_name)
            if section is None:
                continue
            if not isinstance(section, dict):
                issues.append(
                    f"{status_path}: {section_name} must be an object before it can "
                    "authorize current public audit artifacts"
                )
                continue
            for route, raw_path in _status_string_leaves(section):
                if "/audit/" not in raw_path or any(
                    character.isspace() for character in raw_path
                ):
                    continue
                normalized = _safe_relative_path(raw_path)
                route_text = ".".join((section_name, *route))
                if normalized is None or normalized != raw_path:
                    issues.append(
                        f"{status_path}: {route_text} has an unsafe or noncanonical "
                        f"current audit artifact path: {raw_path!r}"
                    )
                    continue
                if not normalized.startswith(expected_prefix):
                    issues.append(
                        f"{status_path}: {route_text} current audit artifact must stay "
                        f"beneath {expected_prefix}: {normalized}"
                    )
                    continue
                if normalized not in candidate_paths:
                    if section_name == "artifacts":
                        issues.append(
                            f"{status_path}: {route_text} declared current audit "
                            "artifact is absent from the exact candidate tree: "
                            f"{normalized}"
                        )
                    continue
                current.add(normalized)
    return current, issues


def _candidate_receipt_review_ledgers(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Read receipt-bound current audit ledgers from the exact candidate tree.

    A direct source-row review is an accepted closeout lane.  Its compact JSON
    ledger is canonical when, and only when, the paper's final closure receipt
    binds that exact paper-local audit path.  Do not require a duplicate status
    field merely to make the public artifact policy recognize this evidence.
    """

    current: set[str] = set()
    issues: list[str] = []
    receipt_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 3
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2] == "FINAL_CLOSURE_RECEIPT.md"
    )
    for receipt_path in receipt_paths:
        paper = PurePosixPath(receipt_path).parts[1]
        try:
            text = _git(repo, ["show", f"{candidate_ref}:{receipt_path}"])
        except RuntimeError as exc:
            issues.append(f"{receipt_path}: cannot read receipt-bound audit ledger: {exc}")
            continue
        match = re.search(
            r"(?ms)^\[review_ledger\]\s*\npath\s*=\s*\"([^\"]+)\"",
            text,
        )
        if match is None:
            continue
        raw_path = match.group(1)
        normalized = _safe_relative_path(raw_path)
        expected_prefix = f"papers/{paper}/audit/"
        if normalized is None or normalized != raw_path:
            issues.append(
                f"{receipt_path}: review_ledger.path has an unsafe or noncanonical "
                f"audit path: {raw_path!r}"
            )
            continue
        if not normalized.startswith(expected_prefix):
            issues.append(
                f"{receipt_path}: review_ledger.path must stay beneath "
                f"{expected_prefix}: {normalized}"
            )
            continue
        if normalized not in candidate_paths:
            issues.append(
                f"{receipt_path}: receipt-bound current audit artifact is absent from "
                f"the exact candidate tree: {normalized}"
            )
            continue
        current.add(normalized)
    return current, issues


def candidate_public_artifact_policy_issues(
    repo: Path,
    candidate_ref: str = "HEAD",
) -> list[str]:
    """Apply public artifact hygiene to every path in the exact candidate tree."""

    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    current_audit_artifacts, issues = _candidate_current_audit_artifacts(
        repo,
        candidate_ref,
        candidate_paths,
    )
    receipt_ledgers, receipt_issues = _candidate_receipt_review_ledgers(
        repo,
        candidate_ref,
        candidate_paths,
    )
    current_audit_artifacts.update(receipt_ledgers)
    issues.extend(receipt_issues)
    try:
        issues.extend(
            public_release_artifact_issues(
                candidate_paths,
                current_audit_artifacts=current_audit_artifacts,
            )
        )
    except ValueError as exc:
        issues.append(f"public artifact policy configuration is invalid: {exc}")
    return issues


def changes_between(repo: Path, old_ref: str, new_ref: str) -> list[CandidateChange]:
    raw = _git(
        repo,
        [
            "diff",
            "--name-status",
            "--no-renames",
            "-z",
            "--diff-filter=ACDMT",
            old_ref,
            new_ref,
        ],
    )
    parts = [part for part in raw.split("\0") if part]
    if len(parts) % 2:
        raise RuntimeError("git name-status output was malformed")
    return sorted(
        (
            CandidateChange(parts[index][0], parts[index + 1])
            for index in range(0, len(parts), 2)
        ),
        key=lambda change: change.path,
    )


def candidate_changes(
    repo: Path, base_ref: str, candidate_ref: str
) -> list[CandidateChange]:
    """Return the final-tree delta; history validation uses ``candidate_history``."""

    return changes_between(repo, base_ref, candidate_ref)


def candidate_history(
    repo: Path, base_ref: str, candidate_ref: str
) -> tuple[list[CandidateCommit], list[str]]:
    """Return the single squashed release commit rooted at the exact public base.

    Net-tree validation cannot make a branch safe to push: a private merge or an
    add-then-delete commit still publishes the intermediate commits and blobs.
    The public candidate therefore consists of exactly one inspected commit
    whose sole parent is the exact base. Merges, stacked commits, private HEAD,
    and add-then-delete histories all fail closed.
    """

    base = resolved_commit(repo, base_ref)
    candidate = resolved_commit(repo, candidate_ref)
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base, candidate],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if ancestor.returncode != 0:
        return [], [f"candidate {candidate_ref} is not based on exact public base {base_ref}"]

    commits = [
        line.strip()
        for line in _git(repo, ["rev-list", "--reverse", f"{base}..{candidate}"]).splitlines()
        if line.strip()
    ]
    history: list[CandidateCommit] = []
    issues: list[str] = []
    if len(commits) != 1:
        issues.append(
            "public release candidate must be exactly one squashed commit whose parent "
            f"is the exact public base; found {len(commits)} candidate commit(s)"
        )
    expected_parent = base
    for commit in commits:
        parent_line = _git(repo, ["rev-list", "--parents", "-n", "1", commit]).split()
        if not parent_line or parent_line[0] != commit:
            issues.append(f"cannot resolve candidate commit parents: {commit}")
            continue
        parents = parent_line[1:]
        if len(parents) != 1:
            issues.append(
                f"candidate history must be linear and merge-free: {commit} has "
                f"{len(parents)} parent(s)"
            )
            continue
        parent = parents[0]
        if parent != expected_parent:
            issues.append(
                f"candidate history is not one linear chain from exact public base: "
                f"{commit} has parent {parent}, expected {expected_parent}"
            )
        history.append(
            CandidateCommit(
                commit=commit,
                parent=parent,
                changes=tuple(changes_between(repo, parent, commit)),
            )
        )
        expected_parent = commit
    if expected_parent != candidate:
        issues.append(
            "candidate history could not be traversed as one linear chain from the exact public base"
        )
    return history, issues


def source_provenance_issues(
    candidate_repo: Path,
    private_repo: Path,
    candidate_ref: str,
    changes: list[CandidateChange],
    entries: list[AllowlistEntry],
    *,
    public_base_ref: str = PUBLIC_BASE_REF,
) -> list[str]:
    """Bind each non-generated change to its exact reviewed source bytes."""

    issues: list[str] = []
    for change in changes:
        entry = matching_allowlist_entry(change.path, entries)
        if entry is None:
            continue
        if change.status == "D":
            if entry.provenance != "public_base_deletion":
                issues.append(
                    f"deleted path needs public_base_deletion provenance: {change.path}"
                )
            continue
        if entry.provenance == "public_base_deletion":
            issues.append(
                f"non-deleted path cannot use public_base_deletion provenance: {change.path}"
            )
            continue
        if entry.provenance == "public_generated":
            continue
        if entry.provenance == "public_base_addition":
            if change.status != "A":
                issues.append(
                    f"public_base_addition path must be an addition, not status "
                    f"{change.status}: {change.path}"
                )
            try:
                base_entry = _tree_entry(candidate_repo, public_base_ref, change.path)
                candidate_entry = _tree_entry(
                    candidate_repo, candidate_ref, change.path
                )
                candidate_blob = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
            except RuntimeError as exc:
                issues.append(
                    f"{change.path}: cannot verify pinned public-base addition: {exc}"
                )
                continue
            if base_entry is not None:
                issues.append(
                    f"{change.path}: public_base_addition requires the path to be "
                    "absent from the public base"
                )
            if candidate_entry is None or candidate_entry.object_type != "blob":
                issues.append(
                    f"{change.path}: public_base_addition requires a candidate blob"
                )
            if _sha256_bytes(candidate_blob) != entry.candidate_blob_sha256:
                issues.append(
                    f"{change.path}: candidate blob does not match allowlisted "
                    "candidate_blob_sha256"
                )
            for source_commit in sorted(
                {
                    item.source_commit
                    for item in entries
                    if item.provenance == "private_blob"
                    and item.source_commit is not None
                }
            ):
                try:
                    source_entry = _tree_entry(
                        private_repo, source_commit, change.path
                    )
                    if source_entry is None:
                        continue
                    source_blob = _git_bytes(
                        private_repo, ["show", f"{source_commit}:{change.path}"]
                    )
                except RuntimeError as exc:
                    issues.append(
                        f"{change.path}: cannot check public-only addition against "
                        f"reviewed private source commit {source_commit}: {exc}"
                    )
                    continue
                if (
                    candidate_entry is not None
                    and candidate_entry.mode == source_entry.mode
                    and candidate_entry.object_type == source_entry.object_type
                    and candidate_blob == source_blob
                ):
                    issues.append(
                        f"{change.path}: byte-identical candidate content already "
                        f"exists at reviewed private source commit {source_commit}; "
                        "use private_blob provenance"
                    )
            continue
        if entry.provenance == "public_base_edit":
            if change.status != "M":
                issues.append(
                    f"public_base_edit path must be an in-place modification, not "
                    f"status {change.status}: {change.path}"
                )
            try:
                base_entry = _tree_entry(candidate_repo, public_base_ref, change.path)
                candidate_entry = _tree_entry(
                    candidate_repo, candidate_ref, change.path
                )
                base_blob = _git_bytes(
                    candidate_repo, ["show", f"{public_base_ref}:{change.path}"]
                )
                candidate_blob = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
            except RuntimeError as exc:
                issues.append(
                    f"{change.path}: cannot verify pinned public-base edit: {exc}"
                )
                continue
            if base_entry is None or candidate_entry is None:
                issues.append(
                    f"{change.path}: public_base_edit requires the path to exist in "
                    "both the public base and candidate"
                )
                continue
            if (
                base_entry.object_type != "blob"
                or candidate_entry.object_type != "blob"
                or base_entry.mode != candidate_entry.mode
            ):
                issues.append(
                    f"{change.path}: public_base_edit cannot change Git mode or object type"
                )
            actual_base_sha256 = _sha256_bytes(base_blob)
            actual_candidate_sha256 = _sha256_bytes(candidate_blob)
            if actual_base_sha256 != entry.public_base_blob_sha256:
                issues.append(
                    f"{change.path}: public base blob does not match allowlisted "
                    "public_base_blob_sha256"
                )
            if actual_candidate_sha256 != entry.candidate_blob_sha256:
                issues.append(
                    f"{change.path}: candidate blob does not match allowlisted "
                    "candidate_blob_sha256"
                )
            continue
        assert entry.source_commit is not None
        try:
            candidate_entry = _tree_entry(candidate_repo, candidate_ref, change.path)
            source_entry = _tree_entry(private_repo, entry.source_commit, change.path)
            candidate_blob = _git_bytes(
                candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
            )
            source_blob = _git_bytes(
                private_repo, ["show", f"{entry.source_commit}:{change.path}"]
            )
        except RuntimeError as exc:
            issues.append(f"{change.path}: cannot verify private blob provenance: {exc}")
            continue
        if candidate_entry is None or source_entry is None:
            issues.append(
                f"{change.path}: candidate or private source tree entry is missing"
            )
            continue
        if (
            candidate_entry.mode != source_entry.mode
            or candidate_entry.object_type != source_entry.object_type
        ):
            issues.append(
                f"{change.path}: candidate Git mode/type differs from private source commit "
                f"{entry.source_commit}"
            )
        if candidate_blob != source_blob:
            issues.append(
                f"{change.path}: candidate blob differs from private source commit "
                f"{entry.source_commit}"
            )
    return issues


def candidate_tree_entry_issues(
    candidate_repo: Path,
    candidate_ref: str,
    changes: list[CandidateChange],
) -> list[str]:
    """Reject non-regular candidate entries regardless of private provenance."""

    issues: list[str] = []
    for change in changes:
        if change.status == "D":
            continue
        try:
            entry = _tree_entry(candidate_repo, candidate_ref, change.path)
        except RuntimeError as exc:
            issues.append(f"{change.path}: cannot inspect candidate tree entry: {exc}")
            continue
        if entry is None:
            issues.append(f"{change.path}: candidate tree entry is missing")
            continue
        if entry.object_type != "blob" or entry.mode not in {"100644", "100755"}:
            issues.append(
                f"{change.path}: public candidate must contain a regular file blob, "
                f"got mode/type {entry.mode}/{entry.object_type}"
            )
        elif change.path in GENERATED_PUBLIC_STATUS_PATHS and entry.mode != "100644":
            issues.append(
                f"{change.path}: generated public status file must use mode 100644"
            )
    return issues


def private_source_commit_issues(
    private_repo: Path,
    entries: list[AllowlistEntry],
    *,
    private_base_ref: str = PRIVATE_BASE_REF,
) -> list[str]:
    issues: list[str] = []
    checked: set[str] = set()
    for entry in entries:
        if entry.provenance != "private_blob" or entry.source_commit is None:
            continue
        if entry.source_commit in checked:
            continue
        checked.add(entry.source_commit)
        exists = subprocess.run(
            ["git", "cat-file", "-e", f"{entry.source_commit}^{{commit}}"],
            cwd=private_repo,
            env=_git_environment(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if exists.returncode != 0:
            issues.append(f"private source commit does not exist: {entry.source_commit}")
            continue
        reachable = subprocess.run(
            [
                "git",
                "merge-base",
                "--is-ancestor",
                entry.source_commit,
                private_base_ref,
            ],
            cwd=private_repo,
            env=_git_environment(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if reachable.returncode != 0:
            issues.append(
                f"private source commit is not reachable from canonical "
                f"{private_base_ref}: {entry.source_commit}"
            )
    return issues


def generated_status_freshness_issues(
    candidate_repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Run the trusted status generator against only the committed candidate tree."""

    if not TRUSTED_STATUS_SYNC.is_file():
        return [f"trusted status generator is missing: {TRUSTED_STATUS_SYNC}"]
    candidate_repo = candidate_repo.resolve()
    with tempfile.TemporaryDirectory(prefix="econcslib-public-tree-") as temp_dir:
        tree_checkout = Path(temp_dir) / "candidate"
        checkout = subprocess.run(
            [
                "git",
                "worktree",
                "add",
                "--detach",
                str(tree_checkout),
                candidate_ref,
            ],
            cwd=candidate_repo,
            env=_git_environment(),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if checkout.returncode != 0:
            return [
                "could not materialize a tree-only public status checkout: "
                + checkout.stdout.strip()
            ]
        try:
            environment = _git_environment()
            environment["ECONCSLIB_REPO_ROOT"] = str(tree_checkout.resolve())
            trusted_status_sync = TRUSTED_STATUS_SYNC.resolve()
            isolated_bootstrap = (
                "import runpy, sys; "
                f"sys.path.insert(0, {str(trusted_status_sync.parent)!r}); "
                f"runpy.run_path({str(trusted_status_sync)!r}, run_name='__main__')"
            )
            result = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-c",
                    isolated_bootstrap,
                    "--repo",
                    str(tree_checkout),
                    "--check",
                ],
                cwd=tree_checkout,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                check=False,
            )
        finally:
            subprocess.run(
                ["git", "worktree", "remove", "--force", str(tree_checkout)],
                cwd=candidate_repo,
                env=_git_environment(),
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
    if result.returncode == 0:
        return []
    return [
        "public status surfaces are not reproducible from the candidate inputs "
        "using the trusted private generator: "
        + result.stdout.strip()
    ]


def run_guard(
    repo: Path,
    *,
    allowlist_path: Path,
    preflight: bool = False,
) -> list[str]:
    repo = repo.resolve()
    private_repo = ROOT.resolve()
    allowlist_path = allowlist_path.resolve()
    approval_path = REVIEWER_APPROVAL_PATH.absolute()
    approval_location = approval_path.parent.resolve() / approval_path.name
    issues: list[str] = []

    if _path_is_within(allowlist_path, repo):
        return [
            "public export allowlist must remain outside the candidate "
            f"repository: {allowlist_path}"
        ]
    approval: ReleaseApproval | None = None
    if not preflight:
        if _path_is_within(approval_location, repo) or _path_is_within(
            approval_location, private_repo
        ):
            return [
                "fixed reviewer approval must remain outside both agent-writable "
                f"repositories: {approval_location}"
            ]
        try:
            approval = load_release_approval(approval_path)
        except ValueError as exc:
            return [str(exc)]
    try:
        allowlist_bytes = allowlist_path.read_bytes()
    except OSError as exc:
        return [f"cannot read public export allowlist {allowlist_path}: {exc}"]
    try:
        entries = parse_allowlist(allowlist_bytes, source=str(allowlist_path))
    except ValueError as exc:
        return [str(exc)]

    if not is_git_repository(repo):
        return [f"public release workspace is not a Git repository: {repo}"]
    if not is_git_repository(private_repo):
        return [f"canonical private ROOT is not a Git repository: {private_repo}"]

    issues.extend(
        canonical_remote_issues(
            repo,
            remote=PUBLIC_REMOTE,
            expected=PUBLIC_REMOTE_RE,
            label="public",
        )
    )
    issues.extend(
        canonical_remote_issues(
            private_repo,
            remote=PRIVATE_REMOTE,
            expected=PRIVATE_REMOTE_RE,
            label="private",
        )
    )
    issues.extend(shared_git_storage_issues(repo, private_repo))

    try:
        trusted_tooling_sha256 = _trusted_tooling_sha256()
    except RuntimeError as exc:
        return [*issues, str(exc)]
    if approval is not None:
        if _sha256_bytes(allowlist_bytes) != approval.allowlist_sha256:
            issues.append(
                "public export allowlist bytes do not match the fixed reviewer approval"
            )
        if _guard_sha256() != approval.guard_sha256:
            issues.append(
                "executed release guard does not match the reviewer-approved SHA256"
            )
        if trusted_tooling_sha256 != approval.trusted_tooling_sha256:
            issues.append(
                "executed trusted tooling bundle does not match the reviewer-approved SHA256"
            )

    status = _git(repo, ["status", "--porcelain"])
    if status.strip():
        issues.append("public release workspace is not clean")
    branch = _git(repo, ["branch", "--show-current"]).strip()
    if not branch.startswith(PUBLIC_BRANCH_PREFIX) or branch in {"main", "master"}:
        issues.append(
            f"candidate branch must use fixed prefix {PUBLIC_BRANCH_PREFIX!r} and "
            f"must not be main/master; got {branch!r}"
        )
    candidate_commit = resolved_commit(repo, "HEAD")
    public_base_commit = resolved_commit(repo, PUBLIC_BASE_REF)
    if approval is not None:
        if candidate_commit != approval.candidate_commit:
            issues.append("candidate HEAD does not match the reviewer-approved commit")
        if public_base_commit != approval.public_base_commit:
            issues.append(
                f"fixed {PUBLIC_BASE_REF} does not match the reviewer-approved public base commit"
            )

    private_source_commits = tuple(
        sorted(
            {
                entry.source_commit
                for entry in entries
                if entry.provenance == "private_blob"
                and entry.source_commit is not None
            }
        )
    )
    if approval is not None and private_source_commits != approval.private_source_commits:
        issues.append(
            "allowlist private source commits do not exactly match the fixed reviewer approval"
        )

    try:
        history, history_issues = candidate_history(
            repo, PUBLIC_BASE_REF, "HEAD"
        )
    except RuntimeError as exc:
        return [*issues, str(exc)]
    issues.extend(history_issues)
    issues.extend(
        private_source_commit_issues(
            private_repo, entries, private_base_ref=PRIVATE_BASE_REF
        )
    )
    used_entries: set[AllowlistEntry] = set()
    changed_lean_entrypoints: set[str] = set()
    for candidate_history_commit in history:
        issues.extend(
            candidate_tree_entry_issues(
                repo,
                candidate_history_commit.commit,
                list(candidate_history_commit.changes),
            )
        )
        for change in candidate_history_commit.changes:
            if change.status != "D" and change.path.endswith(".lean"):
                changed_lean_entrypoints.add(change.path)
            entry = matching_allowlist_entry(change.path, entries)
            if entry is None:
                issues.append(
                    f"commit {candidate_history_commit.commit}: changed path is not "
                    f"public-export allowlisted: {change.path}"
                )
            else:
                used_entries.add(entry)
                if (
                    change.path in GENERATED_PUBLIC_STATUS_PATHS
                    and change.status != "D"
                    and entry.provenance != "public_generated"
                ):
                    issues.append(
                        f"commit {candidate_history_commit.commit}: generated status path "
                        f"must use public_generated provenance: {change.path}"
                    )
                if (
                    entry.provenance == "public_generated"
                    and candidate_history_commit.commit != candidate_commit
                ):
                    issues.append(
                        f"public-generated path may change only in the final candidate commit: "
                        f"{change.path} in {candidate_history_commit.commit}"
                    )
        issues.extend(
            source_provenance_issues(
                repo,
                private_repo,
                candidate_history_commit.commit,
                list(candidate_history_commit.changes),
                entries,
                public_base_ref=public_base_commit,
            )
        )
    issues.extend(unused_allowlist_issues(entries, used_entries))
    issues.extend(status_visibility_issues(repo, candidate_commit))
    issues.extend(source_artifact_leakage_issues(repo, candidate_commit))
    issues.extend(forbidden_candidate_path_issues(repo, candidate_commit))
    issues.extend(candidate_public_artifact_policy_issues(repo, candidate_commit))
    issues.extend(generated_status_freshness_issues(repo, candidate_commit))
    for issue in dependency_closure_issues(
        repo,
        candidate="tree",
        treeish=candidate_commit,
        extra_entrypoints=changed_lean_entrypoints,
    ):
        issues.append("Lean dependency closure: " + issue.format())
    if resolved_commit(repo, "HEAD") != candidate_commit or _git(
        repo, ["status", "--porcelain"]
    ).strip():
        issues.append("public release workspace changed while the guard was running")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--allowlist", type=Path, required=True)
    parser.add_argument(
        "--preflight",
        action="store_true",
        help=(
            "run every candidate check except the fixed external reviewer-approval "
            "pins; this result is non-authoritative"
        ),
    )
    args = parser.parse_args()
    try:
        issues = run_guard(
            args.repo,
            allowlist_path=args.allowlist,
            preflight=args.preflight,
        )
    except RuntimeError as exc:
        parser.error(str(exc))
    for issue in issues:
        print("ERROR: " + issue, file=sys.stderr)
    if issues:
        print(f"Public release candidate guard: {len(issues)} error(s)", file=sys.stderr)
        return 1
    if args.preflight:
        print(
            "Public release candidate guard preflight: OK "
            "(non-authoritative; external schema-2 reviewer approval is still required)"
        )
        print(f"Trusted tooling bundle SHA256: {_trusted_tooling_sha256()}")
    else:
        print("Public release candidate guard: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
