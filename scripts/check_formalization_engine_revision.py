#!/usr/bin/env python3
"""Guard semantic-engine compatibility without making code hashes paper evidence.

The guard is commit, CI, and local closeout infrastructure. It hashes production
audit implementation sources from an exact Git candidate view, then requires that
pair of engine and canonical review-protocol identities to be registered in an
append-only revision chain.  A compatibility-preserving implementation change
may keep the review protocol unchanged, but must be explicitly attested.  A
semantic change is accepted only when the structured review protocol changes.

The engine digest is deliberately *not* a paper closeout or semantic-evidence
identity.  Its only purpose is to prevent an implementation edit from being
silently classified after the fact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence

try:
    from scripts.source_record_raw_producer_compatibility import (
        RAW_PRODUCER_COMPATIBILITY_FIELD,
        raw_producer_compatibility_grant_error,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script import support.
    from source_record_raw_producer_compatibility import (
        RAW_PRODUCER_COMPATIBILITY_FIELD,
        raw_producer_compatibility_grant_error,
    )


LEDGER_PATH = "config/formalization_engine_revisions.json"
PROTOCOL_PATH = "config/formalization_audit_protocol.json"
LEDGER_SCHEMA = 1
ENGINE_DIGEST_SCHEMA = 1
REVIEW_PROTOCOL_DIGEST_SCHEMA = 1
BOUNDARY_ID = "tracked-formalization-engine-production-sources-v1"
ENGINE_ROOTS = ("scripts", "skills/econcs-formalizer/scripts")
ENGINE_SUFFIXES = frozenset({".py", ".lean", ".sh"})
EXCLUDED_PREFIXES = ("scripts/tests/",)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
RELATION_BOOTSTRAP = "bootstrap"
RELATION_COMPATIBLE = "review_compatible"
RELATION_SEMANTIC = "review_semantics_changed"
RELATIONS = frozenset({RELATION_BOOTSTRAP, RELATION_COMPATIBLE, RELATION_SEMANTIC})


class EngineRevisionError(ValueError):
    """The candidate tree or revision chain is unavailable or inconsistent."""


@dataclass(frozen=True)
class CandidateBlob:
    """One exact candidate-tree blob selected by repository-relative path."""

    path: str
    mode: str
    oid: str
    content: bytes


@dataclass(frozen=True)
class RuntimeEngineRegistration:
    """One committed engine revision accepted for local closeout execution."""

    engine_tree_sha256: str
    review_semantic_class_sha256: str
    revision_sequence: int
    relation_to_previous: str
    engine_file_count: int


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _normalized_repository_path(value: str) -> str:
    path = PurePosixPath(value)
    if (
        not value
        or path.is_absolute()
        or "\\" in value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise EngineRevisionError(f"invalid repository-relative path: {value!r}")
    return path.as_posix()


def is_engine_source_path(value: str) -> bool:
    """Select production implementation by location/type, never function name."""

    try:
        path = _normalized_repository_path(value)
    except EngineRevisionError:
        return False
    if any(path.startswith(prefix) for prefix in EXCLUDED_PREFIXES):
        return False
    if "/__pycache__/" in f"/{path}/" or path.endswith(".pyc"):
        return False
    in_root = any(path == root or path.startswith(f"{root}/") for root in ENGINE_ROOTS)
    return in_root and PurePosixPath(path).suffix in ENGINE_SUFFIXES


def engine_tree_digest(blobs: Iterable[CandidateBlob]) -> tuple[str, int]:
    """Return a path-, mode-, and content-sensitive engine identity."""

    records: list[dict[str, object]] = []
    seen: set[str] = set()
    for blob in sorted(blobs, key=lambda item: item.path):
        path = _normalized_repository_path(blob.path)
        if not is_engine_source_path(path):
            continue
        if path in seen:
            raise EngineRevisionError(f"duplicate engine source path: {path}")
        seen.add(path)
        records.append(
            {
                "path": path,
                "mode": str(blob.mode),
                "sha256": hashlib.sha256(blob.content).hexdigest(),
                "size": len(blob.content),
            }
        )
    if not records:
        raise EngineRevisionError("candidate contains no formalization engine sources")
    material = {
        "schema": ENGINE_DIGEST_SCHEMA,
        "boundary": BOUNDARY_ID,
        "files": records,
    }
    return _canonical_digest(material), len(records)


def _without_rule(value: object) -> object:
    if isinstance(value, Mapping):
        return {
            str(key): _without_rule(child)
            for key, child in value.items()
            if str(key) != "rule"
        }
    if isinstance(value, list):
        return [_without_rule(child) for child in value]
    return value


def formalization_review_protocol_digest(payload: object) -> str:
    """Reproduce the canonical structured review-protocol projection.

    This standalone projection lets ``--index`` inspect exact staged protocol
    bytes without importing a possibly different unstaged module.  A parity
    test compares it with ``scripts.formalization_protocol`` so either
    projection must be updated deliberately if that authority changes.
    """

    if not isinstance(payload, Mapping) or payload.get("schema") != 1:
        raise EngineRevisionError("formalization audit protocol schema is invalid")
    for section in ("audit_versions", "coverage", "reuse", "classification"):
        if not isinstance(payload.get(section), Mapping):
            raise EngineRevisionError(
                f"formalization audit protocol {section} must be an object"
            )

    versions: dict[str, object] = {}
    for lane, raw_record in payload["audit_versions"].items():
        if not isinstance(raw_record, Mapping):
            raise EngineRevisionError(
                f"formalization audit protocol lane {lane!r} must be an object"
            )
        record = {
            str(key): value
            for key, value in raw_record.items()
            if str(key)
            not in {
                "meaning",
                "transition",
                "legacy_v10_transition_baseline",
                "required_for",
            }
        }
        if str(lane) == "theorem_realization":
            # Match the authoritative protocol's stable marker for the v11
            # lane. Closeout scheduling does not alter a v10 judgment.
            record["required_for"] = [
                "new_paper_closeout",
                "materially_reissued_closeout",
            ]
        versions[str(lane)] = record

    reuse = {
        str(key): value for key, value in payload["reuse"].items() if str(key) != "rule"
    }
    classification: dict[str, object] = {}
    for category, raw_record in payload["classification"].items():
        if not isinstance(raw_record, Mapping):
            raise EngineRevisionError(
                "formalization audit protocol classification "
                f"{category!r} must be an object"
            )
        classification[str(category)] = {
            str(key): value for key, value in raw_record.items() if str(key) != "rule"
        }
    projection = {
        "protocol_schema": payload["schema"],
        "audit_versions": versions,
        "coverage": _without_rule(payload["coverage"]),
        "reuse": reuse,
        "classification": classification,
    }
    return _canonical_digest(
        {"schema": REVIEW_PROTOCOL_DIGEST_SCHEMA, "protocol": projection}
    )


class GitCandidateView:
    """Read blobs from either the exact Git index or one exact Git tree."""

    def __init__(self, root: Path, *, tree: str | None) -> None:
        self.root = root.resolve()
        self.tree = tree
        self._blob_cache: dict[str, bytes] = {}
        if tree is not None:
            result = self._run_git("rev-parse", "--verify", f"{tree}^{{tree}}")
            self.tree = result.stdout.decode("ascii").strip()

    def _run_git(self, *args: str) -> subprocess.CompletedProcess[bytes]:
        result = subprocess.run(
            ["git", *args],
            cwd=self.root,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode != 0:
            message = result.stderr.decode("utf-8", errors="replace").strip()
            raise EngineRevisionError(
                f"git {' '.join(args)} failed: {message or result.returncode}"
            )
        return result

    @staticmethod
    def _decode_path(raw: bytes) -> str:
        try:
            return raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise EngineRevisionError(
                "formalization engine source path is not valid UTF-8"
            ) from exc

    def _entries(self, pathspecs: Sequence[str]) -> dict[str, tuple[str, str]]:
        if self.tree is None:
            result = self._run_git("ls-files", "-s", "-z", "--", *pathspecs)
            entries: dict[str, tuple[str, str]] = {}
            for raw_record in result.stdout.split(b"\0"):
                if not raw_record:
                    continue
                try:
                    raw_metadata, raw_path = raw_record.split(b"\t", 1)
                    raw_mode, raw_oid, raw_stage = raw_metadata.split(b" ", 2)
                except ValueError as exc:
                    raise EngineRevisionError("malformed git index entry") from exc
                path = self._decode_path(raw_path)
                stage = raw_stage.decode("ascii")
                if stage != "0":
                    raise EngineRevisionError(
                        f"candidate index has an unresolved stage for {path}"
                    )
                if path in entries:
                    raise EngineRevisionError(
                        f"candidate index contains duplicate path {path}"
                    )
                entries[path] = (
                    raw_mode.decode("ascii"),
                    raw_oid.decode("ascii"),
                )
            return entries

        result = self._run_git("ls-tree", "-r", "-z", str(self.tree), "--", *pathspecs)
        entries = {}
        for raw_record in result.stdout.split(b"\0"):
            if not raw_record:
                continue
            try:
                raw_metadata, raw_path = raw_record.split(b"\t", 1)
                raw_mode, raw_type, raw_oid = raw_metadata.split(b" ", 2)
            except ValueError as exc:
                raise EngineRevisionError("malformed git tree entry") from exc
            if raw_type != b"blob":
                continue
            path = self._decode_path(raw_path)
            if path in entries:
                raise EngineRevisionError(
                    f"candidate tree contains duplicate path {path}"
                )
            entries[path] = (
                raw_mode.decode("ascii"),
                raw_oid.decode("ascii"),
            )
        return entries

    def _blob(self, oid: str) -> bytes:
        cached = self._blob_cache.get(oid)
        if cached is not None:
            return cached
        content = self._run_git("cat-file", "blob", oid).stdout
        self._blob_cache[oid] = content
        return content

    def _blobs(self, oids: Iterable[str]) -> None:
        """Populate exact blobs with one Git process rather than one per file."""

        missing = tuple(dict.fromkeys(oid for oid in oids if oid not in self._blob_cache))
        if not missing:
            return
        result = subprocess.run(
            ["git", "cat-file", "--batch"],
            cwd=self.root,
            check=False,
            input=b"".join(f"{oid}\n".encode("ascii") for oid in missing),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode != 0:
            message = result.stderr.decode("utf-8", errors="replace").strip()
            raise EngineRevisionError(
                f"git cat-file --batch failed: {message or result.returncode}"
            )
        output = result.stdout
        offset = 0
        for expected_oid in missing:
            header_end = output.find(b"\n", offset)
            if header_end < 0:
                raise EngineRevisionError("git cat-file --batch returned a short header")
            fields = output[offset:header_end].split(b" ")
            if len(fields) != 3:
                raise EngineRevisionError("git cat-file --batch returned a malformed header")
            raw_oid, raw_type, raw_size = fields
            try:
                actual_oid = raw_oid.decode("ascii")
                size = int(raw_size)
            except (UnicodeDecodeError, ValueError) as exc:
                raise EngineRevisionError(
                    "git cat-file --batch returned malformed blob metadata"
                ) from exc
            if actual_oid != expected_oid or raw_type != b"blob" or size < 0:
                raise EngineRevisionError(
                    f"git object {expected_oid} is not the expected blob"
                )
            content_start = header_end + 1
            content_end = content_start + size
            if content_end >= len(output) or output[content_end : content_end + 1] != b"\n":
                raise EngineRevisionError("git cat-file --batch returned a short blob")
            self._blob_cache[expected_oid] = output[content_start:content_end]
            offset = content_end + 1
        if offset != len(output):
            raise EngineRevisionError("git cat-file --batch returned trailing bytes")

    def read_bytes(self, path: str) -> bytes | None:
        normalized = _normalized_repository_path(path)
        entry = self._entries((normalized,)).get(normalized)
        return None if entry is None else self._blob(entry[1])

    def engine_blobs(self) -> tuple[CandidateBlob, ...]:
        entries = self._entries(ENGINE_ROOTS)
        selected = {
            path: (mode, oid)
            for path, (mode, oid) in entries.items()
            if is_engine_source_path(path)
        }
        self._blobs(oid for _mode, oid in selected.values())
        return tuple(
            CandidateBlob(
                path=path,
                mode=mode,
                oid=oid,
                content=self._blob(oid),
            )
            for path, (mode, oid) in sorted(selected.items())
        )


def _json_from_candidate(view: GitCandidateView, path: str) -> object:
    raw = view.read_bytes(path)
    if raw is None:
        raise EngineRevisionError(f"candidate is missing {path}")
    try:
        return json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EngineRevisionError(f"candidate {path} is not valid JSON: {exc}") from exc


def _validated_sha256(value: object, field: str) -> str:
    digest = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise EngineRevisionError(f"{field} must be a lowercase SHA-256")
    return digest


def _validated_text(value: object, field: str, *, minimum: int = 1) -> str:
    if not isinstance(value, str) or len(value.strip()) < minimum:
        raise EngineRevisionError(
            f"{field} must contain at least {minimum} non-whitespace characters"
        )
    return value.strip()


def _validated_verification(value: object, field: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise EngineRevisionError(f"{field} must be a nonempty list")
    items = [
        _validated_text(item, f"{field}[{index}]") for index, item in enumerate(value)
    ]
    if len(items) != len(set(items)):
        raise EngineRevisionError(f"{field} must not contain duplicates")
    return items


def validate_revision_ledger(
    payload: object,
    *,
    current_engine_sha256: str,
    current_protocol_sha256: str,
) -> dict[str, Any]:
    """Validate the whole chain and require its tip to match the candidate."""

    if not isinstance(payload, Mapping) or set(payload) != {
        "schema",
        "boundary",
        "revisions",
    }:
        raise EngineRevisionError("formalization engine revision file is malformed")
    if payload.get("schema") != LEDGER_SCHEMA:
        raise EngineRevisionError(
            f"formalization engine revision schema must be {LEDGER_SCHEMA}"
        )
    if payload.get("boundary") != BOUNDARY_ID:
        raise EngineRevisionError(
            f"formalization engine boundary must be {BOUNDARY_ID}"
        )
    raw_revisions = payload.get("revisions")
    if not isinstance(raw_revisions, list) or not raw_revisions:
        raise EngineRevisionError(
            "formalization engine has no registered bootstrap revision"
        )

    revisions: list[dict[str, Any]] = []
    prior: dict[str, Any] | None = None
    for offset, raw_revision in enumerate(raw_revisions):
        sequence = offset + 1
        if not isinstance(raw_revision, Mapping):
            raise EngineRevisionError(f"revision {sequence} must be an object")
        relation = str(raw_revision.get("relation_to_previous") or "")
        common_fields = {
            "sequence",
            "engine_tree_sha256",
            "formalization_review_protocol_sha256",
            "relation_to_previous",
            "rationale",
            "verification",
        }
        expected_fields = (
            common_fields
            if relation == RELATION_BOOTSTRAP
            else common_fields
            | {
                "previous_engine_tree_sha256",
                "previous_formalization_review_protocol_sha256",
            }
        )
        raw_producer_compatibility = raw_revision.get(
            RAW_PRODUCER_COMPATIBILITY_FIELD
        )
        if raw_producer_compatibility is not None:
            expected_fields = expected_fields | {
                RAW_PRODUCER_COMPATIBILITY_FIELD
            }
        if set(raw_revision) != expected_fields:
            raise EngineRevisionError(f"revision {sequence} fields are malformed")
        if raw_revision.get("sequence") != sequence:
            raise EngineRevisionError(f"revision {sequence} sequence is malformed")
        if relation not in RELATIONS:
            raise EngineRevisionError(
                f"revision {sequence} has unknown compatibility relation"
            )
        if raw_producer_compatibility is not None:
            if relation != RELATION_COMPATIBLE:
                raise EngineRevisionError(
                    f"revision {sequence} raw-producer compatibility grant "
                    "requires a review-compatible transition"
                )
            grant_error = raw_producer_compatibility_grant_error(
                raw_producer_compatibility
            )
            if grant_error:
                raise EngineRevisionError(
                    f"revision {sequence} {grant_error}"
                )
        engine = _validated_sha256(
            raw_revision.get("engine_tree_sha256"),
            f"revision {sequence} engine_tree_sha256",
        )
        protocol = _validated_sha256(
            raw_revision.get("formalization_review_protocol_sha256"),
            f"revision {sequence} formalization_review_protocol_sha256",
        )
        _validated_text(
            raw_revision.get("rationale"),
            f"revision {sequence} rationale",
            minimum=20,
        )
        _validated_verification(
            raw_revision.get("verification"), f"revision {sequence} verification"
        )

        if sequence == 1:
            if relation != RELATION_BOOTSTRAP:
                raise EngineRevisionError("the first revision must be bootstrap")
        else:
            if relation == RELATION_BOOTSTRAP or prior is None:
                raise EngineRevisionError(
                    f"revision {sequence} cannot introduce another bootstrap"
                )
            previous_engine = _validated_sha256(
                raw_revision.get("previous_engine_tree_sha256"),
                f"revision {sequence} previous_engine_tree_sha256",
            )
            previous_protocol = _validated_sha256(
                raw_revision.get("previous_formalization_review_protocol_sha256"),
                f"revision {sequence} previous_formalization_review_protocol_sha256",
            )
            if (
                previous_engine != prior["engine_tree_sha256"]
                or previous_protocol != prior["formalization_review_protocol_sha256"]
            ):
                raise EngineRevisionError(
                    f"revision {sequence} does not link to the prior revision"
                )
            engine_changed = engine != previous_engine
            protocol_changed = protocol != previous_protocol
            if relation == RELATION_COMPATIBLE and (
                not engine_changed or protocol_changed
            ):
                raise EngineRevisionError(
                    f"revision {sequence} compatible relation requires an engine "
                    "change and an unchanged review protocol"
                )
            if relation == RELATION_SEMANTIC and not protocol_changed:
                raise EngineRevisionError(
                    f"revision {sequence} semantic relation requires a changed "
                    "canonical review protocol"
                )

        revision = dict(raw_revision)
        revision["engine_tree_sha256"] = engine
        revision["formalization_review_protocol_sha256"] = protocol
        revisions.append(revision)
        prior = revision

    current_engine = _validated_sha256(
        current_engine_sha256, "current engine_tree_sha256"
    )
    current_protocol = _validated_sha256(
        current_protocol_sha256,
        "current formalization_review_protocol_sha256",
    )
    assert prior is not None
    if prior["engine_tree_sha256"] != current_engine:
        raise EngineRevisionError(
            "formalization engine implementation changed without a registered "
            "compatibility transition"
        )
    if prior["formalization_review_protocol_sha256"] != current_protocol:
        raise EngineRevisionError(
            "canonical formalization review protocol changed without a registered "
            "semantic transition"
        )
    return {
        "schema": LEDGER_SCHEMA,
        "boundary": BOUNDARY_ID,
        "revisions": revisions,
    }


def validate_append_only_history(current: object, base: object | None) -> None:
    """Require an existing trusted chain to remain an exact prefix.

    Internal hash links cannot prove that somebody did not replace the whole
    file with a new bootstrap.  Index checks therefore compare against HEAD,
    and CI should pass the candidate's parent as ``--base-tree``.
    """

    if base is None:
        return
    if not isinstance(base, Mapping) or not isinstance(current, Mapping):
        raise EngineRevisionError("formalization engine revision history is malformed")
    if base.get("schema") != current.get("schema") or base.get(
        "boundary"
    ) != current.get("boundary"):
        raise EngineRevisionError(
            "formalization engine revision schema or boundary changed across history"
        )
    base_revisions = base.get("revisions")
    current_revisions = current.get("revisions")
    if not isinstance(base_revisions, list) or not isinstance(current_revisions, list):
        raise EngineRevisionError("formalization engine revision history is malformed")
    if not base_revisions:
        # The sole rollout placeholder is not an acceptance credential.  It may
        # be replaced by the first real bootstrap, but no accepted record may
        # ever be removed afterward.
        return
    if current_revisions[: len(base_revisions)] != base_revisions:
        raise EngineRevisionError(
            "formalization engine revision history was rewritten instead of appended"
        )


def bootstrap_payload(
    *, engine_sha256: str, protocol_sha256: str, file_count: int
) -> dict[str, Any]:
    return {
        "schema": LEDGER_SCHEMA,
        "boundary": BOUNDARY_ID,
        "revisions": [
            {
                "sequence": 1,
                "engine_tree_sha256": engine_sha256,
                "formalization_review_protocol_sha256": protocol_sha256,
                "relation_to_previous": RELATION_BOOTSTRAP,
                "rationale": (
                    "Prospective engine-revision guard adoption; existing paper "
                    "evidence is not rewritten or reopened."
                ),
                "verification": [
                    f"exact candidate production-source inventory ({file_count} files)",
                    "canonical structured review-protocol projection parity",
                ],
            }
        ],
    }


def updated_payload(
    payload: object,
    *,
    engine_sha256: str,
    protocol_sha256: str,
    rationale: str,
    verification: Sequence[str],
) -> dict[str, Any]:
    """Return a candidate update; validation still occurs on the next check."""

    if not isinstance(payload, Mapping):
        raise EngineRevisionError("formalization engine revision file is malformed")
    revisions = payload.get("revisions")
    if not isinstance(revisions, list) or not revisions:
        raise EngineRevisionError("bootstrap the formalization engine revision first")
    prior = revisions[-1]
    if not isinstance(prior, Mapping):
        raise EngineRevisionError("formalization engine revision tip is malformed")
    previous_engine = _validated_sha256(
        prior.get("engine_tree_sha256"), "previous engine_tree_sha256"
    )
    previous_protocol = _validated_sha256(
        prior.get("formalization_review_protocol_sha256"),
        "previous formalization_review_protocol_sha256",
    )
    engine = _validated_sha256(engine_sha256, "current engine_tree_sha256")
    protocol = _validated_sha256(
        protocol_sha256, "current formalization_review_protocol_sha256"
    )
    if engine == previous_engine and protocol == previous_protocol:
        raise EngineRevisionError("candidate already matches the registered revision")
    relation = (
        RELATION_SEMANTIC if protocol != previous_protocol else RELATION_COMPATIBLE
    )
    if relation == RELATION_COMPATIBLE and engine == previous_engine:
        raise EngineRevisionError(
            "a compatibility transition must change the engine implementation"
        )
    new_revision = {
        "sequence": len(revisions) + 1,
        "engine_tree_sha256": engine,
        "formalization_review_protocol_sha256": protocol,
        "relation_to_previous": relation,
        "previous_engine_tree_sha256": previous_engine,
        "previous_formalization_review_protocol_sha256": previous_protocol,
        "rationale": _validated_text(rationale, "rationale", minimum=20),
        "verification": _validated_verification(list(verification), "verification"),
    }
    result = {
        "schema": payload.get("schema"),
        "boundary": payload.get("boundary"),
        "revisions": [*revisions, new_revision],
    }
    validate_revision_ledger(
        result,
        current_engine_sha256=engine,
        current_protocol_sha256=protocol,
    )
    return result


def _repository_root(start: Path | None = None) -> Path:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=start,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as exc:
        raise EngineRevisionError(f"could not inspect repository: {exc}") from exc
    if result.returncode != 0:
        raise EngineRevisionError("not inside a Git repository")
    return Path(os.fsdecode(result.stdout).strip()).resolve()


def _candidate_material(
    view: GitCandidateView,
) -> tuple[str, str, int]:
    engine, file_count = engine_tree_digest(view.engine_blobs())
    protocol = formalization_review_protocol_digest(
        _json_from_candidate(view, PROTOCOL_PATH)
    )
    return engine, protocol, file_count


def _nul_separated_paths(raw: bytes) -> set[str]:
    paths: set[str] = set()
    for item in raw.split(b"\0"):
        if not item:
            continue
        try:
            paths.add(_normalized_repository_path(item.decode("utf-8")))
        except UnicodeDecodeError as exc:
            raise EngineRevisionError(
                "formalization engine working-tree path is not valid UTF-8"
            ) from exc
    return paths


def _git_paths(view: GitCandidateView, *args: str) -> set[str]:
    return _nul_separated_paths(view._run_git(*args).stdout)


def _nonstandard_index_paths(
    view: GitCandidateView, pathspecs: Sequence[str]
) -> set[str]:
    """Reject index flags that can hide working-tree differences from Git diff."""

    result = view._run_git("ls-files", "-v", "-z", "--", *pathspecs)
    paths: set[str] = set()
    for item in result.stdout.split(b"\0"):
        if not item:
            continue
        if len(item) < 3 or item[1:2] != b" ":
            raise EngineRevisionError("git ls-files -v returned a malformed record")
        try:
            path = _normalized_repository_path(item[2:].decode("utf-8"))
        except UnicodeDecodeError as exc:
            raise EngineRevisionError(
                "formalization engine index path is not valid UTF-8"
            ) from exc
        if item[:1] != b"H":
            paths.add(path)
    return paths


def _filesystem_json(root: Path, path: str) -> object:
    candidate = root / path
    try:
        if not stat.S_ISREG(candidate.lstat().st_mode):
            raise EngineRevisionError(
                f"working-tree {path} must remain a regular file"
            )
        return json.loads(candidate.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise EngineRevisionError(f"working tree is missing {path}") from exc
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EngineRevisionError(
            f"working-tree {path} is not valid JSON: {exc}"
        ) from exc


def _runtime_dirty_material_paths(
    root: Path,
    *,
    head_view: GitCandidateView,
) -> tuple[str, ...]:
    """Return runtime-relevant paths whose index/worktree is not clean HEAD.

    Production code and the revision ledger require exact clean-HEAD bytes.
    The review protocol is compared through its canonical structured
    projection, so prose-only edits remain operationally neutral.
    """

    pathspecs = (*ENGINE_ROOTS, PROTOCOL_PATH, LEDGER_PATH)
    assert head_view.tree is not None
    staged = _git_paths(
        head_view,
        "diff",
        "--cached",
        "--name-only",
        "-z",
        "--no-renames",
        str(head_view.tree),
        "--",
        *pathspecs,
    )
    unstaged = _git_paths(
        head_view,
        "-c",
        "core.fileMode=true",
        "diff",
        "--name-only",
        "-z",
        "--no-renames",
        "--",
        *pathspecs,
    )
    untracked = _git_paths(
        head_view,
        "ls-files",
        "--others",
        "--exclude-standard",
        "-z",
        "--",
        *pathspecs,
    ) | _git_paths(
        head_view,
        "ls-files",
        "--others",
        "--ignored",
        "--exclude-standard",
        "-z",
        "--",
        *pathspecs,
    )
    changed = staged | unstaged | untracked
    changed |= _nonstandard_index_paths(head_view, pathspecs)
    blocking = {
        path
        for path in changed
        if path == LEDGER_PATH or is_engine_source_path(path)
    }

    if PROTOCOL_PATH in changed:
        head_protocol = formalization_review_protocol_digest(
            _json_from_candidate(head_view, PROTOCOL_PATH)
        )
        if PROTOCOL_PATH in staged:
            index_view = GitCandidateView(root, tree=None)
            index_protocol = formalization_review_protocol_digest(
                _json_from_candidate(index_view, PROTOCOL_PATH)
            )
            if index_protocol != head_protocol:
                blocking.add(PROTOCOL_PATH)
        if PROTOCOL_PATH in unstaged or PROTOCOL_PATH in untracked:
            working_protocol = formalization_review_protocol_digest(
                _filesystem_json(root, PROTOCOL_PATH)
            )
            if working_protocol != head_protocol:
                blocking.add(PROTOCOL_PATH)
    return tuple(sorted(blocking))


def validate_runtime_engine_registration(root: Path) -> RuntimeEngineRegistration:
    """Require local closeout code to be a registered, clean HEAD revision.

    This gate is operational and deliberately absent from paper evidence and
    plan identities.  Exact lane-specific producer pins remain independently
    authoritative even when the repository engine transition is compatible.
    """

    root = root.resolve()
    head_view = GitCandidateView(root, tree="HEAD")
    dirty = _runtime_dirty_material_paths(root, head_view=head_view)
    if dirty:
        rendered = ", ".join(dirty[:8])
        if len(dirty) > 8:
            rendered += f", ... ({len(dirty) - 8} more)"
        raise EngineRevisionError(
            "formalization engine runtime material differs from clean HEAD: "
            f"{rendered}; commit an append-only registered transition before closeout"
        )

    engine, protocol, file_count = _candidate_material(head_view)
    validated = validate_revision_ledger(
        _json_from_candidate(head_view, LEDGER_PATH),
        current_engine_sha256=engine,
        current_protocol_sha256=protocol,
    )
    revisions = validated["revisions"]
    tip = revisions[-1]
    return RuntimeEngineRegistration(
        engine_tree_sha256=engine,
        review_semantic_class_sha256=protocol,
        revision_sequence=int(tip["sequence"]),
        relation_to_previous=str(tip["relation_to_previous"]),
        engine_file_count=file_count,
    )


def validated_runtime_raw_producer_compatibility_ledger(root: Path) -> object:
    """Return the immutable registered ledger for a provenance mismatch.

    This is deliberately separate from normal exact receipt reuse. A caller
    that wants to bridge differing raw-producer code identities must first
    establish clean-HEAD runtime registration, then read the ledger from that
    immutable HEAD tree rather than from a mutable working file.
    """

    root = root.resolve()
    validate_runtime_engine_registration(root)
    head_view = GitCandidateView(root, tree="HEAD")
    return _json_from_candidate(head_view, LEDGER_PATH)


def runtime_engine_registration_error(root: Path) -> str:
    """Return a user-facing runtime registration error, or the empty string."""

    try:
        validate_runtime_engine_registration(root)
    except EngineRevisionError as exc:
        return str(exc)
    return ""


def _optional_candidate_json(view: GitCandidateView | None, path: str) -> object | None:
    if view is None:
        return None
    raw = view.read_bytes(path)
    if raw is None:
        return None
    try:
        return json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EngineRevisionError(f"base {path} is not valid JSON: {exc}") from exc


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument(
        "--index",
        action="store_true",
        help="read exact stage-0 blobs from the Git index",
    )
    source.add_argument(
        "--tree",
        metavar="TREE",
        help="read exact blobs from a Git tree (use HEAD in CI)",
    )
    parser.add_argument(
        "--repo",
        type=Path,
        help="repository root to inspect (used by trusted cross-checkout CI)",
    )
    parser.add_argument(
        "--base-tree",
        metavar="TREE",
        help=(
            "require this tree's registered revision history to remain an exact "
            "prefix (CI should pass the candidate parent)"
        ),
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument(
        "--show-current",
        action="store_true",
        help="print the current engine/protocol identities without accepting them",
    )
    output.add_argument(
        "--print-bootstrap",
        action="store_true",
        help="print a prospective bootstrap file without writing it",
    )
    output.add_argument(
        "--print-update",
        action="store_true",
        help="print a validated next revision file without writing it",
    )
    parser.add_argument(
        "--rationale",
        default="",
        help="review rationale for --print-update",
    )
    parser.add_argument(
        "--verification",
        action="append",
        default=[],
        help="regression evidence for --print-update; repeat as needed",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        requested_root = args.repo.expanduser().resolve() if args.repo else None
        root = _repository_root(requested_root)
        if requested_root is not None and root != requested_root:
            raise EngineRevisionError(
                f"--repo must name the repository root ({root}, not {requested_root})"
            )
        view = GitCandidateView(root, tree=None if args.index else args.tree)
        base_view = (
            GitCandidateView(root, tree=args.base_tree)
            if args.base_tree
            else GitCandidateView(root, tree="HEAD")
            if args.index
            else None
        )
        base_ledger = _optional_candidate_json(base_view, LEDGER_PATH)
        engine, protocol, file_count = _candidate_material(view)
        if args.show_current:
            print(
                json.dumps(
                    {
                        "boundary": BOUNDARY_ID,
                        "engine_file_count": file_count,
                        "engine_tree_sha256": engine,
                        "formalization_review_protocol_sha256": protocol,
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        if args.print_bootstrap:
            if (
                isinstance(base_ledger, Mapping)
                and isinstance(base_ledger.get("revisions"), list)
                and base_ledger["revisions"]
            ):
                raise EngineRevisionError(
                    "a trusted bootstrap already exists; print an update instead"
                )
            print(
                json.dumps(
                    bootstrap_payload(
                        engine_sha256=engine,
                        protocol_sha256=protocol,
                        file_count=file_count,
                    ),
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0

        ledger = _json_from_candidate(view, LEDGER_PATH)
        validate_append_only_history(ledger, base_ledger)
        if args.print_update:
            ledger = updated_payload(
                ledger,
                engine_sha256=engine,
                protocol_sha256=protocol,
                rationale=args.rationale,
                verification=args.verification,
            )
            print(json.dumps(ledger, indent=2, sort_keys=True))
            return 0
        validate_revision_ledger(
            ledger,
            current_engine_sha256=engine,
            current_protocol_sha256=protocol,
        )
    except EngineRevisionError as exc:
        print(f"ERROR {exc}", file=sys.stderr)
        return 1
    print(
        "OK formalization engine revision is registered "
        f"({file_count} production sources)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
