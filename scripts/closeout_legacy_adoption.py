#!/usr/bin/env python3
"""One-time operational baselines for successful pre-plan closeouts.

The record is ignored scheduling state, never semantic evidence. It lets the
planner preserve a known-success legacy closeout without rerunning it while
ensuring that a later material plan identity schedules a current closeout.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

try:
    from scripts.closeout_execution_state import atomic_write_json
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from closeout_execution_state import atomic_write_json


LEGACY_ADOPTION_SCHEMA = 1
LEGACY_ADOPTION_FILE = "closeout_legacy_adoption.json"


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    ).hexdigest()


def legacy_adoption_path(
    root: Path, paper: str, *, deep_paper_prose: bool = False
) -> Path:
    filename = (
        LEGACY_ADOPTION_FILE
        if not deep_paper_prose
        else "closeout_legacy_adoption.deep.json"
    )
    return root / "papers" / paper / ".review_traces" / filename


def _lock_path_matches_fd(fd: int, path: Path) -> bool:
    try:
        opened = os.fstat(fd)
        named = os.stat(path, follow_symlinks=False)
    except OSError:
        return False
    return (opened.st_dev, opened.st_ino) == (named.st_dev, named.st_ino)


def known_success_legacy_completion(
    prior_execution: object, *, paper: str, deep_paper_prose: bool
) -> bool:
    """Recognize only an explicit pass with no claimed current-plan schema."""

    if not isinstance(prior_execution, Mapping):
        return False
    result = prior_execution.get("result")
    if (
        prior_execution.get("state") != "complete"
        or prior_execution.get("paper") != paper
        or prior_execution.get("exit_code") != 0
        or not isinstance(result, Mapping)
        or result.get("semantic_closeout_passed") is not True
        or str(result.get("operational_plan_identity_schema") or "")
    ):
        return False
    request = prior_execution.get("request")
    legacy_deep = (
        request.get("deep_paper_prose") if isinstance(request, Mapping) else None
    )
    return not deep_paper_prose or legacy_deep is True


def adopt_or_validate_legacy_completion(
    root: Path,
    *,
    paper: str,
    plan_identity: str,
    deep_paper_prose: bool,
    prior_execution: object,
    rollout_baseline: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Atomically adopt once, or compare the current plan with that baseline."""

    if not known_success_legacy_completion(
        prior_execution, paper=paper, deep_paper_prose=deep_paper_prose
    ):
        return {
            "state": "not_applicable",
            "acceptance_credential": False,
        }
    prior_digest = _digest(prior_execution)
    expected = {
        "schema": LEGACY_ADOPTION_SCHEMA,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "paper": paper,
        "deep_paper_prose": deep_paper_prose,
        "prior_execution_sha256": prior_digest,
        "adopted_plan_identity": plan_identity,
    }
    path = legacy_adoption_path(
        root, paper, deep_paper_prose=deep_paper_prose
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = path.with_suffix(path.suffix + ".lock")
    for _attempt in range(3):
        lock_fd = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX)
            if not _lock_path_matches_fd(lock_fd, lock_path):
                continue
            try:
                recorded = json.loads(path.read_text(encoding="utf-8"))
            except FileNotFoundError:
                baseline = rollout_baseline or {}
                if baseline.get("ready") is not True:
                    baseline_errors = baseline.get("errors")
                    if isinstance(baseline_errors, list):
                        reason = "; ".join(
                            str(error) for error in baseline_errors if error
                        )
                    else:
                        reason = str(baseline.get("error") or "").strip()
                    return {
                        "state": (
                            "material_changed"
                            if baseline.get("state") == "material_changed"
                            else "error"
                        ),
                        "error": reason
                        or "trusted legacy rollout baseline is unavailable",
                        "acceptance_credential": False,
                    }
                if not _lock_path_matches_fd(lock_fd, lock_path):
                    continue
                atomic_write_json(path, expected)
                if not _lock_path_matches_fd(lock_fd, lock_path):
                    continue
                recorded = expected
            except (OSError, json.JSONDecodeError) as exc:
                return {
                    "state": "error",
                    "error": f"legacy adoption record is unreadable: {exc}",
                    "acceptance_credential": False,
                }
            if not isinstance(recorded, Mapping) or set(recorded) != set(expected):
                return {
                    "state": "error",
                    "error": "legacy adoption record is malformed",
                    "acceptance_credential": False,
                }
            if (
                recorded.get("schema") != LEGACY_ADOPTION_SCHEMA
                or recorded.get("acceptance_credential") is not False
                or recorded.get("operational_scheduling_only") is not True
                or recorded.get("paper") != paper
                or recorded.get("deep_paper_prose") is not deep_paper_prose
                or recorded.get("prior_execution_sha256") != prior_digest
            ):
                return {
                    "state": "error",
                    "error": (
                        "legacy adoption record does not match the terminal legacy run"
                    ),
                    "acceptance_credential": False,
                }
            adopted = str(recorded.get("adopted_plan_identity") or "")
            return {
                "state": (
                    "current" if adopted == plan_identity else "material_changed"
                ),
                "adopted_plan_identity": adopted,
                "current_plan_identity": plan_identity,
                "path": str(path.relative_to(root)),
                "acceptance_credential": False,
            }
        finally:
            os.close(lock_fd)
    return {
        "state": "error",
        "error": "legacy adoption lock pathname changed during acquisition",
        "acceptance_credential": False,
    }
