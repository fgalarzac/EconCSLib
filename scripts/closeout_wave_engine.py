#!/usr/bin/env python3
"""Operational engine-wave admission for closeout raw-receipt reissues.

Raw source-record scans are expensive and serialize Lean work for the whole
repository.  A closeout wave freezes the registered formalization engine for a
batch of those scans.  The snapshot here is deliberately operational: it is
ignored, does not enter a paper fingerprint, and cannot grant closeout
acceptance.  Its sole job is to stop a new raw scan from quietly crossing a
registered engine transition that would make its predecessor/reuse decision
needlessly obsolete.
"""

from __future__ import annotations

from datetime import datetime, timezone
import fcntl
import json
from pathlib import Path
from typing import Mapping
from uuid import uuid4

try:
    from scripts.check_formalization_engine_revision import (
        EngineRevisionError,
        validate_runtime_engine_registration,
    )
    from scripts.closeout_execution_state import atomic_write_json
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from check_formalization_engine_revision import (
        EngineRevisionError,
        validate_runtime_engine_registration,
    )
    from closeout_execution_state import atomic_write_json


CLOSEOUT_WAVE_ENGINE_SNAPSHOT_SCHEMA = 1
CLOSEOUT_WAVE_ENGINE_SNAPSHOT_RELATIVE_PATH = (
    Path(".lake") / "closeout-wave-engine-snapshot.json"
)
CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH = (
    Path(".lake") / "closeout-raw-reissue-transition.lock"
)
CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA = 1
RAW_REISSUE_OPERATION_TRACE_SCHEMA = 1
RAW_REISSUE_TRACE_DIRECTORY = "source_record_raw_reissues"
RAW_REISSUE_OPERATION_TRACE_FILENAME = "raw_reissue_operation.json"
RAW_REISSUE_OPERATION_TERMINAL_STATES = frozenset({"completed", "failed", "stopped"})
_ENGINE_PROJECTION_FIELDS = (
    "engine_tree_sha256",
    "review_semantic_class_sha256",
    "revision_sequence",
    "relation_to_previous",
    "engine_file_count",
)


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _valid_sha256(value: object) -> bool:
    text = str(value or "").strip().lower()
    return len(text) == 64 and all(character in "0123456789abcdef" for character in text)


def normalized_engine_projection(value: object) -> tuple[dict[str, object] | None, str]:
    """Validate the exact registered-engine fields used by a closeout wave."""

    if not isinstance(value, Mapping):
        return None, "engine projection is not an object"
    projection = {field: value.get(field) for field in _ENGINE_PROJECTION_FIELDS}
    if not _valid_sha256(projection["engine_tree_sha256"]):
        return None, "engine projection has an invalid engine_tree_sha256"
    if not _valid_sha256(projection["review_semantic_class_sha256"]):
        return None, "engine projection has an invalid review_semantic_class_sha256"
    if not isinstance(projection["revision_sequence"], int) or projection[
        "revision_sequence"
    ] < 1:
        return None, "engine projection has an invalid revision_sequence"
    if not isinstance(projection["relation_to_previous"], str) or not projection[
        "relation_to_previous"
    ].strip():
        return None, "engine projection has an invalid relation_to_previous"
    if not isinstance(projection["engine_file_count"], int) or projection[
        "engine_file_count"
    ] < 0:
        return None, "engine projection has an invalid engine_file_count"
    return projection, ""


def current_registered_engine_projection(
    root: Path,
) -> tuple[dict[str, object] | None, str]:
    """Return the clean, registered engine projection, or a stable error."""

    try:
        registration = validate_runtime_engine_registration(root.resolve())
    except EngineRevisionError as exc:
        return None, str(exc)
    projection, error = normalized_engine_projection(
        {
            "engine_tree_sha256": registration.engine_tree_sha256,
            "review_semantic_class_sha256": registration.review_semantic_class_sha256,
            "revision_sequence": registration.revision_sequence,
            "relation_to_previous": registration.relation_to_previous,
            "engine_file_count": registration.engine_file_count,
        }
    )
    if projection is None:
        return None, "registered engine projection is malformed: " + error
    return projection, ""


def closeout_wave_engine_snapshot_path(root: Path) -> Path:
    """Return the ignored repository-wide closeout-wave snapshot location."""

    return root.resolve() / CLOSEOUT_WAVE_ENGINE_SNAPSHOT_RELATIVE_PATH


def read_closeout_wave_engine_snapshot(
    root: Path,
) -> tuple[dict[str, object] | None, str]:
    """Read one operational snapshot without replacing malformed state."""

    path = closeout_wave_engine_snapshot_path(root)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, ""
    except (OSError, json.JSONDecodeError) as exc:
        return None, "could not read closeout-wave engine snapshot: " + str(exc)
    if not isinstance(payload, Mapping):
        return None, "closeout-wave engine snapshot is not an object"
    if payload.get("schema") != CLOSEOUT_WAVE_ENGINE_SNAPSHOT_SCHEMA:
        return None, "closeout-wave engine snapshot has an unsupported schema"
    if payload.get("acceptance_credential") is not False:
        return None, "closeout-wave engine snapshot must deny acceptance authority"
    if payload.get("operational_recovery_only") is not True:
        return None, "closeout-wave engine snapshot must be operational-only"
    if payload.get("kind") != "closeout_wave_engine_snapshot":
        return None, "closeout-wave engine snapshot has an invalid kind"
    if not isinstance(payload.get("wave_id"), str) or not str(payload["wave_id"]).strip():
        return None, "closeout-wave engine snapshot has no wave_id"
    if not isinstance(payload.get("started_at"), str) or not str(payload["started_at"]).strip():
        return None, "closeout-wave engine snapshot has no started_at"
    projection, projection_error = normalized_engine_projection(
        payload.get("engine_registration")
    )
    if projection is None:
        return None, "closeout-wave engine snapshot has invalid engine registration: " + projection_error
    normalized = dict(payload)
    normalized["engine_registration"] = projection
    return normalized, ""


def closeout_wave_engine_snapshot_state(root: Path) -> dict[str, object]:
    """Classify an extant wave without creating or resetting it."""

    snapshot, snapshot_error = read_closeout_wave_engine_snapshot(root)
    if snapshot_error:
        return {
            "state": "invalid",
            "reason": snapshot_error,
        }
    if snapshot is None:
        return {"state": "not_started"}
    current, current_error = current_registered_engine_projection(root)
    if current_error:
        return {
            "state": "engine_registration_required",
            "snapshot": snapshot,
            "reason": current_error,
        }
    assert current is not None
    if snapshot["engine_registration"] != current:
        return {
            "state": "reset_required",
            "snapshot": snapshot,
            "current_engine_registration": current,
            "reason": (
                "the registered formalization engine differs from the active "
                "closeout-wave snapshot"
            ),
        }
    return {
        "state": "current",
        "snapshot": snapshot,
        "current_engine_registration": current,
    }


def _new_closeout_wave_engine_snapshot(
    projection: Mapping[str, object],
) -> dict[str, object]:
    normalized, error = normalized_engine_projection(projection)
    if normalized is None:
        raise ValueError("cannot create invalid closeout-wave projection: " + error)
    return {
        "schema": CLOSEOUT_WAVE_ENGINE_SNAPSHOT_SCHEMA,
        "kind": "closeout_wave_engine_snapshot",
        "acceptance_credential": False,
        "operational_recovery_only": True,
        "wave_id": str(uuid4()),
        "started_at": _utc_now(),
        "engine_registration": normalized,
    }


def ensure_closeout_wave_engine_snapshot(
    root: Path,
) -> tuple[dict[str, object] | None, bool, str]:
    """Bind the first raw action in a wave, never auto-reset a changed one."""

    current, current_error = current_registered_engine_projection(root)
    if current_error:
        return None, False, current_error
    assert current is not None
    snapshot, snapshot_error = read_closeout_wave_engine_snapshot(root)
    if snapshot_error:
        return None, False, snapshot_error
    if snapshot is not None:
        if snapshot["engine_registration"] != current:
            return (
                None,
                False,
                "the registered formalization engine differs from the active "
                "closeout-wave snapshot; explicitly reset the wave before another raw reissue",
            )
        return snapshot, False, ""
    payload = _new_closeout_wave_engine_snapshot(current)
    try:
        atomic_write_json(closeout_wave_engine_snapshot_path(root), payload)
    except OSError as exc:
        return None, False, "could not write closeout-wave engine snapshot: " + str(exc)
    return payload, True, ""


def reset_closeout_wave_engine_snapshot(
    root: Path,
) -> tuple[dict[str, object] | None, str]:
    """Explicitly begin a new wave after a registered engine transition."""

    current, current_error = current_registered_engine_projection(root)
    if current_error:
        return None, current_error
    assert current is not None
    payload = _new_closeout_wave_engine_snapshot(current)
    try:
        atomic_write_json(closeout_wave_engine_snapshot_path(root), payload)
    except OSError as exc:
        return None, "could not reset closeout-wave engine snapshot: " + str(exc)
    return payload, ""


def closeout_raw_reissue_wrapper_lease_observation(
    root: Path,
) -> tuple[dict[str, object] | None, str]:
    """Observe the wrapper lease used to serialize raw-reissue transitions."""

    path = root.resolve() / CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH
    try:
        if not path.exists():
            return {
                "schema": CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
                "held": False,
                "state": "absent",
            }, ""
        handle = path.open("a+", encoding="utf-8")
    except OSError as exc:
        return None, "could not open closeout raw-reissue transition lock: " + str(exc)
    try:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            try:
                handle.seek(0)
                owner = json.loads(handle.read())
            except (OSError, json.JSONDecodeError):
                owner = None
            result: dict[str, object] = {
                "schema": CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
                "held": True,
                "state": "held",
            }
            if isinstance(owner, Mapping):
                result["owner"] = dict(owner)
            return result, ""
        except OSError as exc:
            return None, "could not observe closeout raw-reissue transition lock: " + str(exc)
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        except OSError:
            pass
        return {
            "schema": CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
            "held": False,
            "state": "available",
        }, ""
    finally:
        handle.close()


def closeout_raw_reissue_operation_receipt_path(root: Path, paper: str) -> Path | None:
    """Resolve a paper-local raw-operation receipt without accepting path traversal."""

    paper_path = Path(paper)
    if not paper or paper_path.name != paper or paper in {".", ".."}:
        return None
    candidate = (
        root.resolve()
        / "papers"
        / paper
        / ".review_traces"
        / RAW_REISSUE_TRACE_DIRECTORY
        / RAW_REISSUE_OPERATION_TRACE_FILENAME
    )
    try:
        resolved = candidate.resolve()
        resolved.relative_to((root.resolve() / "papers" / paper).resolve())
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved


def read_closeout_raw_reissue_operation_receipt(
    root: Path, paper: str
) -> tuple[dict[str, object] | None, str]:
    """Read the last raw-operation record without replacing ambiguous state.

    This record is operational only, but a live ``running`` record is still a
    hard stop: after an interrupted wrapper, silently overwriting it could
    turn one uncertain expensive scan into a duplicate one.
    """

    path = closeout_raw_reissue_operation_receipt_path(root, paper)
    if path is None:
        return None, "could not resolve the paper-local raw-reissue operation receipt"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, ""
    except (OSError, json.JSONDecodeError) as exc:
        return None, "could not read raw-reissue operation receipt: " + str(exc)
    if not isinstance(payload, Mapping):
        return None, "raw-reissue operation receipt is not an object"
    state = payload.get("state")
    if (
        payload.get("schema") != RAW_REISSUE_OPERATION_TRACE_SCHEMA
        or payload.get("kind") != "source_record_raw_reissue_operation"
        or payload.get("acceptance_credential") is not False
        or payload.get("operational_recovery_only") is not True
        or payload.get("paper") != paper
        or not isinstance(payload.get("operation_id"), str)
        or not str(payload["operation_id"]).strip()
        or state not in {"running", *RAW_REISSUE_OPERATION_TERMINAL_STATES}
    ):
        return None, "raw-reissue operation receipt is malformed or belongs to another paper"
    return dict(payload), ""


def closeout_raw_reissue_operation_receipt_state(
    root: Path, paper: str
) -> dict[str, object]:
    """Classify one durable operation record without treating it as evidence."""

    payload, error = read_closeout_raw_reissue_operation_receipt(root, paper)
    if error:
        return {"state": "invalid", "reason": error}
    if payload is None:
        return {"state": "not_started"}
    return {"state": str(payload["state"]), "receipt": payload}


def _matching_running_raw_reissue_operation_error(
    root: Path,
    paper: str,
    operation_id: str,
    snapshot: Mapping[str, object],
) -> str:
    """Require the wrapper's running receipt, not merely a shared wave epoch."""

    payload, payload_error = read_closeout_raw_reissue_operation_receipt(root, paper)
    if payload_error:
        return payload_error
    if payload is None:
        return "no running raw-reissue operation receipt exists for this paper"
    if (
        payload.get("state") != "running"
        or payload.get("operation_id") != operation_id
        or payload.get("wave_id") != snapshot.get("wave_id")
        or payload.get("engine_registration") != snapshot.get("engine_registration")
    ):
        return "no matching running raw-reissue operation receipt exists for this paper"
    return ""


def closeout_raw_reissue_admission_error(
    root: Path, paper: str, operation_id: str
) -> str:
    """Require a current wave and active wrapper operation before replacing raw bytes."""

    current, current_error = current_registered_engine_projection(root)
    if current_error:
        return current_error
    assert current is not None
    snapshot, snapshot_error = read_closeout_wave_engine_snapshot(root)
    if snapshot_error:
        return snapshot_error
    if snapshot is None:
        return "no active closeout-wave engine snapshot exists"
    if snapshot["engine_registration"] != current:
        return (
            "the registered formalization engine differs from the active "
            "closeout-wave snapshot; explicitly reset the wave before another raw reissue"
        )
    operation_id = str(operation_id or "").strip()
    if not operation_id:
        return "no raw-reissue operation id was supplied by the normal wrapper"
    lease, lease_error = closeout_raw_reissue_wrapper_lease_observation(root)
    if lease_error:
        return lease_error
    assert lease is not None
    owner = lease.get("owner")
    if (
        lease.get("held") is not True
        or not isinstance(owner, Mapping)
        or owner.get("schema") != CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA
        or owner.get("operation") != "freeze_then_raw_reissue"
        or owner.get("paper") != paper
        or owner.get("operation_id") != operation_id
    ):
        return (
            "no matching closeout raw-reissue wrapper lease is active for "
            f"paper {paper}"
        )
    return _matching_running_raw_reissue_operation_error(
        root, paper, operation_id, snapshot
    )
