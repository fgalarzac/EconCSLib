#!/usr/bin/env python3
"""Replay authenticated source-record overlay lanes as a typed union.

An overlay loader is the authority for its own historical transport.  This
module deliberately does not compare source keys, declaration names, binder
names, or function names.  It invokes each registered loader, requires its
private in-memory capability on every returned item, and exposes the resulting
current response slots as named *transport lanes*.  Consumers can then choose
their collision policy explicitly instead of accidentally inheriting dict
merge precedence.

The registry is loaded lazily because a few legacy transports import the
current-revalidation validator while replaying their own receipts.  Callers
therefore import this module only after their shared v10 surface is available.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping


class SourceRecordAuthenticatedOverlayUnionError(ValueError):
    """Raised when a purported loader-authenticated overlay is malformed."""


_LOADED_LANE_SENTINEL = object()


@dataclass(frozen=True)
class AuthenticatedCurrentOverlayLane:
    """One loader-owned set of current response slots.

    ``items`` retains the loader-private dict subclass.  Copying it to an
    ordinary ``dict`` is intentionally left to consumers that no longer need
    the capability; the registry itself uses the capability to reject a
    deserialized provenance marker.
    """

    label: str
    items: dict[str, Mapping[str, Any]]
    _loader_token: object = field(repr=False, compare=False)


def _overlay_modules() -> dict[str, Any]:
    """Import transport modules only while replaying a current union."""

    try:
        from scripts import source_record_attested_selected_reuse as attested
        from scripts import source_record_differential_revalidation as differential
        from scripts import source_record_historical_descriptor_migration as historical
        from scripts import source_record_semantic_rebind as semantic_rebind
        from scripts import source_record_schema4_to5_migration as migration
        from scripts import source_record_scoped_receipt_rebind as scoped_rebind
        from scripts import source_record_component_projection as component_projection
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_attested_selected_reuse as attested
        import source_record_differential_revalidation as differential
        import source_record_historical_descriptor_migration as historical
        import source_record_semantic_rebind as semantic_rebind
        import source_record_schema4_to5_migration as migration
        import source_record_scoped_receipt_rebind as scoped_rebind
        import source_record_component_projection as component_projection
    return {
        "attested_selected": attested,
        "schema4_to5": migration,
        "differential": differential,
        "historical_descriptor": historical,
        "semantic_rebind": semantic_rebind,
        "scoped_receipt": scoped_rebind,
        "component_projection": component_projection,
    }


def _evidence_module() -> Any:
    """Load the neutral current-identity issuer only when a lane needs it."""

    try:
        from scripts import audit_evidence_integrity as evidence
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import audit_evidence_integrity as evidence
    return evidence


def _validated_lane_items(
    label: str,
    loaded: object,
    *,
    is_loaded: Callable[[object], bool],
) -> dict[str, Mapping[str, Any]]:
    """Validate a loader result without accepting serialized provenance.

    A response key is only an address in the already-generated current group
    ledger.  It is not used here, or by callers, to infer a semantic match.
    """

    if not isinstance(loaded, Mapping):
        raise SourceRecordAuthenticatedOverlayUnionError(
            f"authenticated {label} overlay loader returned a non-mapping result"
        )
    out: dict[str, Mapping[str, Any]] = {}
    for raw_key, value in loaded.items():
        key = str(raw_key or "").strip()
        if not key or key in out:
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader returned an empty or duplicate current slot"
            )
        if not isinstance(value, Mapping) or not is_loaded(value):
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader returned an item without its private capability"
            )
        out[key] = value
    return out


def _lane_specs(
    modules: Mapping[str, Any],
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    differential_overlay_path: Path | None,
    differential_current_raw_audit_path: Path | None,
    differential_current_raw_audit_provenance_path: Path | None,
    source_record_identity_context: object | None,
) -> tuple[tuple[str, Callable[[], object], Callable[[object], bool]], ...]:
    """Return the fixed loader registry and its exact current replay inputs."""

    attested = modules["attested_selected"]
    migration = modules["schema4_to5"]
    differential = modules["differential"]
    historical = modules["historical_descriptor"]
    semantic_rebind = modules["semantic_rebind"]
    scoped_rebind = modules["scoped_receipt"]
    identity_context_prepared = False
    identity_context = source_record_identity_context

    def current_identity_context() -> object | None:
        """Issue or revalidate exactly one opaque context for optional lanes."""

        nonlocal identity_context, identity_context_prepared
        if identity_context_prepared:
            return identity_context
        evidence = _evidence_module()
        if identity_context is not None:
            error = evidence.current_source_record_identity_context_error(
                identity_context,
                paper_dir=paper_dir,
                paper=paper,
                current_raw_audit=current_raw_audit,
            )
            if error:
                raise SourceRecordAuthenticatedOverlayUnionError(
                    "authenticated overlay identity context is invalid: " + error
                )
        else:
            # This invokes the external identity helper at most once per union
            # invocation.  ``None`` means the raw surface failed closed; the
            # optional lanes below remain empty rather than replaying it.
            identity_context = evidence.prepare_current_source_record_identity_context(
                paper_dir,
                paper,
                current_raw_audit,
            )
        identity_context_prepared = True
        return identity_context

    semantic_specs: tuple[
        tuple[str, Callable[[], object], Callable[[object], bool]], ...
    ] = ()
    # Schema-2 sidecars and component projection share the same neutral live
    # identity capability.  It is recreated for every union invocation and
    # never becomes a serialized authority.  The legacy historical lane is
    # explicitly told not to re-load schema 2 below.
    if semantic_rebind.source_record_semantic_rebind_overlay_path(paper_dir).is_file():
        def load_semantic_rebind() -> object:
            current_context = current_identity_context()
            if current_context is None:
                return {}
            return semantic_rebind.load_current_source_record_semantic_rebind_items(
                paper_dir,
                paper,
                current_raw_audit,
                source_record_identity_context=current_context,
            )

        semantic_specs = (
            (
                "semantic_rebind",
                load_semantic_rebind,
                semantic_rebind.is_loaded_source_record_semantic_rebind_item,
            ),
        )
    base_specs = (
        (
            "scoped_receipt",
            lambda: scoped_rebind.load_current_source_record_scoped_receipt_rebind_items(
                paper_dir, paper, current_raw_audit
            ),
            scoped_rebind.is_loaded_source_record_scoped_receipt_rebind_item,
        ),
        (
            "attested_selected",
            lambda: attested.load_current_attested_selected_semantic_reuse_items(
                paper_dir, paper, current_raw_audit
            ),
            attested.is_loaded_source_record_attested_selected_reuse_item,
        ),
        *semantic_specs,
        (
            "schema4_to5",
            lambda: migration.load_current_source_record_schema4_to5_migration_items(
                paper_dir, paper, current_raw_audit
            ),
            migration.is_loaded_source_record_schema4_to5_migration_item,
        ),
        (
            "differential",
            lambda: differential.load_current_source_record_differential_revalidation_items(
                paper_dir,
                paper,
                current_raw_audit,
                path=differential_overlay_path,
                current_raw_audit_path=differential_current_raw_audit_path,
                current_raw_audit_provenance_path=(
                    differential_current_raw_audit_provenance_path
                ),
            ),
            differential.is_loaded_source_record_differential_revalidation_item,
        ),
        (
            "historical_descriptor",
            lambda: historical.load_current_source_record_historical_descriptor_migration_items(
                paper_dir,
                paper,
                current_raw_audit,
                include_semantic_rebind=False,
            ),
            historical.is_loaded_source_record_historical_descriptor_migration_item,
        ),
    )
    # No optional receipt means no lane at all.  This preserves the exact
    # five-lane descriptor partition recorded by every existing selected-v2
    # attestation, instead of making old papers appear stale solely because a
    # new generic transport exists in the codebase.
    component_projection = modules["component_projection"]
    if not component_projection.component_projection_artifact_path(paper_dir).is_file():
        return base_specs

    def load_component_projection() -> object:
        current_context = current_identity_context()
        if current_context is None:
            return {}
        return component_projection.load_current_source_record_component_projection_items(
            paper_dir,
            paper,
            current_raw_audit,
            source_record_identity_context=current_context,
        )

    return base_specs + (
        (
            "component_projection",
            load_component_projection,
            component_projection.is_loaded_source_record_component_projection_item,
        ),
    )


def load_authenticated_current_overlay_lanes(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    lane_labels: Iterable[str] | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    source_record_identity_context: object | None = None,
) -> tuple[AuthenticatedCurrentOverlayLane, ...]:
    """Replay registered current transports and retain their private tokens.

    ``lane_labels`` is an explicit selection of registry lanes, not a pattern
    over paths, declaration names, or response keys.  Empty lanes are retained
    so a persisted consumer can bind the complete current transport surface,
    including the fact that a registered lane supplied no current slots.
    """

    modules = _overlay_modules()
    specs = _lane_specs(
        modules,
        paper_dir=paper_dir,
        paper=paper,
        current_raw_audit=current_raw_audit,
        differential_overlay_path=differential_overlay_path,
        differential_current_raw_audit_path=differential_current_raw_audit_path,
        differential_current_raw_audit_provenance_path=(
            differential_current_raw_audit_provenance_path
        ),
        source_record_identity_context=source_record_identity_context,
    )
    available = {label for label, _load, _capability in specs}
    requested = (
        tuple(label for label, _load, _capability in specs)
        if lane_labels is None
        else tuple(str(label or "").strip() for label in lane_labels)
    )
    if not requested or any(not label or label not in available for label in requested):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "authenticated overlay lane selection names an unknown or empty lane"
        )
    if len(set(requested)) != len(requested):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "authenticated overlay lane selection repeats a lane"
        )
    selected = {label for label in requested}
    lanes: list[AuthenticatedCurrentOverlayLane] = []
    for label, load, is_loaded in specs:
        if label not in selected:
            continue
        try:
            loaded = load()
        except Exception as exc:  # noqa: BLE001 - fail closed across transport boundaries.
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader raised {type(exc).__name__}: {exc}"
            ) from exc
        lanes.append(
            AuthenticatedCurrentOverlayLane(
                label=label,
                items=_validated_lane_items(label, loaded, is_loaded=is_loaded),
                _loader_token=_LOADED_LANE_SENTINEL,
            )
        )
    return tuple(lanes)


def strict_authenticated_current_overlay_union(
    lanes: Iterable[AuthenticatedCurrentOverlayLane],
) -> dict[str, Mapping[str, Any]]:
    """Return a union only when every current slot has one transport owner.

    Normal evidence consumption has a documented precedence order.  A manual
    complement must instead know exactly why each omitted current group is
    omitted, so a cross-lane collision is a deterministic error rather than
    an overwrite.
    """

    out: dict[str, Mapping[str, Any]] = {}
    owners: dict[str, str] = {}
    for lane in lanes:
        if not isinstance(lane, AuthenticatedCurrentOverlayLane):
            raise SourceRecordAuthenticatedOverlayUnionError(
                "authenticated overlay union contains an untyped lane"
            )
        if lane._loader_token is not _LOADED_LANE_SENTINEL:
            raise SourceRecordAuthenticatedOverlayUnionError(
                "authenticated overlay union contains a lane without loader authority"
            )
        for key, value in lane.items.items():
            if key in out:
                raise SourceRecordAuthenticatedOverlayUnionError(
                    "authenticated overlay lanes overlap at current semantic group "
                    f"`{key}` ({owners[key]} and {lane.label})"
                )
            out[key] = value
            owners[key] = lane.label
    return out
