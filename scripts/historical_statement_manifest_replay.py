#!/usr/bin/env python3
"""Fail-closed transport for statement receipts across a manifest serializer change.

This module is deliberately narrower than ordinary semantic reuse.  An
archived statement judgment can be carried forward only when an injected,
hermetic runner replays the historical Lean manifest serializer against the
current interface and the resulting historical projection matches the archived
receipt.  Current source-route and current-manifest validation remain owned by
the caller: this module requires both checks as callbacks and retains only
their content receipts.

Pairing never uses a sidecar key, source-map key, declaration name, or raw
pretty-printed Lean text.  The bridge key consists of the source target hash,
Lean-to-TeX target hash, and the historical serializer's signature and ordered
name-free atom projection.  Navigation may be needed inside a runner to ask
Lean for a declaration, but it is not accepted as bridge input or serialized
as bridge identity.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Mapping, Sequence

try:  # Supports package imports and direct focused-test imports.
    from scripts import lean_signature_manifest as manifest_tools
    from scripts import review_dashboard
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import lean_signature_manifest as manifest_tools
    import review_dashboard


HISTORICAL_STATEMENT_MANIFEST_REPLAY_SCHEMA = 1
HISTORICAL_STATEMENT_MANIFEST_REPLAY_ARTIFACT_KIND = (
    "historical_statement_manifest_serializer_replay"
)
HISTORICAL_STATEMENT_MANIFEST_REPLAY_POLICY_VERSION = (
    "historical-statement-manifest-serializer-replay-v1"
)
HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD = (
    "historical_statement_manifest_replay_sha256"
)
HISTORICAL_SERIALIZER_RECIPE_SCHEMA = 2
HISTORICAL_SERIALIZER_RECIPE_ARTIFACT_KIND = (
    "historical_statement_manifest_serializer_recipe"
)
HISTORICAL_SERIALIZER_RECIPE_POLICY_VERSION = (
    "historical-statement-manifest-serializer-recipe-v2"
)
HISTORICAL_ATOM_PROJECTION_SCHEMA = 1
HISTORICAL_ATOM_CANONICAL_EQUIVALENCE_SCHEMA = 1
HISTORICAL_SEMANTIC_SNAPSHOT_SCHEMA = 1
HISTORICAL_SEMANTIC_SNAPSHOT_ARTIFACT_KIND = (
    "historical_statement_manifest_semantic_snapshot"
)
HISTORICAL_SEMANTIC_SNAPSHOT_POLICY_VERSION = (
    "historical-statement-manifest-semantic-snapshot-v1"
)
CURRENT_TARGET_IDENTITY_SCHEMA = 1
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_GIT_OBJECT_ID_RE = re.compile(r"^[0-9a-f]{40}(?:[0-9a-f]{24})?$", re.IGNORECASE)
_BINDER_INFOS = {"explicit", "implicit", "strictImplicit", "instImplicit"}
_CURRENT_TARGET_FIELDS = (
    "lean_signature_sha256",
    "paper_statement_sha256",
    "tex_statement_sha256",
)


class HistoricalStatementManifestReplayError(ValueError):
    """Raised when a historical statement-manifest transport is inadmissible."""


@dataclass(frozen=True)
class ValidatedHistoricalStatementManifestReplay:
    """A bridge authority reconstructed from exact current and historic inputs.

    The mapping keys are canonical archived payload digests, never storage or
    Lean navigation strings.  A later materializer can use the binding only
    after it independently resolves the exact current content identity.
    """

    bindings_by_prior_payload_sha256: Mapping[str, Mapping[str, object]]
    receipt_sha256: str


HistoricalManifestRunner = Callable[
    [Mapping[str, object], Sequence[Mapping[str, object]]], Mapping[str, object]
]
HistoricalBlobVerifier = Callable[[Mapping[str, object]], str | None]
CurrentTargetValidator = Callable[[Mapping[str, object]], str | None]
SourceRouteValidator = Callable[[Mapping[str, object]], str | None]


def _canonical_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _digest(value: object) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _authenticated_store_digest(value: object) -> str:
    """Match the authenticated manifest store's canonical JSON digest."""

    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _git_object_id(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _GIT_OBJECT_ID_RE.fullmatch(text) else ""


def _required_sha256(value: object, *, label: str) -> str:
    digest = _sha256(value)
    if not digest:
        raise HistoricalStatementManifestReplayError(
            f"{label} must be a SHA-256 digest"
        )
    return digest


def _required_git_object_id(value: object, *, label: str) -> str:
    object_id = _git_object_id(value)
    if not object_id:
        raise HistoricalStatementManifestReplayError(
            f"{label} must be a 40- or 64-hex Git object id"
        )
    return object_id


def _required_text(value: object, *, label: str) -> str:
    text = str(value or "").strip()
    if not text:
        raise HistoricalStatementManifestReplayError(f"{label} must be nonempty")
    return text


def _json_object_from_bytes(value: bytes, *, label: str) -> dict[str, Any]:
    try:
        decoded = json.loads(value.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HistoricalStatementManifestReplayError(
            f"{label} is not valid JSON"
        ) from exc
    if not isinstance(decoded, dict):
        raise HistoricalStatementManifestReplayError(f"{label} is not a JSON object")
    return decoded


def current_target_identity(identity: Mapping[str, object]) -> dict[str, str]:
    """Normalize the complete current statement target without navigation data."""

    return {
        field: _required_sha256(identity.get(field), label=field)
        for field in _CURRENT_TARGET_FIELDS
    }


def current_target_identity_sha256(identity: Mapping[str, object]) -> str:
    """Return the name-free content address used only for bridge lookup."""

    return _digest(
        {
            "schema": CURRENT_TARGET_IDENTITY_SCHEMA,
            "identity": current_target_identity(identity),
        }
    )


def _serializer_recipe_payload(recipe: Mapping[str, object]) -> dict[str, object]:
    """Validate and normalize the hermetic serializer recipe.

    The runner, rather than this pure transport module, is responsible for
    obtaining Git blobs.  Requiring both a Git object id and a byte digest
    prevents an object-format change or a misleading ref from changing the
    helper under the same transport recipe.
    """

    if recipe.get("schema") != HISTORICAL_SERIALIZER_RECIPE_SCHEMA:
        raise HistoricalStatementManifestReplayError(
            "historical serializer recipe has an unsupported schema"
        )
    if (
        str(recipe.get("artifact_kind") or "").strip()
        != HISTORICAL_SERIALIZER_RECIPE_ARTIFACT_KIND
    ):
        raise HistoricalStatementManifestReplayError(
            "historical serializer recipe has the wrong artifact kind"
        )
    if (
        str(recipe.get("policy_version") or "").strip()
        != HISTORICAL_SERIALIZER_RECIPE_POLICY_VERSION
    ):
        raise HistoricalStatementManifestReplayError(
            "historical serializer recipe has the wrong policy version"
        )

    historical_commit = _required_git_object_id(
        recipe.get("historical_git_commit"), label="historical_git_commit"
    )
    blobs: dict[str, dict[str, str]] = {}
    for field in ("serializer", "helper"):
        raw_blob = recipe.get(f"historical_{field}_blob")
        if not isinstance(raw_blob, Mapping):
            raise HistoricalStatementManifestReplayError(
                f"historical_{field}_blob must be an object"
            )
        blobs[f"historical_{field}_blob"] = {
            "git_object_id": _required_git_object_id(
                raw_blob.get("git_object_id"),
                label=f"historical_{field}_blob.git_object_id",
            ),
            "bytes_sha256": _required_sha256(
                raw_blob.get("bytes_sha256"),
                label=f"historical_{field}_blob.bytes_sha256",
            ),
        }

    current_execution = recipe.get("current_execution_inputs")
    if not isinstance(current_execution, Mapping):
        raise HistoricalStatementManifestReplayError(
            "historical serializer recipe has no current execution-input receipt"
        )
    execution: dict[str, str] = {}
    for field in (
        "paper_interface_bytes_sha256",
        "lean_toolchain_bytes_sha256",
        "lake_manifest_bytes_sha256",
        "lean_import_closure_sha256",
    ):
        execution[field] = _required_sha256(
            current_execution.get(field), label=f"current_execution_inputs.{field}"
        )

    return {
        "schema": HISTORICAL_SERIALIZER_RECIPE_SCHEMA,
        "artifact_kind": HISTORICAL_SERIALIZER_RECIPE_ARTIFACT_KIND,
        "policy_version": HISTORICAL_SERIALIZER_RECIPE_POLICY_VERSION,
        "historical_git_commit": historical_commit,
        **blobs,
        "current_execution_inputs": execution,
        "runner_identity_sha256": _required_sha256(
            recipe.get("runner_identity_sha256"), label="runner_identity_sha256"
        ),
    }


def historical_serializer_recipe_sha256(recipe: Mapping[str, object]) -> str:
    """Return the content address of a fully normalized serializer recipe."""

    return _digest(_serializer_recipe_payload(recipe))


def _historical_atom_projection(manifest: object) -> tuple[dict[str, object], str]:
    """Project a historic outer interface without requiring its modern graphs.

    Old helpers predate some current closure receipts.  The historic projection
    intentionally validates only the common, name-free outer manifest surface;
    current dependency and proposition graphs are validated separately below.
    """

    if not isinstance(manifest, Mapping):
        return {}, "historical manifest is not an object"
    if str(manifest.get("schema") or "").strip() != "2":
        return {}, "historical manifest is not schema 2"
    declaration_kind = str(manifest.get("declaration_kind") or "").strip()
    if declaration_kind not in manifest_tools.DECLARATION_KINDS:
        return {}, "historical manifest has an invalid declaration kind"
    conclusion_mode = str(manifest.get("conclusion_mode") or "").strip()
    if not conclusion_mode:
        return {}, "historical manifest has no conclusion mode"
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return {}, "historical manifest has no atom list"

    atom_digests: list[str] = []
    refs: set[str] = set()
    for index, raw_atom in enumerate(atoms):
        if not isinstance(raw_atom, Mapping):
            return {}, "historical manifest has a non-object atom"
        ref = str(raw_atom.get("ref") or "").strip()
        role = str(raw_atom.get("role") or "").strip()
        canonical = raw_atom.get("canonical")
        if not ref or ref in refs or role not in manifest_tools.ATOM_ROLES:
            return {}, "historical manifest has a malformed atom identity"
        if not isinstance(canonical, Mapping):
            return {}, "historical manifest atom has no canonical form"
        if role == "conclusion":
            if index != len(atoms) - 1 or ref != "result":
                return {}, "historical manifest conclusion atom is malformed"
        else:
            binder_info = str(raw_atom.get("binder_info") or "").strip()
            if binder_info not in _BINDER_INFOS:
                return {}, "historical manifest binder atom has invalid binder info"
        digest = review_dashboard.signature_manifest_atom_digest(dict(raw_atom))
        if not digest:
            return {}, "historical manifest atom has no name-free digest"
        refs.add(ref)
        atom_digests.append(digest)
    if any(
        str(raw_atom.get("role") or "").strip() == "conclusion"
        for raw_atom in atoms[:-1]
        if isinstance(raw_atom, Mapping)
    ):
        return {}, "historical manifest has a nonterminal conclusion atom"

    projection = {
        "schema": HISTORICAL_ATOM_PROJECTION_SCHEMA,
        "declaration_kind": declaration_kind,
        "conclusion_mode": conclusion_mode,
        "atom_sha256s": atom_digests,
    }
    projection["sha256"] = _digest(projection)
    return projection, ""


def _atom_canonical_sha256(atom: Mapping[str, object]) -> str:
    """Return an exact semantic-form digest under a versioned name-free codec.

    Atom refs are serializer-local navigation and roles/binder slots are only
    structural metadata.  The canonical Lean expression is the generic
    semantic representation shared by historic and current manifests.  A
    replay transport accepts exact equality of this digest, never a same-role
    heuristic.
    """

    canonical = atom.get("canonical")
    if not isinstance(canonical, Mapping):
        return ""
    return _digest(
        {
            "schema": HISTORICAL_ATOM_CANONICAL_EQUIVALENCE_SCHEMA,
            "canonical": dict(canonical),
        }
    )


def _signature_atom_bindings(
    manifest: object,
) -> tuple[list[dict[str, str]], str]:
    """Return ordered ref/role/digest facts needed to transport a v10 ledger."""

    projection, error = _historical_atom_projection(manifest)
    if error:
        return [], error
    assert isinstance(manifest, Mapping)
    atoms = manifest.get("atoms")
    assert isinstance(atoms, list)
    bindings: list[dict[str, str]] = []
    for atom, atom_digest in zip(atoms, projection["atom_sha256s"], strict=True):
        assert isinstance(atom, Mapping)
        role = str(atom.get("role") or "").strip()
        binding = {
            "signature_ref": str(atom.get("ref") or "").strip(),
            "role": role,
            "signature_atom_sha256": str(atom_digest),
            "canonical_sha256": _atom_canonical_sha256(atom),
        }
        if not binding["canonical_sha256"]:
            return [], "historical manifest atom has no canonical semantic form"
        if role != "conclusion":
            binding["binder_info"] = str(atom.get("binder_info") or "").strip()
        bindings.append(binding)
    return bindings, ""


def _compact_historical_outer_manifest(
    manifest: object,
) -> tuple[dict[str, object], str]:
    """Keep the historic ledger surface without a declaration navigation field."""

    projection, error = _historical_atom_projection(manifest)
    if error:
        return {}, error
    assert isinstance(manifest, Mapping)
    supplied_sha = _sha256(manifest.get("sha256"))
    computed_sha = manifest_tools.signature_manifest_digest(dict(manifest))
    if not supplied_sha or supplied_sha != computed_sha:
        return {}, "historical manifest signature is stale"
    raw_atoms = manifest.get("atoms")
    assert isinstance(raw_atoms, list)
    compact_atoms: list[dict[str, object]] = []
    for raw_atom in raw_atoms:
        assert isinstance(raw_atom, Mapping)
        atom = {
            "ref": str(raw_atom.get("ref") or "").strip(),
            "role": str(raw_atom.get("role") or "").strip(),
            "canonical": copy.deepcopy(raw_atom.get("canonical")),
        }
        if atom["role"] != "conclusion":
            atom["binder_info"] = str(raw_atom.get("binder_info") or "").strip()
        compact_atoms.append(atom)
    compact: dict[str, object] = {
        "schema": 2,
        "declaration_kind": str(manifest.get("declaration_kind") or "").strip(),
        "conclusion_mode": str(manifest.get("conclusion_mode") or "").strip(),
        "atoms": compact_atoms,
        "sha256": supplied_sha,
    }
    if manifest_tools.signature_manifest_digest(compact) != supplied_sha:
        return {}, "historical manifest compact projection changes its signature"
    # Keep this check adjacent to the stored compact surface: the aggregate
    # atom digest alone cannot later recover a ledger's signature_ref mapping.
    if str(projection["sha256"]) != _digest(
        {
            "schema": HISTORICAL_ATOM_PROJECTION_SCHEMA,
            "declaration_kind": compact["declaration_kind"],
            "conclusion_mode": compact["conclusion_mode"],
            "atom_sha256s": [
                review_dashboard.signature_manifest_atom_digest(atom)
                for atom in compact_atoms
            ],
        }
    ):
        return {}, "historical manifest compact projection has inconsistent atoms"
    return compact, ""


def _atom_transport(
    historical_atoms: Sequence[Mapping[str, object]],
    current_atoms: Sequence[Mapping[str, object]],
) -> tuple[list[dict[str, str]], str]:
    """Map only canonically identical historic/current atom slots.

    Running an old serializer against the current declaration does not prove
    that a legacy canonicalizer preserved every proposition.  A same-arity,
    same-role ``P`` to ``Q`` change must not become evidence merely because
    its outer binder layout lines up.  The baseline is exact equality of a
    versioned canonical-form digest.  A future cross-codec migration must use
    an explicit independently validated generic equivalence attestation rather
    than weakening this transport rule.
    """

    if len(historical_atoms) != len(current_atoms) or not historical_atoms:
        return [], "historical/current atom interfaces have different arity"
    transport: list[dict[str, str]] = []
    seen_historical: set[str] = set()
    seen_current: set[str] = set()
    for historical, current in zip(historical_atoms, current_atoms, strict=True):
        historical_ref = str(historical.get("signature_ref") or "").strip()
        current_ref = str(current.get("signature_ref") or "").strip()
        historical_role = str(historical.get("role") or "").strip()
        current_role = str(current.get("role") or "").strip()
        historical_digest = _sha256(historical.get("signature_atom_sha256"))
        current_digest = _sha256(current.get("signature_atom_sha256"))
        historical_canonical = _sha256(historical.get("canonical_sha256"))
        current_canonical = _sha256(current.get("canonical_sha256"))
        if (
            not historical_ref
            or not current_ref
            or historical_ref in seen_historical
            or current_ref in seen_current
            or not historical_digest
            or not current_digest
            or not historical_canonical
            or not current_canonical
            or historical_role != current_role
        ):
            return [], "historical/current atom roles cannot be transported"
        if historical_role != "conclusion" and (
            str(historical.get("binder_info") or "").strip()
            != str(current.get("binder_info") or "").strip()
        ):
            return [], "historical/current atom binder information changed"
        if historical_canonical != current_canonical:
            return [], (
                "historical/current atom canonical forms differ; exact canonical "
                "equality is required unless a separately validated generic "
                "canonical-migration equivalence attestation is implemented"
            )
        record = {
            "historical_signature_ref": historical_ref,
            "historical_role": historical_role,
            "historical_signature_atom_sha256": historical_digest,
            "historical_canonical_sha256": historical_canonical,
            "current_signature_ref": current_ref,
            "current_role": current_role,
            "current_signature_atom_sha256": current_digest,
            "current_canonical_sha256": current_canonical,
        }
        transport.append(record)
        seen_historical.add(historical_ref)
        seen_current.add(current_ref)
    return transport, ""


def _outer_binder_semantic_sha256(manifest: object) -> str:
    """Digest the outer binder interface without serializer-local refs.

    Historic/current serializers may choose different ``signature_ref``
    strings for the same binder.  The closure gate needs the mathematical
    outer interface, so it hashes ordered role/binder/canonical facts rather
    than a raw manifest's navigation-bearing binder receipt.
    """

    projection, error = _historical_atom_projection(manifest)
    if error or not isinstance(manifest, Mapping):
        return ""
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list):
        return ""
    rows: list[dict[str, object]] = []
    for raw_atom in atoms:
        if not isinstance(raw_atom, Mapping):
            return ""
        role = str(raw_atom.get("role") or "").strip()
        row: dict[str, object] = {
            "role": role,
            "canonical": copy.deepcopy(raw_atom.get("canonical")),
        }
        if role != "conclusion":
            row["binder_info"] = str(raw_atom.get("binder_info") or "").strip()
        rows.append(row)
    return _digest(
        {
            "schema": HISTORICAL_ATOM_CANONICAL_EQUIVALENCE_SCHEMA,
            "declaration_kind": projection["declaration_kind"],
            "conclusion_mode": projection["conclusion_mode"],
            "outer_binders": rows,
        }
    )


def _current_manifest_evidence(manifest: object) -> tuple[dict[str, object], str]:
    """Validate current Lean facts and retain compact, spelling-free receipts."""

    if not isinstance(manifest, Mapping):
        return {}, "current target has no manifest object"
    normalized = manifest_tools.normalize_signature_manifest(dict(manifest))
    if normalized is None:
        return {}, "current target manifest is not a complete current signature manifest"
    signature = manifest_tools.signature_manifest_digest(normalized)
    if not signature or _sha256(manifest.get("sha256")) != signature:
        return {}, "current target manifest signature is stale"
    projection, projection_error = _historical_atom_projection(normalized)
    if projection_error:
        return {}, "current target " + projection_error
    atom_bindings, atom_bindings_error = _signature_atom_bindings(normalized)
    if atom_bindings_error:
        return {}, "current target " + atom_bindings_error
    dependency = manifest_tools.semantic_dependency_manifest(dict(manifest))
    if not isinstance(dependency, Mapping) or dependency.get("complete") is not True:
        return {}, "current target has no complete semantic dependency receipt"
    semantic_dependency = _sha256(dependency.get("semantic_dependency_sha256"))
    realization_dependency = _sha256(dependency.get("realization_dependency_sha256"))
    semantic_graph = _sha256(dependency.get("semantic_graph_sha256"))
    realization_graph = _sha256(dependency.get("realization_graph_sha256"))
    proposition_graph = _sha256(dependency.get("elaborated_proposition_graph_sha256"))
    if not all(
        (
            semantic_dependency,
            realization_dependency,
            semantic_graph,
            realization_graph,
            proposition_graph,
        )
    ):
        return {}, "current target semantic closure receipt is malformed"
    outer_binders = _outer_binder_semantic_sha256(normalized)
    if not outer_binders:
        return {}, "current target manifest has no outer-binder receipt"
    return {
        "current_manifest_atom_projection_sha256": str(projection["sha256"]),
        "current_manifest_outer_binder_sha256": outer_binders,
        "current_semantic_dependency_sha256": semantic_dependency,
        "current_realization_dependency_sha256": realization_dependency,
        "current_semantic_dependency_graph_sha256": semantic_graph,
        "current_realization_graph_sha256": realization_graph,
        "current_elaborated_proposition_graph_sha256": proposition_graph,
        "current_signature_atom_bindings": atom_bindings,
    }, ""


def _historical_semantic_projection(manifest: object) -> tuple[dict[str, str], str]:
    """Project the semantic closure needed to rule out opaque drift.

    A signature/atom interface can remain unchanged when a transparent or
    opaque dependency changes underneath it.  The historical projection is
    therefore derived from a complete archived manifest, not handwritten
    hashes.  It intentionally contains no declaration or cache-row name.
    """

    if not isinstance(manifest, Mapping):
        return {}, "historical semantic snapshot manifest is not an object"
    normalized = manifest_tools.normalize_signature_manifest(dict(manifest))
    if normalized is None:
        return {}, "historical semantic snapshot manifest is not a complete signature manifest"
    signature = manifest_tools.signature_manifest_digest(normalized)
    if not signature or _sha256(manifest.get("sha256")) != signature:
        return {}, "historical semantic snapshot manifest signature is stale"
    atom_projection, atom_error = _historical_atom_projection(normalized)
    if atom_error:
        return {}, "historical semantic snapshot " + atom_error
    compact_outer, compact_error = _compact_historical_outer_manifest(manifest)
    if compact_error:
        return {}, "historical semantic snapshot " + compact_error
    outer_binders = _outer_binder_semantic_sha256(normalized)
    if not outer_binders:
        return {}, "historical semantic snapshot manifest has no outer-binder receipt"
    dependency = manifest_tools.semantic_dependency_manifest(dict(manifest))
    if not isinstance(dependency, Mapping) or dependency.get("complete") is not True:
        return {}, "historical semantic snapshot manifest has no complete semantic closure receipt"
    field_map = {
        "historical_semantic_dependency_sha256": "semantic_dependency_sha256",
        "historical_realization_dependency_sha256": "realization_dependency_sha256",
        "historical_semantic_dependency_graph_sha256": "semantic_graph_sha256",
        "historical_realization_graph_sha256": "realization_graph_sha256",
        "historical_elaborated_proposition_graph_sha256": (
            "elaborated_proposition_graph_sha256"
        ),
    }
    values = {
        target: _sha256(dependency.get(source))
        for target, source in field_map.items()
    }
    if not all(values.values()):
        return {}, "historical semantic snapshot closure receipt is malformed"
    return {
        "historical_manifest_signature_sha256": signature,
        "historical_manifest_atom_projection_sha256": str(atom_projection["sha256"]),
        "historical_outer_manifest_sha256": _digest(compact_outer),
        "historical_manifest_outer_binder_sha256": outer_binders,
        **values,
    }, ""


def _historical_semantic_snapshot(
    *,
    paper: str,
    carrier: object,
    carrier_bytes: bytes,
    authority: object,
    authority_bytes: bytes,
) -> tuple[dict[str, object], str]:
    """Derive a name-free historic closure snapshot from exact store bytes.

    The authenticated manifest carrier contains full elaborated manifests while
    the authority independently binds their payload, signature, semantic
    dependency, and proposition graph.  We read both byte-pinned JSON values,
    validate their generic store relation, and retain only projections keyed by
    manifest content.  Declaration strings remain internal navigation used to
    join the two store files and are never emitted into the snapshot.
    """

    try:
        decoded_carrier = _json_object_from_bytes(
            carrier_bytes, label="historical semantic snapshot carrier"
        )
        decoded_authority = _json_object_from_bytes(
            authority_bytes, label="historical semantic snapshot authority"
        )
    except HistoricalStatementManifestReplayError as exc:
        return {}, str(exc)
    if not isinstance(carrier, Mapping) or dict(carrier) != decoded_carrier:
        return {}, "historical semantic snapshot carrier differs from its exact bytes"
    if not isinstance(authority, Mapping) or dict(authority) != decoded_authority:
        return {}, "historical semantic snapshot authority differs from its exact bytes"
    if (
        carrier.get("schema") != 1
        or authority.get("schema") != 1
        or str(carrier.get("paper") or "").strip() != paper
        or str(authority.get("paper") or "").strip() != paper
    ):
        return {}, "historical semantic snapshot store has the wrong schema or paper"
    expected_authority_fields = {
        "schema",
        "paper",
        "contexts",
        "contexts_sha256",
        "entries",
        "entries_sha256",
    }
    if set(authority) != expected_authority_fields or set(carrier) != {
        "schema",
        "paper",
        "entries",
    }:
        return {}, "historical semantic snapshot store has unsupported fields"
    contexts = authority.get("contexts")
    authority_entries = authority.get("entries")
    carrier_entries = carrier.get("entries")
    if (
        not isinstance(contexts, list)
        or not isinstance(authority_entries, list)
        or not isinstance(carrier_entries, list)
        or _sha256(authority.get("contexts_sha256"))
        != _authenticated_store_digest(contexts)
        or _sha256(authority.get("entries_sha256"))
        != _authenticated_store_digest(authority_entries)
    ):
        return {}, "historical semantic snapshot store has stale authority digests"

    context_ids: set[str] = set()
    for raw_context in contexts:
        if not isinstance(raw_context, Mapping):
            return {}, "historical semantic snapshot has a non-object context"
        projection = {
            key: raw_context.get(key)
            for key in (
                "import_module",
                "semantic_dependency_modules",
                "manifest_cache_context_sha256",
            )
        }
        context_id = _sha256(raw_context.get("context_id"))
        if (
            set(raw_context) != {*projection, "context_id"}
            or not context_id
            or context_id in context_ids
            or _authenticated_store_digest(projection) != context_id
            or not isinstance(projection["import_module"], str)
            or not str(projection["import_module"]).strip()
            or not isinstance(projection["semantic_dependency_modules"], list)
            or projection["semantic_dependency_modules"]
            != sorted(set(projection["semantic_dependency_modules"]))
            or projection["import_module"]
            not in projection["semantic_dependency_modules"]
            or not _sha256(projection["manifest_cache_context_sha256"])
        ):
            return {}, "historical semantic snapshot has an invalid authority context"
        context_ids.add(context_id)

    carrier_by_coordinate: dict[tuple[str, str], Mapping[str, object]] = {}
    for raw_carrier in carrier_entries:
        if not isinstance(raw_carrier, Mapping):
            return {}, "historical semantic snapshot has a non-object carrier entry"
        qualified = str(raw_carrier.get("qualified_declaration") or "").strip()
        context_id = _sha256(raw_carrier.get("context_id"))
        coordinate = (qualified, context_id)
        if (
            set(raw_carrier) != {"qualified_declaration", "context_id", "manifest"}
            or not all(coordinate)
            or coordinate in carrier_by_coordinate
            or not isinstance(raw_carrier.get("manifest"), Mapping)
        ):
            return {}, "historical semantic snapshot has an invalid carrier entry"
        carrier_by_coordinate[coordinate] = raw_carrier

    authority_by_coordinate: dict[tuple[str, str], Mapping[str, object]] = {}
    required_entry_fields = {
        "qualified_declaration",
        "context_id",
        "elaborated_signature_sha256",
        "semantic_dependency_sha256",
        "elaborated_proposition_graph_sha256",
        "manifest_payload_sha256",
        "authority_binding_sha256",
    }
    for raw_authority in authority_entries:
        if not isinstance(raw_authority, Mapping):
            return {}, "historical semantic snapshot has a non-object authority entry"
        qualified = str(raw_authority.get("qualified_declaration") or "").strip()
        context_id = _sha256(raw_authority.get("context_id"))
        coordinate = (qualified, context_id)
        if (
            set(raw_authority) != required_entry_fields
            or not all(coordinate)
            or coordinate in authority_by_coordinate
            or context_id not in context_ids
            or not all(
                _sha256(raw_authority.get(field))
                for field in required_entry_fields
                - {"qualified_declaration", "context_id"}
            )
        ):
            return {}, "historical semantic snapshot has an invalid authority entry"
        authority_by_coordinate[coordinate] = raw_authority

    projections_by_signature: dict[str, dict[str, str]] = {}
    for coordinate, raw_authority in authority_by_coordinate.items():
        raw_carrier = carrier_by_coordinate.get(coordinate)
        if raw_carrier is None:
            return {}, "historical semantic snapshot authority has no carrier manifest"
        manifest = raw_carrier.get("manifest")
        assert isinstance(manifest, Mapping)
        projection, projection_error = _historical_semantic_projection(manifest)
        if projection_error:
            return {}, projection_error
        signature = projection["historical_manifest_signature_sha256"]
        dependency = manifest_tools.semantic_dependency_manifest(dict(manifest))
        proposition_graph = manifest.get("elaborated_proposition_graph")
        if (
            _authenticated_store_digest(manifest)
            != _sha256(raw_authority.get("manifest_payload_sha256"))
            or signature
            != _sha256(raw_authority.get("elaborated_signature_sha256"))
            or projection["historical_semantic_dependency_sha256"]
            != _sha256(raw_authority.get("semantic_dependency_sha256"))
            or not isinstance(proposition_graph, Mapping)
            or _authenticated_store_digest(proposition_graph)
            != _sha256(raw_authority.get("elaborated_proposition_graph_sha256"))
            or not isinstance(dependency, Mapping)
        ):
            return {}, "historical semantic snapshot carrier does not match its authority"
        previous = projections_by_signature.get(signature)
        if previous is not None and previous != projection:
            return {}, "historical semantic snapshot has ambiguous closure for one signature"
        projections_by_signature[signature] = projection
    if not projections_by_signature:
        return {}, "historical semantic snapshot has no authenticated manifests"
    snapshot: dict[str, object] = {
        "schema": HISTORICAL_SEMANTIC_SNAPSHOT_SCHEMA,
        "artifact_kind": HISTORICAL_SEMANTIC_SNAPSHOT_ARTIFACT_KIND,
        "policy_version": HISTORICAL_SEMANTIC_SNAPSHOT_POLICY_VERSION,
        "historical_manifest_carrier_bytes_sha256": _bytes_sha256(carrier_bytes),
        "historical_manifest_authority_bytes_sha256": _bytes_sha256(authority_bytes),
        "projections": [
            projections_by_signature[signature]
            for signature in sorted(projections_by_signature)
        ],
    }
    snapshot["historical_semantic_snapshot_sha256"] = _digest(snapshot)
    return snapshot, ""


def _validated_historical_semantic_snapshot(
    snapshot: object,
    *,
    paper: str,
    carrier: object,
    carrier_bytes: bytes,
    authority: object,
    authority_bytes: bytes,
) -> tuple[dict[str, dict[str, str]], str]:
    """Reconstruct and validate a persisted historic semantic snapshot."""

    expected, error = _historical_semantic_snapshot(
        paper=paper,
        carrier=carrier,
        carrier_bytes=carrier_bytes,
        authority=authority,
        authority_bytes=authority_bytes,
    )
    if error:
        return {}, error
    if not isinstance(snapshot, Mapping) or dict(snapshot) != expected:
        return {}, "historical semantic snapshot differs from its authenticated source bytes"
    projections = expected.get("projections")
    if not isinstance(projections, list):  # Constructed above; defensive.
        return {}, "historical semantic snapshot has no projection list"
    indexed: dict[str, dict[str, str]] = {}
    for projection in projections:
        if not isinstance(projection, Mapping):
            return {}, "historical semantic snapshot has a malformed projection"
        signature = _sha256(projection.get("historical_manifest_signature_sha256"))
        if not signature or signature in indexed:
            return {}, "historical semantic snapshot has duplicate signature projections"
        indexed[signature] = dict(projection)
    return indexed, ""


def _callback_error(
    callback: Callable[[Mapping[str, object]], str | None] | None,
    value: Mapping[str, object],
    *,
    label: str,
) -> str:
    if callback is None or not callable(callback):
        return f"{label} callback is required"
    try:
        # Validation callbacks receive a snapshot, never a mutable authority
        # that could alter the recipe or current target subsequently hashed.
        outcome = callback(copy.deepcopy(dict(value)))
    except Exception as exc:  # pragma: no cover - defensive callback boundary.
        return f"{label} callback raised {type(exc).__name__}"
    if outcome is None or outcome == "":
        return ""
    if isinstance(outcome, str):
        return outcome
    return f"{label} callback must return an error string or None"


def _validated_current_targets(
    current_targets: Iterable[Mapping[str, object]],
    *,
    current_target_validator: CurrentTargetValidator | None,
    source_route_validator: SourceRouteValidator | None,
) -> tuple[dict[str, dict[str, object]], str]:
    """Validate every current target and index it by a content address."""

    targets: dict[str, dict[str, object]] = {}
    for position, raw_target in enumerate(current_targets):
        label = f"current target {position + 1}"
        if not isinstance(raw_target, Mapping):
            return {}, f"{label} is not an object"
        if error := _callback_error(
            current_target_validator, raw_target, label="current target validation"
        ):
            return {}, f"{label}: {error}"
        if error := _callback_error(
            source_route_validator, raw_target, label="source-route validation"
        ):
            return {}, f"{label}: {error}"
        try:
            identity = current_target_identity(raw_target)
        except HistoricalStatementManifestReplayError as exc:
            return {}, f"{label}: {exc}"
        source_route = _sha256(raw_target.get("source_route_sha256"))
        if not source_route:
            return {}, f"{label} has no current source-route receipt"
        evidence, evidence_error = _current_manifest_evidence(
            raw_target.get("lean_signature_manifest")
        )
        if evidence_error:
            return {}, f"{label}: {evidence_error}"
        if identity["lean_signature_sha256"] != _sha256(
            raw_target.get("lean_signature_manifest", {}).get("sha256")
            if isinstance(raw_target.get("lean_signature_manifest"), Mapping)
            else ""
        ):
            return {}, f"{label} identity does not bind its current manifest signature"
        target_id = current_target_identity_sha256(identity)
        if target_id in targets:
            return {}, "current target identities are ambiguous"
        targets[target_id] = {
            "current_target_identity": identity,
            "current_target_identity_sha256": target_id,
            "current_source_route_sha256": source_route,
            **evidence,
        }
    if not targets:
        return {}, "current target set is empty"
    return targets, ""


def _prior_payload_groups(
    prior_sidecar: Mapping[str, object],
) -> tuple[dict[str, dict[str, object]], str]:
    """Group archived receipts by payload content, ignoring sidecar storage keys."""

    items = prior_sidecar.get("items")
    if not isinstance(items, Mapping):
        return {}, "prior statement sidecar has no object-valued items"
    groups: dict[str, dict[str, object]] = {}
    for raw_value in items.values():
        if not isinstance(raw_value, Mapping):
            return {}, "prior statement sidecar has a non-object receipt"
        try:
            identity = current_target_identity(raw_value)
        except HistoricalStatementManifestReplayError as exc:
            return {}, f"prior statement receipt has no complete identity: {exc}"
        payload = copy.deepcopy(dict(raw_value))
        payload_sha = _digest(payload)
        prior = groups.get(payload_sha)
        if prior is not None:
            prior["occurrences"] = int(prior["occurrences"]) + 1
            continue
        groups[payload_sha] = {
            "prior_entry_payload_sha256": payload_sha,
            "prior_identity": identity,
            "occurrences": 1,
            # Kept in memory only. The receipt pins the exact sidecar bytes
            # and stores a compact historic manifest below instead of copying
            # reviewer prose or a sidecar navigation key into the bridge.
            "prior_entry": payload,
        }
    if not groups:
        return {}, "prior statement sidecar has no receipts"
    return groups, ""


def _prior_observation_key(identity: Mapping[str, object]) -> tuple[str, str, str]:
    normalized = current_target_identity(identity)
    return (
        normalized["lean_signature_sha256"],
        normalized["paper_statement_sha256"],
        normalized["tex_statement_sha256"],
    )


def _historical_pair_sha256(
    *,
    paper_statement_sha256: str,
    tex_statement_sha256: str,
    historical_manifest_signature_sha256: str,
    historical_manifest_atom_projection_sha256: str,
) -> str:
    """Return the only old/current pairing address used by this bridge."""

    return _digest(
        {
            "schema": HISTORICAL_ATOM_PROJECTION_SCHEMA,
            "paper_statement_sha256": paper_statement_sha256,
            "tex_statement_sha256": tex_statement_sha256,
            "historical_manifest_signature_sha256": (
                historical_manifest_signature_sha256
            ),
            "historical_manifest_atom_projection_sha256": (
                historical_manifest_atom_projection_sha256
            ),
        }
    )


def _runner_observations(
    *,
    recipe: Mapping[str, object],
    recipe_sha256: str,
    current_targets: Sequence[Mapping[str, object]],
    runner: HistoricalManifestRunner | None,
) -> tuple[list[dict[str, object]], str]:
    """Run and validate the historic serializer without retaining navigation."""

    if runner is None or not callable(runner):
        return [], "historical manifest runner is required"
    try:
        # The runner may need mutable subprocess configuration, but it cannot
        # be allowed to mutate the pinned recipe or target facts that this
        # builder compares after return.
        result = runner(
            copy.deepcopy(dict(recipe)),
            [copy.deepcopy(dict(target)) for target in current_targets],
        )
    except Exception as exc:  # pragma: no cover - defensive external boundary.
        return [], f"historical manifest runner raised {type(exc).__name__}"
    if not isinstance(result, Mapping):
        return [], "historical manifest runner did not return an object"
    if _sha256(result.get("historical_serializer_recipe_sha256")) != recipe_sha256:
        return [], "historical manifest runner used a different serializer recipe"
    expected_blob_verification = {
        "historical_git_commit": recipe["historical_git_commit"],
        "historical_serializer_blob": recipe["historical_serializer_blob"],
        "historical_helper_blob": recipe["historical_helper_blob"],
    }
    if result.get("verified_historical_git_blobs") != expected_blob_verification:
        return [], "historical manifest runner did not verify the pinned Git blobs"
    execution = recipe.get("current_execution_inputs")
    if not isinstance(execution, Mapping):  # Already checked by recipe parser.
        return [], "historical serializer recipe has no current execution inputs"
    supplied_execution = result.get("current_execution_inputs")
    if not isinstance(supplied_execution, Mapping):
        return [], "historical manifest runner has no current execution-input receipt"
    for field, expected in execution.items():
        if _sha256(supplied_execution.get(field)) != expected:
            return [], "historical manifest runner used different current execution inputs"
    raw_observations = result.get("observations")
    if not isinstance(raw_observations, list):
        return [], "historical manifest runner has no observation list"

    observations: list[dict[str, object]] = []
    seen_current_targets: set[str] = set()
    for position, raw_observation in enumerate(raw_observations):
        label = f"historical observation {position + 1}"
        if not isinstance(raw_observation, Mapping):
            return [], f"{label} is not an object"
        raw_identity = raw_observation.get("current_target_identity")
        if not isinstance(raw_identity, Mapping):
            return [], f"{label} has no current target content identity"
        try:
            current_identity = current_target_identity(raw_identity)
        except HistoricalStatementManifestReplayError as exc:
            return [], f"{label}: {exc}"
        current_target_sha = current_target_identity_sha256(current_identity)
        if current_target_sha in seen_current_targets:
            return [], "historical manifest runner produced duplicate current target observations"
        seen_current_targets.add(current_target_sha)
        historical_signature = _sha256(
            raw_observation.get("historical_manifest_signature_sha256")
        )
        if not historical_signature:
            return [], f"{label} has no historical manifest signature"
        projection, projection_error = _historical_atom_projection(
            raw_observation.get("historical_manifest")
        )
        if projection_error:
            return [], f"{label}: {projection_error}"
        raw_manifest = raw_observation.get("historical_manifest")
        compact_historical_manifest, compact_error = _compact_historical_outer_manifest(
            raw_manifest
        )
        if compact_error:
            return [], f"{label}: {compact_error}"
        historical_atom_bindings, historical_atom_error = _signature_atom_bindings(
            compact_historical_manifest
        )
        if historical_atom_error:
            return [], f"{label}: {historical_atom_error}"
        computed_signature = (
            manifest_tools.signature_manifest_digest(dict(raw_manifest))
            if isinstance(raw_manifest, Mapping)
            else ""
        )
        if computed_signature != historical_signature:
            return [], f"{label} historical manifest does not reproduce its signature"
        manifest_sha = _sha256(
            raw_observation.get("historical_manifest", {}).get("sha256")
            if isinstance(raw_observation.get("historical_manifest"), Mapping)
            else ""
        )
        if manifest_sha != historical_signature:
            return [], f"{label} historical manifest signature is not self-bound"
        runner_current_pins: dict[str, str] = {}
        for field in (
            "current_manifest_atom_projection_sha256",
            "current_manifest_outer_binder_sha256",
            "current_semantic_dependency_sha256",
            "current_realization_dependency_sha256",
            "current_semantic_dependency_graph_sha256",
            "current_realization_graph_sha256",
            "current_elaborated_proposition_graph_sha256",
        ):
            runner_current_pins[field] = _sha256(raw_observation.get(field))
            if not runner_current_pins[field]:
                return [], f"{label} has no {field}"
        observations.append(
            {
                "current_target_identity": current_identity,
                "current_target_identity_sha256": current_target_sha,
                "historical_manifest_signature_sha256": historical_signature,
                "historical_manifest_atom_projection_sha256": str(projection["sha256"]),
                "historical_manifest_atom_sha256s": list(projection["atom_sha256s"]),
                "historical_outer_manifest": compact_historical_manifest,
                "historical_signature_atom_bindings": historical_atom_bindings,
                **runner_current_pins,
            }
        )
    return observations, ""


def _historic_snapshot_matches_current(
    historical: Mapping[str, str], current: Mapping[str, object]
) -> bool:
    """Require exact historic/current closure equality before transport."""

    field_pairs = (
        (
            "historical_manifest_outer_binder_sha256",
            "current_manifest_outer_binder_sha256",
        ),
        ("historical_semantic_dependency_sha256", "current_semantic_dependency_sha256"),
        (
            "historical_realization_dependency_sha256",
            "current_realization_dependency_sha256",
        ),
        (
            "historical_semantic_dependency_graph_sha256",
            "current_semantic_dependency_graph_sha256",
        ),
        ("historical_realization_graph_sha256", "current_realization_graph_sha256"),
        (
            "historical_elaborated_proposition_graph_sha256",
            "current_elaborated_proposition_graph_sha256",
        ),
    )
    for historical_field, current_field in field_pairs:
        historical_digest = _sha256(historical.get(historical_field))
        current_digest = _sha256(current.get(current_field))
        if not historical_digest or not current_digest or historical_digest != current_digest:
            return False
    return True


def _historic_observation_matches_snapshot(
    observation: Mapping[str, object], historical: Mapping[str, str]
) -> bool:
    """Bind the old serializer's outer result to the archived full manifest."""

    outer_manifest = observation.get("historical_outer_manifest")
    if not isinstance(outer_manifest, Mapping):
        return False
    return (
        _sha256(observation.get("historical_manifest_signature_sha256"))
        == _sha256(historical.get("historical_manifest_signature_sha256"))
        and _sha256(observation.get("historical_manifest_atom_projection_sha256"))
        == _sha256(historical.get("historical_manifest_atom_projection_sha256"))
        and _digest(dict(outer_manifest))
        == _sha256(historical.get("historical_outer_manifest_sha256"))
    )


def _current_target_surface_sha256(
    targets: Mapping[str, Mapping[str, object]],
    *,
    current_evidence_sha256: str,
) -> str:
    return _digest(
        {
            "schema": CURRENT_TARGET_IDENTITY_SCHEMA,
            "current_evidence_sha256": current_evidence_sha256,
            "targets": [targets[key] for key in sorted(targets)],
        }
    )


def historical_statement_manifest_replay_digest(payload: Mapping[str, object]) -> str:
    """Hash a bridge receipt after removing its self-integrity field."""

    value = copy.deepcopy(dict(payload))
    value.pop(HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD, None)
    return _digest(value)


def build_historical_statement_manifest_replay(
    *,
    paper: str,
    historical_serializer_recipe: Mapping[str, object],
    prior_sidecar: Mapping[str, object],
    prior_sidecar_bytes: bytes,
    historical_manifest_carrier: Mapping[str, object],
    historical_manifest_carrier_bytes: bytes,
    historical_manifest_authority: Mapping[str, object],
    historical_manifest_authority_bytes: bytes,
    current_targets: Iterable[Mapping[str, object]],
    current_evidence_sha256: str,
    historical_manifest_runner: HistoricalManifestRunner | None,
    historical_blob_verifier: HistoricalBlobVerifier | None,
    current_target_validator: CurrentTargetValidator | None,
    source_route_validator: SourceRouteValidator | None,
) -> tuple[dict[str, object] | None, str]:
    """Build a deterministic historical serializer transport receipt.

    The current-target and source-route callbacks must authenticate their own
    live inputs. ``historical_blob_verifier`` must independently resolve the
    pinned Git objects and check their byte digests before the runner starts;
    the runner must also return its exact blob-verification receipt. This
    function then checks their compact output against a historic runner result,
    making the persisted bridge independent of all navigation strings used to
    reach those inputs. A byte-pinned historical authenticated-manifest store
    must also show that the historic semantic closure equals the current one;
    matching outer atoms alone never authorizes transport.
    """

    paper = str(paper or "").strip()
    if not paper:
        return None, "paper is required"
    try:
        recipe = _serializer_recipe_payload(historical_serializer_recipe)
    except HistoricalStatementManifestReplayError as exc:
        return None, str(exc)
    recipe_sha = _digest(recipe)
    if error := _callback_error(
        historical_blob_verifier, recipe, label="historical Git-blob verification"
    ):
        return None, error
    evidence_sha = _sha256(current_evidence_sha256)
    if not evidence_sha:
        return None, "current evidence receipt must be a SHA-256 digest"
    try:
        from_bytes = _json_object_from_bytes(prior_sidecar_bytes, label="prior statement sidecar")
    except HistoricalStatementManifestReplayError as exc:
        return None, str(exc)
    if from_bytes != dict(prior_sidecar):
        return None, "prior statement sidecar object differs from its exact bytes"
    if str(prior_sidecar.get("paper") or "").strip() != paper:
        return None, "prior statement sidecar belongs to a different paper"
    prior_groups, prior_error = _prior_payload_groups(prior_sidecar)
    if prior_error:
        return None, prior_error
    historical_snapshot, snapshot_error = _historical_semantic_snapshot(
        paper=paper,
        carrier=historical_manifest_carrier,
        carrier_bytes=historical_manifest_carrier_bytes,
        authority=historical_manifest_authority,
        authority_bytes=historical_manifest_authority_bytes,
    )
    if snapshot_error:
        return None, snapshot_error
    historical_projections, projection_error = _validated_historical_semantic_snapshot(
        historical_snapshot,
        paper=paper,
        carrier=historical_manifest_carrier,
        carrier_bytes=historical_manifest_carrier_bytes,
        authority=historical_manifest_authority,
        authority_bytes=historical_manifest_authority_bytes,
    )
    if projection_error:
        return None, projection_error

    raw_targets = list(current_targets)
    targets, targets_error = _validated_current_targets(
        raw_targets,
        current_target_validator=current_target_validator,
        source_route_validator=source_route_validator,
    )
    if targets_error:
        return None, targets_error
    observations, observations_error = _runner_observations(
        recipe=recipe,
        recipe_sha256=recipe_sha,
        current_targets=raw_targets,
        runner=historical_manifest_runner,
    )
    if observations_error:
        return None, observations_error

    observations_by_prior_key: dict[tuple[str, str, str], list[dict[str, object]]] = {}
    for observation in observations:
        target_id = str(observation["current_target_identity_sha256"])
        if target_id not in targets:
            return None, "historical observation names no current content target"
        identity = observation["current_target_identity"]
        assert isinstance(identity, Mapping)  # Constructed by _runner_observations.
        key = _prior_observation_key(
            {
                "lean_signature_sha256": observation[
                    "historical_manifest_signature_sha256"
                ],
                "paper_statement_sha256": identity["paper_statement_sha256"],
                "tex_statement_sha256": identity["tex_statement_sha256"],
            }
        )
        observations_by_prior_key.setdefault(key, []).append(observation)

    bindings: list[dict[str, object]] = []
    bridged_prior: set[str] = set()
    bridged_current: set[str] = set()
    for payload_sha, prior in sorted(prior_groups.items()):
        if int(prior["occurrences"]) != 1:
            # The later materializer must decide how an archived duplicate is
            # retired or superseded. A transport bridge may not collapse it.
            continue
        identity = prior["prior_identity"]
        assert isinstance(identity, Mapping)
        candidates = observations_by_prior_key.get(_prior_observation_key(identity), [])
        if not candidates:
            continue
        if len(candidates) != 1:
            return None, "historical serializer pairing is ambiguous"
        observation = candidates[0]
        target_id = str(observation["current_target_identity_sha256"])
        if target_id in bridged_current:
            return None, "two archived receipts map to one current content target"
        current = targets[target_id]
        for field in (
            "current_manifest_atom_projection_sha256",
            "current_manifest_outer_binder_sha256",
            "current_semantic_dependency_sha256",
            "current_realization_dependency_sha256",
            "current_semantic_dependency_graph_sha256",
            "current_realization_graph_sha256",
            "current_elaborated_proposition_graph_sha256",
        ):
            if observation[field] != current[field]:
                return None, "historical manifest runner did not bind the current target evidence"
        # The runner's content target is verified above; this explicit check
        # makes a source/translation mismatch fail before any transport fact is
        # serialized.
        current_identity = current["current_target_identity"]
        assert isinstance(current_identity, Mapping)
        if (
            current_identity["paper_statement_sha256"]
            != identity["paper_statement_sha256"]
            or current_identity["tex_statement_sha256"]
            != identity["tex_statement_sha256"]
        ):
            return None, "historical serializer pairing has changed source or translation content"
        historical_signature = str(observation["historical_manifest_signature_sha256"])
        if historical_signature != identity["lean_signature_sha256"]:
            return None, "historical serializer signature does not reproduce archived receipt"
        historical_projection = historical_projections.get(historical_signature)
        if historical_projection is None:
            # A receipt without a byte-pinned historic closure remains
            # unbridged. It needs fresh review rather than current-only reuse.
            continue
        if not _historic_observation_matches_snapshot(
            observation, historical_projection
        ):
            return None, (
                "historical serializer outer interface differs from its archived "
                "semantic snapshot"
            )
        historical_manifest = observation["historical_outer_manifest"]
        historical_atoms = observation["historical_signature_atom_bindings"]
        prior_entry = prior["prior_entry"]
        assert isinstance(historical_manifest, Mapping)
        assert isinstance(historical_atoms, list)
        assert isinstance(prior_entry, Mapping)
        ledger_error = review_dashboard.semantic_obligation_ledger_error(
            dict(prior_entry), dict(historical_manifest)
        )
        if ledger_error:
            return None, "archived semantic obligation ledger is invalid under historic replay: " + ledger_error
        current_atoms = current.get("current_signature_atom_bindings")
        if not isinstance(current_atoms, list):
            return None, "current target has no signature-atom bindings"
        atom_transport, transport_error = _atom_transport(historical_atoms, current_atoms)
        if transport_error:
            return None, transport_error
        if not _historic_snapshot_matches_current(historical_projection, current):
            # Preserve an unchanged sibling's bridge, but never carry a
            # receipt across a changed semantic/proposition closure.
            continue
        pair_sha = _historical_pair_sha256(
            paper_statement_sha256=str(identity["paper_statement_sha256"]),
            tex_statement_sha256=str(identity["tex_statement_sha256"]),
            historical_manifest_signature_sha256=historical_signature,
            historical_manifest_atom_projection_sha256=str(
                observation["historical_manifest_atom_projection_sha256"]
            ),
        )
        binding = {
            "prior_entry_payload_sha256": payload_sha,
            "prior_identity": dict(identity),
            "historical_pair_sha256": pair_sha,
            "historical_manifest_signature_sha256": historical_signature,
            "historical_manifest_atom_projection_sha256": observation[
                "historical_manifest_atom_projection_sha256"
            ],
            "historical_manifest_atom_sha256s": observation[
                "historical_manifest_atom_sha256s"
            ],
            "historical_outer_manifest": historical_manifest,
            "historical_signature_atom_bindings": historical_atoms,
            "historical_semantic_snapshot_projection": historical_projection,
            "atom_transport": atom_transport,
            **current,
        }
        bindings.append(binding)
        bridged_prior.add(payload_sha)
        bridged_current.add(target_id)

    current_surface_sha = _current_target_surface_sha256(
        targets, current_evidence_sha256=evidence_sha
    )
    receipt: dict[str, object] = {
        "schema": HISTORICAL_STATEMENT_MANIFEST_REPLAY_SCHEMA,
        "artifact_kind": HISTORICAL_STATEMENT_MANIFEST_REPLAY_ARTIFACT_KIND,
        "policy_version": HISTORICAL_STATEMENT_MANIFEST_REPLAY_POLICY_VERSION,
        "paper": paper,
        "historical_serializer_recipe": recipe,
        "historical_serializer_recipe_sha256": recipe_sha,
        "prior_sidecar_bytes_sha256": _bytes_sha256(prior_sidecar_bytes),
        "historical_semantic_snapshot": historical_snapshot,
        "current_evidence_sha256": evidence_sha,
        "current_target_surface_sha256": current_surface_sha,
        "bindings": sorted(
            bindings, key=lambda binding: str(binding["prior_entry_payload_sha256"])
        ),
        "unbridged_prior_entry_payload_sha256": sorted(
            set(prior_groups) - bridged_prior
        ),
        "unbridged_current_target_identity_sha256": sorted(
            set(targets) - bridged_current
        ),
    }
    receipt[HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD] = (
        historical_statement_manifest_replay_digest(receipt)
    )
    return receipt, ""


def _digest_list(value: object, *, label: str) -> tuple[list[str], str]:
    if not isinstance(value, list):
        return [], f"{label} is not a list"
    digests = [_sha256(item) for item in value]
    if any(not digest for digest in digests) or len(digests) != len(set(digests)):
        return [], f"{label} has malformed or duplicate digests"
    return digests, ""


def _static_binding_error(
    binding: Mapping[str, object],
    *,
    prior: Mapping[str, object],
    current: Mapping[str, object],
    historical_projections: Mapping[str, Mapping[str, str]],
) -> str:
    """Validate one stored transport without invoking Lean a second time."""

    prior_payload = _sha256(binding.get("prior_entry_payload_sha256"))
    if not prior_payload or prior_payload != prior.get("prior_entry_payload_sha256"):
        return "binding does not name its exact archived payload"
    prior_identity = binding.get("prior_identity")
    if not isinstance(prior_identity, Mapping) or dict(prior_identity) != prior.get(
        "prior_identity"
    ):
        return "binding prior identity differs from archived payload"
    historical_manifest = binding.get("historical_outer_manifest")
    compact_historical, compact_error = _compact_historical_outer_manifest(
        historical_manifest
    )
    if compact_error or dict(historical_manifest or {}) != compact_historical:
        return "binding historical manifest is malformed or not compact"
    historical_signature = _sha256(
        binding.get("historical_manifest_signature_sha256")
    )
    if historical_signature != _sha256(compact_historical.get("sha256")):
        return "binding historical manifest signature is stale"
    historical_projection = historical_projections.get(historical_signature)
    if historical_projection is None:
        return "binding historical signature has no authenticated semantic snapshot"
    if binding.get("historical_semantic_snapshot_projection") != historical_projection:
        return "binding historical semantic snapshot projection is stale"
    identity = prior.get("prior_identity")
    if not isinstance(identity, Mapping) or historical_signature != identity.get(
        "lean_signature_sha256"
    ):
        return "binding historical signature does not reproduce archived receipt"
    projection, projection_error = _historical_atom_projection(compact_historical)
    if projection_error:
        return "binding historical atom projection is malformed"
    if (
        binding.get("historical_manifest_atom_projection_sha256")
        != projection.get("sha256")
        or binding.get("historical_manifest_atom_sha256s")
        != projection.get("atom_sha256s")
    ):
        return "binding historical atom projection differs from historic manifest"
    observation = {
        "historical_manifest_signature_sha256": historical_signature,
        "historical_manifest_atom_projection_sha256": projection.get("sha256"),
        "historical_outer_manifest": compact_historical,
    }
    if not _historic_observation_matches_snapshot(observation, historical_projection):
        return "binding historical outer interface differs from its authenticated snapshot"
    historical_atoms, historical_atoms_error = _signature_atom_bindings(
        compact_historical
    )
    if historical_atoms_error or binding.get("historical_signature_atom_bindings") != historical_atoms:
        return "binding historical signature-ref mapping is stale"
    prior_entry = prior.get("prior_entry")
    if not isinstance(prior_entry, Mapping):
        return "archived payload is unavailable"
    ledger_error = review_dashboard.semantic_obligation_ledger_error(
        dict(prior_entry), compact_historical
    )
    if ledger_error:
        return "archived semantic obligation ledger is invalid: " + ledger_error
    current_identity = current.get("current_target_identity")
    if (
        not isinstance(current_identity, Mapping)
        or binding.get("current_target_identity") != current_identity
        or binding.get("current_target_identity_sha256")
        != current.get("current_target_identity_sha256")
    ):
        return "binding current target identity is stale"
    for field in (
        "current_source_route_sha256",
        "current_manifest_atom_projection_sha256",
        "current_manifest_outer_binder_sha256",
        "current_semantic_dependency_sha256",
        "current_realization_dependency_sha256",
        "current_semantic_dependency_graph_sha256",
        "current_realization_graph_sha256",
        "current_elaborated_proposition_graph_sha256",
        "current_signature_atom_bindings",
    ):
        if binding.get(field) != current.get(field):
            return f"binding {field} differs from current target evidence"
    if not _historic_snapshot_matches_current(historical_projection, current):
        return "binding historic semantic closure differs from current target evidence"
    if (
        current_identity.get("paper_statement_sha256")
        != identity.get("paper_statement_sha256")
        or current_identity.get("tex_statement_sha256") != identity.get("tex_statement_sha256")
    ):
        return "binding changes source or Lean-to-TeX content"
    atom_transport, transport_error = _atom_transport(
        historical_atoms,
        current.get("current_signature_atom_bindings", []),
    )
    if transport_error or binding.get("atom_transport") != atom_transport:
        return "binding signature-ref transport is stale"
    expected_pair = _historical_pair_sha256(
        paper_statement_sha256=str(identity.get("paper_statement_sha256") or ""),
        tex_statement_sha256=str(identity.get("tex_statement_sha256") or ""),
        historical_manifest_signature_sha256=historical_signature,
        historical_manifest_atom_projection_sha256=str(projection.get("sha256") or ""),
    )
    if binding.get("historical_pair_sha256") != expected_pair:
        return "binding historical content pairing identity is stale"
    return ""


def validate_historical_statement_manifest_replay_static(
    receipt: object,
    *,
    paper: str,
    historical_serializer_recipe: Mapping[str, object],
    prior_sidecar: Mapping[str, object],
    prior_sidecar_bytes: bytes,
    historical_manifest_carrier: Mapping[str, object],
    historical_manifest_carrier_bytes: bytes,
    historical_manifest_authority: Mapping[str, object],
    historical_manifest_authority_bytes: bytes,
    current_targets: Iterable[Mapping[str, object]],
    current_evidence_sha256: str,
    current_target_validator: CurrentTargetValidator | None,
    source_route_validator: SourceRouteValidator | None,
) -> tuple[ValidatedHistoricalStatementManifestReplay | None, str]:
    """Validate a frozen bridge without a second historical Lean invocation.

    This is the normal materialization-time gate.  It validates the exact
    archived sidecar bytes, all current source-route/manifest callbacks, the
    compact historic manifest, its complete semantic-obligation ledger, and
    every old-ref/current-ref rewrite.  Use the explicit replay validator below
    at generation time or when intentionally rechecking the historic runner.
    """

    if not isinstance(receipt, Mapping):
        return None, "historical statement-manifest replay is not an object"
    if receipt.get("schema") != HISTORICAL_STATEMENT_MANIFEST_REPLAY_SCHEMA:
        return None, "historical statement-manifest replay has an unsupported schema"
    if (
        str(receipt.get("artifact_kind") or "").strip()
        != HISTORICAL_STATEMENT_MANIFEST_REPLAY_ARTIFACT_KIND
    ):
        return None, "historical statement-manifest replay has the wrong artifact kind"
    if (
        str(receipt.get("policy_version") or "").strip()
        != HISTORICAL_STATEMENT_MANIFEST_REPLAY_POLICY_VERSION
    ):
        return None, "historical statement-manifest replay has the wrong policy version"
    supplied_digest = _sha256(
        receipt.get(HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD)
    )
    if not supplied_digest or supplied_digest != historical_statement_manifest_replay_digest(
        receipt
    ):
        return None, "historical statement-manifest replay has a stale integrity digest"
    paper = str(paper or "").strip()
    if not paper or receipt.get("paper") != paper:
        return None, "historical statement-manifest replay belongs to a different paper"
    try:
        recipe = _serializer_recipe_payload(historical_serializer_recipe)
    except HistoricalStatementManifestReplayError as exc:
        return None, str(exc)
    if (
        receipt.get("historical_serializer_recipe") != recipe
        or receipt.get("historical_serializer_recipe_sha256") != _digest(recipe)
    ):
        return None, "historical serializer recipe differs from the frozen bridge"
    try:
        from_bytes = _json_object_from_bytes(prior_sidecar_bytes, label="prior statement sidecar")
    except HistoricalStatementManifestReplayError as exc:
        return None, str(exc)
    if from_bytes != dict(prior_sidecar):
        return None, "prior statement sidecar object differs from its exact bytes"
    if str(prior_sidecar.get("paper") or "").strip() != paper:
        return None, "prior statement sidecar belongs to a different paper"
    if receipt.get("prior_sidecar_bytes_sha256") != _bytes_sha256(prior_sidecar_bytes):
        return None, "prior statement sidecar bytes differ from the frozen bridge"
    historical_projections, snapshot_error = _validated_historical_semantic_snapshot(
        receipt.get("historical_semantic_snapshot"),
        paper=paper,
        carrier=historical_manifest_carrier,
        carrier_bytes=historical_manifest_carrier_bytes,
        authority=historical_manifest_authority,
        authority_bytes=historical_manifest_authority_bytes,
    )
    if snapshot_error:
        return None, snapshot_error
    prior_groups, prior_error = _prior_payload_groups(prior_sidecar)
    if prior_error:
        return None, prior_error
    evidence_sha = _sha256(current_evidence_sha256)
    if not evidence_sha or receipt.get("current_evidence_sha256") != evidence_sha:
        return None, "current evidence receipt differs from the frozen bridge"
    targets, targets_error = _validated_current_targets(
        list(current_targets),
        current_target_validator=current_target_validator,
        source_route_validator=source_route_validator,
    )
    if targets_error:
        return None, targets_error
    if receipt.get("current_target_surface_sha256") != _current_target_surface_sha256(
        targets, current_evidence_sha256=evidence_sha
    ):
        return None, "current target surface differs from the frozen bridge"
    bindings = receipt.get("bindings")
    if not isinstance(bindings, list):
        return None, "historical statement-manifest replay has no binding list"
    binding_by_prior: dict[str, Mapping[str, object]] = {}
    bound_current: set[str] = set()
    for binding in bindings:
        if not isinstance(binding, Mapping):
            return None, "historical statement-manifest replay has a non-object binding"
        prior_payload = _sha256(binding.get("prior_entry_payload_sha256"))
        if not prior_payload or prior_payload in binding_by_prior:
            return None, "historical statement-manifest replay has duplicate prior bindings"
        prior = prior_groups.get(prior_payload)
        if prior is None or int(prior.get("occurrences") or 0) != 1:
            return None, "historical statement-manifest replay binds an unavailable archived payload"
        current_identity = binding.get("current_target_identity")
        if not isinstance(current_identity, Mapping):
            return None, "historical statement-manifest replay binding has no current identity"
        try:
            current_id = current_target_identity_sha256(current_identity)
        except HistoricalStatementManifestReplayError as exc:
            return None, str(exc)
        current = targets.get(current_id)
        if current is None or current_id in bound_current:
            return None, "historical statement-manifest replay has ambiguous current target binding"
        if error := _static_binding_error(
            binding,
            prior=prior,
            current=current,
            historical_projections=historical_projections,
        ):
            return None, error
        binding_by_prior[prior_payload] = binding
        bound_current.add(current_id)
    unbridged_prior, unbridged_prior_error = _digest_list(
        receipt.get("unbridged_prior_entry_payload_sha256"),
        label="unbridged prior payloads",
    )
    if unbridged_prior_error or set(unbridged_prior) != set(prior_groups) - set(
        binding_by_prior
    ):
        return None, "unbridged archived payload list is stale"
    unbridged_current, unbridged_current_error = _digest_list(
        receipt.get("unbridged_current_target_identity_sha256"),
        label="unbridged current targets",
    )
    if unbridged_current_error or set(unbridged_current) != set(targets) - bound_current:
        return None, "unbridged current target list is stale"
    return (
        ValidatedHistoricalStatementManifestReplay(
            bindings_by_prior_payload_sha256=binding_by_prior,
            receipt_sha256=supplied_digest,
        ),
        "",
    )


def validate_historical_statement_manifest_replay_replay(
    receipt: object,
    *,
    paper: str,
    historical_serializer_recipe: Mapping[str, object],
    prior_sidecar: Mapping[str, object],
    prior_sidecar_bytes: bytes,
    historical_manifest_carrier: Mapping[str, object],
    historical_manifest_carrier_bytes: bytes,
    historical_manifest_authority: Mapping[str, object],
    historical_manifest_authority_bytes: bytes,
    current_targets: Iterable[Mapping[str, object]],
    current_evidence_sha256: str,
    historical_manifest_runner: HistoricalManifestRunner | None,
    historical_blob_verifier: HistoricalBlobVerifier | None,
    current_target_validator: CurrentTargetValidator | None,
    source_route_validator: SourceRouteValidator | None,
) -> tuple[ValidatedHistoricalStatementManifestReplay | None, str]:
    """Strong validator that deliberately reruns the historic serializer once."""

    raw_targets = list(current_targets)
    context, error = validate_historical_statement_manifest_replay_static(
        receipt,
        paper=paper,
        historical_serializer_recipe=historical_serializer_recipe,
        prior_sidecar=prior_sidecar,
        prior_sidecar_bytes=prior_sidecar_bytes,
        historical_manifest_carrier=historical_manifest_carrier,
        historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
        historical_manifest_authority=historical_manifest_authority,
        historical_manifest_authority_bytes=historical_manifest_authority_bytes,
        current_targets=raw_targets,
        current_evidence_sha256=current_evidence_sha256,
        current_target_validator=current_target_validator,
        source_route_validator=source_route_validator,
    )
    if error or context is None:
        return None, error
    expected, rebuild_error = build_historical_statement_manifest_replay(
        paper=paper,
        historical_serializer_recipe=historical_serializer_recipe,
        prior_sidecar=prior_sidecar,
        prior_sidecar_bytes=prior_sidecar_bytes,
        historical_manifest_carrier=historical_manifest_carrier,
        historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
        historical_manifest_authority=historical_manifest_authority,
        historical_manifest_authority_bytes=historical_manifest_authority_bytes,
        current_targets=raw_targets,
        current_evidence_sha256=current_evidence_sha256,
        historical_manifest_runner=historical_manifest_runner,
        historical_blob_verifier=historical_blob_verifier,
        current_target_validator=current_target_validator,
        source_route_validator=source_route_validator,
    )
    if rebuild_error or expected is None:
        return None, "historical statement-manifest replay cannot be reconstructed: " + rebuild_error
    if dict(receipt) != expected:
        return None, "historical statement-manifest replay differs from exact replay evidence"
    return context, ""


def validate_historical_statement_manifest_replay(
    receipt: object,
    *,
    paper: str,
    historical_serializer_recipe: Mapping[str, object],
    prior_sidecar: Mapping[str, object],
    prior_sidecar_bytes: bytes,
    historical_manifest_carrier: Mapping[str, object],
    historical_manifest_carrier_bytes: bytes,
    historical_manifest_authority: Mapping[str, object],
    historical_manifest_authority_bytes: bytes,
    current_targets: Iterable[Mapping[str, object]],
    current_evidence_sha256: str,
    current_target_validator: CurrentTargetValidator | None,
    source_route_validator: SourceRouteValidator | None,
) -> tuple[ValidatedHistoricalStatementManifestReplay | None, str]:
    """Normal no-rerun alias for the static exact-artifact validator."""

    return validate_historical_statement_manifest_replay_static(
        receipt,
        paper=paper,
        historical_serializer_recipe=historical_serializer_recipe,
        prior_sidecar=prior_sidecar,
        prior_sidecar_bytes=prior_sidecar_bytes,
        historical_manifest_carrier=historical_manifest_carrier,
        historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
        historical_manifest_authority=historical_manifest_authority,
        historical_manifest_authority_bytes=historical_manifest_authority_bytes,
        current_targets=current_targets,
        current_evidence_sha256=current_evidence_sha256,
        current_target_validator=current_target_validator,
        source_route_validator=source_route_validator,
    )


def replay_binding_for_current_target(
    bridge: ValidatedHistoricalStatementManifestReplay | None,
    *,
    prior_entry_payload_sha256: str,
    current_identity: Mapping[str, object],
) -> Mapping[str, object] | None:
    """Return an exact binding only for matching old and current content facts."""

    if not isinstance(bridge, ValidatedHistoricalStatementManifestReplay):
        return None
    prior_payload = _sha256(prior_entry_payload_sha256)
    if not prior_payload:
        return None
    binding = bridge.bindings_by_prior_payload_sha256.get(prior_payload)
    if not isinstance(binding, Mapping):
        return None
    try:
        expected = current_target_identity(current_identity)
    except HistoricalStatementManifestReplayError:
        return None
    recorded = binding.get("current_target_identity")
    if not isinstance(recorded, Mapping):
        return None
    try:
        return binding if current_target_identity(recorded) == expected else None
    except HistoricalStatementManifestReplayError:
        return None
