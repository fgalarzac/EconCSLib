#!/usr/bin/env python3
"""Extract name-independent reviewed-declaration manifests with Lean.

The helper asks Lean for each declaration's elaborated type, traverses every
outer Pi binder after reducible head unfolding, and emits one atom per binder
plus one atom for the final result. For definitions and abbreviations, that
result atom includes the instantiated value as well as its type. For inductive,
structure, and class declarations, it includes name-independent constructor
types. Theorem and opaque proof bodies remain excluded. Python never parses
pretty-printed Lean.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import signal
import shutil
import subprocess
import sys
import tempfile
from copy import deepcopy
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Mapping


HELPER_PATH = Path(__file__).with_name("lean_signature_manifest_helper.lean")
COMPILED_AUDIT_HELPER_MODULE = "EconCSLib.Audit.SignatureManifest"
COMPILED_AUDIT_HELPER_SOURCE = Path("EconCSLib") / "Audit" / "SignatureManifest.lean"
CLOSURE_SUBPROCESS_TRAMPOLINE_PATH = Path(__file__).with_name(
    "lean_closure_subprocess.py"
)
SENTINEL = "LEAN_SIGNATURE_MANIFEST:"
SIGNATURE_MANIFEST_REVALIDATION_SENTINEL = "LEAN_SIGNATURE_MANIFEST_REVALIDATION:"
PROPOSITION_SPEC_PROOF_SENTINEL = "LEAN_PROPOSITION_SPEC_PROOF_MATCH:"
SEMANTIC_CONTRACT_SENTINEL = "LEAN_SEMANTIC_CONTRACT_MATCH:"
OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_SENTINEL = "LEAN_OPERATIONAL_OUTCOME_DOMAIN_BRIDGE:"
OperationalOutcomeDomainRoute = tuple[str, str, int, int, int, int, str, str]
OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_SENTINEL = (
    "LEAN_OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE:"
)
OperationalOutcomeStateTransitionRoute = tuple[
    str, str, str, int, int, int, int, int, int, str, str, str
]
SEMANTIC_CONTRACT_TRANSPARENCY_SENTINEL = "LEAN_SEMANTIC_CONTRACT_TRANSPARENCY:"
SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_SCHEMA = 1
SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_SCHEMA = 1
SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_FIELD = (
    "semantic_contract_executable_terminal_receipts"
)
SEMANTIC_CONTRACT_CLOSURE_SENTINEL = "LEAN_SEMANTIC_CONTRACT_CLOSURE:"
SEMANTIC_CONTRACT_CLOSURE_ERROR_SENTINEL = "LEAN_SEMANTIC_CONTRACT_CLOSURE_ERROR:"
SOURCE_PREMISE_FALSE_SCAN_SENTINEL = "LEAN_SOURCE_PREMISE_FALSE_SCAN:"
CONSTRUCTOR_RESULT_TYPE_MATCH_SENTINEL = "LEAN_CONSTRUCTOR_RESULT_TYPE_MATCH:"
RECURSIVE_FIELD_PROPOSITION_SORT_SENTINEL = "LEAN_RECURSIVE_FIELD_PROPOSITION_SORT:"
CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL = "LEAN_CONSTRUCTOR_FIELD_SLOT_COUNTS:"
INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL = (
    "LEAN_INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS:"
)
TYPE_WITNESS_PAYLOAD_SAFETY_SENTINEL = "LEAN_TYPE_WITNESS_PAYLOAD_SAFETY:"
DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL = (
    "LEAN_DIRECT_LIBRARY_DEPENDENCY_SURFACE:"
)
DIRECT_LIBRARY_DEPENDENCY_SURFACE_SCHEMA = 1
TRANSPARENT_PAPER_SPEC_DISPLAY_SENTINEL = "LEAN_TRANSPARENT_PAPER_SPEC_DISPLAY:"
TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA = 1
TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL = (
    "LEAN_TRANSPARENT_PAPER_DECLARATION_DISPLAY:"
)
TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA = 1
TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL = (
    "LEAN_TRANSPARENT_LIBRARY_DECLARATION_DISPLAY:"
)
TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA = 1
TYPE_WITNESS_PAYLOAD_SAFETY_SCHEMA = 1
RECURSIVE_FIELD_SAFETY_LOCATOR_SCHEMA = 1
RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA = 1
FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION = "foundation-structural-data-v4"
FOUNDATION_STRUCTURAL_DATA_HEADS = (
    ("Nat", "Init.Prelude"),
    ("Int", "Init.Prelude"),
    ("Finset", "Mathlib.Data.Finset.Defs"),
    ("List", "Init.Prelude"),
    ("Array", "Init.Prelude"),
    ("Option", "Init.Prelude"),
    ("Prod", "Init.Prelude"),
    ("Sum", "Init.Prelude"),
    ("Bool", "Init.Prelude"),
    ("Char", "Init.Prelude"),
    ("String", "Init.Prelude"),
    ("Float", "Init.Prelude"),
    ("UInt8", "Init.Prelude"),
    ("UInt16", "Init.Prelude"),
    ("UInt32", "Init.Prelude"),
    ("UInt64", "Init.Prelude"),
    ("USize", "Init.Prelude"),
    ("Real", "Mathlib.Data.Real.Basic"),
    ("NNReal", "Mathlib.Data.NNReal.Defs"),
)
FOUNDATION_STRUCTURAL_DATA_MODULE_BY_HEAD = dict(FOUNDATION_STRUCTURAL_DATA_HEADS)
FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256 = hashlib.sha256(
    json.dumps(
        {
            "version": FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION,
            "heads": FOUNDATION_STRUCTURAL_DATA_HEADS,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
).hexdigest()
MANIFEST_SCHEMA = 2
ATOM_ROLES = {"parameter", "assumption", "conclusion"}
TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA = 1
TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION = (
    "definition_value_outer_telescope"
)
DECLARATION_KINDS = {
    "axiom",
    "definition",
    "theorem",
    "opaque",
    "quotient",
    "inductive",
    "constructor",
    "recursor",
}
SEMANTIC_DEPENDENCY_TAGS = {
    "inlined_definition",
    "internal_proof",
    "local_theorem",
    "local_inductive",
    "local_constructor",
    "local_recursor",
    "local_opaque",
    "local_axiom",
}
SEMANTIC_DEPENDENCY_GRAPH_SCHEMA = 1
SEMANTIC_DEPENDENCY_MANIFEST_SCHEMA = 1
SEMANTIC_DEPENDENCY_GRAPH_ORIGINS = {
    "review_closure",
    "imported_terminal",
    "unresolved",
}
MAX_COMPACT_CANONICAL_BYTES = 1_000_000
# The signature manifest may expand local structures and inductives while
# preserving an exact Lean-owned canonical type tree.  Keep the supplemental
# execution/refinement scan bounded as well: it is a review trigger, never a
# substitute for checking a proof or executing a transition system.
EXECUTION_STATE_REFINEMENT_SHAPE_SCHEMA = 2
EXECUTION_STATE_REFINEMENT_SHAPE_DETECTOR_BASIS = (
    "lean_statement_dependency_graph_structural_v1"
)
MAX_EXECUTION_STATE_REFINEMENT_CANONICAL_NODES = 100_000
_REFL_TRANS_GEN_CONSTANT = "Relation.ReflTransGen"
# A non-chunked failed bulk run may isolate a few malformed or unusually
# expensive rows, but it must not fan out without bound for a paper. Residuals
# below this cap are bisected, so successful siblings stay batched and only an
# unresolved leaf reaches a singleton process.
MAX_INDIVIDUAL_MANIFEST_RETRIES = 8
# A Lean signature request materializes an elaborated dependency graph. Its
# peak memory is governed by that graph, not declaration spelling or source
# length, so co-locating even unrelated rows can exceed a constrained host's
# memory budget. Run one exact row per Lean process by default. Machines with
# measured headroom may opt into a deterministic larger capacity via
# `ECONCSLIB_MANIFEST_BATCH_SIZE`; this changes scheduling only, never a
# manifest's inputs, signatures, or cache authority.
DEFAULT_MANIFEST_BATCH_SIZE = 1
MAX_MANIFEST_BATCH_SIZE = 64
MANIFEST_BATCH_SIZE_ENV = "ECONCSLIB_MANIFEST_BATCH_SIZE"
MIN_CHUNKED_MANIFEST_REQUEST_ROWS = DEFAULT_MANIFEST_BATCH_SIZE + 1
# Progress events are operational diagnostics only.  They intentionally omit
# declaration names and are never incorporated into a manifest, cache key, or
# source-record receipt.
MANIFEST_PROGRESS_EVENT_SCHEMA = 1
# The value below is a per-declaration share, not a whole-batch cap. A chunk's
# wall budget scales with its exact row count up to the caller's bound; treating
# four additive traversals as one 60-second task caused avoidable timeouts and
# repeated Lean startup. Residual retries bisect only missing rows.
MAX_CHUNKED_MANIFEST_TIMEOUT_SECONDS = 60
# A recursive model surface can contain hundreds of Lean-owned constructor or
# projection slots. Passing them through one JSON command makes the helper fail
# as a unit, which would erase independent safety receipts. Keep this separate
# from declaration manifests because the payload is substantially larger.
RECURSIVE_FIELD_SAFETY_CHUNK_SIZE = 24
MAX_RECURSIVE_FIELD_SAFETY_CHUNKS = 32
MAX_CHUNKED_RECURSIVE_FIELD_SAFETY_TIMEOUT_SECONDS = 60
# Type-witness result traversal can recurse through proposition wrappers.  One
# exhausted traversal must not make every independently reviewed declaration
# disappear from the audit result.  Partition only by exact request count; a
# declaration's spelling or source text never selects a retry path.
TYPE_WITNESS_PAYLOAD_SAFETY_CHUNK_SIZE = 4
MAX_TYPE_WITNESS_PAYLOAD_SAFETY_CHUNKS = 32
MAX_CHUNKED_TYPE_WITNESS_PAYLOAD_SAFETY_TIMEOUT_SECONDS = 60
# Exact-contract matching and the transparency gate each elaborate the helper
# once per generated script.  Keep their paper-closeout requests bounded
# independently of the signature-manifest batching policy above.  These are
# capacity bounds, not declaration-name filters: every requested route or Spec
# receives the identical Lean-owned check.
SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE = 8
MIN_CHUNKED_SEMANTIC_CONTRACT_MATCH_ROUTES = 16
MAX_SEMANTIC_CONTRACT_MATCH_CHUNKS = 32
MAX_CHUNKED_SEMANTIC_CONTRACT_MATCH_TIMEOUT_SECONDS = 60
SEMANTIC_CONTRACT_TRANSPARENCY_CHUNK_SIZE = 4
MIN_CHUNKED_SEMANTIC_CONTRACT_TRANSPARENCY_ROWS = 16
MAX_SEMANTIC_CONTRACT_TRANSPARENCY_CHUNKS = 32
SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE = 4
MIN_CHUNKED_SEMANTIC_CONTRACT_CLOSURE_ROWS = 16
MAX_SEMANTIC_CONTRACT_CLOSURE_CHUNKS = 32
# Production closure surfaces are compact fingerprint receipts. This hard cap
# keeps a helper regression from materializing recursive canonical trees in a
# Python process or temporary artifact before the parser can reject them.
MAX_SEMANTIC_CONTRACT_CLOSURE_OUTPUT_BYTES = 8 * 1024 * 1024
SEMANTIC_CONTRACT_CLOSURE_OUTPUT_LIMIT_SENTINEL = (
    "LEAN_SEMANTIC_CONTRACT_CLOSURE_OUTPUT_LIMIT:"
)
# The Lean closure helper traverses elaborated expressions.  Its semantic work
# is bounded separately by `max_expansions`, but unbounded Lean recursion and
# heartbeat limits can exhaust the host before the subprocess wall timeout can
# return a useful failure.  These are operational limits only: an exhausted
# run fails closed and records an actionable diagnostic rather than changing a
# closure's semantics or accepting a partial receipt.
SEMANTIC_CONTRACT_CLOSURE_MAX_RECURSION_DEPTH = 4096
SEMANTIC_CONTRACT_CLOSURE_MAX_HEARTBEATS = 8_000_000
# Lean reserves a large virtual heap when importing a large compiled paper
# interface.  The closure route uses one worker and a 4 GiB Lean cap: enough
# for the largest current interface import, while avoiding the old 6 GiB cap
# that could let the host terminate a child before Lean returned a fail-closed
# diagnostic.  The recursive walk itself is Lean's compact environment utility
# and no longer materializes a second expanded closure tree.
SEMANTIC_CONTRACT_CLOSURE_MAX_MEMORY_MB = 4096
SEMANTIC_CONTRACT_CLOSURE_MAX_THREADS = 1
SEMANTIC_CONTRACT_CLOSURE_MAX_ADDRESS_SPACE_BYTES = 12 * 1024 * 1024 * 1024
SEMANTIC_CONTRACT_CLOSURE_RUNNER_FAILURE_SENTINEL = (
    "LEAN_SEMANTIC_CONTRACT_CLOSURE_RUNNER_FAILURE:"
)
LEAN_SIGNATURE_MANIFEST_TIMEOUT_SENTINEL = "LEAN_SIGNATURE_MANIFEST_TIMEOUT:"
_CACHE: dict[
    tuple[str, str, tuple[int, int], tuple[int, int], str, str, tuple[str, ...]],
    dict[str, dict[str, Any]],
] = {}
# This is deliberately narrower than the full-manifest cache.  A compact
# revalidation receipt can only avoid a duplicate request within the same
# Python process after the complete compiled-context coordinate has matched.
# It is neither persisted nor used as a manifest carrier or audit authority.
_MANIFEST_REVALIDATION_RECEIPT_CACHE: dict[
    tuple[tuple[Any, ...], str], dict[str, Any]
] = {}
_PROPOSITION_SPEC_PROOF_CACHE: dict[
    tuple[str, str, tuple[int, int], tuple[int, int], tuple[tuple[str, str], ...]],
    dict[tuple[str, str], bool],
] = {}
_SEMANTIC_CONTRACT_CACHE: dict[
    tuple[str, str, tuple[int, int], tuple[int, int], tuple[tuple[str, str, str], ...]],
    dict[tuple[str, str, str], bool],
] = {}
_OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_CACHE: dict[
    tuple[
        str,
        str,
        tuple[int, int],
        tuple[int, int],
        tuple[OperationalOutcomeDomainRoute, ...],
    ],
    dict[OperationalOutcomeDomainRoute, bool],
] = {}
_OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_CACHE: dict[
    tuple[
        str,
        str,
        tuple[int, int],
        tuple[int, int],
        tuple[OperationalOutcomeStateTransitionRoute, ...],
    ],
    dict[OperationalOutcomeStateTransitionRoute, bool],
] = {}
_SEMANTIC_CONTRACT_TRANSPARENCY_CACHE: dict[
    tuple[
        str,
        str,
        tuple[int, int],
        tuple[int, int],
        tuple[tuple[str, tuple[int, int] | None], ...],
        tuple[str, ...],
        tuple[str, ...],
        int,
    ],
    dict[str, dict[str, Any]],
] = {}
_SEMANTIC_CONTRACT_CLOSURE_CACHE: dict[
    tuple[
        str,
        str,
        tuple[int, int],
        tuple[int, int],
        tuple[tuple[str, tuple[int, int] | None], ...],
        str,
        tuple[str, ...],
        tuple[str, ...],
        tuple[str, ...],
        str,
        str,
        int,
    ],
    dict[str, dict[str, Any]],
] = {}
# Structural checks cache one exact Lean-owned query at a time.  The first key
# component is a mutation-checked environment identity over current repository
# sources, build controls, the complete repository import-artifact closure,
# and the Lean helper.  Names below are therefore routing coordinates inside
# an already authenticated environment, never semantic cache authority by
# themselves.
_SOURCE_PREMISE_FALSE_SCAN_CACHE: dict[
    tuple[str, tuple[str, ...], str], list[dict[str, Any]]
] = {}
_CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE: dict[
    tuple[str, str, str, tuple[str, str, str]], bool
] = {}
_RECURSIVE_FIELD_PROPOSITION_SORT_CACHE: dict[tuple[str, str], dict[str, object]] = {}
_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE: dict[tuple[str, str], int] = {}
_INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE: dict[
    tuple[str, str], dict[str, int]
] = {}
_TYPE_WITNESS_PAYLOAD_SAFETY_CACHE: dict[tuple[str, str], list[dict[str, object]]] = {}
_SUCCESSFUL_BUILD_SNAPSHOT_CACHE: dict[
    tuple[str, str],
    tuple[str, tuple[tuple[str, tuple[str, int]], ...]],
] = {}
_LEAN_LOADED_MODULE_CLOSURE_CACHE: dict[tuple[str, str, str], tuple[str, ...]] = {}


def _compact_canonical(value: Any, *, preserve_root_definition: bool = False) -> Any:
    """Replace expanded dependency closures with name-free semantic fingerprints."""

    if isinstance(value, list):
        return [_compact_canonical(item) for item in value]
    if not isinstance(value, dict):
        return value
    compact = {key: _compact_canonical(item) for key, item in value.items()}
    tag = str(compact.get("tag") or "")
    if tag in SEMANTIC_DEPENDENCY_TAGS and not (
        preserve_root_definition and tag == "definition"
    ):
        if set(compact) == {"tag", "sha256"} and re.fullmatch(
            r"[0-9a-f]{64}", str(compact.get("sha256") or "")
        ):
            return compact
        encoded = json.dumps(
            compact, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
        return {"tag": tag, "sha256": hashlib.sha256(encoded).hexdigest()}
    return compact


def _semantic_json_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


_ELABORATED_PROPOSITION_NODE_KINDS = {
    "forall",
    "implication",
    "conjunction",
    "iff",
    "exists",
    "negation",
    "transparent_wrapper",
    "application",
    "lambda",
    "let",
    "metadata",
    "projection",
    "constant",
    "free_variable",
    "bound_variable",
    "sort",
    "literal",
    "metavariable",
}
_ELABORATED_PROPOSITION_EDGE_ROLES = {
    "antecedent",
    "consequent",
    "domain",
    "body",
    "left",
    "right",
    "function",
    "argument",
    "expanded_body",
    "type",
    "value",
    "projected",
}


def normalize_elaborated_proposition_graph(value: object) -> dict[str, Any] | None:
    """Validate Lean's rooted connective DAG and attach a name-free digest."""

    if not isinstance(value, Mapping) or str(value.get("schema")) != "1":
        return None
    complete = value.get("complete")
    raw_nodes = value.get("nodes")
    raw_edges = value.get("edges")
    raw_failures = value.get("failures", [])
    if (
        not isinstance(complete, bool)
        or not isinstance(raw_nodes, list)
        or not isinstance(raw_edges, list)
        or not isinstance(raw_failures, list)
    ):
        return None
    nodes: list[dict[str, Any]] = []
    paths: set[str] = set()
    for raw in raw_nodes:
        if not isinstance(raw, Mapping):
            return None
        path = str(raw.get("path") or "").strip()
        kind = str(raw.get("kind") or "").strip()
        canonical = raw.get("canonical")
        supplied_sha = str(raw.get("semantic_sha256") or "").strip().lower()
        if (
            not path
            or path in paths
            or kind not in _ELABORATED_PROPOSITION_NODE_KINDS
            or (
                not isinstance(canonical, Mapping)
                and not re.fullmatch(r"[0-9a-f]{64}", supplied_sha)
            )
        ):
            return None
        compact = (
            _compact_canonical(canonical) if isinstance(canonical, Mapping) else None
        )
        semantic_sha = (
            _semantic_json_sha256({"kind": kind, "canonical": compact})
            if compact is not None
            else supplied_sha
        )
        if supplied_sha and supplied_sha != semantic_sha:
            return None
        node: dict[str, Any] = {
            "path": path,
            "kind": kind,
            "semantic_sha256": semantic_sha,
        }
        # The normalized graph is a semantic receipt, not a second pretty
        # printer for every subexpression. The exact canonical node is
        # validated above and retained through its digest; omitting the raw
        # duplicate keeps large paper statements bounded and still makes any
        # node or topology change alter the aggregate graph identity.
        nodes.append(node)
        paths.add(path)
    if "result" not in paths:
        return None
    edges: list[dict[str, str]] = []
    edge_keys: set[tuple[str, str, str]] = set()
    incoming: dict[str, int] = {path: 0 for path in paths}
    adjacency: dict[str, list[str]] = {}
    for raw in raw_edges:
        if not isinstance(raw, Mapping):
            return None
        source = str(raw.get("source") or "").strip()
        target = str(raw.get("target") or "").strip()
        role = str(raw.get("role") or "").strip()
        key = (source, target, role)
        if (
            source not in paths
            or target not in paths
            or role not in _ELABORATED_PROPOSITION_EDGE_ROLES
            or key in edge_keys
        ):
            return None
        edge_keys.add(key)
        incoming[target] += 1
        adjacency.setdefault(source, []).append(target)
        edges.append({"source": source, "target": target, "role": role})
    if incoming["result"] != 0 or any(
        count < 1 for path, count in incoming.items() if path != "result"
    ):
        return None
    reachable = {"result"}
    pending = ["result"]
    while pending:
        source = pending.pop()
        for target in adjacency.get(source, []):
            if target not in reachable:
                reachable.add(target)
                pending.append(target)
    if reachable != paths:
        return None
    # Reachability alone does not rule out a back-edge into an already reached
    # semantic state. Kahn's algorithm keeps this check iterative for graphs
    # near the Lean traversal bound and counts distinct role-labelled edges.
    remaining_incoming = dict(incoming)
    ready = ["result"]
    processed = 0
    while ready:
        source = ready.pop()
        processed += 1
        for target in adjacency.get(source, []):
            remaining_incoming[target] -= 1
            if remaining_incoming[target] == 0:
                ready.append(target)
    if processed != len(paths):
        return None
    failures: list[dict[str, str]] = []
    for raw in raw_failures:
        if not isinstance(raw, Mapping):
            return None
        path = str(raw.get("path") or "").strip()
        tag = str(raw.get("tag") or "").strip()
        if not path or not tag:
            return None
        failures.append({"path": path, "tag": tag})
    if complete != (not failures):
        return None
    semantic_payload = {
        "schema": 1,
        "complete": complete,
        "nodes": sorted(
            (
                {
                    "path": node["path"],
                    "kind": node["kind"],
                    "semantic_sha256": node["semantic_sha256"],
                }
                for node in nodes
            ),
            key=lambda item: item["path"],
        ),
        "edges": sorted(
            edges, key=lambda item: (item["source"], item["target"], item["role"])
        ),
        "failure_tags": sorted(failure["tag"] for failure in failures),
    }
    computed_graph_sha = _semantic_json_sha256(semantic_payload)
    supplied_graph_sha = str(value.get("semantic_graph_sha256") or "").strip().lower()
    if supplied_graph_sha and supplied_graph_sha != computed_graph_sha:
        return None
    return {
        "schema": 1,
        "complete": complete,
        "nodes": sorted(nodes, key=lambda item: item["path"]),
        "edges": semantic_payload["edges"],
        "failures": sorted(failures, key=lambda item: (item["path"], item["tag"])),
        "semantic_graph_sha256": computed_graph_sha,
    }


def normalize_semantic_dependency_graph(value: object) -> dict[str, Any] | None:
    """Validate Lean's dependency graph and derive a spelling-free digest."""

    if not isinstance(value, Mapping) or str(value.get("schema")) != str(
        SEMANTIC_DEPENDENCY_GRAPH_SCHEMA
    ):
        return None
    root = str(value.get("root_declaration") or "").strip()
    complete = value.get("complete")
    protocol_complete = value.get("realization_complete", complete)
    raw_nodes = value.get("nodes")
    raw_edges = value.get("edges")
    raw_failures = value.get("failures")
    raw_semantic_external_origins = value.get("semantic_external_module_origins", [])
    raw_realization_external_origins = value.get(
        "realization_external_module_origins", []
    )
    if (
        not root
        or not isinstance(complete, bool)
        or not isinstance(protocol_complete, bool)
        or not isinstance(raw_nodes, list)
        or not isinstance(raw_edges, list)
        or not isinstance(raw_failures, list)
        or not isinstance(raw_semantic_external_origins, list)
        or not isinstance(raw_realization_external_origins, list)
    ):
        return None
    semantic_external_origins = [
        str(origin).strip() for origin in raw_semantic_external_origins
    ]
    realization_external_origins = [
        str(origin).strip() for origin in raw_realization_external_origins
    ]
    if (
        any(not origin for origin in semantic_external_origins)
        or any(not origin for origin in realization_external_origins)
        or len(set(semantic_external_origins)) != len(semantic_external_origins)
        or len(set(realization_external_origins)) != len(realization_external_origins)
        or not set(semantic_external_origins).issubset(realization_external_origins)
    ):
        return None
    nodes: list[dict[str, Any]] = []
    node_semantics: dict[str, str] = {}
    for raw in raw_nodes:
        if not isinstance(raw, Mapping):
            return None
        declaration = str(raw.get("declaration") or "").strip()
        module_origin = str(raw.get("module_origin") or "").strip()
        origin_class = str(raw.get("origin_class") or "").strip()
        kind = str(raw.get("declaration_kind") or "").strip()
        identity = raw.get("canonical_identity")
        pre_normalized_sha = (
            str(raw.get("semantic_identity_sha256") or "").strip().lower()
        )
        if (
            not declaration
            or declaration in node_semantics
            or not module_origin
            or origin_class not in SEMANTIC_DEPENDENCY_GRAPH_ORIGINS
            or kind not in DECLARATION_KINDS
            or (
                not isinstance(identity, Mapping)
                and not re.fullmatch(r"[0-9a-f]{64}", pre_normalized_sha)
            )
        ):
            return None
        compact_identity = (
            _compact_canonical(identity) if isinstance(identity, Mapping) else None
        )
        semantic_sha = (
            _semantic_json_sha256(
                {
                    "origin_class": origin_class,
                    "declaration_kind": kind,
                    "canonical_identity": compact_identity,
                }
            )
            if compact_identity is not None
            else pre_normalized_sha
        )
        if pre_normalized_sha and pre_normalized_sha != semantic_sha:
            return None
        node_semantics[declaration] = semantic_sha
        node = {
            "declaration": declaration,
            "module_origin": module_origin,
            "origin_class": origin_class,
            "declaration_kind": kind,
            "semantic_identity_sha256": semantic_sha,
        }
        # The canonical identity has been validated and reduced to the exact
        # digest above. Graph consumers need origin, kind, reachability, and
        # topology; retaining every raw expression would duplicate much of the
        # outer signature and can dominate manifests for local inductives.
        nodes.append(node)
    if root not in node_semantics:
        return None
    edges: list[dict[str, str]] = []
    semantic_edges: list[dict[str, str]] = []
    dangling_targets: set[str] = set()
    for raw in raw_edges:
        if not isinstance(raw, Mapping):
            return None
        source = str(raw.get("source") or "").strip()
        target = str(raw.get("target") or "").strip()
        role = str(raw.get("role") or "").strip()
        if source not in node_semantics or not target or not role:
            return None
        edges.append({"source": source, "target": target, "role": role})
        if target in node_semantics:
            semantic_edges.append(
                {
                    "source_semantic_sha256": node_semantics[source],
                    "target_semantic_sha256": node_semantics[target],
                    "role": role,
                }
            )
        else:
            dangling_targets.add(target)
    failures: list[dict[str, str]] = []
    for raw in raw_failures:
        if not isinstance(raw, Mapping):
            return None
        tag = str(raw.get("tag") or "").strip()
        declaration = str(raw.get("declaration") or "").strip()
        if not tag or not declaration:
            return None
        failures.append({"tag": tag, "declaration": declaration})
    if protocol_complete != (not failures):
        return None
    statement_adjacency: dict[str, set[str]] = {}
    for edge in edges:
        if edge["role"] == "proof_uses_constant":
            continue
        statement_adjacency.setdefault(edge["source"], set()).add(edge["target"])
    statement_reachable = {root}
    pending = [root]
    while pending:
        source = pending.pop()
        for target in statement_adjacency.get(source, set()):
            if target not in statement_reachable:
                statement_reachable.add(target)
                pending.append(target)
    for node in nodes:
        node["statement_reachable"] = node["declaration"] in statement_reachable
    statement_semantic_edges = []
    realization_semantic_edges = []
    for raw_edge in edges:
        source_semantic = node_semantics.get(raw_edge["source"])
        target_semantic = node_semantics.get(raw_edge["target"])
        if source_semantic is None or target_semantic is None:
            continue
        semantic_edge = {
            "source_semantic_sha256": source_semantic,
            "target_semantic_sha256": target_semantic,
            "role": raw_edge["role"],
        }
        realization_semantic_edges.append(semantic_edge)
        if (
            raw_edge["role"] != "proof_uses_constant"
            and raw_edge["source"] in statement_reachable
            and raw_edge["target"] in statement_reachable
        ):
            statement_semantic_edges.append(semantic_edge)
    semantic_failure_tags = sorted(
        {
            failure["tag"]
            for failure in failures
            if failure["declaration"] in statement_reachable
        }
        | (
            {"unresolved_statement_dependency"}
            if dangling_targets & statement_reachable
            else set()
        )
    )
    semantic_complete = not semantic_failure_tags
    realization_complete = protocol_complete and not dangling_targets
    semantic_payload = {
        "schema": SEMANTIC_DEPENDENCY_GRAPH_SCHEMA,
        "complete": semantic_complete,
        "root_semantic_sha256": node_semantics[root],
        "node_semantic_sha256": sorted(
            node_semantics[name]
            for name in statement_reachable
            if name in node_semantics
        ),
        "edges": sorted(
            statement_semantic_edges,
            key=lambda item: (
                item["source_semantic_sha256"],
                item["target_semantic_sha256"],
                item["role"],
            ),
        ),
        "failure_tags": semantic_failure_tags,
    }
    realization_payload = {
        "schema": SEMANTIC_DEPENDENCY_GRAPH_SCHEMA,
        "complete": realization_complete,
        "root_semantic_sha256": node_semantics[root],
        "node_semantic_sha256": sorted(node_semantics.values()),
        "edges": sorted(
            realization_semantic_edges,
            key=lambda item: (
                item["source_semantic_sha256"],
                item["target_semantic_sha256"],
                item["role"],
            ),
        ),
        "failure_tags": sorted(failure["tag"] for failure in failures),
    }
    computed_semantic_sha = _semantic_json_sha256(semantic_payload)
    computed_realization_sha = _semantic_json_sha256(realization_payload)
    supplied_semantic_sha = (
        str(value.get("semantic_graph_sha256") or "").strip().lower()
    )
    supplied_realization_sha = (
        str(value.get("realization_graph_sha256") or "").strip().lower()
    )
    if (supplied_semantic_sha and supplied_semantic_sha != computed_semantic_sha) or (
        supplied_realization_sha
        and supplied_realization_sha != computed_realization_sha
    ):
        return None
    return {
        "schema": SEMANTIC_DEPENDENCY_GRAPH_SCHEMA,
        "root_declaration": root,
        "complete": semantic_complete,
        "realization_complete": realization_complete,
        "nodes": sorted(nodes, key=lambda item: item["declaration"]),
        "edges": sorted(
            edges, key=lambda item: (item["source"], item["target"], item["role"])
        ),
        "failures": sorted(
            failures, key=lambda item: (item["tag"], item["declaration"])
        ),
        "semantic_external_module_origins": sorted(semantic_external_origins),
        "realization_external_module_origins": sorted(realization_external_origins),
        "semantic_graph_sha256": computed_semantic_sha,
        "realization_graph_sha256": computed_realization_sha,
    }


def _canonical_is_prop_sort(value: object) -> bool:
    """Whether a canonical expression is the elaborated ``Prop`` sort.

    This deliberately distinguishes a relation *value* of type
    ``state -> state -> Prop`` from a proof-valued universal statement whose
    final expression merely has proposition sort.  It operates on Lean's
    canonical expression protocol, not pretty-printed source text.
    """

    return bool(
        isinstance(value, Mapping)
        and value.get("tag") == "sort"
        and isinstance(value.get("level"), Mapping)
        and value["level"].get("tag") == "zero"
    )


def _canonical_lift_bound_indices(
    value: object, *, amount: int, cutoff: int = 0
) -> object:
    """Lift canonical de-Bruijn indices through one or more binders.

    The two domains of an elaborated ``state -> state -> Prop`` relation are
    serialized at adjacent binder depths.  Their shared outer state type is
    therefore shifted by one index in the second domain.  This small canonical
    operation compares the domains modulo that ordinary binder shift without
    consulting display names.
    """

    if isinstance(value, list):
        return [
            _canonical_lift_bound_indices(item, amount=amount, cutoff=cutoff)
            for item in value
        ]
    if not isinstance(value, Mapping):
        return value
    tag = value.get("tag")
    if tag == "bvar":
        raw_index = str(value.get("index") or "")
        if raw_index.isdigit() and int(raw_index) >= cutoff:
            lifted = dict(value)
            lifted["index"] = str(int(raw_index) + amount)
            return lifted
    lifted = {}
    for key, item in value.items():
        nested_cutoff = cutoff
        if tag in {"forall", "lam"} and key == "body":
            nested_cutoff += 1
        elif tag == "let" and key == "body":
            nested_cutoff += 1
        lifted[key] = _canonical_lift_bound_indices(
            item, amount=amount, cutoff=nested_cutoff
        )
    return lifted


def _canonical_relation_valued_state_transition(value: object) -> bool:
    """Recognize an elaborated endorelation ending in the ``Prop`` sort.

    A state transition may carry action parameters before its two state
    endpoints, so inspect the complete Pi chain and require two adjacent,
    structurally identical endpoint domains immediately before ``Prop``.
    The comparison is alpha-invariant because Lean has already converted all
    bound variables to canonical indices.  No declaration, record, binder, or
    field name participates in this decision.
    """

    domains: list[object] = []
    current = value
    while isinstance(current, Mapping) and current.get("tag") == "forall":
        domain = current.get("domain")
        body = current.get("body")
        if domain is None or body is None:
            return False
        domains.append(domain)
        current = body
    return bool(
        len(domains) >= 2
        and _canonical_is_prop_sort(current)
        and domains[-1] == _canonical_lift_bound_indices(domains[-2], amount=1)
    )


def _legacy_elaborated_execution_state_refinement_shape(
    manifest: Mapping[str, Any],
) -> dict[str, object]:
    """Read the legacy bounded shape from pre-schema-2 canonical atoms.

    The scan is deliberately limited to two mathematical structures:

    * the standard ``Relation.ReflTransGen`` reachability constructor; and
    * a relation-valued state transition, recognized by its elaborated
      endorelation type rather than a local field/function name.

    This fallback exists only for manifests produced before Lean emitted the
    generalized structural summary. New manifests never use a declaration
    name as evidence.
    """

    raw_atoms = manifest.get("atoms")
    roots: list[object] = []
    if isinstance(raw_atoms, list):
        for atom in raw_atoms:
            if isinstance(atom, Mapping) and atom.get("canonical") is not None:
                roots.append(atom["canonical"])

    stack = list(reversed(roots))
    nodes_seen = 0
    has_refl_trans_gen_path = False
    has_relation_valued_transition = False
    while stack and nodes_seen < MAX_EXECUTION_STATE_REFINEMENT_CANONICAL_NODES:
        current = stack.pop()
        nodes_seen += 1
        if isinstance(current, Mapping):
            if (
                current.get("tag") == "const"
                and current.get("name") == _REFL_TRANS_GEN_CONSTANT
            ):
                has_refl_trans_gen_path = True
            if _canonical_relation_valued_state_transition(current):
                has_relation_valued_transition = True
            stack.extend(
                value
                for value in current.values()
                if isinstance(value, (Mapping, list))
            )
        elif isinstance(current, list):
            stack.extend(reversed(current))

    scan_complete = not stack
    detected = (
        has_refl_trans_gen_path and has_relation_valued_transition and scan_complete
    )
    return {
        "schema": 1,
        "scan_complete": scan_complete,
        "canonical_nodes_scanned": nodes_seen,
        "has_refl_trans_gen_path": has_refl_trans_gen_path,
        "has_relation_valued_state_transition": has_relation_valued_transition,
        "detected": detected,
    }


def _normalize_execution_state_refinement_shape(
    value: object,
) -> dict[str, object] | None:
    """Validate Lean's compact structural execution/refinement summary."""

    if not isinstance(value, Mapping):
        return None
    try:
        schema = int(str(value.get("schema") or ""))
    except ValueError:
        return None
    if schema not in {1, EXECUTION_STATE_REFINEMENT_SHAPE_SCHEMA}:
        return None
    scan_complete = value.get("scan_complete")
    has_path = value.get("has_refl_trans_gen_path")
    has_transition = value.get("has_relation_valued_state_transition")
    detected = value.get("detected")
    if not all(
        isinstance(flag, bool)
        for flag in (scan_complete, has_path, has_transition, detected)
    ) or detected != (scan_complete and has_path and has_transition):
        return None
    raw_nodes_scanned = value.get("canonical_nodes_scanned", 0)
    if isinstance(raw_nodes_scanned, bool):
        return None
    try:
        nodes_scanned = int(str(raw_nodes_scanned))
    except ValueError:
        return None
    if nodes_scanned < 0:
        return None
    normalized: dict[str, object] = {
        "schema": schema,
        "scan_complete": scan_complete,
        "canonical_nodes_scanned": nodes_scanned,
        # Historical compatibility label: schema 2 generalizes this to any
        # elaborated path-operator telescope with a relation and endpoints.
        "has_refl_trans_gen_path": has_path,
        "has_relation_valued_state_transition": has_transition,
        "detected": detected,
    }
    if schema == EXECUTION_STATE_REFINEMENT_SHAPE_SCHEMA:
        detector_basis = str(value.get("detector_basis") or "").strip()
        if detector_basis != EXECUTION_STATE_REFINEMENT_SHAPE_DETECTOR_BASIS:
            return None
        normalized["detector_basis"] = detector_basis
    return normalized


def _validated_execution_state_refinement_shape(
    manifest: Mapping[str, Any],
) -> dict[str, object] | None:
    raw = manifest.get("elaborated_execution_state_refinement_shape")
    if raw is not None:
        return _normalize_execution_state_refinement_shape(raw)
    return _legacy_elaborated_execution_state_refinement_shape(manifest)


def elaborated_execution_state_refinement_shape(
    manifest: Mapping[str, Any],
) -> dict[str, object]:
    """Return the name-independent Lean structural review trigger.

    ``has_refl_trans_gen_path`` is retained as a historical consumer label.
    In schema 2 it means any graph-reached elaborated path operator with a
    relation domain and matching state endpoints; no declaration, field,
    record, binder, or module spelling participates.
    """

    normalized = _validated_execution_state_refinement_shape(manifest)
    if normalized is not None:
        return normalized
    return {
        "schema": EXECUTION_STATE_REFINEMENT_SHAPE_SCHEMA,
        "detector_basis": EXECUTION_STATE_REFINEMENT_SHAPE_DETECTOR_BASIS,
        "scan_complete": False,
        "canonical_nodes_scanned": 0,
        "has_refl_trans_gen_path": False,
        "has_relation_valued_state_transition": False,
        "detected": False,
    }


def _canonical_payload(manifest: dict[str, Any]) -> dict[str, Any] | None:
    """Return the name-free payload used for freshness hashing."""

    raw_schema = manifest.get("schema")
    if str(raw_schema) != str(MANIFEST_SCHEMA):
        return None
    declaration_kind = str(manifest.get("declaration_kind") or "").strip()
    conclusion_mode = str(manifest.get("conclusion_mode") or "").strip()
    if declaration_kind not in DECLARATION_KINDS:
        return None
    expected_mode = (
        "type_and_value" if declaration_kind == "definition" else "type_only"
    )
    if conclusion_mode != expected_mode:
        return None
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return None
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for atom in atoms:
        if not isinstance(atom, dict):
            return None
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip()
        canonical = atom.get("canonical")
        if not ref or ref in seen or role not in ATOM_ROLES or canonical is None:
            return None
        seen.add(ref)
        compact_canonical = _compact_canonical(
            canonical,
            preserve_root_definition=(
                ref == "result" and declaration_kind == "definition"
            ),
        )
        if (
            len(
                json.dumps(
                    compact_canonical,
                    ensure_ascii=False,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            )
            > MAX_COMPACT_CANONICAL_BYTES
        ):
            return None
        item: dict[str, Any] = {
            "ref": ref,
            "role": role,
            "canonical": compact_canonical,
        }
        if role != "conclusion":
            binder_info = str(atom.get("binder_info") or "").strip()
            if binder_info not in {
                "explicit",
                "implicit",
                "strictImplicit",
                "instImplicit",
            }:
                return None
            item["binder_info"] = binder_info
        normalized.append(item)
    if normalized[-1]["ref"] != "result" or normalized[-1]["role"] != "conclusion":
        return None
    if any(atom["role"] == "conclusion" for atom in normalized[:-1]):
        return None
    return {
        "schema": MANIFEST_SCHEMA,
        "declaration_kind": declaration_kind,
        "conclusion_mode": conclusion_mode,
        "atoms": normalized,
    }


def signature_manifest_digest(manifest: dict[str, Any]) -> str:
    """Hash canonical semantic structure, excluding display and declaration names."""

    payload = _canonical_payload(manifest)
    if payload is None:
        return ""
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def semantic_dependency_manifest(
    manifest: Mapping[str, Any],
    module_identities: list[dict[str, str]] | None = None,
    environment_identities: list[dict[str, str]] | None = None,
) -> dict[str, Any] | None:
    """Return the shared transitive per-row semantic reuse identity.

    The identity combines Lean's spelling-free dependency/proposition graphs
    with exact artifacts for every reached compiled module.  Diagnostic
    declaration and module names remain outside the digest; they can route a
    reviewer, but cannot decide semantic equivalence.
    """

    graph = normalize_semantic_dependency_graph(
        manifest.get("semantic_dependency_graph")
    )
    proposition_graph = normalize_elaborated_proposition_graph(
        manifest.get("elaborated_proposition_graph")
    )
    execution_shape = _validated_execution_state_refinement_shape(manifest)
    if (
        not isinstance(graph, Mapping)
        or graph.get("schema") != SEMANTIC_DEPENDENCY_GRAPH_SCHEMA
        or graph.get("complete") is not True
        or not isinstance(proposition_graph, Mapping)
        or proposition_graph.get("schema") != 1
        or proposition_graph.get("complete") is not True
        or execution_shape is None
    ):
        return None
    # Aggregate digests supplied in JSON are never trusted. Both graph
    # normalizers above recompute them from validated canonical nodes and edge
    # topology, including pre-normalized node identities.
    graph_sha = str(graph.get("semantic_graph_sha256") or "").strip().lower()
    realization_sha = str(graph.get("realization_graph_sha256") or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", graph_sha) or not re.fullmatch(
        r"[0-9a-f]{64}", realization_sha
    ):
        return None
    proposition_sha = (
        str(proposition_graph.get("semantic_graph_sha256") or "").strip().lower()
    )
    if not re.fullmatch(r"[0-9a-f]{64}", proposition_sha):
        return None
    execution_shape_sha = _semantic_json_sha256(execution_shape)
    identities = module_identities
    if identities is None:
        raw_identities = manifest.get("semantic_dependency_module_identities")
        identities = raw_identities if isinstance(raw_identities, list) else []
    normalized_modules: list[dict[str, str]] = []
    semantic_modules: list[dict[str, str]] = []
    realization_modules: list[dict[str, str]] = []
    supplied_origins: dict[str, str] = {}
    for raw in identities:
        if not isinstance(raw, Mapping):
            return None
        module_origin = str(raw.get("module_origin") or "").strip()
        artifact_scope = str(raw.get("artifact_scope") or "").strip()
        artifact_sha = str(raw.get("artifact_sha256") or "").strip().lower()
        dependency_lane = str(raw.get("dependency_lane") or "semantic").strip()
        if (
            not module_origin
            or not artifact_scope
            or not re.fullmatch(r"[0-9a-f]{64}", artifact_sha)
            or dependency_lane not in {"semantic", "realization"}
            or module_origin in supplied_origins
        ):
            return None
        supplied_origins[module_origin] = dependency_lane
        normalized_modules.append(
            {
                "module_origin": module_origin,
                "artifact_scope": artifact_scope,
                "artifact_sha256": artifact_sha,
                "dependency_lane": dependency_lane,
            }
        )
        compact_module = {
            "artifact_scope": artifact_scope,
            "artifact_sha256": artifact_sha,
        }
        realization_modules.append(compact_module)
        if dependency_lane == "semantic":
            semantic_modules.append(compact_module)
    expected_semantic_origins = {
        str(origin).strip()
        for origin in graph.get("semantic_external_module_origins", [])
        if str(origin).strip()
    }
    expected_realization_origins = {
        str(origin).strip()
        for origin in graph.get("realization_external_module_origins", [])
        if str(origin).strip()
    }
    for node in graph.get("nodes", []):
        if not isinstance(node, Mapping):
            return None
        origin = str(node.get("module_origin") or "").strip()
        if origin in {"", "<inline>", "<internal>"}:
            continue
        terminal = node.get("origin_class") == "imported_terminal"
        opaque_local = (
            node.get("origin_class") == "review_closure"
            and node.get("declaration_kind") == "opaque"
        )
        proof_only_local = (
            node.get("origin_class") == "review_closure"
            and node.get("statement_reachable") is not True
        )
        if terminal or opaque_local or proof_only_local:
            expected_realization_origins.add(origin)
            if node.get("statement_reachable") is True and not proof_only_local:
                expected_semantic_origins.add(origin)
    expected_all_origins = expected_semantic_origins | expected_realization_origins
    if set(supplied_origins) != expected_all_origins or any(
        supplied_origins[origin]
        != ("semantic" if origin in expected_semantic_origins else "realization")
        for origin in expected_all_origins
    ):
        return None
    raw_environment = environment_identities
    if raw_environment is None:
        candidate_environment = manifest.get(
            "semantic_dependency_environment_identities"
        )
        raw_environment = (
            candidate_environment if isinstance(candidate_environment, list) else []
        )
    normalized_environment: list[dict[str, str]] = []
    environment_paths: set[str] = set()
    for raw in raw_environment:
        if not isinstance(raw, Mapping):
            return None
        path = str(raw.get("path") or "").strip()
        sha = str(raw.get("sha256") or "").strip().lower()
        if (
            not path
            or path in environment_paths
            or not re.fullmatch(r"[0-9a-f]{64}", sha)
        ):
            return None
        environment_paths.add(path)
        normalized_environment.append({"path": path, "sha256": sha})
    if environment_paths != {"lean-toolchain", "lake-manifest.json"}:
        return None
    semantic_payload = {
        "schema": SEMANTIC_DEPENDENCY_MANIFEST_SCHEMA,
        "semantic_graph_sha256": graph_sha,
        "elaborated_proposition_graph_sha256": proposition_sha,
        "execution_state_refinement_shape_sha256": execution_shape_sha,
        "module_artifacts": sorted(
            semantic_modules,
            key=lambda item: (item["artifact_scope"], item["artifact_sha256"]),
        ),
        "environment_artifacts": sorted(
            normalized_environment, key=lambda item: item["path"]
        ),
    }
    realization_payload = {
        "schema": SEMANTIC_DEPENDENCY_MANIFEST_SCHEMA,
        "semantic_dependency_sha256": _semantic_json_sha256(semantic_payload),
        "realization_graph_sha256": realization_sha,
        "module_artifacts": sorted(
            realization_modules,
            key=lambda item: (item["artifact_scope"], item["artifact_sha256"]),
        ),
        "environment_artifacts": sorted(
            normalized_environment, key=lambda item: item["path"]
        ),
    }
    return {
        "schema": SEMANTIC_DEPENDENCY_MANIFEST_SCHEMA,
        "complete": True,
        "semantic_graph_sha256": graph_sha,
        "realization_graph_sha256": realization_sha,
        "elaborated_proposition_graph_sha256": proposition_sha,
        "execution_state_refinement_shape_sha256": execution_shape_sha,
        "module_identities": sorted(
            normalized_modules,
            key=lambda item: (item["module_origin"], item["dependency_lane"]),
        ),
        "environment_identities": sorted(
            normalized_environment, key=lambda item: item["path"]
        ),
        "semantic_dependency_sha256": _semantic_json_sha256(semantic_payload),
        "realization_dependency_sha256": _semantic_json_sha256(realization_payload),
    }


def signature_manifest_outer_binder_digest(manifest: dict[str, Any]) -> str:
    """Hash the exact name-free outer theorem interface, excluding its result.

    Schema-3 uses this narrow pin to detect extra or altered parameters,
    assumptions, and instance inputs.  It is intentionally distinct from the
    full signature digest: a conclusion change is reviewed through the source
    specification and result contract, while this value makes interface
    smuggling fail closed.
    """

    payload = _canonical_payload(manifest)
    if payload is None:
        return ""
    atoms = payload["atoms"]
    if not atoms or atoms[-1].get("ref") != "result":
        return ""
    interface = {
        "schema": MANIFEST_SCHEMA,
        "declaration_kind": payload["declaration_kind"],
        "outer_binders": atoms[:-1],
    }
    encoded = json.dumps(
        interface, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def normalize_transparent_value_presentation_telescope(
    value: object,
) -> dict[str, Any] | None:
    """Validate Lean's nonreducing transparent-definition value telescope.

    This is a positional source-presentation receipt, not a replacement for a
    declaration's ordinary reduced signature manifest.  The latter remains
    authoritative for semantic dependency and proposition-graph review.
    """

    if not isinstance(value, Mapping):
        return None
    if (
        str(value.get("schema"))
        != str(TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA)
        or value.get("reduction")
        != TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION
    ):
        return None
    raw_atoms = value.get("atoms")
    if not isinstance(raw_atoms, list) or not raw_atoms:
        return None
    atoms: list[dict[str, Any]] = []
    for index, raw_atom in enumerate(raw_atoms):
        if not isinstance(raw_atom, Mapping):
            return None
        ref = str(raw_atom.get("ref") or "").strip()
        role = str(raw_atom.get("role") or "").strip()
        canonical = raw_atom.get("canonical")
        display = str(raw_atom.get("display") or "").strip()
        expected_ref = "result" if index == len(raw_atoms) - 1 else f"b/{index}"
        expected_role = "conclusion" if index == len(raw_atoms) - 1 else None
        if (
            ref != expected_ref
            or not display
            or canonical is None
            or (expected_role is not None and role != expected_role)
            or (expected_role is None and role not in {"parameter", "assumption"})
        ):
            return None
        atom: dict[str, Any] = {
            "ref": ref,
            "role": role,
            "canonical": _compact_canonical(canonical),
            "display": display,
        }
        if expected_role is None:
            binder_info = str(raw_atom.get("binder_info") or "").strip()
            if binder_info not in {
                "explicit",
                "implicit",
                "strictImplicit",
                "instImplicit",
            }:
                return None
            atom["binder_info"] = binder_info
        atoms.append(atom)
    canonical_payload = {
        "schema": TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA,
        "reduction": TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION,
        "atoms": [
            {
                key: value
                for key, value in atom.items()
                if key != "display"
            }
            for atom in atoms
        ],
    }
    return {
        "schema": TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA,
        "reduction": TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION,
        "atoms": atoms,
        "sha256": _semantic_json_sha256(canonical_payload),
    }


def normalize_signature_manifest(manifest: dict[str, Any]) -> dict[str, Any] | None:
    """Validate Lean output and attach its canonical freshness digest."""

    payload = _canonical_payload(manifest)
    dependency_graph = normalize_semantic_dependency_graph(
        manifest.get("semantic_dependency_graph")
    )
    proposition_graph = normalize_elaborated_proposition_graph(
        manifest.get("elaborated_proposition_graph")
    )
    raw_transparent_result_graph = manifest.get(
        "elaborated_transparent_result_value_graph"
    )
    transparent_result_graph = (
        normalize_elaborated_proposition_graph(raw_transparent_result_graph)
        if raw_transparent_result_graph is not None
        else None
    )
    raw_presentation_telescope = manifest.get(
        "transparent_value_presentation_telescope"
    )
    presentation_telescope = (
        normalize_transparent_value_presentation_telescope(raw_presentation_telescope)
        if raw_presentation_telescope is not None
        else None
    )
    presentation_telescope_is_valid = (
        raw_presentation_telescope is None
        or (
            payload is not None
            and payload.get("declaration_kind") == "definition"
            and presentation_telescope is not None
        )
    )
    execution_shape = _validated_execution_state_refinement_shape(manifest)
    if (
        payload is None
        or dependency_graph is None
        or proposition_graph is None
        or proposition_graph.get("complete") is not True
        or (
            raw_transparent_result_graph is not None
            and (
                transparent_result_graph is None
                or transparent_result_graph.get("complete") is not True
            )
        )
        or not presentation_telescope_is_valid
        or execution_shape is None
    ):
        return None
    raw_atoms = manifest.get("atoms") or []
    atoms: list[dict[str, Any]] = []
    for canonical, raw in zip(payload["atoms"], raw_atoms, strict=True):
        item = dict(canonical)
        display = str(raw.get("display") or "").strip()
        if not display:
            return None
        item["display"] = display
        atoms.append(item)
    normalized = {
        "schema": MANIFEST_SCHEMA,
        "declaration_kind": payload["declaration_kind"],
        "conclusion_mode": payload["conclusion_mode"],
        "atoms": atoms,
        # This is a generated, noncanonical review trigger.  The signature
        # digest remains the exact interface fingerprint above; retaining the
        # trigger separately lets source-record review distinguish a concrete
        # reachability/refinement route without treating a declaration name as
        # semantic evidence.
        "elaborated_execution_state_refinement_shape": (execution_shape),
        "elaborated_proposition_graph": proposition_graph,
        "elaborated_transparent_result_value_graph": transparent_result_graph,
        "transparent_value_presentation_telescope": presentation_telescope,
        "semantic_dependency_graph": dependency_graph,
    }
    normalized["sha256"] = signature_manifest_digest(normalized)
    return normalized


def parse_signature_manifest_output(output: str) -> dict[str, dict[str, Any]]:
    """Parse only sentinel-delimited JSON emitted by the Lean meta command."""

    manifests: dict[str, dict[str, Any]] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(SENTINEL)
        if marker < 0:
            continue
        payload = raw_line[marker + len(SENTINEL) :]
        try:
            name, raw_json = payload.split(":", 1)
            decoded = json.loads(raw_json)
        except (ValueError, json.JSONDecodeError):
            return {}
        if not name.strip() or not isinstance(decoded, dict):
            return {}
        normalized = normalize_signature_manifest(decoded)
        if normalized is None or name.strip() in manifests:
            return {}
        manifests[name.strip()] = normalized
    return manifests


def parse_direct_library_dependency_surface_output(
    output: str,
    requested_declarations: Iterable[str],
) -> dict[str, tuple[str, ...]]:
    """Parse one Lean-owned direct reusable-library dependency surface.

    The helper resolves the declaration body after elaboration.  This parser
    only validates a narrow, deterministic JSON transport: source tokens and
    Python namespace guesses never decide which reusable declaration is used.
    """

    requested = sorted(
        {str(name).strip() for name in requested_declarations if str(name).strip()}
    )
    matches = [
        line[line.find(DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL) + len(DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL) :]
        for line in output.splitlines()
        if DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL in line
    ]
    if len(matches) != 1:
        return {}
    try:
        payload = json.loads(matches[0])
    except json.JSONDecodeError:
        return {}
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "roots"}:
        return {}
    if payload.get("schema") != str(DIRECT_LIBRARY_DEPENDENCY_SURFACE_SCHEMA):
        return {}
    roots = payload.get("roots")
    if not isinstance(roots, list) or len(roots) != len(requested):
        return {}
    parsed: dict[str, tuple[str, ...]] = {}
    for raw in roots:
        if not isinstance(raw, Mapping) or set(raw) != {
            "declaration",
            "direct_library_declarations",
        }:
            return {}
        declaration = str(raw.get("declaration") or "").strip()
        dependencies = raw.get("direct_library_declarations")
        if (
            not declaration
            or declaration in parsed
            or not isinstance(dependencies, list)
            or any(not isinstance(value, str) for value in dependencies)
        ):
            return {}
        normalized = tuple(str(value).strip() for value in dependencies)
        if (
            any(
                not value.startswith("EconCSLib.") or not value
                for value in normalized
            )
            or list(normalized) != sorted(set(normalized))
        ):
            return {}
        parsed[declaration] = normalized
    return parsed if sorted(parsed) == requested else {}


def parse_transparent_paper_spec_display_output(
    output: str,
    requested_specifications: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate Lean-owned readable expansions for exact paper ``Spec`` roots.

    The textual display is deliberately emitted by Lean after elaboration and
    transparent paper-local delta reduction.  Python validates only a small
    transport envelope; it does not expand names or reconstruct semantics from
    source tokens.
    """

    requested = sorted(
        {str(name).strip() for name in requested_specifications if str(name).strip()}
    )
    matches = [
        line[
            line.find(TRANSPARENT_PAPER_SPEC_DISPLAY_SENTINEL)
            + len(TRANSPARENT_PAPER_SPEC_DISPLAY_SENTINEL) :
        ]
        for line in output.splitlines()
        if TRANSPARENT_PAPER_SPEC_DISPLAY_SENTINEL in line
    ]
    if len(matches) != 1:
        return {}
    try:
        payload = json.loads(matches[0])
    except json.JSONDecodeError:
        return {}
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) != len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "specification",
            "complete",
            "expansion_count",
            "expanded_declarations",
            "prerequisite_declarations",
            "library_declarations",
            "blocked_declarations",
            "display",
        }:
            return {}
        specification = str(raw.get("specification") or "").strip()
        complete = raw.get("complete")
        expansion_count = raw.get("expansion_count")
        expanded = raw.get("expanded_declarations")
        prerequisites = raw.get("prerequisite_declarations")
        libraries = raw.get("library_declarations")
        blocked = raw.get("blocked_declarations")
        display = raw.get("display")
        if (
            not specification
            or specification in parsed
            or complete is not True
            or not isinstance(expansion_count, str)
            or not expansion_count.isdigit()
            or not isinstance(expanded, list)
            or not isinstance(prerequisites, list)
            or not isinstance(libraries, list)
            or not isinstance(blocked, list)
            or blocked
            or not isinstance(display, str)
            or not display.strip()
            or any(not isinstance(value, str) or not value.strip() for value in expanded)
            or any(not isinstance(value, str) or not value.strip() for value in prerequisites)
            or any(
                not isinstance(value, str)
                or not value.strip().startswith("EconCSLib.")
                for value in libraries
            )
        ):
            return {}
        normalized_expanded = [str(value).strip() for value in expanded]
        normalized_prerequisites = [str(value).strip() for value in prerequisites]
        normalized_libraries = [str(value).strip() for value in libraries]
        if (
            normalized_expanded != sorted(set(normalized_expanded))
            or normalized_prerequisites != sorted(set(normalized_prerequisites))
            or normalized_libraries != sorted(set(normalized_libraries))
        ):
            return {}
        parsed[specification] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "expansion_count": int(expansion_count),
            "expanded_declarations": tuple(normalized_expanded),
            "prerequisite_declarations": tuple(normalized_prerequisites),
            "library_declarations": tuple(normalized_libraries),
        }
    return parsed if sorted(parsed) == requested else {}


def parse_transparent_paper_declaration_display_output(
    output: str,
    requested_declarations: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate Lean-owned semantic displays for paper-local prerequisites.

    The initial names and every recursively retained paper-local declaration
    are emitted by Lean.  Python validates the transport envelope and hashes
    the exact display, but never discovers or expands source declarations.
    """

    requested = sorted(
        {str(name).strip() for name in requested_declarations if str(name).strip()}
    )
    matches = [
        line[
            line.find(TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL)
            + len(TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL) :
        ]
        for line in output.splitlines()
        if TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL in line
    ]
    if len(matches) != 1:
        return {}
    try:
        payload = json.loads(matches[0])
    except json.JSONDecodeError:
        return {}
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) < len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    allowed_kinds = {"definition", "opaque_definition", "non_definition"}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "declaration",
            "declaration_kind",
            "root_expanded",
            "direct_paper_declarations",
            "direct_library_declarations",
            "display",
        }:
            return {}
        declaration = str(raw.get("declaration") or "").strip()
        kind = str(raw.get("declaration_kind") or "").strip()
        root_expanded = raw.get("root_expanded")
        paper_dependencies = raw.get("direct_paper_declarations")
        library_dependencies = raw.get("direct_library_declarations")
        display = raw.get("display")
        if (
            not declaration
            or declaration in parsed
            or kind not in allowed_kinds
            or not isinstance(root_expanded, bool)
            or (kind == "definition") != root_expanded
            or not isinstance(paper_dependencies, list)
            or not isinstance(library_dependencies, list)
            or not isinstance(display, str)
            or not display.strip()
        ):
            return {}
        normalized_paper_dependencies = [str(value).strip() for value in paper_dependencies]
        normalized_library_dependencies = [
            str(value).strip() for value in library_dependencies
        ]
        if (
            any(not isinstance(value, str) or not value.strip() for value in paper_dependencies)
            or normalized_paper_dependencies != sorted(set(normalized_paper_dependencies))
            or declaration in normalized_paper_dependencies
            or any(
                not isinstance(value, str)
                or not value.strip().startswith("EconCSLib.")
                for value in library_dependencies
            )
            or normalized_library_dependencies != sorted(set(normalized_library_dependencies))
        ):
            return {}
        parsed[declaration] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "declaration_kind": kind,
            "root_expanded": root_expanded,
            "direct_paper_declarations": tuple(normalized_paper_dependencies),
            "direct_library_declarations": tuple(normalized_library_dependencies),
        }
    return parsed if set(requested).issubset(parsed) else {}


def parse_transparent_library_declaration_display_output(
    output: str,
    requested_declarations: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate Lean-owned target displays for reusable declarations.

    A definition target is its own delta-reduced body with all declaration
    binders reinstated.  Other Lean declaration kinds have a meaningful
    signature but no reducible body; their exact bounded source declaration is
    retained by the caller for the constructor/field-level review.
    """

    requested = sorted(
        {str(name).strip() for name in requested_declarations if str(name).strip()}
    )
    matches = [
        line[
            line.find(TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL)
            + len(TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL) :
        ]
        for line in output.splitlines()
        if TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL in line
    ]
    if len(matches) != 1:
        return {}
    try:
        payload = json.loads(matches[0])
    except json.JSONDecodeError:
        return {}
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) < len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    allowed_kinds = {"definition", "opaque_definition", "non_definition"}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "declaration",
            "declaration_kind",
            "root_expanded",
            "direct_library_declarations",
            "display",
        }:
            return {}
        declaration = str(raw.get("declaration") or "").strip()
        kind = str(raw.get("declaration_kind") or "").strip()
        root_expanded = raw.get("root_expanded")
        dependencies = raw.get("direct_library_declarations")
        display = raw.get("display")
        if (
            not declaration.startswith("EconCSLib.")
            or declaration in parsed
            or kind not in allowed_kinds
            or not isinstance(root_expanded, bool)
            or (kind == "definition") != root_expanded
            or not isinstance(dependencies, list)
            or not isinstance(display, str)
            or not display.strip()
        ):
            return {}
        normalized_dependencies = [str(value).strip() for value in dependencies]
        if (
            any(
                not isinstance(value, str)
                or not value.strip().startswith("EconCSLib.")
                or value.strip() == declaration
                for value in dependencies
            )
            or normalized_dependencies != sorted(set(normalized_dependencies))
        ):
            return {}
        parsed[declaration] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "declaration_kind": kind,
            "root_expanded": root_expanded,
            "direct_library_declarations": tuple(normalized_dependencies),
        }
    return parsed if set(requested).issubset(parsed) else {}


def _semantic_dependency_root_identity(
    graph: Mapping[str, Any], declaration: str
) -> str:
    """Return the unique canonical identity for one graph root coordinate."""

    if str(graph.get("root_declaration") or "").strip() != declaration:
        return ""
    roots = [
        str(node.get("semantic_identity_sha256") or "").strip().lower()
        for node in graph.get("nodes", [])
        if isinstance(node, Mapping)
        and str(node.get("declaration") or "").strip() == declaration
        and node.get("statement_reachable") is True
        and node.get("origin_class") == "review_closure"
    ]
    return (
        roots[0] if len(roots) == 1 and re.fullmatch(r"[0-9a-f]{64}", roots[0]) else ""
    )


def parse_signature_manifest_revalidation_output(
    output: str,
) -> dict[str, dict[str, Any]]:
    """Parse compact current-environment receipts for persisted manifests."""

    receipts: dict[str, dict[str, Any]] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(SIGNATURE_MANIFEST_REVALIDATION_SENTINEL)
        if marker < 0:
            continue
        payload = raw_line[marker + len(SIGNATURE_MANIFEST_REVALIDATION_SENTINEL) :]
        try:
            declaration, raw_json = payload.split(":", 1)
            decoded = json.loads(raw_json)
        except (ValueError, json.JSONDecodeError):
            return {}
        declaration = declaration.strip()
        if (
            not declaration
            or declaration in receipts
            or not isinstance(decoded, Mapping)
            or str(decoded.get("schema") or "") != "1"
        ):
            return {}
        declaration_kind = str(decoded.get("declaration_kind") or "").strip()
        conclusion_mode = str(decoded.get("conclusion_mode") or "").strip()
        expected_mode = (
            "type_and_value" if declaration_kind == "definition" else "type_only"
        )
        graph = normalize_semantic_dependency_graph(
            decoded.get("semantic_dependency_graph")
        )
        execution_shape = _normalize_execution_state_refinement_shape(
            decoded.get("elaborated_execution_state_refinement_shape")
        )
        root_identity = (
            _semantic_dependency_root_identity(graph, declaration)
            if isinstance(graph, Mapping)
            else ""
        )
        if (
            declaration_kind not in DECLARATION_KINDS
            or conclusion_mode != expected_mode
            or not isinstance(graph, Mapping)
            or graph.get("complete") is not True
            or graph.get("realization_complete") is not True
            or execution_shape is None
            or not root_identity
        ):
            return {}
        receipts[declaration] = {
            "schema": 1,
            "declaration_kind": declaration_kind,
            "conclusion_mode": conclusion_mode,
            "root_semantic_identity_sha256": root_identity,
            "elaborated_execution_state_refinement_shape": execution_shape,
            "semantic_dependency_graph": graph,
        }
    return receipts


_MANIFEST_ITEM_REVALIDATION_CONTEXT_FIELDS = (
    "schema",
    "import_module",
    "helper_fingerprint",
    "semantic_hash_tool_identity",
    "canonical_representation",
    "audit_modules",
)


def signature_manifest_item_revalidation_matches(
    manifest: Mapping[str, Any],
    receipt: Mapping[str, Any],
    *,
    declaration: str,
    prior_context: Mapping[str, Any],
    current_context: Mapping[str, Any],
) -> bool:
    """Validate a persisted manifest after an unrelated module-level change.

    Exact source equality is a separate caller obligation.  Here Lean
    recomputes the complete name-independent dependency graph, the canonical
    root identity (type plus value for definitions), and the structural
    execution shape.  With the identical helper, ownership scope, and hash
    tool, equality of those receipts also fixes the atom decomposition and
    proposition DAG retained in ``manifest``.  Changed reached artifacts are
    checked separately when the caller reattaches the dependency manifest.
    """

    if any(
        prior_context.get(field) != current_context.get(field)
        for field in _MANIFEST_ITEM_REVALIDATION_CONTEXT_FIELDS
    ):
        return False
    prior_graph = normalize_semantic_dependency_graph(
        manifest.get("semantic_dependency_graph")
    )
    current_graph = normalize_semantic_dependency_graph(
        receipt.get("semantic_dependency_graph")
    )
    prior_shape = _validated_execution_state_refinement_shape(manifest)
    current_shape = _normalize_execution_state_refinement_shape(
        receipt.get("elaborated_execution_state_refinement_shape")
    )
    if (
        not isinstance(prior_graph, Mapping)
        or not isinstance(current_graph, Mapping)
        or prior_graph.get("complete") is not True
        or current_graph.get("complete") is not True
        or prior_graph.get("realization_complete") is not True
        or current_graph.get("realization_complete") is not True
        or prior_shape is None
        or current_shape is None
        or prior_shape != current_shape
        or manifest.get("declaration_kind") != receipt.get("declaration_kind")
        or manifest.get("conclusion_mode") != receipt.get("conclusion_mode")
    ):
        return False
    prior_root = _semantic_dependency_root_identity(prior_graph, declaration)
    current_root = _semantic_dependency_root_identity(current_graph, declaration)
    if (
        not prior_root
        or prior_root != current_root
        or current_root
        != str(receipt.get("root_semantic_identity_sha256") or "").strip().lower()
    ):
        return False
    return all(
        prior_graph.get(field) == current_graph.get(field)
        for field in ("semantic_graph_sha256", "realization_graph_sha256")
    )


def parse_proposition_spec_proof_output(
    output: str,
) -> dict[tuple[str, str], bool]:
    """Parse fail-closed Meta results for proposition-spec proof routes."""

    matches: dict[tuple[str, str], bool] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(PROPOSITION_SPEC_PROOF_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(PROPOSITION_SPEC_PROOF_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict) or not isinstance(
            decoded.get("matches"), bool
        ):
            return {}
        spec = str(decoded.get("spec") or "").strip()
        proof = str(decoded.get("proof") or "").strip()
        key = (spec, proof)
        if not spec or not proof or key in matches:
            return {}
        matches[key] = decoded["matches"]
    return matches


def parse_semantic_contract_output(
    output: str,
) -> dict[tuple[str, str, str], bool]:
    """Parse fail-closed Meta results for exact semantic contracts."""

    matches: dict[tuple[str, str, str], bool] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(SEMANTIC_CONTRACT_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(SEMANTIC_CONTRACT_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict) or not isinstance(
            decoded.get("matches"), bool
        ):
            return {}
        spec = str(decoded.get("spec") or "").strip()
        evidence = str(decoded.get("evidence") or "").strip()
        mode = str(decoded.get("mode") or "").strip()
        key = (spec, evidence, mode)
        if (
            not spec
            or not evidence
            or mode not in {"proves", "refutes", "definitionally_realizes"}
            or key in matches
        ):
            return {}
        matches[key] = decoded["matches"]
    return matches


def parse_operational_outcome_domain_bridge_output(
    output: str,
) -> dict[OperationalOutcomeDomainRoute, bool]:
    """Parse Lean-owned nonvacuity bridge checks fail-closed.

    The route contains only exact declaration coordinates, outer-telescope
    positions, and direct elaborated model/transition roots. Its truth value
    is produced by Lean's elaborated type checker; no binder spelling
    participates in deciding a match.
    """

    matches: dict[OperationalOutcomeDomainRoute, bool] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict) or not isinstance(
            decoded.get("matches"), bool
        ):
            return {}
        target = str(decoded.get("target") or "").strip()
        bridge = str(decoded.get("bridge") or "").strip()
        indices: list[int] = []
        for field in (
            "model_index",
            "terminal_index",
            "run_index",
            "terminal_predicate_index",
        ):
            raw_index = decoded.get(field)
            if not isinstance(raw_index, str) or not raw_index.isdigit():
                return {}
            indices.append(int(raw_index))
        model_root = str(decoded.get("model_root") or "").strip()
        transition_root = str(decoded.get("transition_root") or "").strip()
        key: OperationalOutcomeDomainRoute = (
            target,
            bridge,
            *indices,
            model_root,
            transition_root,
        )
        if (
            not target
            or not bridge
            or not model_root
            or not transition_root
            or key in matches
        ):
            return {}
        matches[key] = decoded["matches"]
    return matches


def parse_operational_outcome_state_transition_bridge_output(
    output: str,
) -> dict[OperationalOutcomeStateTransitionRoute, bool]:
    """Parse result-local state/transition bridge checks fail-closed.

    The route is a tuple of exact declaration coordinates, elaborated outer
    binder positions, and resolved roots.  It deliberately contains no
    presentation label or semantic classification inferred from a name.
    """

    matches: dict[OperationalOutcomeStateTransitionRoute, bool] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[
            marker + len(OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_SENTINEL) :
        ]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict) or not isinstance(
            decoded.get("matches"), bool
        ):
            return {}
        target = str(decoded.get("target") or "").strip()
        bridge = str(decoded.get("bridge") or "").strip()
        initial_witness = str(decoded.get("initial_witness") or "").strip()
        indices: list[int] = []
        for field in (
            "model_index",
            "state_index",
            "initial_predicate_index",
            "terminal_index",
            "run_index",
            "terminal_predicate_index",
        ):
            raw_index = decoded.get(field)
            if not isinstance(raw_index, str) or not raw_index.isdigit():
                return {}
            indices.append(int(raw_index))
        model_root = str(decoded.get("model_root") or "").strip()
        state_root = str(decoded.get("state_root") or "").strip()
        transition_root = str(decoded.get("transition_root") or "").strip()
        key: OperationalOutcomeStateTransitionRoute = (
            target,
            bridge,
            initial_witness,
            *indices,
            model_root,
            state_root,
            transition_root,
        )
        if (
            not target
            or not bridge
            or not initial_witness
            or not model_root
            or not state_root
            or not transition_root
            or key in matches
        ):
            return {}
        matches[key] = decoded["matches"]
    return matches


def canonical_semantic_contract_executable_terminals(
    value: object,
) -> list[dict[str, object]] | None:
    """Normalize the Lean-owned occurrence set for executable recursion.

    A recursive executor is accepted only through an exact receipt set.  The
    receipt deliberately records the elaborated traversal path and the full
    application result types in addition to its declaration identity.  This
    keeps two occurrences of one recursive definition distinct and prevents
    a Python caller from reducing the evidence to a function-name allowlist.
    """

    if not isinstance(value, list):
        return None
    normalized: list[dict[str, object]] = []
    required_fields = {
        "declaration",
        "occurrence_path",
        "application_arity",
        "application_result_type",
        "normalized_result_type",
    }
    for raw in value:
        if not isinstance(raw, dict) or set(raw) != required_fields:
            return None
        declaration = str(raw.get("declaration") or "").strip()
        path = raw.get("occurrence_path")
        raw_application_arity = raw.get("application_arity")
        application_result_type = str(raw.get("application_result_type") or "").strip()
        normalized_result_type = str(raw.get("normalized_result_type") or "").strip()
        if isinstance(raw_application_arity, int) and not isinstance(
            raw_application_arity, bool
        ):
            application_arity = raw_application_arity
        elif isinstance(raw_application_arity, str) and raw_application_arity.isdigit():
            application_arity = int(raw_application_arity)
        else:
            application_arity = 0
        if (
            not declaration
            or not isinstance(path, list)
            or not path
            or any(
                not isinstance(segment, str) or not segment.strip() for segment in path
            )
            or application_arity < 1
            or not application_result_type
            or not normalized_result_type
        ):
            return None
        normalized.append(
            {
                "declaration": declaration,
                "occurrence_path": [segment.strip() for segment in path],
                "application_arity": application_arity,
                "application_result_type": application_result_type,
                "normalized_result_type": normalized_result_type,
            }
        )
    normalized.sort(
        key=lambda terminal: json.dumps(
            terminal, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        )
    )
    rendered = [
        json.dumps(terminal, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        for terminal in normalized
    ]
    if len(rendered) != len(set(rendered)):
        return None
    return normalized


def semantic_contract_executable_terminal_receipt_sha256(
    terminals: object,
) -> str | None:
    """Hash one normalized executable-recursion occurrence set."""

    normalized = canonical_semantic_contract_executable_terminals(terminals)
    if normalized is None:
        return None
    payload = {
        "schema": SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_SCHEMA,
        "terminals": normalized,
    }
    return hashlib.sha256(
        json.dumps(
            payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("utf-8")
    ).hexdigest()


def parse_semantic_contract_transparency_output(
    output: str,
) -> dict[str, dict[str, Any]]:
    """Parse fail-closed transitive transparency verdicts for contract Specs.

    The Lean helper decides ownership from compiled module origins and follows
    only the supplied exact paper-module closure.  Python validates the small
    result protocol; it never decides whether a declaration name is semantic.
    """

    results: dict[str, dict[str, Any]] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(SEMANTIC_CONTRACT_TRANSPARENCY_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(SEMANTIC_CONTRACT_TRANSPARENCY_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        spec = str(decoded.get("spec") or "").strip()
        passes = decoded.get("passes")
        failure_tag = str(decoded.get("failure_tag") or "")
        failure_declaration = str(decoded.get("failure_declaration") or "")
        expanded = decoded.get("expanded")
        terminal_schema = decoded.get("recursive_executable_terminal_schema")
        raw_terminals = decoded.get("recursive_executable_terminals", [])
        terminals = canonical_semantic_contract_executable_terminals(raw_terminals)
        if (
            not spec
            or spec in results
            or not isinstance(passes, bool)
            or not isinstance(expanded, str)
            or not expanded.isdigit()
            or terminal_schema != str(SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_SCHEMA)
            or terminals is None
            or (passes and (failure_tag or failure_declaration or terminals))
            or (not passes and not failure_tag)
            or (
                failure_tag == "recursive_executable_terminal"
                and (
                    not terminals
                    or failure_declaration
                    not in {str(terminal["declaration"]) for terminal in terminals}
                )
            )
            or (failure_tag != "recursive_executable_terminal" and terminals)
        ):
            return {}
        results[spec] = {
            "passes": passes,
            "failure_tag": failure_tag,
            "failure_declaration": failure_declaration,
            "recursive_executable_terminals": terminals,
            "expanded": int(expanded),
        }
    return results


SEMANTIC_CONTRACT_CLOSURE_SCHEMA = 1
SEMANTIC_CONTRACT_CLOSURE_ORIGIN_CLASSES = {
    "paper",
    "workspace",
    "foundation",
    "external",
    "unresolved",
}
# The helper classifies declarations from Lean's module origin.  These are
# package module roots, not declaration-name prefixes.  Any loaded module that
# is neither workspace-owned nor registered here is retained as an external
# dependency and makes the closure fail closed.
DEFAULT_SEMANTIC_CONTRACT_FOUNDATION_MODULES = (
    "Init",
    "Lean",
    "Std",
    "Batteries",
    "Qq",
    "Aesop",
    "Cli",
    "ImportGraph",
    "ProofWidgets",
    "LeanSearchClient",
    "Plausible",
    "Mathlib",
    "Cslib",
    # EconCSLib definitions are library prerequisites with their own current
    # source-to-Lean screening lane; they are not paper-local source claims.
    "EconCSLib",
)


def _closure_json_sha256(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(
            value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


def _normalize_semantic_contract_expr_fingerprint(
    decoded: object,
) -> dict[str, str] | None:
    """Validate one compact, name-free Lean expression fingerprint."""

    if not isinstance(decoded, dict) or set(decoded) != {
        "tag",
        "canonical_sha256",
        "canonical_bytes",
    }:
        return None
    if str(decoded.get("tag") or "") != "expr_fingerprint":
        return None
    canonical_sha256 = str(decoded.get("canonical_sha256") or "").lower()
    canonical_bytes = decoded.get("canonical_bytes")
    if (
        not re.fullmatch(r"[0-9a-f]{64}", canonical_sha256)
        or not isinstance(canonical_bytes, str)
        or not canonical_bytes.isdigit()
    ):
        return None
    return {
        "tag": "expr_fingerprint",
        "canonical_sha256": canonical_sha256,
        "canonical_bytes": canonical_bytes,
    }


def _normalize_semantic_contract_closure(
    decoded: object,
) -> dict[str, Any] | None:
    """Validate and name-normalize one Lean-owned Spec closure manifest.

    Lean owns declaration lookup, elaboration, module ownership, and the
    closure traversal.  Python only validates this narrow JSON protocol and
    derives stable hashes from the elaborated output.  The structural digest
    intentionally excludes diagnostic declaration and module spellings, while
    retaining Lean's declaration type/value fingerprints so independently
    renamed workspace constants cannot collapse into one anonymous node.
    """

    if not isinstance(decoded, dict):
        return None
    if str(decoded.get("schema") or "") != str(SEMANTIC_CONTRACT_CLOSURE_SCHEMA):
        return None
    specification = str(decoded.get("spec") or "").strip()
    passes = decoded.get("passes")
    expanded = decoded.get("expanded")
    surface_mode = str(decoded.get("surface_mode") or "").strip()
    surface = decoded.get("surface")
    raw_nodes = decoded.get("nodes")
    raw_reached_modules = decoded.get("reached_modules")
    raw_failures = decoded.get("failures")
    raw_scope = decoded.get("scope")
    if (
        not specification
        or not isinstance(passes, bool)
        or not isinstance(expanded, str)
        or not expanded.isdigit()
        or surface_mode
        not in {
            "closure_expanded",
            "terminal_fallback",
            "closure_fingerprints",
            "terminal_fingerprints",
            "lean_dependency_fingerprint",
        }
        or (surface is not None and not isinstance(surface, dict))
        or not isinstance(raw_nodes, list)
        or not isinstance(raw_reached_modules, list)
        or not isinstance(raw_failures, list)
        or not isinstance(raw_scope, dict)
    ):
        return None

    normalized_surface: dict[str, Any] | None = None
    if surface is not None:
        surface_tag = str(surface.get("tag") or "")
        if surface_tag == "lean_declaration_fingerprint":
            if (
                surface_mode != "lean_dependency_fingerprint"
                or str(surface.get("schema") or "") != "1"
                or set(surface) != {
                    "tag",
                    "schema",
                    "declaration_kind",
                    "declaration_type_sha256",
                    "declaration_value_sha256",
                }
            ):
                return None
            declaration_kind = str(surface.get("declaration_kind") or "")
            type_hash = str(surface.get("declaration_type_sha256") or "")
            value_hash = str(surface.get("declaration_value_sha256") or "")
            if (
                not declaration_kind
                or not re.fullmatch(r"[0-9a-f]{64}", type_hash)
                or not re.fullmatch(r"[0-9a-f]{64}", value_hash)
            ):
                return None
            normalized_surface = {
                "schema": 1,
                "representation": "lean_environment_dependency_closure_v1",
                "declaration_kind": declaration_kind,
                "declaration_type_sha256": type_hash,
                "declaration_value_sha256": value_hash,
            }
        else:
            raw_binders = surface.get("binder_domains")
            if not isinstance(raw_binders, list):
                return None
            binders: list[dict[str, Any]] = []
            seen_indices: set[str] = set()
            for binder in raw_binders:
                if not isinstance(binder, dict):
                    return None
                index = str(binder.get("index") or "")
                binder_info = str(binder.get("binder_info") or "")
                domain_is_proposition = binder.get("domain_is_proposition")
                if (
                    not index.isdigit()
                    or index in seen_indices
                    or binder_info
                    not in {"explicit", "implicit", "strictImplicit", "instImplicit"}
                    or not isinstance(domain_is_proposition, bool)
                ):
                    return None
                seen_indices.add(index)
                normalized_binder: dict[str, Any] = {
                    "index": index,
                    "binder_info": binder_info,
                    "domain_is_proposition": domain_is_proposition,
                }
                if surface_tag == "spec_surface":
                    canonical = binder.get("canonical")
                    if canonical is None:
                        return None
                    normalized_binder["canonical"] = canonical
                elif surface_tag == "spec_surface_fingerprints":
                    fingerprint = _normalize_semantic_contract_expr_fingerprint(
                        binder.get("fingerprint")
                    )
                    if fingerprint is None:
                        return None
                    normalized_binder["fingerprint"] = fingerprint
                else:
                    return None
                binders.append(normalized_binder)
            if [int(item["index"]) for item in binders] != list(range(len(binders))):
                return None
            if surface_tag == "spec_surface":
                if surface_mode not in {"closure_expanded", "terminal_fallback"}:
                    return None
                body = surface.get("body")
                if body is None:
                    return None
                normalized_surface = {"binder_domains": binders, "body": body}
            else:
                fingerprint_schema = str(surface.get("schema") or "")
                if surface_mode not in {
                    "closure_fingerprints",
                    "terminal_fingerprints",
                } or fingerprint_schema not in {"2", "3"}:
                    return None
                body_fingerprint = _normalize_semantic_contract_expr_fingerprint(
                    surface.get("body_fingerprint")
                )
                if body_fingerprint is None:
                    return None
                normalized_surface = {
                    "schema": int(fingerprint_schema),
                    "representation": (
                        "lean_canonical_surface_sha256_v1"
                        if fingerprint_schema == "2"
                        else "lean_compact_canonical_surface_sha256_v2"
                    ),
                    "binder_domains": binders,
                    "body_fingerprint": body_fingerprint,
                }

    nodes: list[dict[str, Any]] = []
    for raw_node in raw_nodes:
        if not isinstance(raw_node, dict):
            return None
        structural_path = str(raw_node.get("structural_path") or "").strip()
        node_role = str(raw_node.get("node_role") or "").strip()
        origin_class = str(raw_node.get("origin_class") or "").strip()
        module_origin = str(raw_node.get("module_origin") or "")
        declaration = str(raw_node.get("declaration") or "").strip()
        identity = raw_node.get("canonical_identity")
        if (
            not structural_path
            or not node_role
            or origin_class not in SEMANTIC_CONTRACT_CLOSURE_ORIGIN_CLASSES
            or not declaration
            or not isinstance(identity, dict)
            or not str(identity.get("tag") or "").strip()
        ):
            return None
        # A compiled dependency with an absent module origin cannot receive
        # terminal credit.  `<inline>` and `<internal>` are explicit Lean
        # helper contexts, never ordinary imported-module placeholders.
        if (
            origin_class in {"workspace", "foundation", "external"}
            and not module_origin
        ):
            return None
        if origin_class == "unresolved" and module_origin:
            return None
        normalized = {
            "structural_path": structural_path,
            "node_role": node_role,
            "origin_class": origin_class,
            "module_origin": module_origin,
            "declaration": declaration,
            "canonical_identity": identity,
        }
        normalized["canonical_identity_sha256"] = _closure_json_sha256(identity)
        # This is an identity pin, not an acceptance rule: the terminal is
        # admitted only when Lean classified its module as an allowed
        # foundation.  Keeping the exact compiled module plus declaration
        # identity prevents two same-typed opaque primitives from collapsing
        # in correspondence records, while the broader structural digest
        # remains insensitive to paper-local transparent wrapper names.
        normalized["pinned_declaration_identity_sha256"] = _closure_json_sha256(
            {
                "module_origin": module_origin,
                "declaration": declaration,
                "canonical_identity": identity,
            }
        )
        nodes.append(normalized)

    reached_modules: list[dict[str, str]] = []
    seen_reached_modules: set[tuple[str, str]] = set()
    for raw_reached in raw_reached_modules:
        if not isinstance(raw_reached, dict):
            return None
        origin_class = str(raw_reached.get("origin_class") or "").strip()
        module_origin = str(raw_reached.get("module_origin") or "").strip()
        key = (origin_class, module_origin)
        if (
            origin_class not in SEMANTIC_CONTRACT_CLOSURE_ORIGIN_CLASSES
            or origin_class == "unresolved"
            or not module_origin
            or key in seen_reached_modules
        ):
            return None
        seen_reached_modules.add(key)
        reached_modules.append(
            {"origin_class": origin_class, "module_origin": module_origin}
        )

    failures: list[dict[str, str]] = []
    for raw_failure in raw_failures:
        if not isinstance(raw_failure, dict):
            return None
        tag = str(raw_failure.get("tag") or "").strip()
        declaration = str(raw_failure.get("declaration") or "").strip()
        if not tag or not declaration:
            return None
        failures.append({"tag": tag, "declaration": declaration})
    if passes != (not failures):
        return None
    if passes and surface_mode not in {
        "closure_expanded",
        "closure_fingerprints",
        "lean_dependency_fingerprint",
    }:
        return None
    if passes and any(
        node["origin_class"] in {"workspace", "external", "unresolved"}
        for node in nodes
    ):
        return None

    scope: dict[str, Any] = {}
    for key in ("paper_modules", "workspace_modules", "foundation_modules"):
        values = raw_scope.get(key)
        if not isinstance(values, list) or any(
            not isinstance(value, str) or not value.strip() for value in values
        ):
            return None
        scope[key] = list(values)
    inline_paper_scope = raw_scope.get("inline_paper_scope")
    hash_tool_path = str(raw_scope.get("hash_tool_path") or "").strip()
    if not isinstance(inline_paper_scope, bool) or not hash_tool_path:
        return None
    scope["inline_paper_scope"] = inline_paper_scope
    scope["hash_tool_path"] = hash_tool_path

    structural_payload = {
        "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
        "passes": passes,
        "expanded": int(expanded),
        "surface_mode": surface_mode,
        "surface": normalized_surface,
        "nodes": [
            {
                "structural_path": node["structural_path"],
                "node_role": node["node_role"],
                "origin_class": node["origin_class"],
                **(
                    {"canonical_identity": node["canonical_identity"]}
                    if node["origin_class"] != "paper"
                    else {}
                ),
            }
            for node in nodes
        ],
        "failure_tags": [failure["tag"] for failure in failures],
    }
    return {
        "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
        "spec": specification,
        "passes": passes,
        "expanded": int(expanded),
        "surface_mode": surface_mode,
        "surface": normalized_surface,
        "nodes": nodes,
        "reached_modules": reached_modules,
        "failures": failures,
        "scope": scope,
        "sha256": _closure_json_sha256(structural_payload),
        "surface_sha256": (
            _closure_json_sha256(normalized_surface)
            if normalized_surface is not None
            else ""
        ),
    }


def parse_semantic_contract_closure_output(
    output: str,
) -> dict[str, dict[str, Any]]:
    """Parse closure manifests emitted by the Lean Meta command, fail closed."""

    results: dict[str, dict[str, Any]] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(SEMANTIC_CONTRACT_CLOSURE_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(SEMANTIC_CONTRACT_CLOSURE_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        normalized = _normalize_semantic_contract_closure(decoded)
        if normalized is None:
            return {}
        specification = str(normalized["spec"])
        if specification in results:
            return {}
        results[specification] = normalized
    return results


def parse_source_premise_false_scan_output(
    output: str,
) -> dict[str, list[dict[str, Any]]]:
    """Parse elaborated source-input-to-``False`` eliminator routes.

    The Lean helper reports only candidates whose terminal result is
    definitionally ``False``, whose input is definitionally equal to the
    reviewed type, and which have no additional proposition-valued premise.
    Candidate names remain diagnostics only; the route decision is made by
    elaborated type shape in Lean.
    """

    payloads: list[dict[str, Any]] = []
    for raw_line in output.splitlines():
        marker = raw_line.find(SOURCE_PREMISE_FALSE_SCAN_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(SOURCE_PREMISE_FALSE_SCAN_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        payloads.append(decoded)
    if len(payloads) != 1:
        return {}
    raw_items = payloads[0].get("reviewed_inputs")
    if not isinstance(raw_items, list):
        return {}
    out: dict[str, list[dict[str, Any]]] = {}
    for raw_item in raw_items:
        if not isinstance(raw_item, dict):
            return {}
        reviewed = str(raw_item.get("reviewed") or "").strip()
        raw_candidates = raw_item.get("candidates")
        if not reviewed or reviewed in out or not isinstance(raw_candidates, list):
            return {}
        candidates: list[dict[str, Any]] = []
        seen_candidates: set[tuple[str, str]] = set()
        for raw_candidate in raw_candidates:
            if not isinstance(raw_candidate, dict):
                return {}
            candidate = str(raw_candidate.get("candidate") or "").strip()
            matched_index = str(raw_candidate.get("matched_binder_index") or "").strip()
            raw_data_indices = raw_candidate.get("candidate_only_data_binder_indices")
            direct = raw_candidate.get("direct_eliminator")
            if (
                not candidate
                or not matched_index.isdecimal()
                or not isinstance(raw_data_indices, list)
                or not isinstance(direct, bool)
            ):
                return {}
            data_indices = [str(index).strip() for index in raw_data_indices]
            if any(not index.isdecimal() for index in data_indices):
                return {}
            key = (candidate, matched_index)
            if key in seen_candidates:
                return {}
            seen_candidates.add(key)
            candidates.append(
                {
                    "candidate": candidate,
                    "matched_binder_index": matched_index,
                    "candidate_only_data_binder_indices": data_indices,
                    "direct_eliminator": direct,
                }
            )
        out[reviewed] = candidates
    return out


def parse_constructor_result_type_match_output(
    output: str,
) -> dict[tuple[str, str, str], bool]:
    """Parse Lean-Meta result-type compatibility verdicts fail-closed.

    The route identity only locates a reviewed binder and candidate declaration.
    Lean decides compatibility by elaborated definitional equality, with the
    reviewed binder's parameters and universes rigid.
    """

    matches: dict[tuple[str, str, str], bool] = {}
    for raw_line in output.splitlines():
        marker = raw_line.find(CONSTRUCTOR_RESULT_TYPE_MATCH_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(CONSTRUCTOR_RESULT_TYPE_MATCH_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        reviewed = str(decoded.get("reviewed") or "").strip()
        candidate = str(decoded.get("candidate") or "").strip()
        binder = str(decoded.get("binder") or "").strip()
        matched = decoded.get("matches")
        if not reviewed or not candidate or not binder or not isinstance(matched, bool):
            return {}
        key = (reviewed, binder, candidate)
        if key in matches:
            return {}
        matches[key] = matched
    return matches


def recursive_field_safety_locator_identity(locator: Mapping[str, object]) -> str:
    """Hash one elaborated field locator without its transport identity."""

    material = {
        key: value for key, value in locator.items() if key != "field_identity_sha256"
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def canonical_recursive_field_safety_locator(
    locator: object,
) -> dict[str, object] | None:
    """Validate one name-independent field-slot locator before Lean sees it.

    A display field name cannot select safety treatment.  The only accepted
    addresses are either an actual projection declaration whose Lean-owned
    ordinal is checked, or an actual constructor declaration plus field slot.
    The locator hash binds that exact tuple into the raw-audit digest.
    """

    if not isinstance(locator, Mapping):
        return None
    kind = str(locator.get("kind") or "").strip()
    identity = str(locator.get("field_identity_sha256") or "").strip().lower()
    field_index = locator.get("field_index")
    if (
        locator.get("schema") != RECURSIVE_FIELD_SAFETY_LOCATOR_SCHEMA
        or kind not in {"projection", "constructor_argument"}
        or type(field_index) is not int
        or field_index < 0
        or len(identity) != 64
        or any(character not in "0123456789abcdef" for character in identity)
    ):
        return None
    declaration_key = "declaration" if kind == "projection" else "constructor"
    declaration = str(locator.get(declaration_key) or "").strip()
    expected_keys = {
        "schema",
        "field_identity_sha256",
        "kind",
        declaration_key,
        "field_index",
    }
    if set(locator) != expected_keys or not declaration or "." not in declaration:
        return None
    canonical = {
        "schema": RECURSIVE_FIELD_SAFETY_LOCATOR_SCHEMA,
        "field_identity_sha256": identity,
        "kind": kind,
        declaration_key: declaration,
        "field_index": field_index,
    }
    if recursive_field_safety_locator_identity(canonical) != identity:
        return None
    return canonical


def parse_recursive_field_proposition_sort_output(
    output: str,
) -> dict[str, dict[str, object]]:
    """Parse exact Lean-owned field payload-safety receipts fail-closed.

    ``field_identity_sha256`` joins each response back to a constructor slot or
    projection slot.  Safety classification is produced by Lean from the
    elaborated type; source field spelling is only display metadata elsewhere.
    """

    payloads: list[dict[str, Any]] = []
    for raw_line in output.splitlines():
        marker = raw_line.find(RECURSIVE_FIELD_PROPOSITION_SORT_SENTINEL)
        if marker < 0:
            continue
        raw_json = raw_line[marker + len(RECURSIVE_FIELD_PROPOSITION_SORT_SENTINEL) :]
        try:
            decoded = json.loads(raw_json)
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        payloads.append(decoded)
    if len(payloads) != 1:
        return {}
    raw_fields = payloads[0].get("fields")
    if not isinstance(raw_fields, list):
        return {}
    results: dict[str, dict[str, object]] = {}
    for raw_field in raw_fields:
        if not isinstance(raw_field, dict):
            return {}
        identity = str(raw_field.get("field_identity_sha256") or "").strip().lower()
        kind = str(raw_field.get("kind") or "").strip()
        declaration_key = "declaration" if kind == "projection" else "constructor"
        declaration = str(raw_field.get(declaration_key) or "").strip()
        field_index_text = str(raw_field.get("field_index") or "").strip()
        value_sort = str(raw_field.get("value_sort") or "").strip()
        payload_safety = str(raw_field.get("payload_safety") or "").strip()
        status = str(raw_field.get("status") or "").strip()
        route = str(raw_field.get("route") or "").strip()
        normalized_type = raw_field.get("normalized_type")
        reason_codes = raw_field.get("reason_codes")
        foundation_module = str(raw_field.get("foundation_module") or "").strip()
        foundation_head = str(raw_field.get("foundation_head") or "").strip()
        allowlist_version = str(
            raw_field.get("foundation_allowlist_version") or ""
        ).strip()
        field_index = int(field_index_text) if field_index_text.isdigit() else -1
        if (
            not identity
            or identity in results
            or kind not in {"projection", "constructor_argument"}
            or not declaration
            or field_index < 0
            or value_sort not in {"true", "false", "unknown"}
            or payload_safety
            not in {
                "structural_data",
                "proof_payload",
                "requires_source_or_lean_closure",
                "requires_semantic_route",
                "unknown",
            }
            or status not in {"ok", "error"}
            or not route
            or not isinstance(normalized_type, str)
            or not normalized_type
            or not isinstance(reason_codes, list)
            or any(not isinstance(code, str) or not code for code in reason_codes)
            or allowlist_version != FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION
            or (
                payload_safety == "structural_data"
                and FOUNDATION_STRUCTURAL_DATA_MODULE_BY_HEAD.get(foundation_head)
                != foundation_module
            )
            or (
                payload_safety != "structural_data"
                and (foundation_head or foundation_module)
            )
        ):
            return {}
        results[identity] = {
            "kind": kind,
            declaration_key: declaration,
            "field_index": field_index,
            "value_sort": value_sort,
            "payload_safety": payload_safety,
            "status": status,
            "route": route,
            "normalized_type": normalized_type,
            "reason_codes": reason_codes,
            "foundation_module": foundation_module,
            "foundation_head": foundation_head,
            "foundation_allowlist_version": allowlist_version,
        }
    return results


def parse_constructor_field_slot_count_output(output: str) -> dict[str, int]:
    """Parse exact Lean-owned stored-field counts fail-closed.

    The count is a structural Lean fact used only to verify that every stored
    constructor slot has an exact field-safety locator.  It comes from
    `CtorInfo.numFields` for inductive constructors and `StructureInfo` for
    generated structure/class `.mk` constructors; source binder labels never
    determine whether a slot exists.
    """

    payloads: list[dict[str, Any]] = []
    for raw_line in output.splitlines():
        marker = raw_line.find(CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL)
        if marker < 0:
            continue
        try:
            decoded = json.loads(
                raw_line[marker + len(CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL) :]
            )
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        payloads.append(decoded)
    if len(payloads) != 1:
        return {}
    raw_constructors = payloads[0].get("constructors")
    if not isinstance(raw_constructors, list):
        return {}
    counts: dict[str, int] = {}
    for raw_constructor in raw_constructors:
        if not isinstance(raw_constructor, dict):
            return {}
        constructor = str(raw_constructor.get("constructor") or "").strip()
        num_fields_text = str(raw_constructor.get("num_fields") or "").strip()
        if not constructor or constructor in counts or not num_fields_text.isdecimal():
            return {}
        counts[constructor] = int(num_fields_text)
    return counts


def parse_inductive_constructor_field_slot_count_output(
    output: str,
) -> dict[str, dict[str, int]]:
    """Parse Lean-owned inductive constructor sets and stored-slot counts."""

    payloads: list[dict[str, Any]] = []
    for raw_line in output.splitlines():
        marker = raw_line.find(INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL)
        if marker < 0:
            continue
        try:
            decoded = json.loads(
                raw_line[
                    marker + len(INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL) :
                ]
            )
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        payloads.append(decoded)
    if len(payloads) != 1:
        return {}
    raw_inductives = payloads[0].get("inductives")
    if not isinstance(raw_inductives, list):
        return {}
    result: dict[str, dict[str, int]] = {}
    for raw_inductive in raw_inductives:
        if not isinstance(raw_inductive, dict):
            return {}
        inductive = str(raw_inductive.get("inductive") or "").strip()
        constructors = raw_inductive.get("constructors")
        if not inductive or inductive in result or not isinstance(constructors, list):
            return {}
        encoded = json.dumps(
            {"constructors": constructors}, separators=(",", ":"), sort_keys=True
        )
        counts = parse_constructor_field_slot_count_output(
            CONSTRUCTOR_FIELD_SLOT_COUNTS_SENTINEL + encoded
        )
        if len(counts) != len(constructors):
            return {}
        result[inductive] = counts
    return result


def parse_type_witness_payload_safety_output(
    output: str,
) -> dict[str, list[dict[str, object]]]:
    """Parse Lean-owned Type-witness safety receipts fail-closed.

    Witness paths are generated from the elaborated proposition expression
    (`Nonempty`, `Exists`, proposition-constructor slots), not from source
    words such as "certificate" or a binder label.  A nonstructural/unknown
    witness must remain visible to the source-record obligation surface.
    """

    payloads: list[dict[str, Any]] = []
    for raw_line in output.splitlines():
        marker = raw_line.find(TYPE_WITNESS_PAYLOAD_SAFETY_SENTINEL)
        if marker < 0:
            continue
        try:
            decoded = json.loads(
                raw_line[marker + len(TYPE_WITNESS_PAYLOAD_SAFETY_SENTINEL) :]
            )
        except json.JSONDecodeError:
            return {}
        if not isinstance(decoded, dict):
            return {}
        payloads.append(decoded)
    if len(payloads) != 1:
        return {}
    raw_declarations = payloads[0].get("declarations")
    if not isinstance(raw_declarations, list):
        return {}
    parsed: dict[str, list[dict[str, object]]] = {}
    for raw_declaration in raw_declarations:
        if not isinstance(raw_declaration, dict):
            return {}
        declaration = str(raw_declaration.get("declaration") or "").strip()
        witnesses = raw_declaration.get("witnesses")
        if not declaration or declaration in parsed or not isinstance(witnesses, list):
            return {}
        parsed_witnesses: list[dict[str, object]] = []
        seen_paths: set[str] = set()
        for raw_witness in witnesses:
            if not isinstance(raw_witness, dict):
                return {}
            path = str(raw_witness.get("path") or "").strip()
            occurrence_role = str(raw_witness.get("occurrence_role") or "").strip()
            witness_type_head = raw_witness.get("witness_type_head")
            value_sort = str(raw_witness.get("value_sort") or "").strip()
            payload_safety = str(raw_witness.get("payload_safety") or "").strip()
            status = str(raw_witness.get("status") or "").strip()
            route = str(raw_witness.get("route") or "").strip()
            normalized_type = raw_witness.get("normalized_type")
            reason_codes = raw_witness.get("reason_codes")
            foundation_head = str(raw_witness.get("foundation_head") or "").strip()
            foundation_module = str(raw_witness.get("foundation_module") or "").strip()
            allowlist_version = str(
                raw_witness.get("foundation_allowlist_version") or ""
            ).strip()
            if (
                not path
                or path in seen_paths
                or occurrence_role != "provided_result"
                or not isinstance(witness_type_head, str)
                or value_sort != "false"
                or payload_safety
                not in {
                    "structural_data",
                    "requires_source_or_lean_closure",
                    "requires_semantic_route",
                    "unknown",
                }
                or status not in {"ok", "error"}
                or not route
                or not isinstance(normalized_type, str)
                or not normalized_type
                or not isinstance(reason_codes, list)
                or any(not isinstance(code, str) or not code for code in reason_codes)
                or allowlist_version != FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION
                or (
                    payload_safety == "structural_data"
                    and FOUNDATION_STRUCTURAL_DATA_MODULE_BY_HEAD.get(foundation_head)
                    != foundation_module
                )
                or (
                    payload_safety != "structural_data"
                    and (foundation_head or foundation_module)
                )
            ):
                return {}
            seen_paths.add(path)
            parsed_witnesses.append(
                {
                    "path": path,
                    "occurrence_role": occurrence_role,
                    "witness_type_head": witness_type_head,
                    "value_sort": value_sort,
                    "payload_safety": payload_safety,
                    "status": status,
                    "route": route,
                    "normalized_type": normalized_type,
                    "reason_codes": reason_codes,
                    "foundation_head": foundation_head,
                    "foundation_module": foundation_module,
                    "foundation_allowlist_version": allowlist_version,
                }
            )
        parsed[declaration] = parsed_witnesses
    return parsed


def _compose_helper_script(script_prefix: str, helper: str, commands: str) -> str:
    """Compose every Meta helper invocation with its exact Lean API import.

    The helper's recursive statement reachability is provided by Lean's
    elaborated-expression and environment APIs. Keeping this preamble in one
    composer prevents a command-specific runner from accidentally falling
    back to a Python- or text-derived graph protocol.
    """

    # The helper is also a standalone compiled Lean module and therefore
    # starts with its own imports.  Hermetic fixtures inject that same source
    # after runner-specific options; imports are no longer legal there.  The
    # common preamble below already imports its complete API requirement, so
    # remove only the contiguous leading imports from the injected copy.
    helper_body = re.sub(r"\A(?:import [^\n]+\n)+", "", helper)
    return (
        "import ImportGraph.Imports.RequiredModules\n"
        f"{script_prefix.rstrip()}\n\n{helper_body}\n\n{commands}\n"
    )


def _compiled_audit_helper_available(root: Path) -> bool:
    """Whether this checkout can import the separately compiled audit helper.

    Minimal temporary fixtures intentionally retain the injected-source path;
    a production checkout uses the compiled helper so reviewing a large paper
    does not elaborate the helper implementation in the same Lean process.
    """

    return (root / COMPILED_AUDIT_HELPER_SOURCE).is_file()


def _build_compiled_audit_helper(root: Path, timeout_seconds: int) -> bool:
    """Build the audit helper explicitly, never as a paper-theorem dependency."""

    if not _compiled_audit_helper_available(root):
        return False
    try:
        proc = subprocess.run(
            ["lake", "build", COMPILED_AUDIT_HELPER_MODULE],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return proc.returncode == 0


def _emit_manifest_timeout_diagnostic(
    declaration_names: Iterable[str],
    *,
    timeout_seconds: int,
    completed_declarations: Iterable[str],
) -> None:
    """Emit one bounded, machine-readable diagnostic for a killed Lean batch."""

    requested = sorted(
        {str(name).strip() for name in declaration_names if str(name).strip()}
    )
    completed = {
        str(name).strip() for name in completed_declarations if str(name).strip()
    }
    missing = [name for name in requested if name not in completed]
    payload = {
        "schema": 1,
        "timeout_seconds": timeout_seconds,
        "requested_count": len(requested),
        "completed_count": len(requested) - len(missing),
        "missing_count": len(missing),
        "missing_declarations": missing[:8],
        "missing_declarations_truncated": len(missing) > 8,
    }
    print(
        LEAN_SIGNATURE_MANIFEST_TIMEOUT_SENTINEL
        + json.dumps(payload, sort_keys=True, separators=(",", ":")),
        file=sys.stderr,
    )


def _run_manifest_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    timeout_seconds: int,
    audit_modules: str = "",
    hash_tool_path: str | None = None,
) -> dict[str, dict[str, Any]]:
    if not declaration_names or not HELPER_PATH.exists():
        return {}
    if hash_tool_path is None:
        hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
        if hash_tool_identity is None:
            return {}
        hash_tool_path = hash_tool_identity["resolved_path"]
    try:
        resolved_hash_tool = str(Path(hash_tool_path).resolve(strict=True))
    except OSError:
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        f"#signature_manifest {json.dumps(name)} {json.dumps(audit_modules)} "
        f"{json.dumps(resolved_hash_tool)}"
        for name in declaration_names
    )
    # The subprocess wall timeout is the operational resource bound. Large
    # but finite elaborated signatures must not fail earlier because Lean's
    # unrelated default heartbeat/recursion limits are lower than that bound.
    manifest_prefix = (
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0"
    )
    script = _compose_helper_script(manifest_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "signature_manifest.lean"
        path.write_text(script, encoding="utf-8")
        timed_out = False
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, _stderr = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                stdout_bytes, _stderr = proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                _emit_manifest_timeout_diagnostic(
                    declaration_names,
                    timeout_seconds=timeout_seconds,
                    completed_declarations=(),
                )
                return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0 and not timed_out:
        diagnostic = _stderr.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean signature-manifest extraction failed:\n" + diagnostic[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_signature_manifest_output(stdout)
    if timed_out:
        _emit_manifest_timeout_diagnostic(
            declaration_names,
            timeout_seconds=timeout_seconds,
            completed_declarations=parsed,
        )
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_SIGNATURE_MANIFEST_DIAGNOSTIC:" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
        elif stdout.strip():
            print(
                "Lean direct-library dependency extraction returned no valid receipt:\n"
                + stdout[:8000],
                file=sys.stderr,
            )
    return parsed


def _run_direct_library_dependency_surface_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    timeout_seconds: int,
) -> dict[str, tuple[str, ...]]:
    """Ask Lean for direct EconCSLib dependencies without materializing graphs.

    This intentionally has a much smaller memory profile than a full signature
    manifest: it uses the same elaborated declaration bodies, but returns only
    the direct reusable-library coordinates required to construct the human
    source-to-library review surface.
    """

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    if not names or not HELPER_PATH.exists():
        return {}
    try:
        helper = HELPER_PATH.read_text(encoding="utf-8")
    except OSError:
        return {}
    script = _compose_helper_script(
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0",
        helper,
        "#direct_library_dependency_surface " + json.dumps(json.dumps(names)),
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "direct_library_dependency_surface.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, stderr_bytes = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
            return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        diagnostic = stderr_bytes.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean direct-library dependency extraction failed:\n" + diagnostic[:8000],
                file=sys.stderr,
            )
        else:
            print(
                "Lean direct-library dependency extraction failed without stderr "
                f"(exit {proc.returncode}):\n"
                + stdout_bytes.decode("utf-8", errors="replace")[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_direct_library_dependency_surface_output(stdout, names)
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_DIRECT_LIBRARY_DEPENDENCY_SURFACE" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
    return parsed


def _run_manifest_revalidation_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    timeout_seconds: int,
    audit_modules: str,
    hash_tool_path: str,
) -> dict[str, dict[str, Any]]:
    """Run compact item-level receipts without rebuilding full manifests."""

    if not declaration_names or not HELPER_PATH.exists():
        return {}
    try:
        resolved_hash_tool = str(Path(hash_tool_path).resolve(strict=True))
    except OSError:
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        f"#signature_manifest_revalidation {json.dumps(name)} "
        f"{json.dumps(audit_modules)} {json.dumps(resolved_hash_tool)}"
        for name in declaration_names
    )
    script = _compose_helper_script(
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0",
        helper,
        commands,
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "signature_manifest_revalidation.lean"
        path.write_text(script, encoding="utf-8")
        timed_out = False
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, stderr_bytes = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                stdout_bytes, stderr_bytes = proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                _emit_manifest_timeout_diagnostic(
                    declaration_names,
                    timeout_seconds=timeout_seconds,
                    completed_declarations=(),
                )
                return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0 and not timed_out:
        diagnostic = stderr_bytes.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean signature-manifest item revalidation failed:\n"
                + diagnostic[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_signature_manifest_revalidation_output(stdout)
    if timed_out:
        _emit_manifest_timeout_diagnostic(
            declaration_names,
            timeout_seconds=timeout_seconds,
            completed_declarations=parsed,
        )
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_SIGNATURE_MANIFEST_REVALIDATION_DIAGNOSTIC:" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
    return parsed


def _run_proposition_spec_proof_script(
    root: Path,
    script_prefix: str,
    routes: list[tuple[str, str]],
    timeout_seconds: int,
) -> dict[tuple[str, str], bool]:
    if not routes or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        f"#proposition_spec_proof_match {json.dumps(spec)} {json.dumps(proof)}"
        for spec, proof in routes
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "proposition_spec_proof_match.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_proposition_spec_proof_output(stdout)


def _run_semantic_contract_script(
    root: Path,
    script_prefix: str,
    routes: list[tuple[str, str, str]],
    timeout_seconds: int,
) -> dict[tuple[str, str, str], bool]:
    if not routes or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        f"#semantic_contract_match {json.dumps(spec)} {json.dumps(evidence)} {json.dumps(mode)}"
        for spec, evidence, mode in routes
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "semantic_contract_match.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_semantic_contract_output(stdout)


def _run_operational_outcome_domain_bridge_script(
    root: Path,
    script_prefix: str,
    routes: list[OperationalOutcomeDomainRoute],
    timeout_seconds: int,
) -> dict[OperationalOutcomeDomainRoute, bool]:
    """Ask Lean to check terminal-existence bridges for result domains."""

    if not routes or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        "#operational_outcome_domain_bridge "
        f"{json.dumps(target)} {json.dumps(bridge)} "
        f"{json.dumps(str(model_index))} {json.dumps(str(terminal_index))} "
        f"{json.dumps(str(run_index))} {json.dumps(str(terminal_predicate_index))} "
        f"{json.dumps(model_root)} {json.dumps(transition_root)}"
        for (
            target,
            bridge,
            model_index,
            terminal_index,
            run_index,
            terminal_predicate_index,
            model_root,
            transition_root,
        ) in routes
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "operational_outcome_domain_bridge.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_operational_outcome_domain_bridge_output(stdout)


def _run_operational_outcome_state_transition_bridge_script(
    root: Path,
    script_prefix: str,
    routes: list[OperationalOutcomeStateTransitionRoute],
    timeout_seconds: int,
) -> dict[OperationalOutcomeStateTransitionRoute, bool]:
    """Ask Lean to check result-local state/transition nonvacuity bridges."""

    if not routes or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        "#operational_outcome_state_transition_bridge "
        f"{json.dumps(target)} {json.dumps(bridge)} {json.dumps(initial_witness)} "
        f"{json.dumps(str(model_index))} {json.dumps(str(state_index))} "
        f"{json.dumps(str(initial_predicate_index))} {json.dumps(str(terminal_index))} "
        f"{json.dumps(str(run_index))} {json.dumps(str(terminal_predicate_index))} "
        f"{json.dumps(model_root)} {json.dumps(state_root)} {json.dumps(transition_root)}"
        for (
            target,
            bridge,
            initial_witness,
            model_index,
            state_index,
            initial_predicate_index,
            terminal_index,
            run_index,
            terminal_predicate_index,
            model_root,
            state_root,
            transition_root,
        ) in routes
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "operational_outcome_state_transition_bridge.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_operational_outcome_state_transition_bridge_output(stdout)


def _run_semantic_contract_transparency_script(
    root: Path,
    script_prefix: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    max_expansions: int,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Run the Lean-owned transitive wrapper scan for one fixed module scope."""

    if (
        not specification_names
        or not HELPER_PATH.exists()
        or not (1 <= max_expansions <= 4096)
        or any(not module for module in paper_modules)
    ):
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    encoded_scope = json.dumps(list(paper_modules), ensure_ascii=True)
    commands = "\n".join(
        "#semantic_contract_transparency "
        f"{json.dumps(specification)} {json.dumps(encoded_scope)} "
        f"{json.dumps(str(max_expansions))}"
        for specification in specification_names
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "semantic_contract_transparency.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_semantic_contract_transparency_output(stdout)


def _terminate_semantic_contract_closure_process(proc: Any) -> None:
    """Best-effort termination that remains usable in restricted runtimes."""

    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except OSError:
        try:
            proc.kill()
        except (AttributeError, OSError):
            pass


def _run_semantic_contract_closure_script(
    root: Path,
    script_prefix: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    workspace_modules: tuple[str, ...],
    foundation_modules: tuple[str, ...],
    *,
    hash_tool_path: str | None = None,
    inline_paper_scope: bool,
    use_compiled_helper: bool = False,
    max_expansions: int,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Run the Lean-owned elaborated closure manifest for exact `Spec` names."""

    resolved_hash_tool = hash_tool_path or shutil.which("sha256sum") or ""
    try:
        resolved_hash_tool = str(Path(resolved_hash_tool).resolve(strict=True))
    except OSError:
        return {}
    if (
        not specification_names
        or not HELPER_PATH.exists()
        or not (1 <= max_expansions <= 4096)
        or any(not module for module in paper_modules)
        or any(not module for module in workspace_modules)
        or any(not module for module in foundation_modules)
    ):
        return {}
    if use_compiled_helper:
        if not _compiled_audit_helper_available(root):
            return {}
        helper = ""
        script_prefix = script_prefix + f"\nimport {COMPILED_AUDIT_HELPER_MODULE}"
    else:
        helper = HELPER_PATH.read_text(encoding="utf-8")
    encoded_scope = json.dumps(
        {
            "paper_modules": list(paper_modules),
            "workspace_modules": list(workspace_modules),
            "foundation_modules": list(foundation_modules),
            "hash_tool_path": resolved_hash_tool,
            "inline_paper_scope": inline_paper_scope,
        },
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    commands = "\n".join(
        "#semantic_contract_closure "
        f"{json.dumps(specification)} {json.dumps(encoded_scope)} "
        f"{json.dumps(str(max_expansions))}"
        for specification in specification_names
    )
    # `max_expansions` remains the semantic traversal fuel.  The finite Lean
    # budgets below are a separate host-protection boundary: they turn a
    # pathological elaborated closure into a fail-closed receipt failure,
    # rather than allowing it to consume the parent process's resources.
    closure_prefix = (
        script_prefix
        + f"\nset_option maxRecDepth {SEMANTIC_CONTRACT_CLOSURE_MAX_RECURSION_DEPTH}"
        + f"\nset_option maxHeartbeats {SEMANTIC_CONTRACT_CLOSURE_MAX_HEARTBEATS}"
    )
    script = _compose_helper_script(closure_prefix, helper, commands)

    def emit_runner_failure(
        failure_kind: str,
        *,
        detail: str = "",
        returncode: int | None = None,
        signal_number: int | None = None,
    ) -> None:
        requested = sorted({name.strip() for name in specification_names if name.strip()})
        payload: dict[str, Any] = {
            "schema": 1,
            "failure_kind": failure_kind,
            "timeout_seconds": timeout_seconds,
            "max_expansions": max_expansions,
            "max_recursion_depth": SEMANTIC_CONTRACT_CLOSURE_MAX_RECURSION_DEPTH,
            "max_heartbeats": SEMANTIC_CONTRACT_CLOSURE_MAX_HEARTBEATS,
            "max_memory_mb": SEMANTIC_CONTRACT_CLOSURE_MAX_MEMORY_MB,
            "max_threads": SEMANTIC_CONTRACT_CLOSURE_MAX_THREADS,
            "max_address_space_bytes": SEMANTIC_CONTRACT_CLOSURE_MAX_ADDRESS_SPACE_BYTES,
            "address_space_runner": "posix_exec_trampoline",
            "requested_count": len(requested),
            "requested_specifications": requested[:8],
            "requested_specifications_truncated": len(requested) > 8,
        }
        if returncode is not None:
            payload["returncode"] = returncode
        if signal_number is not None:
            payload["signal_number"] = signal_number
        if detail:
            payload["detail"] = detail[:2000]
        print(
            SEMANTIC_CONTRACT_CLOSURE_RUNNER_FAILURE_SENTINEL
            + json.dumps(payload, sort_keys=True, separators=(",", ":")),
            file=sys.stderr,
        )

    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "semantic_contract_closure.lean"
        path.write_text(script, encoding="utf-8")
        if not CLOSURE_SUBPROCESS_TRAMPOLINE_PATH.is_file():
            emit_runner_failure("runner_unavailable")
            return {}
        try:
            proc = subprocess.Popen(
                [
                    sys.executable,
                    str(CLOSURE_SUBPROCESS_TRAMPOLINE_PATH),
                    "--address-space-bytes",
                    str(SEMANTIC_CONTRACT_CLOSURE_MAX_ADDRESS_SPACE_BYTES),
                    "--",
                    "lake",
                    "env",
                    "lean",
                    "-M",
                    str(SEMANTIC_CONTRACT_CLOSURE_MAX_MEMORY_MB),
                    "-j",
                    str(SEMANTIC_CONTRACT_CLOSURE_MAX_THREADS),
                    str(path),
                ],
                cwd=str(root),
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
                close_fds=True,
            )
        except OSError as error:
            emit_runner_failure("startup_error", detail=str(error))
            return {}
        try:
            stdout, stderr = proc.communicate(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            _terminate_semantic_contract_closure_process(proc)
            try:
                stdout, stderr = proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                stdout, stderr = "", ""
            emit_runner_failure("wall_timeout")
            if stderr.strip():
                print(stderr[:8000], file=sys.stderr)
            return {}
        except OSError as error:
            _terminate_semantic_contract_closure_process(proc)
            emit_runner_failure("communication_error", detail=str(error))
            return {}
    if proc.returncode != 0:
        diagnostic_stream = stderr if stderr.strip() else stdout
        preview = diagnostic_stream[:8000]
        if len(diagnostic_stream) > len(preview):
            preview += "\n[Lean diagnostic truncated]"
        if proc.returncode < 0:
            emit_runner_failure(
                "signal_exit",
                detail=preview,
                returncode=proc.returncode,
                signal_number=-proc.returncode,
            )
        else:
            emit_runner_failure(
                "nonzero_exit",
                detail=preview,
                returncode=proc.returncode,
            )
        print(
            "Lean semantic-contract closure extraction failed with exit code "
            + str(proc.returncode)
            + ((":\n" + preview) if preview.strip() else " and no diagnostic"),
            file=sys.stderr,
        )
        return {}
    output_bytes = len(stdout.encode("utf-8"))
    if output_bytes > MAX_SEMANTIC_CONTRACT_CLOSURE_OUTPUT_BYTES:
        diagnostic = {
            "schema": 1,
            "output_bytes": output_bytes,
            "max_output_bytes": MAX_SEMANTIC_CONTRACT_CLOSURE_OUTPUT_BYTES,
            "requested_specifications": len(specification_names),
        }
        print(
            SEMANTIC_CONTRACT_CLOSURE_OUTPUT_LIMIT_SENTINEL
            + json.dumps(diagnostic, sort_keys=True, separators=(",", ":")),
            file=sys.stderr,
        )
        return {}
    diagnostics = [
        line[line.find(SEMANTIC_CONTRACT_CLOSURE_ERROR_SENTINEL) :]
        for line in stdout.splitlines()
        if SEMANTIC_CONTRACT_CLOSURE_ERROR_SENTINEL in line
    ]
    if diagnostics:
        print("\n".join(diagnostics), file=sys.stderr)
    if not stdout.strip():
        detail = stderr[:4000].strip()
        print(
            "Lean semantic-contract closure extraction emitted no receipt for the requested batch"
            + ("\n" + detail if detail else ""),
            file=sys.stderr,
        )
    parsed = parse_semantic_contract_closure_output(stdout)
    if not parsed and stdout.strip():
        preview = stdout[:8000]
        if len(stdout) > len(preview):
            preview += "\n[closure output truncated]"
        print(
            "Lean emitted a malformed semantic-contract closure receipt:\n" + preview,
            file=sys.stderr,
        )
    return parsed


def _semantic_contract_transparency_batches(names: list[str]) -> list[list[str]]:
    """Split bounded paper-closeout requests without inspecting declarations."""

    maximum_rows = (
        SEMANTIC_CONTRACT_TRANSPARENCY_CHUNK_SIZE
        * MAX_SEMANTIC_CONTRACT_TRANSPARENCY_CHUNKS
    )
    if MIN_CHUNKED_SEMANTIC_CONTRACT_TRANSPARENCY_ROWS <= len(names) <= maximum_rows:
        return [
            names[index : index + SEMANTIC_CONTRACT_TRANSPARENCY_CHUNK_SIZE]
            for index in range(0, len(names), SEMANTIC_CONTRACT_TRANSPARENCY_CHUNK_SIZE)
        ]
    return [names]


def _semantic_contract_closure_batches(names: list[str]) -> list[list[str]]:
    """Split closure requests by row count only, never declaration spelling."""

    maximum_rows = (
        SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE * MAX_SEMANTIC_CONTRACT_CLOSURE_CHUNKS
    )
    if MIN_CHUNKED_SEMANTIC_CONTRACT_CLOSURE_ROWS <= len(names) <= maximum_rows:
        return [
            names[index : index + SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE]
            for index in range(0, len(names), SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE)
        ]
    return [names]


def _requested_semantic_contract_transparency_checks(
    checks: dict[str, dict[str, Any]], names: list[str]
) -> dict[str, dict[str, Any]]:
    """Retain only exact requested routes; missing Lean output remains a failure."""

    return {name: checks[name] for name in names if name in checks}


def _requested_semantic_contract_closure_manifests(
    manifests: dict[str, dict[str, Any]], names: list[str]
) -> dict[str, dict[str, Any]]:
    """Retain only exact requested closure rows; missing Lean output fails closed."""

    return {name: manifests[name] for name in names if name in manifests}


def _semantic_contract_match_batches(
    routes: list[tuple[str, str, str]],
) -> list[list[tuple[str, str, str]]]:
    """Split bounded exact-contract requests without inspecting route content."""

    maximum_routes = (
        SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE * MAX_SEMANTIC_CONTRACT_MATCH_CHUNKS
    )
    if MIN_CHUNKED_SEMANTIC_CONTRACT_MATCH_ROUTES <= len(routes) <= maximum_routes:
        return [
            routes[index : index + SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE]
            for index in range(0, len(routes), SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE)
        ]
    return [routes]


def _requested_semantic_contract_matches(
    matches: dict[tuple[str, str, str], bool],
    routes: list[tuple[str, str, str]],
) -> dict[tuple[str, str, str], bool]:
    """Keep only exact requested contract output in deterministic route order."""

    return {route: matches[route] for route in routes if route in matches}


def _run_source_premise_false_scan_script(
    root: Path,
    script_prefix: str,
    reviewed_names: list[str],
    audit_modules: tuple[str, ...],
    timeout_seconds: int,
) -> dict[str, list[dict[str, Any]]]:
    if not reviewed_names or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    reviewed_json = json.dumps(reviewed_names, ensure_ascii=True)
    scope = ",".join(audit_modules)
    command = (
        f"#source_premise_false_scan {json.dumps(reviewed_json)} {json.dumps(scope)}"
    )
    script = _compose_helper_script(script_prefix, helper, command)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "source_premise_false_scan.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_source_premise_false_scan_output(stdout)


def _run_constructor_result_type_match_script(
    root: Path,
    script_prefix: str,
    routes: list[tuple[str, str, str]],
    timeout_seconds: int,
    *,
    lean_path: str | None = None,
) -> dict[tuple[str, str, str], bool]:
    """Ask Lean whether each candidate can construct the exact reviewed type.

    ``lean_path`` is used only by the current-source constructor gate.  It
    places an isolated freshly elaborated review artifact ahead of Lake's
    ordinary build output, so an import cannot silently resolve an older
    ``PaperInterface.olean`` with the same module name.
    """

    if not routes or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    commands = "\n".join(
        "#constructor_result_type_match "
        f"{json.dumps(reviewed)} {json.dumps(binder)} "
        f"{json.dumps(candidate)}"
        for reviewed, binder, candidate in routes
    )
    script = _compose_helper_script(script_prefix, helper, commands)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "constructor_result_type_match.lean"
        path.write_text(script, encoding="utf-8")
        command = ["lake", "env", "lean", str(path)]
        if lean_path is not None:
            command = [
                "lake",
                "env",
                "env",
                f"LEAN_PATH={lean_path}",
                "lean",
                str(path),
            ]
        try:
            proc = subprocess.Popen(
                command,
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_constructor_result_type_match_output(stdout)


def _run_recursive_field_proposition_sort_script(
    root: Path,
    script_prefix: str,
    locators: list[dict[str, object]],
    timeout_seconds: int,
) -> dict[str, dict[str, object]]:
    """Ask Lean for exact constructor/projection field-safety receipts."""

    if not locators or not HELPER_PATH.exists():
        return {}
    canonical_locators: list[dict[str, object]] = []
    seen_identities: set[str] = set()
    for locator in locators:
        canonical = canonical_recursive_field_safety_locator(locator)
        if canonical is None:
            return {}
        identity = str(canonical["field_identity_sha256"])
        if identity in seen_identities:
            return {}
        seen_identities.add(identity)
        canonical_locators.append(canonical)
    canonical_locators.sort(key=lambda locator: str(locator["field_identity_sha256"]))
    helper = HELPER_PATH.read_text(encoding="utf-8")
    # The helper receives canonical string encodings for numeric transport.
    # The generated raw locator itself remains typed and hash-bound above.
    encoded_fields = json.dumps(
        [
            {
                "schema": str(locator["schema"]),
                "field_identity_sha256": locator["field_identity_sha256"],
                "kind": locator["kind"],
                (
                    "declaration" if locator["kind"] == "projection" else "constructor"
                ): locator[
                    "declaration" if locator["kind"] == "projection" else "constructor"
                ],
                "field_index": str(locator["field_index"]),
            }
            for locator in canonical_locators
        ],
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    command = "#recursive_field_proposition_sort " + json.dumps(encoded_fields)
    script = _compose_helper_script(script_prefix, helper, command)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "recursive_field_proposition_sort.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    parsed = parse_recursive_field_proposition_sort_output(stdout)
    if set(parsed) != seen_identities:
        return {}
    receipts: dict[str, dict[str, object]] = {}
    for locator in canonical_locators:
        identity = str(locator["field_identity_sha256"])
        receipt = parsed.get(identity)
        if not isinstance(receipt, dict):
            return {}
        declaration_key = (
            "declaration" if locator["kind"] == "projection" else "constructor"
        )
        if (
            receipt.get("kind") != locator["kind"]
            or receipt.get(declaration_key) != locator[declaration_key]
            or receipt.get("field_index") != locator["field_index"]
        ):
            return {}
        normalized_type = receipt.pop("normalized_type", None)
        if not isinstance(normalized_type, str):
            return {}
        receipt["schema"] = RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA
        receipt["field_identity_sha256"] = identity
        receipt["normalized_type_sha256"] = hashlib.sha256(
            normalized_type.encode("utf-8")
        ).hexdigest()
        receipt["foundation_allowlist_sha256"] = (
            FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256
        )
        receipts[identity] = receipt
    return receipts


def _recursive_field_safety_batches(
    locators: list[dict[str, object]],
) -> list[list[dict[str, object]]]:
    """Partition large exact field-slot probes without using field names.

    The bound is based only on the number of Lean-owned locators. For very
    large surfaces, widen the batches just enough to cap process fan-out while
    retaining a failure boundary much smaller than the whole paper model.
    """

    if not locators:
        return []
    if len(locators) <= RECURSIVE_FIELD_SAFETY_CHUNK_SIZE:
        return [locators]
    width = max(
        RECURSIVE_FIELD_SAFETY_CHUNK_SIZE,
        (len(locators) + MAX_RECURSIVE_FIELD_SAFETY_CHUNKS - 1)
        // MAX_RECURSIVE_FIELD_SAFETY_CHUNKS,
    )
    return [locators[index : index + width] for index in range(0, len(locators), width)]


def _run_constructor_field_slot_count_script(
    root: Path,
    script_prefix: str,
    constructor_names: list[str],
    timeout_seconds: int,
) -> dict[str, int]:
    """Ask Lean for exact stored-field counts for constructor-like names.

    Inductives use `CtorInfo.numFields`; generated structure/class `.mk`
    declarations resolve through their owning elaborated `StructureInfo`.
    """

    names = sorted({name.strip() for name in constructor_names if name.strip()})
    if not names or len(names) != len(constructor_names) or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    command = "#constructor_field_slot_counts " + json.dumps(
        json.dumps(names, ensure_ascii=True, separators=(",", ":"))
    )
    script = _compose_helper_script(script_prefix, helper, command)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "constructor_field_slot_counts.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_constructor_field_slot_count_output(stdout)


def _run_inductive_constructor_field_slot_count_script(
    root: Path,
    script_prefix: str,
    inductive_names: list[str],
    timeout_seconds: int,
) -> dict[str, dict[str, int]]:
    """Ask Lean for each exact `InductInfo.ctors` set and slot count."""

    names = sorted({name.strip() for name in inductive_names if name.strip()})
    if not names or len(names) != len(inductive_names) or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    command = "#inductive_constructor_field_slot_counts " + json.dumps(
        json.dumps(names, ensure_ascii=True, separators=(",", ":"))
    )
    script = _compose_helper_script(script_prefix, helper, command)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "inductive_constructor_field_slot_counts.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    return parse_inductive_constructor_field_slot_count_output(stdout)


def _run_type_witness_payload_safety_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    timeout_seconds: int,
) -> dict[str, list[dict[str, object]]]:
    """Ask Lean for elaborated Type-witness payload receipts."""

    names = sorted({name.strip() for name in declaration_names if name.strip()})
    if not names or len(names) != len(declaration_names) or not HELPER_PATH.exists():
        return {}
    helper = HELPER_PATH.read_text(encoding="utf-8")
    command = "#type_witness_payload_safety " + json.dumps(
        json.dumps(names, ensure_ascii=True, separators=(",", ":"))
    )
    script = _compose_helper_script(script_prefix, helper, command)
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "type_witness_payload_safety.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            return {}
    if proc.returncode != 0:
        return {}
    parsed = parse_type_witness_payload_safety_output(stdout)
    # The helper normally emits one aggregate payload, but a future
    # declaration-local helper error must not erase receipts that Lean did
    # emit for other exact declarations.  Unexpected identities remain a
    # fail-closed protocol error; omitted identities are isolated by the
    # caller's name-independent bisection below.
    if not set(parsed).issubset(set(names)):
        return {}
    receipts: dict[str, list[dict[str, object]]] = {}
    for name in names:
        if name not in parsed:
            continue
        normalized: list[dict[str, object]] = []
        for raw_receipt in parsed[name]:
            receipt = dict(raw_receipt)
            normalized_type = receipt.pop("normalized_type", None)
            if not isinstance(normalized_type, str):
                return {}
            receipt["schema"] = TYPE_WITNESS_PAYLOAD_SAFETY_SCHEMA
            receipt["normalized_type_sha256"] = hashlib.sha256(
                normalized_type.encode("utf-8")
            ).hexdigest()
            receipt["foundation_allowlist_sha256"] = (
                FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256
            )
            normalized.append(receipt)
        receipts[name] = normalized
    return receipts


def _type_witness_payload_safety_batches(names: list[str]) -> list[list[str]]:
    """Partition exact Type-witness probes without inspecting declaration names.

    The initial width bounds process fan-out for large paper interfaces.  A
    failed batch is recursively split by request position so that every
    declaration receives either Lean-owned receipts or an explicit missing
    receipt surface at its caller; a failure never becomes an empty witness
    list.
    """

    if not names:
        return []
    if len(names) <= TYPE_WITNESS_PAYLOAD_SAFETY_CHUNK_SIZE:
        return [names]
    width = max(
        TYPE_WITNESS_PAYLOAD_SAFETY_CHUNK_SIZE,
        (len(names) + MAX_TYPE_WITNESS_PAYLOAD_SAFETY_CHUNKS - 1)
        // MAX_TYPE_WITNESS_PAYLOAD_SAFETY_CHUNKS,
    )
    return [names[index : index + width] for index in range(0, len(names), width)]


def _collect_type_witness_payload_safeties(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    timeout_seconds: int,
    *,
    execution_counts: dict[str, int] | None = None,
) -> dict[str, list[dict[str, object]]]:
    """Collect all independently obtainable Type-witness receipts.

    An individual declaration can legitimately have zero witnesses, which is
    represented by a successful empty list.  In contrast, a missing mapping
    entry means Lean produced no valid receipt for that exact declaration even
    after singleton isolation.  Callers must surface that distinction as a
    failure rather than treating it as no witnesses.
    """

    found: dict[str, list[dict[str, object]]] = {}
    batches = _type_witness_payload_safety_batches(declaration_names)
    if execution_counts is not None:
        execution_counts["batch_count"] = 0
        execution_counts["isolation_retry_count"] = 0
    uses_chunking = len(batches) > 1
    batch_timeout = (
        min(timeout_seconds, MAX_CHUNKED_TYPE_WITNESS_PAYLOAD_SAFETY_TIMEOUT_SECONDS)
        if uses_chunking
        else timeout_seconds
    )
    for batch in batches:
        # The helper's current aggregate command is all-or-nothing: one
        # traversal exhaustion can suppress the entire payload.  Recurse only
        # over exact names still lacking a result.  This is independent of
        # theorem names, result shapes, and source wording.
        pending_batches = [batch]
        while pending_batches:
            current_batch = pending_batches.pop()
            if execution_counts is not None:
                execution_counts["batch_count"] += 1
            extracted = _run_type_witness_payload_safety_script(
                root,
                script_prefix,
                current_batch,
                batch_timeout,
            )
            requested = set(current_batch)
            found.update(
                {
                    name: receipts
                    for name, receipts in extracted.items()
                    if name in requested
                }
            )
            missing = [name for name in current_batch if name not in found]
            if len(missing) > 1:
                midpoint = len(missing) // 2
                pending_batches.append(missing[midpoint:])
                pending_batches.append(missing[:midpoint])
                if execution_counts is not None:
                    execution_counts["isolation_retry_count"] += 2
    return {name: found[name] for name in declaration_names if name in found}


def _review_source_module_name(root: Path, source_path: Path) -> str | None:
    """Return the Lean module dictated by one repository source path.

    The constructor gate is only meaningful when its reviewed declaration is
    imported from the exact source file the source-record audit parsed.  This
    mapping comes from the Lean library layout, not declaration names.
    """

    try:
        relative = source_path.resolve().relative_to(root.resolve()).with_suffix("")
    except (OSError, ValueError):
        return None
    parts = list(relative.parts)
    if parts and parts[0] == "papers":
        parts = parts[1:]
    if not parts:
        return None
    return ".".join(parts)


def _source_sha256(path: Path) -> str | None:
    """Return a content identity, or ``None`` when it cannot be read."""

    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def _lake_env_lean_path(root: Path, timeout_seconds: int) -> str | None:
    """Read Lake's configured Lean search path without inheriting stale output."""

    try:
        proc = subprocess.run(
            ["lake", "env"],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    for line in proc.stdout.splitlines():
        if line.startswith("LEAN_PATH="):
            value = line.removeprefix("LEAN_PATH=")
            return value or None
    return None


def _closure_module_artifact_sha256(path: Path) -> str:
    """Return an exact content pin for one compiled module artifact.

    Filesystem metadata is deliberately not a trust identity. A caller may
    memoize this result only inside an immutable paper transaction; this
    standalone helper rereads bytes so restored timestamps cannot retain a
    stale semantic closure.
    """

    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _closure_module_artifact_location(
    root: Path,
    module_origin: str,
    lean_path: str | None,
) -> tuple[str, Path] | None:
    """Resolve one module by Lean's ordered search path and classify its owner."""

    module_parts = [part for part in module_origin.split(".") if part]
    if not module_parts or ".".join(module_parts) != module_origin:
        return None
    relative = Path(*module_parts).with_suffix(".olean")
    workspace_root = root / ".lake" / "build" / "lib" / "lean"
    candidates: list[Path] = []
    if lean_path:
        candidates.extend(
            Path(entry) / relative for entry in lean_path.split(os.pathsep) if entry
        )
    else:
        # Test and bootstrap callers may not have a Lake environment yet. The
        # production closure path requires a nonempty `lake env` search path.
        candidates.append(workspace_root / relative)
    try:
        resolved_workspace_root = workspace_root.resolve()
    except OSError:
        return None
    seen: set[Path] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved in seen or not resolved.is_file():
            continue
        seen.add(resolved)
        scope = (
            "workspace"
            if resolved.is_relative_to(resolved_workspace_root)
            else "external"
        )
        return scope, resolved
    return None


def _closure_module_artifact_identity(
    root: Path,
    module_origin: str,
    lean_path: str | None,
) -> dict[str, str]:
    """Pin one closure module by its exact loaded `.olean` content when found.

    The Lean helper already determines the module origin.  This function only
    resolves that exact module to the current Lake search path and hashes its
    compiled artifact; it never infers a dependency from a declaration name.
    """

    location = _closure_module_artifact_location(root, module_origin, lean_path)
    if location is not None:
        scope, resolved = location
        return {
            "module_origin": module_origin,
            "artifact_scope": scope,
            "artifact_sha256": _closure_module_artifact_sha256(resolved),
        }
    return {
        "module_origin": module_origin,
        "artifact_scope": "unresolved",
        "artifact_sha256": "",
    }


def _with_semantic_dependency_module_identities(
    root: Path,
    manifests: Mapping[str, Mapping[str, Any]],
    *,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Attach exact artifacts for modules reached by each elaborated row graph."""

    def graph_origins(graph: Mapping[str, Any], *, lane: str) -> set[str]:
        field = (
            "semantic_external_module_origins"
            if lane == "semantic"
            else "realization_external_module_origins"
        )
        raw_origins = graph.get(field)
        origins = (
            {
                str(origin).strip()
                for origin in raw_origins
                if str(origin).strip() not in {"", "<inline>", "<internal>"}
            }
            if isinstance(raw_origins, list)
            else set()
        )
        nodes = graph.get("nodes")
        if not isinstance(nodes, list):
            return origins
        for node in nodes:
            if not isinstance(node, Mapping):
                continue
            statement_reachable = node.get("statement_reachable") is True
            if lane == "semantic" and not statement_reachable:
                continue
            if (
                node.get("origin_class") == "review_closure"
                and node.get("declaration_kind") == "opaque"
            ):
                origin = str(node.get("module_origin") or "").strip()
                if origin not in {"", "<inline>", "<internal>"}:
                    origins.add(origin)
            if (
                lane == "realization"
                and node.get("origin_class") == "review_closure"
                and not statement_reachable
            ):
                origin = str(node.get("module_origin") or "").strip()
                if origin not in {"", "<inline>", "<internal>"}:
                    origins.add(origin)
        return origins

    environment_identities: list[dict[str, str]] = []
    for relative in ("lean-toolchain", "lake-manifest.json"):
        path = root / relative
        try:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError:
            digest = ""
        environment_identities.append({"path": relative, "sha256": digest})

    reached_origins: set[str] = set()
    for manifest in manifests.values():
        graph = manifest.get("semantic_dependency_graph")
        if not isinstance(graph, Mapping):
            continue
        reached_origins.update(graph_origins(graph, lane="realization"))
    lean_path = _lake_env_lean_path(root, timeout_seconds) if reached_origins else None
    identities_by_origin = {
        origin: _closure_module_artifact_identity(root, origin, lean_path)
        for origin in sorted(reached_origins)
    }
    attached: dict[str, dict[str, Any]] = {}
    for declaration, raw_manifest in manifests.items():
        manifest = dict(raw_manifest)
        graph = manifest.get("semantic_dependency_graph")
        # Some narrow callers mock only the canonical signature surface. Do
        # not turn that partial test protocol into a malformed dependency
        # manifest; production helper output always includes the graph and is
        # validated by ``semantic_dependency_manifest`` below.
        if not isinstance(graph, Mapping):
            attached[declaration] = manifest
            continue
        semantic_origins = (
            graph_origins(graph, lane="semantic")
            if isinstance(graph, Mapping)
            else set()
        )
        realization_origins = (
            graph_origins(graph, lane="realization")
            if isinstance(graph, Mapping)
            else set()
        )
        identities = [
            {
                **identities_by_origin[origin],
                "dependency_lane": (
                    "semantic" if origin in semantic_origins else "realization"
                ),
            }
            for origin in sorted(realization_origins | semantic_origins)
        ]
        manifest["semantic_dependency_module_identities"] = identities
        manifest["semantic_dependency_environment_identities"] = environment_identities
        dependency = semantic_dependency_manifest(
            manifest, identities, environment_identities
        )
        if dependency is not None:
            manifest["semantic_dependency_manifest"] = dependency
        attached[declaration] = manifest
    return attached


def reattach_semantic_dependency_module_identities(
    root: Path,
    manifests: Mapping[str, Mapping[str, Any]],
    *,
    timeout_seconds: int = 600,
) -> dict[str, dict[str, Any]]:
    """Rebind saved Lean graphs to current reached-module artifacts.

    Persisted callers may carry a previously emitted elaborated graph, but
    they must not carry its imported-module identities across a new audit.
    This public entry point preserves the Lean-emitted graph and refreshes the
    exact artifacts reached by that graph. Callers must recompute and compare
    the resulting semantic-dependency digest before accepting any item.
    """

    return _with_semantic_dependency_module_identities(
        root,
        manifests,
        timeout_seconds=timeout_seconds,
    )


def _closure_module_origin_pairs(
    manifest: Mapping[str, Any],
) -> list[tuple[str, str]]:
    """Return the normalized module origins actually reached by one Spec."""

    reached_modules = manifest.get("reached_modules")
    if not isinstance(reached_modules, list):
        return []
    return sorted(
        {
            (
                str(module.get("origin_class") or ""),
                str(module.get("module_origin") or ""),
            )
            for module in reached_modules
            if isinstance(module, dict)
            and str(module.get("module_origin") or "") not in {"<inline>", "<internal>"}
        }
    )


def _closure_module_artifact_snapshot(
    root: Path,
    module_origins: Iterable[str],
    *,
    timeout_seconds: int,
    lean_path: str | None = None,
) -> dict[str, dict[str, str]]:
    """Hash the current first-search-path artifact for each exact module."""

    modules = sorted(set(module_origins))
    resolved_lean_path = (
        lean_path
        if lean_path is not None
        else (_lake_env_lean_path(root, timeout_seconds) if modules else None)
    )
    return {
        module_origin: _closure_module_artifact_identity(
            root, module_origin, resolved_lean_path
        )
        for module_origin in modules
    }


def _closure_module_identity_snapshot(
    root: Path,
    manifests: Mapping[str, Mapping[str, Any]],
    *,
    timeout_seconds: int,
    lean_path: str | None = None,
) -> dict[str, list[dict[str, str]]]:
    """Hash every reached module once for one coherent closure snapshot."""

    # Foundation entries are package roots, deliberately not individual
    # ``.olean`` modules.  Their immutable package/toolchain identity is
    # attached separately by ``_semantic_contract_closure_foundation_context``.
    # Requiring a fictitious ``Mathlib.olean`` or ``Batteries.olean`` here
    # would turn a valid compact package receipt into an unresolved artifact.
    # Paper and unregistered external origins, in contrast, remain exact
    # module artifacts and are byte-pinned below.
    origins_by_specification = {
        specification: [
            (origin_class, module_origin)
            for origin_class, module_origin in _closure_module_origin_pairs(manifest)
            if not (
                manifest.get("surface_mode") == "lean_dependency_fingerprint"
                and origin_class == "foundation"
            )
        ]
        for specification, manifest in manifests.items()
    }
    reached_origins = {
        origin for origins in origins_by_specification.values() for origin in origins
    }
    # Every reached module receives an exact `.olean` content pin. Package and
    # toolchain identities remain additional context, not a substitute for
    # the compiled bytes Lean actually traversed.
    artifacts_by_module = _closure_module_artifact_snapshot(
        root,
        {module_origin for _origin_class, module_origin in reached_origins},
        timeout_seconds=timeout_seconds,
        lean_path=lean_path,
    )
    return {
        specification: [
            {
                "origin_class": origin_class,
                **artifacts_by_module[module_origin],
            }
            for origin_class, module_origin in origins
        ]
        for specification, origins in origins_by_specification.items()
    }


def _closure_module_identities(
    root: Path,
    manifest: dict[str, Any],
    *,
    timeout_seconds: int,
) -> list[dict[str, str]]:
    """Return exact artifact pins for module origins actually reached by one Spec."""

    return _closure_module_identity_snapshot(
        root,
        {"<manifest>": manifest},
        timeout_seconds=timeout_seconds,
    )["<manifest>"]


def _semantic_contract_closure_cached_module_identities_are_current(
    root: Path,
    manifests: Mapping[str, Mapping[str, Any]],
    *,
    timeout_seconds: int,
) -> bool:
    """Revalidate exact reached `.olean` bytes before serving a cached receipt."""

    if not manifests:
        return False
    current = _closure_module_identity_snapshot(
        root,
        manifests,
        timeout_seconds=timeout_seconds,
    )
    if set(current) != set(manifests):
        return False
    for specification, manifest in manifests.items():
        stored = manifest.get("closure_module_identities")
        identities = current[specification]
        if (
            not isinstance(stored, list)
            or stored != identities
            or any(
                not re.fullmatch(
                    r"[0-9a-f]{64}",
                    str(identity.get("artifact_sha256") or ""),
                )
                for identity in identities
            )
        ):
            return False
    return True


def _lean_loaded_module_candidates(
    root: Path,
    import_module: str,
    *,
    timeout_seconds: int,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[str, ...] | None:
    """Return Lean's exact loaded modules with process-local snapshot reuse."""

    if provider is not None:
        if provider.root != root.resolve():
            return None
        modules = provider.lean_loaded_module_names(
            import_module,
            timeout_seconds=timeout_seconds,
        )
        return modules or None

    # The no-provider route deliberately does not consult the Python import
    # parser before asking Lean.  That parser cannot be cache authority for
    # syntax it does not understand.  Closeout callers pass one shared
    # provider; this direct route is a correct, uncached compatibility path.
    try:
        if __package__:
            from .lean_import_closure import lean_loaded_module_closure
        else:
            from lean_import_closure import lean_loaded_module_closure

        modules, error = lean_loaded_module_closure(
            root,
            import_module,
            timeout_seconds,
        )
    except (ImportError, OSError, RuntimeError):
        return None
    if modules is None or error or import_module not in modules:
        return None
    return modules


def _legacy_cached_lean_loaded_module_candidates(
    root: Path,
    import_module: str,
    *,
    timeout_seconds: int,
) -> tuple[str, ...] | None:
    """Legacy exact-snapshot cache retained for nonacceptance diagnostics."""

    snapshot = repository_build_input_snapshot(
        root,
        import_module,
    )
    if snapshot is None:
        return None
    cache_key = (str(root.resolve()), import_module, snapshot)
    cached = _LEAN_LOADED_MODULE_CLOSURE_CACHE.get(cache_key)
    if cached is not None:
        return cached

    try:
        if __package__:
            from .lean_import_closure import lean_loaded_module_closure
        else:
            from lean_import_closure import lean_loaded_module_closure

        modules, error = lean_loaded_module_closure(
            root,
            import_module,
            timeout_seconds,
        )
    except (ImportError, OSError, RuntimeError):
        return None
    if modules is None or error or import_module not in modules:
        return None
    _LEAN_LOADED_MODULE_CLOSURE_CACHE[cache_key] = modules
    return modules


def _semantic_contract_closure_reached_artifacts_match_candidates(
    candidate_artifacts: Mapping[str, Mapping[str, str]],
    reached_artifacts: Mapping[str, list[dict[str, str]]],
) -> bool:
    """Require every semantically reached artifact to match its prepass pin."""

    if not reached_artifacts or any(
        not identities for identities in reached_artifacts.values()
    ):
        return False
    for identities in reached_artifacts.values():
        for identity in identities:
            module_origin = str(identity.get("module_origin") or "")
            expected = candidate_artifacts.get(module_origin)
            if expected is None or dict(expected) != {
                key: value for key, value in identity.items() if key != "origin_class"
            }:
                return False
    return True


def _remove_overlay_artifact(artifact: Path) -> None:
    """Remove every generated form so a failed source pass cannot fall back."""

    for suffix in (
        ".olean",
        ".ilean",
        ".olean.hash",
        ".ilean.hash",
        ".trace",
        ".c",
    ):
        artifact.with_suffix(suffix).unlink(missing_ok=True)


@contextmanager
def _fresh_constructor_result_type_overlay(
    root: Path,
    import_module: str,
    review_source_path: Path,
    *,
    build_timeout_seconds: int,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> Iterator[tuple[str, str] | None]:
    """Yield an overlay that imports an exact current review source, or ``None``.

    A successful normal ``lake build`` is insufficient for this audit: an
    incremental artifact can remain available even when the static
    source-record parser has read a newer source file.  This helper stages
    dependencies, deletes the copied review artifact, elaborates the exact
    current source into the overlay, and pins the source digest both before
    and after the Meta invocation.  Every failure path yields ``None``.
    """

    source_path = review_source_path.resolve()
    module_name = _review_source_module_name(root, source_path)
    if (
        not source_path.is_file()
        or module_name != import_module
        or not _build_import_target(
            root,
            import_module,
            build_timeout_seconds,
            provider=build_input_provider,
        )
    ):
        yield None
        return
    source_sha256 = _source_sha256(source_path)
    if source_sha256 is None:
        yield None
        return

    artifact_library = root / ".lake" / "build" / "lib" / "lean"
    module_parts = [part for part in import_module.split(".") if part]
    if not module_parts:
        yield None
        return
    namespace_artifacts = artifact_library / module_parts[0]
    if not namespace_artifacts.is_dir():
        yield None
        return
    base_lean_path = _lake_env_lean_path(root, build_timeout_seconds)
    if base_lean_path is None:
        yield None
        return

    with tempfile.TemporaryDirectory(prefix="constructor-result-type-fresh-") as tmpdir:
        overlay_root = Path(tmpdir)
        try:
            shutil.copytree(namespace_artifacts, overlay_root / module_parts[0])
        except OSError:
            yield None
            return
        overlay_artifact = overlay_root.joinpath(*module_parts)
        overlay_artifact.parent.mkdir(parents=True, exist_ok=True)
        _remove_overlay_artifact(overlay_artifact)
        overlay_lean_path = f"{overlay_root}{os.pathsep}{base_lean_path}"
        try:
            proc = subprocess.run(
                [
                    "lake",
                    "env",
                    "env",
                    f"LEAN_PATH={overlay_lean_path}",
                    "lean",
                    "--root",
                    str(root),
                    "-o",
                    str(overlay_artifact.with_suffix(".olean")),
                    "-i",
                    str(overlay_artifact.with_suffix(".ilean")),
                    str(source_path),
                ],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=build_timeout_seconds,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            yield None
            return
        if (
            proc.returncode != 0
            or not overlay_artifact.with_suffix(".olean").is_file()
            or _source_sha256(source_path) != source_sha256
        ):
            yield None
            return
        yield overlay_lean_path, source_sha256


def _repository_module_source_candidates(root: Path, module: str) -> tuple[Path, ...]:
    """Return every repository source candidate for one valid Lean module."""

    if not re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module
    ):
        return ()
    parts = module.split(".")
    candidates = (
        root.joinpath(*parts).with_suffix(".lean"),
        (root / "papers").joinpath(*parts).with_suffix(".lean"),
    )
    return tuple(sorted({path.resolve() for path in candidates if path.is_file()}))


def _repository_module_source_path(root: Path, module: str) -> Path | None:
    """Resolve one repository module exactly, rejecting ambiguous layouts."""

    matches = _repository_module_source_candidates(root, module)
    return matches[0] if len(matches) == 1 else None


class RepositoryBuildInputSnapshotProvider:
    """Share one Lean-authored import closure across a repository run.

    A validated saved ``lean_import_closure`` receipt can be adopted without
    rerunning Lean.  Otherwise the provider asks the existing strict worktree
    closure provider for Lean's emitted loaded-module graph.  Python import
    parsing is retained only through an explicitly named diagnostic method;
    it never supplies modules, source bytes, or cache identity on this class's
    canonical methods.

    Every adopted receipt is checked against exact current source bytes,
    source ownership, build controls, Lake routing, and external artifacts.
    The same immutable bytes then feed every build and structural query in the
    process.  The caller must invoke :meth:`finalize_unchanged` once before
    publishing derived results.  That boundary rereads only receipt-owned
    inputs, so unrelated paper directories and unimported scratch files do not
    invalidate a closeout.
    """

    _IMPORT_NAME = re.compile(
        r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
    )
    _CONTROL_PATHS = (
        "lean-toolchain",
        "lake-manifest.json",
    )

    def __init__(
        self,
        root: Path | str,
        *,
        lean_import_closure_payload: object | None = None,
        module_graph_loader: Callable[
            [Path, str, int], tuple[tuple[str, ...] | None, str]
        ]
        | None = None,
        lean_graph_timeout_seconds: int = 600,
    ) -> None:
        self.root = Path(root).resolve()
        self._module_graph_loader = module_graph_loader
        self._lean_graph_timeout_seconds = lean_graph_timeout_seconds
        self._live_closure_provider: object | None = None
        self._resolved_paths: dict[str, Path | None] = {}
        self._source_bytes: dict[str, bytes] = {}
        self._source_digests: dict[str, str] = {}
        self._loaded_modules: dict[str, tuple[str, ...]] = {}
        self._imports: dict[str, tuple[str, ...] | None] = {}
        self._closures: dict[str, tuple[str, ...]] = {}
        self._closure_receipts: dict[str, dict[str, object]] = {}
        self._snapshots: dict[str, str | None] = {}
        self._control_bytes = {
            relative: self._read_optional_bytes(self.root / relative)
            for relative in self._CONTROL_PATHS
        }
        self._diagnostics = {
            "snapshot_requests": 0,
            "snapshot_reuses": 0,
            "closure_requests": 0,
            "closure_reuses": 0,
            "module_resolutions": 0,
            "source_reads": 0,
            "source_reuses": 0,
            "parse_requests": 0,
            "parse_reuses": 0,
            "lean_graph_requests": 0,
            "lean_graph_reuses": 0,
            "saved_receipts_adopted": 0,
            "finalization_checks": 0,
            "finalization_failures": 0,
        }
        if lean_import_closure_payload is not None:
            self.adopt_lean_import_closure_payload(lean_import_closure_payload)

    @staticmethod
    def _read_optional_bytes(path: Path) -> bytes | None:
        try:
            return path.read_bytes()
        except OSError:
            return None

    def _diagnostic_routing_inventory(self) -> tuple[tuple[str, str], ...]:
        """Return ambient roots for the explicitly legacy parser only."""

        papers_root = self.root / "papers"
        inventory = {
            ("root_module", path.stem)
            for path in self.root.glob("*.lean")
            if path.is_file()
        }
        if papers_root.is_dir():
            inventory.update(
                ("paper_directory", path.name)
                for path in papers_root.iterdir()
                if path.is_dir()
            )
            inventory.update(
                ("papers_module", path.stem)
                for path in papers_root.glob("*.lean")
                if path.is_file()
            )
        return tuple(sorted(inventory))

    def _resolve(self, module: str) -> Path | None:
        if module in self._resolved_paths:
            return self._resolved_paths[module]
        self._diagnostics["module_resolutions"] += 1
        path = _repository_module_source_path(self.root, module)
        self._resolved_paths[module] = path
        return path

    def _source(self, module: str) -> bytes | None:
        if module in self._source_bytes:
            self._diagnostics["source_reuses"] += 1
            return self._source_bytes[module]
        path = self._resolve(module)
        if path is None:
            return None
        try:
            source = path.read_bytes()
        except OSError:
            return None
        self._diagnostics["source_reads"] += 1
        self._source_bytes[module] = source
        self._source_digests[module] = hashlib.sha256(source).hexdigest()
        return source

    @staticmethod
    def _masked_import_source(text: str) -> str | None:
        """Mask Lean comments with the legacy fallback parser's semantics."""

        index = 0
        depth = 0
        masked: list[str] = []
        length = len(text)
        while index < length:
            next_open = text.find("/-", index)
            next_close = text.find("-/", index) if depth else -1
            next_line = text.find("--", index) if not depth else -1
            events = [
                position
                for position in (next_open, next_close, next_line)
                if position >= 0
            ]
            if not events:
                if depth:
                    return None
                masked.append(text[index:])
                break
            event = min(events)
            prefix = text[index:event]
            masked.append(re.sub(r"[^\n]", " ", prefix) if depth else prefix)
            if event == next_open:
                depth += 1
                masked.extend((" ", " "))
                index = event + 2
                continue
            if event == next_close:
                depth -= 1
                masked.extend((" ", " "))
                index = event + 2
                continue
            newline = text.find("\n", event)
            if newline < 0:
                masked.append(" " * (length - event))
                break
            masked.append(" " * (newline - event))
            masked.append("\n")
            index = newline + 1
        return None if depth else "".join(masked)

    def _parsed_imports(self, module: str) -> tuple[str, ...] | None:
        self._diagnostics["parse_requests"] += 1
        if module in self._imports:
            self._diagnostics["parse_reuses"] += 1
            return self._imports[module]
        source = self._source(module)
        if source is None:
            self._imports[module] = None
            return None
        try:
            text = source.decode("utf-8")
        except UnicodeError:
            self._imports[module] = None
            return None
        masked = self._masked_import_source(text)
        if masked is None:
            self._imports[module] = None
            return None
        imported: list[str] = []
        for line in masked.splitlines():
            match = re.match(r"^\s*import\s+(.+?)\s*$", line)
            if match is None:
                continue
            names = match.group(1).split()
            if not names or any(
                self._IMPORT_NAME.fullmatch(name) is None for name in names
            ):
                self._imports[module] = None
                return None
            imported.extend(names)
        result = tuple(imported)
        self._imports[module] = result
        return result

    def diagnostic_python_module_names_in_import_closure(
        self, import_module: str
    ) -> tuple[str, ...]:
        """Parse imports for diagnostics, never for acceptance or cache keys."""

        self._diagnostics["closure_requests"] += 1
        if self._resolve(import_module) is None:
            return ()
        repository_roots = frozenset(
            value[1] for value in self._diagnostic_routing_inventory()
        )
        modules: set[str] = set()
        pending = [import_module]
        seen: set[str] = set()
        while pending:
            module = pending.pop(0)
            if module in seen:
                continue
            seen.add(module)
            if self._resolve(module) is None:
                return ()
            imports = self._parsed_imports(module)
            if imports is None:
                return ()
            modules.add(module)
            for imported in imports:
                imported_source = self._resolve(imported)
                if imported_source is not None:
                    pending.append(imported)
                elif imported.split(".", 1)[0] in repository_roots:
                    return ()
        return tuple(sorted(modules))

    @staticmethod
    def _closure_helpers() -> tuple[Any, Any, Any, Any, Any, Any, Any]:
        try:
            if __package__:
                from .lean_import_closure import (
                    WorktreeImportClosureProvider,
                    durable_lake_routing_projection,
                    external_module_artifact_records,
                    external_module_artifacts_sha256,
                    lake_routing_projection,
                    lean_loaded_module_closure,
                    validated_lean_import_closure_payload,
                )
            else:
                from lean_import_closure import (
                    WorktreeImportClosureProvider,
                    durable_lake_routing_projection,
                    external_module_artifact_records,
                    external_module_artifacts_sha256,
                    lake_routing_projection,
                    lean_loaded_module_closure,
                    validated_lean_import_closure_payload,
                )
        except ImportError as exc:
            raise ValueError("Lean import-closure authority is unavailable") from exc
        return (
            WorktreeImportClosureProvider,
            durable_lake_routing_projection,
            external_module_artifact_records,
            external_module_artifacts_sha256,
            lake_routing_projection,
            lean_loaded_module_closure,
            validated_lean_import_closure_payload,
        )

    def _validated_current_receipt(
        self,
        payload: object,
        *,
        reuse_cached_sources: bool = True,
    ) -> tuple[dict[str, object], dict[str, tuple[Path, bytes]]]:
        """Validate one receipt and return its exact current source bytes."""

        (
            _worktree_provider,
            durable_lake_routing_projection,
            external_module_artifact_records,
            external_module_artifacts_sha256,
            lake_routing_projection,
            _lean_loader,
            validated_lean_import_closure_payload,
        ) = self._closure_helpers()
        validated = validated_lean_import_closure_payload(payload)
        entry_module = str(validated["entry_module"])
        entrypoint = str(validated["entrypoint"])
        entry_path = (self.root / entrypoint).resolve()
        try:
            entry_path.relative_to(self.root)
        except ValueError as exc:
            raise ValueError(
                "Lean import-closure entrypoint escapes the repository"
            ) from exc

        current_sources: dict[str, tuple[Path, bytes]] = {}
        raw_sources = validated["sources"]
        assert isinstance(raw_sources, list)
        for raw in raw_sources:
            assert isinstance(raw, Mapping)
            module = str(raw["module"])
            relative = str(raw["path"])
            path = (self.root / relative).resolve()
            try:
                path.relative_to(self.root)
            except ValueError as exc:
                raise ValueError(
                    f"Lean import-closure source escapes the repository: {relative}"
                ) from exc
            if _repository_module_source_path(self.root, module) != path:
                raise ValueError(
                    f"Lean import-closure source ownership changed: {module}"
                )
            content = None
            if reuse_cached_sources and self._resolved_paths.get(module) == path:
                candidate = self._source_bytes.get(module)
                if candidate is not None and (
                    len(candidate) == raw["byte_length"]
                    and hashlib.sha256(candidate).hexdigest() == raw["sha256"]
                ):
                    content = candidate
                    self._diagnostics["source_reuses"] += 1
            if content is None:
                content = self._read_optional_bytes(path)
                self._diagnostics["source_reads"] += 1
            if content is None or (
                len(content) != raw["byte_length"]
                or hashlib.sha256(content).hexdigest() != raw["sha256"]
            ):
                raise ValueError(
                    f"Lean import-closure source bytes changed: {relative}"
                )
            current_sources[module] = (path, content)
        if current_sources.get(entry_module, (None, b""))[0] != entry_path:
            raise ValueError(
                "Lean import-closure entrypoint source association changed"
            )
        raw_external = validated["external_import_modules"]
        assert isinstance(raw_external, list)
        for module in (str(value) for value in raw_external):
            candidates = _repository_module_source_candidates(self.root, module)
            if len(candidates) > 1:
                raise ValueError(
                    "Lean import-closure external module has ambiguous repository "
                    f"source ownership: {module}"
                )
            if candidates:
                raise ValueError(
                    "Lean import-closure external module gained repository "
                    f"source ownership: {module}"
                )

        raw_controls = validated["build_controls"]
        assert isinstance(raw_controls, list)
        current_control_bytes = {
            relative: self._read_optional_bytes(self.root / relative)
            for relative in self._CONTROL_PATHS
        }
        if current_control_bytes != self._control_bytes:
            raise ValueError(
                "Lean build controls changed after snapshot-provider construction"
            )
        for raw in raw_controls:
            assert isinstance(raw, Mapping)
            relative = str(raw["path"])
            if relative not in self._CONTROL_PATHS:
                continue
            content = current_control_bytes.get(relative)
            if content is None or (
                len(content) != raw["byte_length"]
                or hashlib.sha256(content).hexdigest() != raw["sha256"]
            ):
                raise ValueError(
                    f"Lean import-closure build control changed: {relative}"
                )

        routing, routing_error = lake_routing_projection(self.root, entry_module)
        if routing is None or durable_lake_routing_projection(
            routing
        ) != durable_lake_routing_projection(validated["lake_routing"]):
            raise ValueError(
                routing_error or "Lean import-closure Lake routing changed"
            )

        artifacts, artifact_error = external_module_artifact_records(
            self.root,
            (str(module) for module in raw_external),
            timeout_seconds=min(self._lean_graph_timeout_seconds, 60),
        )
        if artifacts is None or (
            external_module_artifacts_sha256(artifacts)
            != validated["external_module_artifacts_sha256"]
        ):
            raise ValueError(
                artifact_error or "Lean import-closure external artifacts changed"
            )
        return validated, current_sources

    def adopt_lean_import_closure_payload(self, payload: object) -> str:
        """Adopt one current Lean-owned receipt and return its entry module."""

        validated, current_sources = self._validated_current_receipt(payload)
        entry_module = str(validated["entry_module"])
        if entry_module in self._closure_receipts:
            if self._closure_receipts[entry_module] != validated:
                raise ValueError(
                    "conflicting Lean import-closure receipts for one entry module"
                )
            self._diagnostics["lean_graph_reuses"] += 1
            return entry_module

        for module, (path, content) in current_sources.items():
            previous_path = self._resolved_paths.get(module)
            previous_content = self._source_bytes.get(module)
            if (previous_path is not None and previous_path != path) or (
                previous_content is not None and previous_content != content
            ):
                raise ValueError(
                    f"conflicting Lean source snapshots for module: {module}"
                )
            self._resolved_paths[module] = path
            self._source_bytes[module] = content
            self._source_digests[module] = hashlib.sha256(content).hexdigest()

        loaded = tuple(str(module) for module in validated["lean_loaded_modules"])
        for module in loaded:
            if module in current_sources:
                continue
            if (
                module in self._resolved_paths
                and self._resolved_paths[module] is not None
            ):
                raise ValueError(f"conflicting external module ownership: {module}")
            self._resolved_paths[module] = None
        repository_modules = tuple(sorted(current_sources))
        self._loaded_modules[entry_module] = loaded
        self._closures[entry_module] = repository_modules
        self._closure_receipts[entry_module] = deepcopy(validated)
        self._diagnostics["saved_receipts_adopted"] += 1
        return entry_module

    def _acquire_live_receipt(
        self,
        import_module: str,
        timeout_seconds: int,
    ) -> bool:
        """Ask the strict worktree provider for one Lean-emitted receipt."""

        (
            WorktreeImportClosureProvider,
            _durable_lake_routing,
            _external_records,
            _external_sha256,
            _lake_routing,
            lean_loaded_module_closure,
            _validate_payload,
        ) = self._closure_helpers()
        if self._live_closure_provider is None:
            loader = self._module_graph_loader or lean_loaded_module_closure
            self._live_closure_provider = WorktreeImportClosureProvider(
                self.root,
                module_graph_loader=loader,
                graph_timeout_seconds=max(
                    1, min(timeout_seconds, self._lean_graph_timeout_seconds)
                ),
                eager_source_snapshot=False,
                allow_dirty_worktree_sources=True,
            )
        source = _repository_module_source_path(self.root, import_module)
        if source is None:
            return False
        try:
            entrypoint = source.relative_to(self.root).as_posix()
        except ValueError:
            return False
        self._diagnostics["lean_graph_requests"] += 1
        record, problem = self._live_closure_provider.record_for_entrypoint(entrypoint)
        if record is None or problem is not None:
            return False
        try:
            adopted = self.adopt_lean_import_closure_payload(record)
        except ValueError:
            return False
        return adopted == import_module

    def lean_loaded_module_names(
        self,
        import_module: str,
        *,
        timeout_seconds: int | None = None,
    ) -> tuple[str, ...]:
        """Return Lean's exact loaded modules, adopting or emitting once."""

        if import_module in self._loaded_modules:
            self._diagnostics["lean_graph_reuses"] += 1
            return self._loaded_modules[import_module]
        if not self._acquire_live_receipt(
            import_module,
            timeout_seconds or self._lean_graph_timeout_seconds,
        ):
            return ()
        return self._loaded_modules.get(import_module, ())

    def module_names_in_import_closure(self, import_module: str) -> tuple[str, ...]:
        """Return repository sources selected by Lean's loaded-module graph."""

        self._diagnostics["closure_requests"] += 1
        if import_module in self._closures:
            self._diagnostics["closure_reuses"] += 1
            return self._closures[import_module]
        if not self.lean_loaded_module_names(import_module):
            return ()
        return self._closures.get(import_module, ())

    def repository_source_snapshot(
        self,
        import_module: str,
    ) -> tuple[tuple[str, Path, bytes, str], ...]:
        """Expose the exact cached repository closure without rereading it."""

        modules = self.module_names_in_import_closure(import_module)
        if not modules:
            return ()
        snapshots: list[tuple[str, Path, bytes, str]] = []
        for module in modules:
            path = self._resolved_paths.get(module)
            content = self._source_bytes.get(module)
            digest = self._source_digests.get(module)
            if path is None or content is None or digest is None:
                return ()
            snapshots.append((module, path, content, digest))
        return tuple(snapshots)

    def lean_import_closure_receipt(
        self, import_module: str
    ) -> dict[str, object] | None:
        """Return a defensive copy of Lean's validated loaded-module receipt."""

        if import_module not in self._closure_receipts:
            if not self.lean_loaded_module_names(import_module):
                return None
        receipt = self._closure_receipts.get(import_module)
        return deepcopy(receipt) if receipt is not None else None

    def repository_source_path(self, module: str) -> Path | None:
        """Return one receipt-frozen source-ownership decision.

        Unseen modules are not resolved from the ambient tree.  Call
        :meth:`lean_loaded_module_names` for an entrypoint first so Lean can
        authorize and freeze every loaded module's ownership.
        """

        return self._resolved_paths.get(module)

    def snapshot(self, import_module: str) -> str | None:
        """Return one memoized digest of a Lean-owned closure and controls."""

        self._diagnostics["snapshot_requests"] += 1
        if import_module in self._snapshots:
            self._diagnostics["snapshot_reuses"] += 1
            return self._snapshots[import_module]
        modules = self.module_names_in_import_closure(import_module)
        if not modules:
            self._snapshots[import_module] = None
            return None
        identities: list[tuple[str, str, str]] = []
        for module in modules:
            if module not in self._source_bytes:
                self._snapshots[import_module] = None
                return None
            identities.append(("module", module, self._source_digests[module]))
        receipt = self._closure_receipts.get(import_module)
        if receipt is None:
            self._snapshots[import_module] = None
            return None
        for relative in self._CONTROL_PATHS:
            content = self._control_bytes[relative]
            digest = (
                hashlib.sha256(content).hexdigest()
                if content is not None
                else "<missing>"
            )
            identities.append(("control", relative, digest))
        raw_controls = receipt.get("build_controls")
        assert isinstance(raw_controls, list)
        for raw in raw_controls:
            assert isinstance(raw, Mapping)
            relative = str(raw["path"])
            if relative not in self._CONTROL_PATHS:
                # The payload validator permits only the exact historical
                # control tuple. Its recorded digest preserves the old build
                # snapshot without rereading retired operational tooling.
                identities.append(("control", relative, str(raw["sha256"])))
        identities.append(
            (
                "lean_import_closure",
                import_module,
                hashlib.sha256(
                    json.dumps(
                        receipt,
                        ensure_ascii=True,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest(),
            )
        )
        value = hashlib.sha256(
            json.dumps(
                identities,
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        self._snapshots[import_module] = value
        return value

    def finalize_unchanged(self) -> bool:
        """Confirm that every receipt-owned input stayed immutable."""

        self._diagnostics["finalization_checks"] += 1
        unchanged = True
        try:
            for receipt in self._closure_receipts.values():
                self._validated_current_receipt(
                    receipt,
                    reuse_cached_sources=False,
                )
        except ValueError:
            unchanged = False
        if not unchanged:
            self._diagnostics["finalization_failures"] += 1
        return unchanged

    def diagnostics(self) -> dict[str, int]:
        """Return non-authoritative counters for profiling and regression tests."""

        return dict(self._diagnostics)


def _build_target_input_snapshot(
    root: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> str | None:
    """Hash repository sources and build controls for one target.

    A provider makes this a Lean-owned closure identity.  The no-provider path
    remains only for legacy diagnostics and compatibility tests.
    """

    if provider is not None:
        if provider.root != root.resolve():
            return None
        return provider.snapshot(import_module)
    modules = repository_module_names_in_import_closure(root, import_module)
    if not modules:
        return None
    identities: list[tuple[str, str, str]] = []
    for module in modules:
        source = _repository_module_source_path(root, module)
        if source is None:
            return None
        digest = _source_sha256(source)
        if digest is None:
            return None
        identities.append(("module", module, digest))
    for relative in (
        "lean-toolchain",
        "lake-manifest.json",
        "lakefile.lean",
        "lakefile.toml",
    ):
        path = root / relative
        digest = _source_sha256(path)
        identities.append(("control", relative, digest or "<missing>"))
    return hashlib.sha256(
        json.dumps(
            identities,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def repository_build_input_snapshot(
    root: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> str | None:
    """Return the exact repository/build-control identity for one Lean target."""

    return _build_target_input_snapshot(
        root.resolve(), import_module, provider=provider
    )


def _build_target_artifact_snapshot(
    root: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[tuple[str, tuple[str, int]], ...] | None:
    """Pin every repository-owned compiled artifact in the import closure."""

    modules = repository_module_names_in_import_closure(
        root,
        import_module,
        provider=provider,
    )
    if not modules:
        return None
    artifacts: list[tuple[str, tuple[str, int]]] = []
    for module in modules:
        fingerprint = _built_olean_fingerprint(root, module)
        if fingerprint is None:
            return None
        artifacts.append((module, fingerprint))
    return tuple(artifacts)


def _build_import_target(
    root: Path,
    import_module: str,
    timeout_seconds: int,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> bool:
    """Build once per exact immutable source/artifact snapshot.

    When ``provider`` is shared, its owner must call ``finalize_unchanged``
    after the last derived query and before publishing any of their results.
    """

    root = root.resolve()
    if provider is not None and provider.root != root:
        return False
    snapshot_before = _build_target_input_snapshot(
        root,
        import_module,
        provider=provider,
    )
    cache_key = (str(root), import_module)
    cached = _SUCCESSFUL_BUILD_SNAPSHOT_CACHE.get(cache_key)
    if snapshot_before is not None and cached is not None:
        cached_snapshot, cached_artifacts = cached
        artifacts_before = _build_target_artifact_snapshot(
            root,
            import_module,
            provider=provider,
        )
        if (
            cached_snapshot == snapshot_before
            and artifacts_before == cached_artifacts
            and _build_target_input_snapshot(
                root,
                import_module,
                provider=provider,
            )
            == snapshot_before
            and _build_target_artifact_snapshot(
                root,
                import_module,
                provider=provider,
            )
            == artifacts_before
        ):
            return True

    try:
        proc = subprocess.Popen(
            ["lake", "build", import_module],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        proc.communicate(timeout=timeout_seconds)
    except (OSError, subprocess.TimeoutExpired):
        if "proc" in locals():
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
        return False
    if proc.returncode != 0:
        return False
    snapshot_after = _build_target_input_snapshot(
        root,
        import_module,
        provider=provider,
    )
    artifact_snapshot = _build_target_artifact_snapshot(
        root,
        import_module,
        provider=provider,
    )
    if (
        snapshot_before is None
        or snapshot_after != snapshot_before
        or artifact_snapshot is None
        or _build_target_input_snapshot(
            root,
            import_module,
            provider=provider,
        )
        != snapshot_before
        or _build_target_artifact_snapshot(
            root,
            import_module,
            provider=provider,
        )
        != artifact_snapshot
    ):
        return False
    _SUCCESSFUL_BUILD_SNAPSHOT_CACHE[cache_key] = (
        snapshot_after,
        artifact_snapshot,
    )
    return True


def _file_fingerprint(path: Path) -> tuple[int, int] | None:
    """Return metadata used only for non-semantic workspace inventory."""

    try:
        stat = path.stat()
    except OSError:
        return None
    return stat.st_mtime_ns, stat.st_size


def _file_content_fingerprint(path: Path) -> tuple[str, int] | None:
    """Return an exact content identity for a semantic audit artifact."""

    try:
        content = path.read_bytes()
    except OSError:
        return None
    return hashlib.sha256(content).hexdigest(), len(content)


def _built_olean_fingerprint(root: Path, import_module: str) -> tuple[str, int] | None:
    relative = Path(*import_module.split(".")).with_suffix(".olean")
    return _file_content_fingerprint(
        root / ".lake" / "build" / "lib" / "lean" / relative
    )


STRUCTURAL_SCAN_ENVIRONMENT_SCHEMA = 1
STRUCTURAL_SCAN_DIAGNOSTICS_SCHEMA = 1


def _structural_scan_environment_snapshot(
    root: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> str | None:
    """Hash the complete repository environment used by a structural query.

    The build-input snapshot owns source and build-control bytes.  The artifact
    snapshot owns every repository `.olean` in Lean's import closure.  The
    helper fingerprint owns the Meta implementation.  Reading this composite
    before and after every cache/helper path prevents a dependency-only edit or
    a concurrent rebuild from preserving a process-local structural verdict.
    """

    input_snapshot = _build_target_input_snapshot(
        root,
        import_module,
        provider=provider,
    )
    artifact_snapshot = _build_target_artifact_snapshot(
        root,
        import_module,
        provider=provider,
    )
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    if (
        input_snapshot is None
        or artifact_snapshot is None
        or helper_fingerprint is None
    ):
        return None
    payload = {
        "schema": STRUCTURAL_SCAN_ENVIRONMENT_SCHEMA,
        "root": str(root.resolve()),
        "import_module": import_module,
        "build_input_sha256": input_snapshot,
        "repository_import_artifacts": [
            [module, list(fingerprint)] for module, fingerprint in artifact_snapshot
        ],
        "helper_fingerprint": list(helper_fingerprint),
        "foundation_allowlist_sha256": (FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256),
    }
    return hashlib.sha256(
        json.dumps(
            payload,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _structural_scan_environment_identity(
    root: Path,
    import_module: str,
    *,
    build_timeout_seconds: int,
    ensure_built: bool = True,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> str | None:
    """Return one stable current structural environment identity.

    A double read rejects mutation while the identity itself is assembled.
    Callers perform another identity read after serving cache entries or
    running Lean; only an unchanged identity may be returned to an audit.
    """

    if ensure_built and not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=provider,
    ):
        return None
    before = _structural_scan_environment_snapshot(
        root,
        import_module,
        provider=provider,
    )
    after = _structural_scan_environment_snapshot(
        root,
        import_module,
        provider=provider,
    )
    if before is None or before != after:
        return None
    return before


def _publish_structural_scan_diagnostics(
    diagnostics_out: dict[str, Any] | None,
    *,
    stage: str,
    requested_count: int,
    reused_count: int,
    fresh_count: int,
    batch_count: int = 0,
    isolation_retry_count: int = 0,
    missing_identities: Iterable[str] = (),
    unexpected_identities: Iterable[str] = (),
    environment_changed: bool = False,
) -> None:
    """Expose operational counters without making them semantic evidence."""

    if diagnostics_out is None:
        return
    missing = sorted(set(missing_identities))
    unexpected = sorted(set(unexpected_identities))
    diagnostics_out.clear()
    diagnostics_out.update(
        {
            "schema": STRUCTURAL_SCAN_DIAGNOSTICS_SCHEMA,
            "stage": stage,
            "requested_count": requested_count,
            "reused_count": reused_count,
            "fresh_count": fresh_count,
            "batch_count": batch_count,
            "isolation_retry_count": isolation_retry_count,
            "missing_count": len(missing),
            "missing_identities": missing,
            "unexpected_count": len(unexpected),
            "unexpected_identities": unexpected,
            "environment_changed": environment_changed,
        }
    )


def repository_module_names_in_import_closure(
    root: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[str, ...]:
    """Return repository-owned modules for one Lean entry module.

    With ``provider``, Lean's emitted loaded-module graph is authoritative and
    ambient sibling and scratch files never enter the result.  The no-provider
    branch is the legacy source-parser diagnostic retained for callers that do
    not publish audit acceptance; canonical closeout paths must share a
    provider so parser coverage cannot become cache or closure authority.
    """

    root = root.resolve()
    if provider is not None:
        if provider.root != root:
            return ()
        return provider.module_names_in_import_closure(import_module)
    papers_root = root / "papers"
    import_name = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")

    repository_roots = {path.stem for path in root.glob("*.lean") if path.is_file()}
    if papers_root.is_dir():
        repository_roots.update(
            path.name for path in papers_root.iterdir() if path.is_dir()
        )
        repository_roots.update(
            path.stem for path in papers_root.glob("*.lean") if path.is_file()
        )

    seed = _repository_module_source_path(root, import_module)
    if seed is None:
        return ()
    modules: set[str] = set()
    pending = [import_module]
    seen: set[str] = set()
    try:
        while pending:
            module = pending.pop(0)
            if module in seen:
                continue
            seen.add(module)
            source = _repository_module_source_path(root, module)
            if source is None:
                return ()
            modules.add(module)
            text = source.read_text(encoding="utf-8")
            # Reuse the parser's nested-comment masking rather than treating
            # commented examples as import graph edges.
            index = 0
            depth = 0
            masked: list[str] = []
            while index < len(text):
                if text.startswith("/-", index):
                    depth += 1
                    masked.extend("  ")
                    index += 2
                    continue
                if depth and text.startswith("-/", index):
                    depth -= 1
                    masked.extend("  ")
                    index += 2
                    continue
                if depth:
                    masked.append("\n" if text[index] == "\n" else " ")
                    index += 1
                    continue
                if text.startswith("--", index):
                    newline = text.find("\n", index)
                    if newline < 0:
                        masked.extend(" " * (len(text) - index))
                        break
                    masked.extend(" " * (newline - index))
                    masked.append("\n")
                    index = newline + 1
                    continue
                masked.append(text[index])
                index += 1
            if depth:
                return ()
            for line in "".join(masked).splitlines():
                match = re.match(r"^\s*import\s+(.+?)\s*$", line)
                if match is None:
                    continue
                imported_modules = match.group(1).split()
                if not imported_modules or any(
                    not import_name.fullmatch(imported) for imported in imported_modules
                ):
                    return ()
                for imported in imported_modules:
                    imported_source = _repository_module_source_path(root, imported)
                    if imported_source is not None:
                        pending.append(imported)
                    elif imported.split(".", 1)[0] in repository_roots:
                        return ()
    except (OSError, UnicodeError, ValueError):
        return ()
    return tuple(sorted(modules))


def paper_owned_module_names_in_import_closure(
    root: Path,
    paper_folder: Path,
    import_module: str,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[str, ...]:
    """Return exact imported modules owned by one paper directory.

    Lean's loaded-module header determines the complete closure. Ownership is
    then a source-path boundary: modules under the selected paper
    directory (plus its optional paper aggregator) may be semantically
    expanded; shared library and other-paper imports remain terminals whose
    reached ``.olean`` identities are pinned by the manifest. Ambient paper
    files that are not imported never enter this set.  Lean's loaded-module
    graph remains authoritative; ``provider`` only freezes the fallback input
    identity and repository source routing used around that Lean result.
    """

    try:
        root = root.resolve()
        folder = paper_folder.resolve()
        papers_root = (root / "papers").resolve()
        relative_folder = folder.relative_to(papers_root)
    except (OSError, ValueError):
        return ()
    if len(relative_folder.parts) != 1 or not folder.is_dir():
        return ()
    if provider is not None and provider.root != root:
        return ()
    loaded_modules = _lean_loaded_module_candidates(
        root,
        import_module,
        timeout_seconds=600,
        provider=provider,
    )
    if not loaded_modules:
        return ()
    seed = (
        provider.repository_source_path(import_module)
        if provider is not None
        else _repository_module_source_path(root, import_module)
    )
    if seed is None:
        return ()
    try:
        seed.resolve().relative_to(folder)
    except (OSError, ValueError):
        return ()
    aggregator = (papers_root / f"{relative_folder.name}.lean").resolve()
    owned: list[str] = []
    for module in loaded_modules:
        source = (
            provider.repository_source_path(module)
            if provider is not None
            else _repository_module_source_path(root, module)
        )
        if source is None:
            # Dependency-package modules have no repository source and remain
            # imported terminals. A module under this paper's namespace must
            # resolve uniquely or ownership is ambiguous and fails closed.
            if module == relative_folder.name or module.startswith(
                relative_folder.name + "."
            ):
                return ()
            continue
        try:
            resolved = source.resolve()
            is_paper_source = resolved == aggregator or folder in resolved.parents
        except OSError:
            return ()
        if is_paper_source:
            owned.append(module)
    if import_module not in owned:
        return ()
    return tuple(sorted(owned))


def paper_local_module_names(
    root: Path,
    paper_folder: Path,
    *,
    provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[str, ...]:
    """Compatibility wrapper for the PaperInterface-owned import closure."""

    try:
        paper_name = (
            paper_folder.resolve().relative_to((root / "papers").resolve()).name
        )
    except (OSError, ValueError):
        return ()
    return paper_owned_module_names_in_import_closure(
        root,
        paper_folder,
        f"{paper_name}.PaperInterface",
        provider=provider,
    )


def _paper_module_olean_fingerprints(
    root: Path, paper_modules: tuple[str, ...]
) -> tuple[tuple[str, tuple[str, int] | None], ...]:
    """Fingerprint exactly the compiled modules authorized for expansion."""

    fingerprints: list[tuple[str, tuple[str, int] | None]] = []
    for module in paper_modules:
        # Unimported paper files need not have an olean after a focused
        # `PaperInterface` build. They cannot occur in Lean's loaded
        # environment, but retaining their explicit absent marker keeps the
        # cache scope fail-closed if the module set changes.
        fingerprints.append((module, _built_olean_fingerprint(root, module)))
    return tuple(fingerprints)


def _built_workspace_module_inventory(root: Path) -> tuple[tuple[str, ...], str] | None:
    """Return exact module origins built by this workspace and their identity.

    Dependency packages keep their oleans under `.lake/packages`, while every
    repository-local Lean library target is emitted under this workspace's
    `.lake/build/lib/lean`. Using exact module origins avoids both declaration-
    namespace heuristics and a hard-coded list of local library roots.
    """

    build_root = root / ".lake" / "build" / "lib" / "lean"
    if not build_root.is_dir():
        return None
    entries: list[tuple[str, int, int]] = []
    for path in sorted(build_root.rglob("*.olean")):
        fingerprint = _file_fingerprint(path)
        if fingerprint is None:
            return None
        relative = path.relative_to(build_root).with_suffix("")
        module = ".".join(relative.parts)
        if not module:
            return None
        entries.append((module, *fingerprint))
    if not entries:
        return None
    identity = hashlib.sha256(
        json.dumps(entries, ensure_ascii=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return tuple(module for module, _mtime, _size in entries), identity


def _loaded_workspace_module_scope(
    root: Path,
    loaded_modules: Iterable[str],
    lean_path: str,
) -> tuple[tuple[str, ...], str] | None:
    """Return the exact loaded workspace origins used for ownership classification.

    Closure extraction needs the workspace-owned modules in the imported Lean
    environment, not metadata for every unrelated artifact that happens to be
    built in the repository. Exact content pins for modules actually reached by
    a Spec are attached and rechecked separately.
    """

    workspace_modules: list[str] = []
    for module in sorted(set(loaded_modules)):
        location = _closure_module_artifact_location(root, module, lean_path)
        if location is None:
            return None
        artifact_scope, _artifact = location
        if artifact_scope == "workspace":
            workspace_modules.append(module)
    modules = tuple(workspace_modules)
    if not modules:
        return None
    identity = _closure_json_sha256(
        {
            "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "workspace_modules": list(modules),
        }
    )
    return modules, identity


def _audit_module_scope(
    import_module: str, workspace_modules: tuple[str, ...] = ()
) -> tuple[str, ...]:
    """Return the exact module that owns the configured review surface.

    A signature manifest expands transparent declarations only to make a
    paper-facing declaration's own elaborated interface inspectable.  A shared
    namespace is not an import graph: expanding every workspace module below a
    paper namespace can make one review row traverse unrelated proof modules
    merely because they share a prefix. The source-record audit owns the
    separate, semantic traversal of imported terminal definitions, with source
    anchors and bounded bridge requirements.

    ``workspace_modules`` remains an optional test/validation input, but never
    authorizes a namespace-wide expansion.
    """

    if not import_module:
        return ()
    if workspace_modules and import_module not in workspace_modules:
        return ()
    return (import_module,)


def _audit_scope_fingerprint(
    import_module: str,
    olean_fingerprint: tuple[str, int],
    audit_modules: tuple[str, ...],
) -> str:
    """Return a deterministic freshness identity for the exact review scope."""

    payload = {
        "schema": 1,
        "import_module": import_module,
        "import_olean_fingerprint": list(olean_fingerprint),
        "audit_modules": list(audit_modules),
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def signature_manifest_cache_context(
    root: Path,
    import_module: str,
    *,
    build_timeout_seconds: int = 600,
    semantic_dependency_modules: tuple[str, ...] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, Any] | None:
    """Return a persisted-cache context after rebuilding a review import target.

    The context records the built review-module artifact and manifest helper.
    It deliberately does not use every workspace artifact as a cache input:
    unrelated proof modules neither alter the configured review interface nor
    belong in its transparent-definition expansion.  Imported terminal model
    definitions are covered by the independently source-anchored source-record
    audit, rather than by a namespace-prefix heuristic here.
    """

    if not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return None
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
    if (
        olean_fingerprint is None
        or helper_fingerprint is None
        or hash_tool_identity is None
    ):
        return None
    audit_modules = tuple(
        sorted(
            set(
                semantic_dependency_modules
                if semantic_dependency_modules is not None
                else _audit_module_scope(import_module)
            )
            | {import_module}
        )
    )
    if not audit_modules:
        return None
    semantic_module_fingerprints = tuple(
        (
            module,
            olean_fingerprint
            if module == import_module
            else _built_olean_fingerprint(root, module),
        )
        for module in audit_modules
    )
    return {
        "schema": 3,
        "import_module": import_module,
        "olean_fingerprint": list(olean_fingerprint),
        "helper_fingerprint": list(helper_fingerprint),
        "semantic_hash_tool_identity": dict(hash_tool_identity),
        "canonical_representation": "lean_compact_canonical_v2",
        "audit_scope_fingerprint": _audit_scope_fingerprint(
            import_module,
            olean_fingerprint,
            audit_modules,
        ),
        "audit_modules": list(audit_modules),
        "semantic_module_fingerprints": [
            [module, list(fingerprint) if fingerprint is not None else None]
            for module, fingerprint in semantic_module_fingerprints
        ],
    }


def signature_manifest_cache_context_sha256(context: Mapping[str, Any]) -> str:
    """Hash one exact persisted manifest-cache context."""

    required = {
        "schema",
        "import_module",
        "olean_fingerprint",
        "helper_fingerprint",
        "semantic_hash_tool_identity",
        "canonical_representation",
        "audit_scope_fingerprint",
        "audit_modules",
        "semantic_module_fingerprints",
    }
    if not required <= set(context):
        return ""
    return _closure_json_sha256(dict(context))


def _signature_manifest_context_cache_coordinates(
    root: Path,
    import_module: str,
    context: Mapping[str, Any],
    semantic_dependency_modules: tuple[str, ...] | None,
) -> tuple[tuple[Any, ...], tuple[str, ...], dict[str, Any]] | None:
    """Return the exact context entry used by every manifest request subset."""

    try:
        olean_fingerprint = tuple(context["olean_fingerprint"])
        helper_fingerprint = tuple(context["helper_fingerprint"])
        raw_hash_tool_identity = context.get("semantic_hash_tool_identity")
        if not isinstance(raw_hash_tool_identity, dict):
            return None
        hash_tool_path = str(raw_hash_tool_identity.get("resolved_path") or "")
        if not hash_tool_path:
            return None
        hash_tool_fingerprint = _closure_json_sha256(raw_hash_tool_identity)
        audit_modules = tuple(
            sorted(
                set(
                    semantic_dependency_modules
                    if semantic_dependency_modules is not None
                    else tuple(str(module) for module in context["audit_modules"])
                )
                | {import_module}
            )
        )
        audit_scope_fingerprint = _audit_scope_fingerprint(
            import_module, tuple(context["olean_fingerprint"]), audit_modules
        )
        semantic_module_fingerprints = tuple(
            (
                str(raw_module),
                tuple(raw_fingerprint)
                if isinstance(raw_fingerprint, list) and len(raw_fingerprint) == 2
                else None,
            )
            for raw_module, raw_fingerprint in context["semantic_module_fingerprints"]
        )
    except (KeyError, TypeError, ValueError):
        return None
    if (
        context.get("schema") != 3
        or context.get("import_module") != import_module
        or context.get("audit_scope_fingerprint") != audit_scope_fingerprint
        or list(context.get("audit_modules") or []) != list(audit_modules)
        or [
            [module, list(fingerprint) if fingerprint is not None else None]
            for module, fingerprint in semantic_module_fingerprints
        ]
        != context.get("semantic_module_fingerprints")
    ):
        return None
    return (
        (
            str(root.resolve()),
            import_module,
            olean_fingerprint,
            helper_fingerprint,
            audit_scope_fingerprint,
            semantic_module_fingerprints,
            hash_tool_fingerprint,
            ",".join(audit_modules),
            (),
        ),
        audit_modules,
        raw_hash_tool_identity,
    )


def seed_lean_signature_manifest_context_cache(
    root: Path,
    import_module: str,
    manifests: Mapping[str, Mapping[str, Any]],
    validated_manifest_pins: Mapping[str, Mapping[str, str]],
    *,
    build_timeout_seconds: int = 600,
    semantic_dependency_modules: tuple[str, ...] | None = None,
    current_context: Mapping[str, Any] | None = None,
) -> set[str]:
    """Seed exact authenticated roots for later subset requests.

    This API does not establish persistence trust. Its caller must pass roots
    that an independent authority already accepted, together with that
    authority's exact context/signature/dependency pins. Every pin is checked
    again against the current compiled context and canonical manifest before
    insertion into the context entry shared by later singleton/subset calls.
    """

    if not manifests or set(manifests) != set(validated_manifest_pins):
        return set()
    # Authenticated-store priming may already have obtained this exact current
    # context from ``signature_manifest_cache_context`` in the same call. Reuse
    # that in-memory value to avoid a second build-closure scan. The complete
    # context digest, canonical tool identity, signature digest, and dependency
    # digest are still checked below before any cache entry is installed.
    context = (
        dict(current_context)
        if isinstance(current_context, Mapping)
        else signature_manifest_cache_context(
            root,
            import_module,
            build_timeout_seconds=build_timeout_seconds,
            semantic_dependency_modules=semantic_dependency_modules,
        )
    )
    if not isinstance(context, Mapping):
        return set()
    coordinates = _signature_manifest_context_cache_coordinates(
        root, import_module, context, semantic_dependency_modules
    )
    context_sha256 = signature_manifest_cache_context_sha256(context)
    if coordinates is None or not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return set()
    context_cache_key, _audit_modules, hash_tool_identity = coordinates
    canonical_representation = str(
        context.get("canonical_representation") or ""
    ).strip()

    accepted: dict[str, dict[str, Any]] = {}
    for declaration, raw_manifest in manifests.items():
        pin = validated_manifest_pins.get(declaration)
        if not isinstance(raw_manifest, Mapping) or not isinstance(pin, Mapping):
            continue
        if set(pin) != {
            "manifest_cache_context_sha256",
            "elaborated_signature_sha256",
            "semantic_dependency_sha256",
        }:
            continue
        expected_context = (
            str(pin.get("manifest_cache_context_sha256") or "").strip().lower()
        )
        expected_signature = (
            str(pin.get("elaborated_signature_sha256") or "").strip().lower()
        )
        expected_dependency = (
            str(pin.get("semantic_dependency_sha256") or "").strip().lower()
        )
        manifest = dict(raw_manifest)
        dependency = semantic_dependency_manifest(manifest)
        if (
            expected_context != context_sha256
            or not re.fullmatch(r"[0-9a-f]{64}", expected_signature)
            or not re.fullmatch(r"[0-9a-f]{64}", expected_dependency)
            or manifest.get("canonical_representation") != canonical_representation
            or manifest.get("semantic_hash_tool_identity") != hash_tool_identity
            or str(manifest.get("sha256") or "").strip().lower() != expected_signature
            or signature_manifest_digest(manifest) != expected_signature
            or not isinstance(dependency, Mapping)
            or str(dependency.get("semantic_dependency_sha256") or "").strip().lower()
            != expected_dependency
        ):
            continue
        manifest["semantic_dependency_manifest"] = dict(dependency)
        accepted[declaration] = manifest

    cached = dict(_CACHE.get(context_cache_key, {}))
    seeded: set[str] = set()
    for declaration, manifest in accepted.items():
        existing = cached.get(declaration)
        if existing is not None and (
            signature_manifest_digest(existing) != signature_manifest_digest(manifest)
            or semantic_dependency_manifest(existing)
            != semantic_dependency_manifest(manifest)
        ):
            continue
        cached[declaration] = manifest
        seeded.add(declaration)
    if seeded:
        _CACHE[context_cache_key] = cached
        context_prefix = context_cache_key[:-1]
        for cache_key in list(_CACHE):
            if cache_key != context_cache_key and cache_key[:-1] == context_prefix:
                del _CACHE[cache_key]
    return seeded


def _manifest_batch_size() -> int:
    """Return the explicit, bounded capacity for one Lean manifest process."""

    raw = os.environ.get(MANIFEST_BATCH_SIZE_ENV, "").strip()
    if not raw:
        return DEFAULT_MANIFEST_BATCH_SIZE
    try:
        configured = int(raw)
    except ValueError:
        return DEFAULT_MANIFEST_BATCH_SIZE
    return min(MAX_MANIFEST_BATCH_SIZE, max(1, configured))


def _manifest_chunks(
    names: list[str], *, batch_size: int | None = None
) -> list[list[str]]:
    """Split requests by a resource capacity, never by declaration identity."""

    capacity = _manifest_batch_size() if batch_size is None else batch_size
    if capacity < 1:
        raise ValueError("manifest batch capacity must be positive")
    return [names[index : index + capacity] for index in range(0, len(names), capacity)]


def _manifest_initial_batches(names: list[str]) -> list[list[str]]:
    """Schedule every row under the configured per-process resource bound."""

    return _manifest_chunks(names)


def _emit_manifest_batch_progress(
    callback: Callable[[Mapping[str, Any]], None] | None,
    *,
    runner: str,
    status: str,
    batch_number: int,
    batch_total: int,
    root_count: int,
    completed_count: int = 0,
    missing_count: int = 0,
) -> None:
    """Best-effort progress for one fresh Lean batch without affecting receipts."""

    if callback is None:
        return
    event = {
        "schema": MANIFEST_PROGRESS_EVENT_SCHEMA,
        "runner": runner,
        "status": status,
        "batch_number": batch_number,
        "batch_total": batch_total,
        "root_count": root_count,
        "completed_count": completed_count,
        "missing_count": missing_count,
    }
    try:
        callback(event)
    except Exception:  # noqa: BLE001 - diagnostics cannot affect extraction.
        pass


def _manifest_batch_timeout_seconds(
    batch: list[str], caller_timeout_seconds: int, *, chunked: bool
) -> int:
    """Give a bounded batch an additive, declaration-count resource budget."""

    # A singleton has no co-located graph to protect from.  It must retain the
    # caller's full budget even when its siblings make the overall request
    # chunked, otherwise a 300-second dashboard row is silently truncated to
    # the generic short-batch cap.
    if not chunked or len(batch) == 1:
        return caller_timeout_seconds
    return min(
        caller_timeout_seconds,
        MAX_CHUNKED_MANIFEST_TIMEOUT_SECONDS * max(1, len(batch)),
    )


def _manifest_retry_batches(missing_names: list[str]) -> list[list[str]]:
    """Return bounded residual retries after an incomplete initial request."""

    if len(missing_names) == 1:
        return [missing_names]
    if 1 < len(missing_names) <= MAX_INDIVIDUAL_MANIFEST_RETRIES:
        midpoint = len(missing_names) // 2
        return [missing_names[:midpoint], missing_names[midpoint:]]
    return []


def _manifest_adaptive_retries(
    missing_names: list[str],
    run_batch: Callable[[list[str]], Mapping[str, Mapping[str, Any]]],
) -> dict[str, dict[str, Any]]:
    """Bisect only unresolved rows, retaining every completed Lean receipt."""

    recovered: dict[str, dict[str, Any]] = {}
    pending = _manifest_retry_batches(missing_names)
    while pending:
        batch = pending.pop(0)
        extracted = run_batch(batch)
        recovered.update(_requested_manifests(dict(extracted), batch))
        unresolved = [name for name in batch if name not in recovered]
        if len(batch) > 1 and unresolved:
            pending[0:0] = _manifest_retry_batches(unresolved)
    return recovered


def _requested_manifests(
    manifests: dict[str, dict[str, Any]], request_names: list[str]
) -> dict[str, dict[str, Any]]:
    """Keep only requested helper output in the request's deterministic order."""

    return {name: manifests[name] for name in request_names if name in manifests}


def run_lean_signature_manifests(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    semantic_dependency_modules: tuple[str, ...] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    manifest_checkpoint: Callable[
        [Mapping[str, Any], Mapping[str, Mapping[str, Any]]], None
    ]
    | None = None,
    progress_callback: Callable[[Mapping[str, Any]], None] | None = None,
) -> dict[str, dict[str, Any]]:
    """Return current manifests for declarations imported from one Lean module.

    ``semantic_dependency_modules`` must be the exact configured-interface
    import closure when the caller will use the transitive dependency digest.
    The default preserves the historical single-module signature surface for
    callers that need only the outer elaborated type.

    ``manifest_checkpoint`` is an optional best-effort durability hook for
    independently completed Lean batches.  It receives the exact compiled
    context and raw Lean-owned manifests before the final dependency-artifact
    attachment.  A callback is never allowed to affect extraction; persistent
    consumers must independently revalidate its records before reuse.

    ``progress_callback`` receives best-effort operational events for fresh
    initial Lean batches. It cannot affect scheduling, cache authority, or the
    returned manifests, and receives no declaration names.

    """

    names = sorted(set(declaration_names))
    if not names:
        return {}
    context = signature_manifest_cache_context(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        semantic_dependency_modules=semantic_dependency_modules,
        build_input_provider=build_input_provider,
    )
    if context is None:
        return {}
    coordinates = _signature_manifest_context_cache_coordinates(
        root, import_module, context, semantic_dependency_modules
    )
    if coordinates is None:
        return {}
    context_cache_key, audit_modules, raw_hash_tool_identity = coordinates
    hash_tool_path = str(raw_hash_tool_identity.get("resolved_path") or "")
    cache_key = (*context_cache_key[:-1], tuple(names))

    def checkpoint(
        extracted: Mapping[str, Mapping[str, Any]], batch: list[str]
    ) -> None:
        """Persist one completed raw batch without making persistence authoritative."""

        if manifest_checkpoint is None:
            return
        completed = _requested_manifests(dict(extracted), batch)
        if not completed:
            return
        try:
            # The callback may perform I/O. Give it detached data and make all
            # failures an optimization miss rather than an extraction failure.
            manifest_checkpoint(deepcopy(dict(context)), deepcopy(completed))
        except Exception:  # noqa: BLE001 - checkpointing cannot alter evidence.
            pass

    if cache_key not in _CACHE:
        # The context entry is populated only from this process's fresh Lean
        # output. It is keyed by the built review artifact, helper, and exact
        # audit-module scope, so a later narrower request can reuse a manifest
        # only when it would have asked Lean about the identical declaration
        # in the identical compiled environment. Declaration spellings route
        # this cache lookup; they are never semantic evidence.
        cached_context = _CACHE.get(context_cache_key, {})
        manifests = dict(cached_context)
        missing_names = [name for name in names if name not in manifests]
        initial_batches = (
            _manifest_initial_batches(missing_names) if missing_names else []
        )
        uses_chunking = len(initial_batches) > 1
        for batch_number, batch in enumerate(initial_batches, start=1):
            _emit_manifest_batch_progress(
                progress_callback,
                runner="full_manifest",
                status="started",
                batch_number=batch_number,
                batch_total=len(initial_batches),
                root_count=len(batch),
            )
            extracted = _run_manifest_script(
                root,
                f"import Lean\nimport {import_module}",
                batch,
                _manifest_batch_timeout_seconds(
                    batch, timeout_seconds, chunked=uses_chunking
                ),
                ",".join(audit_modules),
                hash_tool_path,
            )
            manifests.update(_requested_manifests(extracted, batch))
            checkpoint(extracted, batch)
            # Preserve independently obtained exact results before a later
            # batch or retry fails. This is process-local only; a new audit
            # still receives fresh Lean output for its compiled environment.
            _CACHE[context_cache_key] = dict(manifests)
            missing_batch_names = [name for name in batch if name not in manifests]
            _emit_manifest_batch_progress(
                progress_callback,
                runner="full_manifest",
                status="finished",
                batch_number=batch_number,
                batch_total=len(initial_batches),
                root_count=len(batch),
                completed_count=len(batch) - len(missing_batch_names),
                missing_count=len(missing_batch_names),
            )
            if uses_chunking and len(missing_batch_names) > 1:
                # Retry failures locally, before another chunk can obscure
                # which bounded request caused the missing result. Singleton
                # requests cannot be split further and are not repeated.
                retried = _manifest_adaptive_retries(
                    missing_batch_names,
                    lambda retry_names: _run_manifest_script(
                        root,
                        f"import Lean\nimport {import_module}",
                        retry_names,
                        timeout_seconds,
                        ",".join(audit_modules),
                        hash_tool_path,
                    ),
                )
                manifests.update(retried)
                checkpoint(retried, missing_batch_names)
                _CACHE[context_cache_key] = dict(manifests)
        missing_names = [name for name in names if name not in manifests]
        if len(names) > 1 and not uses_chunking:
            retried = _manifest_adaptive_retries(
                missing_names,
                lambda retry_names: _run_manifest_script(
                    root,
                    f"import Lean\nimport {import_module}",
                    retry_names,
                    timeout_seconds,
                    ",".join(audit_modules),
                    hash_tool_path,
                ),
            )
            manifests.update(retried)
            checkpoint(retried, missing_names)
            _CACHE[context_cache_key] = dict(manifests)
        manifests = _with_semantic_dependency_module_identities(
            root, manifests, timeout_seconds=build_timeout_seconds
        )
        manifests = {
            name: {
                **manifest,
                "canonical_representation": "lean_compact_canonical_v2",
                "semantic_hash_tool_identity": dict(raw_hash_tool_identity),
            }
            for name, manifest in manifests.items()
        }
        _CACHE[context_cache_key] = dict(manifests)
        _CACHE[cache_key] = _requested_manifests(manifests, names)
    return _CACHE[cache_key]


def run_lean_direct_library_dependency_surface(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
) -> dict[str, tuple[str, ...]]:
    """Return each current Spec's direct elaborated EconCSLib dependencies.

    Unlike the full manifest route this retains neither recursive graphs nor
    proof bodies.  It is the narrow source-to-library review inventory: Lean
    resolves every direct constant in the transparent Spec, and callers decide
    which reviewed library declaration owns a projection or structure field.
    A failed build or incomplete Lean response yields no surface, never a
    source-token fallback.
    """

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    if not names or not _build_import_target(root, import_module, build_timeout_seconds):
        return {}
    return _run_direct_library_dependency_surface_script(
        root,
        f"import Lean\nimport {import_module}",
        names,
        timeout_seconds,
    )


def _run_transparent_paper_spec_display_script(
    root: Path,
    script_prefix: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    max_expansions: int,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Ask Lean to pretty-print current transparent paper-local Spec bodies."""

    names = sorted({str(name).strip() for name in specification_names if str(name).strip()})
    modules = tuple(sorted({str(module).strip() for module in paper_modules if str(module).strip()}))
    if (
        not names
        or not modules
        or not HELPER_PATH.exists()
        or not (1 <= max_expansions <= 4096)
    ):
        return {}
    try:
        helper = HELPER_PATH.read_text(encoding="utf-8")
    except OSError:
        return {}
    request = json.dumps(
        {"specifications": names, "paper_modules": list(modules)},
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    script = _compose_helper_script(
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0",
        helper,
        "#transparent_paper_spec_display "
        + json.dumps(request)
        + " "
        + json.dumps(str(max_expansions)),
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "transparent_paper_spec_display.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, stderr_bytes = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
            return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        diagnostic = stderr_bytes.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean transparent-Spec display extraction failed:\n" + diagnostic[:8000],
                file=sys.stderr,
            )
        else:
            print(
                "Lean transparent-Spec display extraction failed without stderr "
                f"(exit {proc.returncode}):\n"
                + stdout[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_transparent_paper_spec_display_output(stdout, names)
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_TRANSPARENT_PAPER_SPEC_DISPLAY" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
    return parsed


def _run_transparent_paper_declaration_display_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Ask Lean for a recursive paper-prerequisite display closure."""

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    modules = tuple(
        sorted({str(module).strip() for module in paper_modules if str(module).strip()})
    )
    if not names or not modules or not HELPER_PATH.exists():
        return {}
    try:
        helper = HELPER_PATH.read_text(encoding="utf-8")
    except OSError:
        return {}
    request = json.dumps(
        {"specifications": names, "paper_modules": list(modules)},
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    script = _compose_helper_script(
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0",
        helper,
        "#transparent_paper_declaration_display " + json.dumps(request),
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "transparent_paper_declaration_display.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, stderr_bytes = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
            return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        diagnostic = stderr_bytes.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean paper-prerequisite display extraction failed:\n" + diagnostic[:8000],
                file=sys.stderr,
            )
        else:
            print(
                "Lean paper-prerequisite display extraction failed without stderr "
                f"(exit {proc.returncode}):\n" + stdout[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_transparent_paper_declaration_display_output(stdout, names)
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_TRANSPARENT_PAPER_DECLARATION_DISPLAY" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
        elif stdout.strip():
            print(
                "Lean paper-prerequisite display extraction emitted no valid receipt:\n"
                + stdout[:8000],
                file=sys.stderr,
            )
    return parsed


def _run_transparent_library_declaration_display_script(
    root: Path,
    script_prefix: str,
    declaration_names: list[str],
    *,
    timeout_seconds: int,
) -> dict[str, dict[str, Any]]:
    """Ask Lean for each library root's own transparent semantic target."""

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    if (
        not names
        or any(not name.startswith("EconCSLib.") for name in names)
        or not HELPER_PATH.exists()
    ):
        return {}
    try:
        helper = HELPER_PATH.read_text(encoding="utf-8")
    except OSError:
        return {}
    script = _compose_helper_script(
        script_prefix
        + "\nset_option maxRecDepth 100000"
        + "\nset_option maxHeartbeats 0",
        helper,
        "#transparent_library_declaration_display "
        + json.dumps(
            json.dumps(names, ensure_ascii=True, separators=(",", ":")),
            ensure_ascii=True,
        ),
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        path = Path(tmpdir) / "transparent_library_declaration_display.lean"
        path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, stderr_bytes = proc.communicate(timeout=timeout_seconds)
        except OSError:
            return {}
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
            return {}
    stdout = stdout_bytes.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        diagnostic = stderr_bytes.decode("utf-8", errors="replace")
        if diagnostic.strip():
            print(
                "Lean transparent-library display extraction failed:\n" + diagnostic[:8000],
                file=sys.stderr,
            )
        else:
            print(
                "Lean transparent-library display extraction failed without stderr "
                f"(exit {proc.returncode}):\n" + stdout[:8000],
                file=sys.stderr,
            )
        return {}
    parsed = parse_transparent_library_declaration_display_output(stdout, names)
    if not parsed:
        diagnostics = [
            line
            for line in stdout.splitlines()
            if "LEAN_TRANSPARENT_LIBRARY_DECLARATION_DISPLAY" in line
        ]
        if diagnostics:
            print("\n".join(diagnostics[:8]), file=sys.stderr)
        elif stdout.strip():
            print(
                "Lean transparent-library display extraction emitted no valid receipt:\n"
                + stdout[:8000],
                file=sys.stderr,
            )
    return parsed


def run_lean_transparent_paper_spec_displays(
    root: Path,
    import_module: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    max_expansions: int = 512,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    """Return Lean-owned readable semantic targets for source-to-Spec review.

    A target is available only after Lean builds the selected import module and
    fully eliminates transparent declarations owned by the paper.  Imported
    library declarations intentionally remain visible so the separate library
    review surface can show their exact definitions and source connections.
    """

    names = sorted({str(name).strip() for name in specification_names if str(name).strip()})
    modules = tuple(sorted({str(module).strip() for module in paper_modules if str(module).strip()}))
    if not names or not modules or not (1 <= max_expansions <= 4096):
        return {}
    # Receipt-producing audit callers leave this enabled.  Packet rendering is
    # deliberately non-certifying and may reuse a just-built interface: asking
    # Lake to rebuild the same large import closure immediately before the
    # independent Lean display pass can consume the whole renderer budget.
    if require_build and not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    return _run_transparent_paper_spec_display_script(
        root,
        f"import Lean\nimport {import_module}",
        names,
        modules,
        max_expansions=max_expansions,
        timeout_seconds=timeout_seconds,
    )


def run_lean_transparent_paper_declaration_displays(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    """Return Lean-owned semantic displays for retained paper-local objects.

    Every transparent definition is opened exactly at its own root.  Named
    paper and library dependencies left in that elaborated body become
    recursive review cards; Python only carries Lean's resulting closure.
    """

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    modules = tuple(
        sorted({str(module).strip() for module in paper_modules if str(module).strip()})
    )
    if not names or not modules:
        return {}
    if require_build and not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    return _run_transparent_paper_declaration_display_script(
        root,
        f"import Lean\nimport {import_module}",
        names,
        modules,
        timeout_seconds=timeout_seconds,
    )


def run_lean_transparent_library_declaration_displays(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    require_build: bool = True,
) -> dict[str, dict[str, Any]]:
    """Return Lean-expanded own bodies for reusable library declarations.

    This is deliberately a shallow declaration-level expansion: names left in
    a definition's body form their own library review cards instead of being
    hidden by a recursive pretty-printer.  The function is Lean-owned; Python
    only validates and hashes the emitted transport.
    """

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    if not names or any(not name.startswith("EconCSLib.") for name in names):
        return {}
    if require_build and not _build_import_target(
        root, import_module, build_timeout_seconds
    ):
        return {}
    return _run_transparent_library_declaration_display_script(
        root,
        f"import Lean\nimport {import_module}",
        names,
        timeout_seconds=timeout_seconds,
    )


def run_lean_signature_manifest_revalidations(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    semantic_dependency_modules: tuple[str, ...] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    current_context: Mapping[str, Any] | None = None,
    progress_callback: Callable[[Mapping[str, Any]], None] | None = None,
) -> dict[str, dict[str, Any]]:
    """Return compact Lean receipts for item-level persisted-manifest reuse.

    These receipts are not manifests and cannot seed the manifest cache.  They
    only let a caller retain a separately authenticated full carrier when the
    exact declaration source is unchanged and this current Lean run reproduces
    its canonical root/dependency identities.
    """

    names = sorted(set(declaration_names))
    if not names:
        return {}
    context = (
        dict(current_context)
        if isinstance(current_context, Mapping)
        else signature_manifest_cache_context(
            root,
            import_module,
            build_timeout_seconds=build_timeout_seconds,
            semantic_dependency_modules=semantic_dependency_modules,
            build_input_provider=build_input_provider,
        )
    )
    if not isinstance(context, Mapping):
        return {}
    coordinates = _signature_manifest_context_cache_coordinates(
        root, import_module, context, semantic_dependency_modules
    )
    if coordinates is None:
        return {}
    context_cache_key, audit_modules, raw_hash_tool_identity = coordinates
    hash_tool_path = str(raw_hash_tool_identity.get("resolved_path") or "")
    receipt_cache_keys = {
        name: (context_cache_key, name)
        for name in names
    }
    # A declaration identifier only addresses an exact compiled context.  The
    # context coordinate includes the root, imported module, olean/helper
    # fingerprints, semantic module identities, audit scope, and hash tool;
    # it is the reuse authority, never a spelling-based cache key.
    receipts: dict[str, dict[str, Any]] = {
        name: deepcopy(_MANIFEST_REVALIDATION_RECEIPT_CACHE[cache_key])
        for name, cache_key in receipt_cache_keys.items()
        if cache_key in _MANIFEST_REVALIDATION_RECEIPT_CACHE
    }
    pending_names = [name for name in names if name not in receipts]
    initial_batches = _manifest_initial_batches(pending_names)
    uses_chunking = len(initial_batches) > 1

    def retain_successful_receipts(
        extracted: Mapping[str, Mapping[str, Any]],
        requested: Iterable[str],
    ) -> None:
        """Keep only successful exact receipts, with caller/cache isolation."""

        for name, receipt in _requested_manifests(extracted, requested).items():
            stored = deepcopy(dict(receipt))
            receipts[name] = stored
            _MANIFEST_REVALIDATION_RECEIPT_CACHE[receipt_cache_keys[name]] = (
                deepcopy(stored)
            )

    for batch_number, batch in enumerate(initial_batches, start=1):
        _emit_manifest_batch_progress(
            progress_callback,
            runner="manifest_revalidation",
            status="started",
            batch_number=batch_number,
            batch_total=len(initial_batches),
            root_count=len(batch),
        )
        extracted = _run_manifest_revalidation_script(
            root,
            f"import Lean\nimport {import_module}",
            batch,
            _manifest_batch_timeout_seconds(
                batch, timeout_seconds, chunked=uses_chunking
            ),
            ",".join(audit_modules),
            hash_tool_path,
        )
        retain_successful_receipts(extracted, batch)
        missing = [name for name in batch if name not in receipts]
        _emit_manifest_batch_progress(
            progress_callback,
            runner="manifest_revalidation",
            status="finished",
            batch_number=batch_number,
            batch_total=len(initial_batches),
            root_count=len(batch),
            completed_count=len(batch) - len(missing),
            missing_count=len(missing),
        )
        if uses_chunking and len(missing) > 1:
            retried = _manifest_adaptive_retries(
                missing,
                lambda retry_names: _run_manifest_revalidation_script(
                    root,
                    f"import Lean\nimport {import_module}",
                    retry_names,
                    timeout_seconds,
                    ",".join(audit_modules),
                    hash_tool_path,
                ),
            )
            retain_successful_receipts(retried, missing)
    missing = [name for name in names if name not in receipts]
    if len(pending_names) > 1 and not uses_chunking:
        retried = _manifest_adaptive_retries(
            missing,
            lambda retry_names: _run_manifest_revalidation_script(
                root,
                f"import Lean\nimport {import_module}",
                retry_names,
                timeout_seconds,
                ",".join(audit_modules),
                hash_tool_path,
            ),
        )
        retain_successful_receipts(retried, missing)
    return {
        name: deepcopy(receipts[name])
        for name in names
        if name in receipts
    }


def run_lean_signature_manifests_for_source(
    root: Path,
    source: str,
    declaration_names: list[str],
    timeout_seconds: int = 120,
) -> dict[str, dict[str, Any]]:
    """Test helper: elaborate declarations supplied directly in a Lean source string."""

    hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
    if hash_tool_identity is None:
        return {}
    manifests = _run_manifest_script(
        root,
        f"import Lean\n\n{source}",
        sorted(set(declaration_names)),
        timeout_seconds,
        "",
        hash_tool_identity["resolved_path"],
    )
    manifests = _with_semantic_dependency_module_identities(
        root, manifests, timeout_seconds=timeout_seconds
    )
    return {
        name: {
            **manifest,
            "canonical_representation": "lean_compact_canonical_v2",
            "semantic_hash_tool_identity": dict(hash_tool_identity),
        }
        for name, manifest in manifests.items()
    }


def run_lean_proposition_spec_proof_matches(
    root: Path,
    import_module: str,
    routes: list[tuple[str, str]],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[tuple[str, str], bool]:
    """Check proof routes by definitional equality of elaborated Lean types."""

    canonical_routes = sorted(set(routes))
    if not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        tuple(canonical_routes),
    )
    if cache_key not in _PROPOSITION_SPEC_PROOF_CACHE:
        _PROPOSITION_SPEC_PROOF_CACHE[cache_key] = _run_proposition_spec_proof_script(
            root,
            f"import Lean\nimport {import_module}",
            canonical_routes,
            timeout_seconds,
        )
    return _PROPOSITION_SPEC_PROOF_CACHE[cache_key]


def run_lean_proposition_spec_proof_matches_for_source(
    root: Path,
    source: str,
    routes: list[tuple[str, str]],
    timeout_seconds: int = 120,
) -> dict[tuple[str, str], bool]:
    """Test helper for proposition-spec routes declared in inline Lean source."""

    return _run_proposition_spec_proof_script(
        root,
        f"import Lean\n\n{source}",
        sorted(set(routes)),
        timeout_seconds,
    )


def run_lean_semantic_contract_matches(
    root: Path,
    import_module: str,
    routes: list[tuple[str, str, str]],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[tuple[str, str, str], bool]:
    """Check exact proof/refutation contracts using elaborated Lean types."""

    canonical_routes = sorted(set(routes))
    if not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        tuple(canonical_routes),
    )
    if cache_key not in _SEMANTIC_CONTRACT_CACHE:
        batches = _semantic_contract_match_batches(canonical_routes)
        uses_chunking = len(batches) > 1
        batch_timeout = min(
            timeout_seconds, MAX_CHUNKED_SEMANTIC_CONTRACT_MATCH_TIMEOUT_SECONDS
        )
        matches: dict[tuple[str, str, str], bool] = {}
        for batch in batches:
            extracted = _run_semantic_contract_script(
                root,
                f"import Lean\nimport {import_module}",
                batch,
                batch_timeout if uses_chunking else timeout_seconds,
            )
            matches.update(_requested_semantic_contract_matches(extracted, batch))
            if uses_chunking:
                # A missing Lean result is never credited.  Retry only that
                # exact route so a resource failure in one bounded script does
                # not discard independently checkable contracts in the batch.
                for route in batch:
                    if route in matches:
                        continue
                    retried = _run_semantic_contract_script(
                        root,
                        f"import Lean\nimport {import_module}",
                        [route],
                        batch_timeout,
                    )
                    matches.update(
                        _requested_semantic_contract_matches(retried, [route])
                    )
        _SEMANTIC_CONTRACT_CACHE[cache_key] = _requested_semantic_contract_matches(
            matches, canonical_routes
        )
    return _SEMANTIC_CONTRACT_CACHE[cache_key]


def run_lean_semantic_contract_matches_for_source(
    root: Path,
    source: str,
    routes: list[tuple[str, str, str]],
    timeout_seconds: int = 120,
) -> dict[tuple[str, str, str], bool]:
    """Test helper for exact semantic contracts declared in inline Lean source."""

    return _run_semantic_contract_script(
        root,
        f"import Lean\n\n{source}",
        sorted(set(routes)),
        timeout_seconds,
    )


def run_lean_operational_outcome_domain_bridges(
    root: Path,
    import_module: str,
    routes: list[OperationalOutcomeDomainRoute],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[OperationalOutcomeDomainRoute, bool]:
    """Check terminal-existence bridge routes from elaborated Lean types.

    Each route is ``(target, bridge, model, terminal, run, terminal_predicate,
    model_root, transition_root)`` using outer Pi indices and exact resolved
    declaration roots. The checker derives the existential result domain,
    requires an exact-header bridge theorem, and verifies that the model value
    occurs in the concrete transition relation. Route names only locate Lean
    declarations; mathematical acceptance is entirely Meta-level.
    """

    canonical_routes = sorted(set(routes))
    if not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        tuple(canonical_routes),
    )
    if cache_key not in _OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_CACHE:
        checked = _run_operational_outcome_domain_bridge_script(
            root,
            f"import Lean\nimport {import_module}",
            canonical_routes,
            timeout_seconds,
        )
        _OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_CACHE[cache_key] = {
            route: checked[route] for route in canonical_routes if route in checked
        }
    return _OPERATIONAL_OUTCOME_DOMAIN_BRIDGE_CACHE[cache_key]


def run_lean_operational_outcome_domain_bridges_for_source(
    root: Path,
    source: str,
    routes: list[OperationalOutcomeDomainRoute],
    timeout_seconds: int = 120,
) -> dict[OperationalOutcomeDomainRoute, bool]:
    """Test helper for terminal-existence bridge checks in inline Lean code."""

    return _run_operational_outcome_domain_bridge_script(
        root,
        f"import Lean\n\n{source}",
        sorted(set(routes)),
        timeout_seconds,
    )


def run_lean_operational_outcome_state_transition_bridges(
    root: Path,
    import_module: str,
    routes: list[OperationalOutcomeStateTransitionRoute],
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[OperationalOutcomeStateTransitionRoute, bool]:
    """Check exact bridges for result-local operational state domains.

    Each route is ``(target, terminal_bridge, initial_witness, model, state,
    initial, terminal, run, terminal_predicate, model_root, state_root,
    transition_root)``.  Lean derives both exact-header proof types and
    verifies the direct state/transition occurrence relations.  Names only
    locate declarations and roots supplied by the generated manifest; they
    are not used for semantic classification.
    """

    canonical_routes = sorted(set(routes))
    if not _build_import_target(
        root,
        import_module,
        build_timeout_seconds,
        provider=build_input_provider,
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        tuple(canonical_routes),
    )
    if cache_key not in _OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_CACHE:
        checked = _run_operational_outcome_state_transition_bridge_script(
            root,
            f"import Lean\nimport {import_module}",
            canonical_routes,
            timeout_seconds,
        )
        _OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_CACHE[cache_key] = {
            route: checked[route] for route in canonical_routes if route in checked
        }
    return _OPERATIONAL_OUTCOME_STATE_TRANSITION_BRIDGE_CACHE[cache_key]


def run_lean_operational_outcome_state_transition_bridges_for_source(
    root: Path,
    source: str,
    routes: list[OperationalOutcomeStateTransitionRoute],
    timeout_seconds: int = 120,
) -> dict[OperationalOutcomeStateTransitionRoute, bool]:
    """Test helper for result-local state/transition bridge checks."""

    return _run_operational_outcome_state_transition_bridge_script(
        root,
        f"import Lean\n\n{source}",
        sorted(set(routes)),
        timeout_seconds,
    )


def run_lean_semantic_contract_transparency_checks(
    root: Path,
    import_module: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    max_expansions: int = 512,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, dict[str, Any]]:
    """Check that exact-contract Specs have no opaque paper-local wrappers.

    Lean determines every dependency from elaborated expressions and module
    provenance.  ``paper_modules`` must be the exact filesystem-derived module
    set for the reviewed paper; names merely select declarations and never
    establish ownership or semantic equivalence.
    """

    specifications = tuple(
        sorted(set(name.strip() for name in specification_names if name.strip()))
    )
    modules = tuple(
        sorted(set(module.strip() for module in paper_modules if module.strip()))
    )
    if (
        not specifications
        or not modules
        or not (1 <= max_expansions <= 4096)
        or not _build_import_target(
            root,
            import_module,
            build_timeout_seconds,
            provider=build_input_provider,
        )
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    module_fingerprints = _paper_module_olean_fingerprints(root, modules)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        module_fingerprints,
        specifications,
        modules,
        max_expansions,
    )
    if cache_key not in _SEMANTIC_CONTRACT_TRANSPARENCY_CACHE:
        names = list(specifications)
        batches = _semantic_contract_transparency_batches(names)
        uses_chunking = len(batches) > 1
        batch_timeout = min(timeout_seconds, MAX_CHUNKED_MANIFEST_TIMEOUT_SECONDS)
        checks: dict[str, dict[str, Any]] = {}
        for batch in batches:
            extracted = _run_semantic_contract_transparency_script(
                root,
                f"import Lean\nimport {import_module}",
                batch,
                modules,
                max_expansions,
                batch_timeout if uses_chunking else timeout_seconds,
            )
            checks.update(
                _requested_semantic_contract_transparency_checks(extracted, batch)
            )
            if uses_chunking:
                # A missing verdict is not credited.  Retry just that contract
                # so a resource failure in one bounded script does not mask a
                # neighbouring route, while preserving a finite total effort.
                for specification in batch:
                    if specification in checks:
                        continue
                    retried = _run_semantic_contract_transparency_script(
                        root,
                        f"import Lean\nimport {import_module}",
                        [specification],
                        modules,
                        max_expansions,
                        batch_timeout,
                    )
                    checks.update(
                        _requested_semantic_contract_transparency_checks(
                            retried, [specification]
                        )
                    )
        _SEMANTIC_CONTRACT_TRANSPARENCY_CACHE[cache_key] = (
            _requested_semantic_contract_transparency_checks(checks, names)
        )
    return _SEMANTIC_CONTRACT_TRANSPARENCY_CACHE[cache_key]


def run_lean_semantic_contract_transparency_checks_for_source(
    root: Path,
    source: str,
    specification_names: list[str],
    *,
    max_expansions: int = 512,
    timeout_seconds: int = 120,
) -> dict[str, dict[str, Any]]:
    """Test helper for inline Specs without a compiled module origin.

    The Lean command conservatively treats unresolved-origin fixture
    declarations as local, while ordinary imported Lean primitives retain
    their module provenance and remain canonical terminals.
    """

    specifications = sorted(
        set(name.strip() for name in specification_names if name.strip())
    )
    return _run_semantic_contract_transparency_script(
        root,
        f"import Lean\n\n{source}",
        specifications,
        (),
        max_expansions,
        timeout_seconds,
    )


def _semantic_contract_closure_context_sha256(
    root: Path,
    import_module: str,
    paper_modules: tuple[str, ...],
    workspace_scope_sha256: str,
    foundation_modules: tuple[str, ...],
) -> str:
    """Bind a closure receipt to its module/package ownership context."""

    extractor_identity = _semantic_contract_closure_extractor_identity()
    if extractor_identity is None:
        return ""
    package_files = (
        root / "lake-manifest.json",
        root / "lean-toolchain",
        root / "scripts" / "lean_import_graph_helper.lean",
    )
    package_identities = [
        {
            "path": path.relative_to(root).as_posix(),
            "sha256": (
                hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else ""
            ),
        }
        for path in package_files
    ]
    return _closure_json_sha256(
        {
            "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "import_module": import_module,
            "paper_modules": list(paper_modules),
            "workspace_module_scope_sha256": workspace_scope_sha256,
            "foundation_module_roots": list(foundation_modules),
            "extractor_identity": extractor_identity,
            "package_identities": package_identities,
        }
    )


SEMANTIC_CONTRACT_CLOSURE_PYTHON_IDENTITY_ROOTS = (
    "run_lean_semantic_contract_closure_manifests",
)


def _semantic_contract_closure_extractor_identity() -> dict[str, str] | None:
    """Pin only code transitively reachable from closure extraction."""

    try:
        from scripts.python_source_slice_identity import (
            transitive_top_level_source_slice_identity,
        )
    except ImportError:
        try:
            from python_source_slice_identity import (
                transitive_top_level_source_slice_identity,
            )
        except ImportError:
            return None

    python_identity = transitive_top_level_source_slice_identity(
        Path(__file__),
        SEMANTIC_CONTRACT_CLOSURE_PYTHON_IDENTITY_ROOTS,
    )
    if python_identity is None:
        return None
    try:
        lean_helper_sha256 = hashlib.sha256(HELPER_PATH.read_bytes()).hexdigest()
    except OSError:
        return None

    return {
        "schema": "4",
        "canonical_surface_representation": "lean_compact_canonical_surface_sha256_v2",
        "digest_algorithm": "sha256",
        "lean_helper_sha256": lean_helper_sha256,
        "python_source_slice_schema": python_identity["schema"],
        "python_source_slice_sha256": python_identity["source_slice_sha256"],
        "python_source_slice_builder_sha256": python_identity[
            "identity_builder_sha256"
        ],
        "python_source_slice_roots_sha256": python_identity["roots_sha256"],
        "python_source_slice_symbols_sha256": python_identity["symbols_sha256"],
        "python_source_slice_symbol_count": python_identity["symbol_count"],
        "python_source_slice_local_imports_sha256": python_identity[
            "local_imports_sha256"
        ],
        "python_source_slice_local_import_count": python_identity["local_import_count"],
    }


def _semantic_contract_closure_hash_tool_identity() -> dict[str, str] | None:
    """Resolve, pin, and self-test the exact SHA-256 executable used by Lean."""

    command = shutil.which("sha256sum")
    if not command:
        return None
    try:
        resolved = Path(command).resolve(strict=True)
        executable_sha256 = hashlib.sha256(resolved.read_bytes()).hexdigest()
        version = subprocess.run(
            [str(resolved), "--version"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=5,
            check=False,
        )
        known = subprocess.run(
            [str(resolved)],
            input=b"abc",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    expected = b"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad  -\n"
    if (
        version.returncode != 0
        or not version.stdout
        or version.stderr
        or known.returncode != 0
        or known.stdout != expected
        or known.stderr
    ):
        return None
    try:
        version_banner = version.stdout.decode("utf-8").splitlines()[0]
    except (UnicodeDecodeError, IndexError):
        return None
    return {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": str(resolved),
        "executable_sha256": executable_sha256,
        "version_stdout_sha256": hashlib.sha256(version.stdout).hexdigest(),
        "version_banner": version_banner,
        "known_vector": "sha256(abc)",
        "known_vector_sha256": expected[:64].decode("ascii"),
    }


def _with_semantic_contract_closure_context(
    manifests: dict[str, dict[str, Any]],
    context_sha256: str,
) -> dict[str, dict[str, Any]]:
    """Attach an ownership/package context without mutating cached Lean output."""

    return {
        specification: {
            **manifest,
            "closure_context_sha256": context_sha256,
        }
        for specification, manifest in manifests.items()
    }


def _semantic_contract_closure_foundation_context_sha256(
    root: Path,
    foundation_modules: list[str],
) -> str:
    """Pin trusted foundation terminals by package/toolchain context, once."""

    package_identities: list[dict[str, str]] = []
    for path in (root / "lake-manifest.json", root / "lean-toolchain"):
        try:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError:
            digest = ""
        package_identities.append({"path": path.name, "sha256": digest})
    return _closure_json_sha256(
        {
            "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "foundation_module_roots": foundation_modules,
            "package_identities": package_identities,
        }
    )


def _with_semantic_contract_closure_module_identities(
    root: Path,
    manifests: dict[str, dict[str, Any]],
    *,
    hash_tool_identity: Mapping[str, str],
    timeout_seconds: int,
    module_identity_snapshot: Mapping[str, list[dict[str, str]]] | None = None,
) -> dict[str, dict[str, Any]]:
    """Attach exact encountered module pins to each independently audited Spec."""

    extractor_identity = _semantic_contract_closure_extractor_identity()
    if extractor_identity is None:
        return {}
    identity_snapshot = (
        _closure_module_identity_snapshot(
            root,
            manifests,
            timeout_seconds=timeout_seconds,
        )
        if module_identity_snapshot is None
        else module_identity_snapshot
    )
    attached: dict[str, dict[str, Any]] = {}
    for specification, manifest in manifests.items():
        scope = manifest.get("scope")
        if not isinstance(scope, dict) or scope.get(
            "hash_tool_path"
        ) != hash_tool_identity.get("resolved_path"):
            continue
        identities = [
            dict(identity) for identity in identity_snapshot.get(specification, [])
        ]
        if any(
            not re.fullmatch(
                r"[0-9a-f]{64}", str(identity.get("artifact_sha256") or "")
            )
            for identity in identities
        ):
            continue
        foundation_modules = (
            [str(value) for value in scope.get("foundation_modules", [])]
            if isinstance(scope, dict)
            else []
        )
        foundation_context_sha256 = (
            _semantic_contract_closure_foundation_context_sha256(
                root, foundation_modules
            )
        )
        module_context_sha256 = _closure_json_sha256(
            {
                "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
                "foundation_context_sha256": foundation_context_sha256,
                "module_identities": identities,
                "extractor_identity": extractor_identity,
            }
        )
        attached[specification] = {
            **manifest,
            "closure_module_identities": identities,
            "closure_foundation_context_sha256": foundation_context_sha256,
            "closure_extractor_identity": extractor_identity,
            "closure_hash_tool_identity": dict(hash_tool_identity),
            "closure_module_context_sha256": module_context_sha256,
        }
    return attached


def _semantic_contract_closure_core_digests_are_current(
    manifest: Mapping[str, Any],
) -> bool:
    """Authenticate the name-free closure core before reattaching context."""

    surface = manifest.get("surface")
    nodes = manifest.get("nodes")
    failures = manifest.get("failures")
    expanded = manifest.get("expanded")
    passes = manifest.get("passes")
    surface_mode = manifest.get("surface_mode")
    if (
        manifest.get("schema") != SEMANTIC_CONTRACT_CLOSURE_SCHEMA
        or not isinstance(passes, bool)
        or not isinstance(expanded, int)
        or isinstance(expanded, bool)
        or expanded < 0
        or not isinstance(surface_mode, str)
        or (surface is not None and not isinstance(surface, dict))
        or not isinstance(nodes, list)
        or not isinstance(failures, list)
    ):
        return False
    structural_nodes: list[dict[str, Any]] = []
    for node in nodes:
        if not isinstance(node, Mapping):
            return False
        path = str(node.get("structural_path") or "")
        role = str(node.get("node_role") or "")
        origin = str(node.get("origin_class") or "")
        identity = node.get("canonical_identity")
        if not path or not role or not origin or not isinstance(identity, dict):
            return False
        structural_nodes.append(
            {
                "structural_path": path,
                "node_role": role,
                "origin_class": origin,
                **({"canonical_identity": identity} if origin != "paper" else {}),
            }
        )
    failure_tags: list[str] = []
    for failure in failures:
        if not isinstance(failure, Mapping):
            return False
        tag = str(failure.get("tag") or "")
        if not tag:
            return False
        failure_tags.append(tag)
    structural_payload = {
        "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
        "passes": passes,
        "expanded": expanded,
        "surface_mode": surface_mode,
        "surface": surface,
        "nodes": structural_nodes,
        "failure_tags": failure_tags,
    }
    expected_surface = _closure_json_sha256(surface) if surface is not None else ""
    return str(manifest.get("surface_sha256") or "") == expected_surface and str(
        manifest.get("sha256") or ""
    ) == _closure_json_sha256(structural_payload)


def reattach_semantic_contract_closure_module_identities(
    root: Path,
    manifests: Mapping[str, Mapping[str, Any]],
    *,
    timeout_seconds: int = 600,
) -> dict[str, dict[str, Any]]:
    """Revalidate saved closure receipts against their current narrow context.

    This accepts only authenticated closure cores already emitted under the
    current extractor identity. The hash tool, foundation context, every
    reached module artifact, and the resulting environment digest must also
    remain byte-for-byte equal. A caller must separately establish that these
    are the current requested Spec roots; this function never infers roots
    from declaration spellings.
    """

    extractor_identity = _semantic_contract_closure_extractor_identity()
    hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
    if extractor_identity is None or hash_tool_identity is None:
        return {}
    eligible = {
        specification: dict(manifest)
        for specification, manifest in manifests.items()
        if _semantic_contract_closure_core_digests_are_current(manifest)
        and manifest.get("closure_extractor_identity") == extractor_identity
        and manifest.get("closure_hash_tool_identity") == hash_tool_identity
    }
    if not eligible:
        return {}
    rebound = _with_semantic_contract_closure_module_identities(
        root,
        eligible,
        hash_tool_identity=hash_tool_identity,
        timeout_seconds=timeout_seconds,
    )
    return {
        specification: current
        for specification, current in rebound.items()
        if specification in eligible
        and eligible[specification].get("closure_module_identities")
        == current.get("closure_module_identities")
        and eligible[specification].get("closure_foundation_context_sha256")
        == current.get("closure_foundation_context_sha256")
        and eligible[specification].get("closure_module_context_sha256")
        == current.get("closure_module_context_sha256")
    }


def run_lean_semantic_contract_closure_manifests(
    root: Path,
    import_module: str,
    specification_names: list[str],
    paper_modules: tuple[str, ...],
    *,
    foundation_modules: tuple[str, ...] = DEFAULT_SEMANTIC_CONTRACT_FOUNDATION_MODULES,
    max_expansions: int = 512,
    timeout_seconds: int = 180,
    build_timeout_seconds: int = 600,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, dict[str, Any]]:
    """Return bounded Lean-owned closure manifests for transparent `Spec : Prop`.

    `paper_modules` is the exact filesystem-derived paper module set.  The
    Lean helper identifies the recursive declaration closure with Lean's own
    environment utility.  It receives only that paper set and the explicit
    foundation package registry: any other loaded dependency is visible as an
    unregistered external terminal and fails closed.  This avoids an
    expensive, unrelated inventory of every compiled workspace module.
    """

    specifications = tuple(
        sorted(set(name.strip() for name in specification_names if name.strip()))
    )
    modules = tuple(
        sorted(set(module.strip() for module in paper_modules if module.strip()))
    )
    foundations = tuple(
        sorted(set(module.strip() for module in foundation_modules if module.strip()))
    )
    use_compiled_helper = _compiled_audit_helper_available(root)
    hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
    if (
        not specifications
        or not modules
        or not foundations
        or hash_tool_identity is None
        or not (1 <= max_expansions <= 4096)
        or not _build_import_target(
            root,
            import_module,
            build_timeout_seconds,
            provider=build_input_provider,
        )
        or (
            use_compiled_helper
            and not _build_compiled_audit_helper(root, build_timeout_seconds)
        )
    ):
        return {}
    olean_fingerprint = _built_olean_fingerprint(root, import_module)
    helper_fingerprint = _file_content_fingerprint(HELPER_PATH)
    module_fingerprints = _paper_module_olean_fingerprints(root, modules)
    if olean_fingerprint is None or helper_fingerprint is None:
        return {}
    if import_module not in modules:
        return {}
    # Production uses the compiled Lean utility. It does not need a Python
    # inventory of the entire imported workspace: any local module outside
    # the explicit paper set becomes an unregistered external dependency and
    # blocks the receipt. Hermetic source-injection fixtures retain the older
    # explicit inventory path so they can exercise its historical parser.
    loaded_candidates: tuple[str, ...] = ()
    if use_compiled_helper:
        workspace_modules: tuple[str, ...] = ()
        workspace_scope_sha256 = _closure_json_sha256(
            {
                "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
                "ownership_policy": "unregistered_loaded_module_is_external_fail_closed_v1",
                "paper_modules": list(modules),
            }
        )
    else:
        loaded = _lean_loaded_module_candidates(
            root,
            import_module,
            timeout_seconds=build_timeout_seconds,
            provider=build_input_provider,
        )
        if loaded is None:
            return {}
        loaded_candidates = loaded
        provisional_lean_path = _lake_env_lean_path(root, build_timeout_seconds)
        if not provisional_lean_path:
            return {}
        legacy_workspace_scope = _loaded_workspace_module_scope(
            root, loaded_candidates, provisional_lean_path
        )
        if legacy_workspace_scope is None:
            return {}
        workspace_modules, workspace_scope_sha256 = legacy_workspace_scope
        if import_module not in workspace_modules:
            return {}
    # Obtain Lean's package search path once before launching the bounded
    # closure subprocess. Reusing it for both before/after artifact pins
    # avoids a second Lake environment process immediately after a large Lean
    # import, which was pure overhead and could briefly exceed host memory.
    lean_path = _lake_env_lean_path(root, build_timeout_seconds)
    if not lean_path:
        return {}
    context_sha256 = _semantic_contract_closure_context_sha256(
        root,
        import_module,
        modules,
        workspace_scope_sha256,
        foundations,
    )
    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return {}
    cache_key = (
        str(root.resolve()),
        import_module,
        olean_fingerprint,
        helper_fingerprint,
        module_fingerprints,
        workspace_scope_sha256,
        specifications,
        modules,
        foundations,
        context_sha256,
        _closure_json_sha256(hash_tool_identity),
        max_expansions,
    )
    cached = _SEMANTIC_CONTRACT_CLOSURE_CACHE.get(cache_key)
    if cached is not None:
        if _semantic_contract_closure_cached_module_identities_are_current(
            root,
            cached,
            timeout_seconds=build_timeout_seconds,
        ):
            return cached
        del _SEMANTIC_CONTRACT_CLOSURE_CACHE[cache_key]

    # A compiled compact closure can only reach paper modules (which are exact
    # byte-pinned artifacts) and registered foundation package roots (which
    # are pinned by the Lake/toolchain foundation context). The injected test
    # fallback retains its legacy prepass for fixture compatibility.
    candidate_artifacts = _closure_module_artifact_snapshot(
        root,
        modules if use_compiled_helper else loaded_candidates,
        timeout_seconds=build_timeout_seconds,
        lean_path=lean_path,
    )
    names = list(specifications)
    # A statement closure is compact, but a long paper still accumulates Meta
    # state while Lean elaborates each request. Keep the bounded four-row
    # batches so any pathological row fails closed without turning an entire
    # paper's receipt into one large resident process.
    batches = _semantic_contract_closure_batches(names)
    uses_chunking = len(batches) > 1
    # Each requested timeout is already an external per-process wall bound.
    # Do not silently replace it with the short generic manifest cap: large
    # semantic closures need the caller's full allowance in both the initial
    # bounded batch and an individual retry.
    batch_timeout = timeout_seconds
    manifests: dict[str, dict[str, Any]] = {}
    for batch in batches:
        extracted = _run_semantic_contract_closure_script(
            root,
            f"import Lean\nimport {import_module}",
            batch,
            modules,
            workspace_modules,
            foundations,
            hash_tool_path=hash_tool_identity["resolved_path"],
            inline_paper_scope=not use_compiled_helper,
            use_compiled_helper=use_compiled_helper,
            max_expansions=max_expansions,
            timeout_seconds=(batch_timeout if uses_chunking else timeout_seconds),
        )
        manifests.update(
            _requested_semantic_contract_closure_manifests(extracted, batch)
        )
        if uses_chunking:
            for specification in batch:
                if specification in manifests:
                    continue
                retried = _run_semantic_contract_closure_script(
                    root,
                    f"import Lean\nimport {import_module}",
                    [specification],
                    modules,
                    workspace_modules,
                    foundations,
                    hash_tool_path=hash_tool_identity["resolved_path"],
                    inline_paper_scope=not use_compiled_helper,
                    use_compiled_helper=use_compiled_helper,
                    max_expansions=max_expansions,
                    timeout_seconds=batch_timeout,
                )
                manifests.update(
                    _requested_semantic_contract_closure_manifests(
                        retried, [specification]
                    )
                )
    requested = _requested_semantic_contract_closure_manifests(manifests, names)
    if _paper_module_olean_fingerprints(root, modules) != module_fingerprints:
        return {}
    if (
        _semantic_contract_closure_context_sha256(
            root,
            import_module,
            modules,
            workspace_scope_sha256,
            foundations,
        )
        != context_sha256
    ):
        return {}
    contextualized = _with_semantic_contract_closure_context(
        requested,
        context_sha256,
    )
    reached_artifacts = _closure_module_identity_snapshot(
        root,
        contextualized,
        timeout_seconds=build_timeout_seconds,
        lean_path=lean_path,
    )
    if not _semantic_contract_closure_reached_artifacts_match_candidates(
        candidate_artifacts,
        reached_artifacts,
    ):
        return {}
    attached = _with_semantic_contract_closure_module_identities(
        root,
        contextualized,
        hash_tool_identity=hash_tool_identity,
        timeout_seconds=build_timeout_seconds,
        module_identity_snapshot=reached_artifacts,
    )
    if attached:
        _SEMANTIC_CONTRACT_CLOSURE_CACHE[cache_key] = attached
    return attached


def run_lean_semantic_contract_closure_manifests_for_source(
    root: Path,
    source: str,
    specification_names: list[str],
    *,
    foundation_modules: tuple[str, ...] = DEFAULT_SEMANTIC_CONTRACT_FOUNDATION_MODULES,
    max_expansions: int = 512,
    timeout_seconds: int = 120,
) -> dict[str, dict[str, Any]]:
    """Test helper for explicit inline-paper `Spec` closure fixtures.

    Inline declarations have no compiled module index, so this deliberately
    marks the source string as one explicit paper scope.  Production calls use
    `run_lean_semantic_contract_closure_manifests`, where absent origins fail
    closed instead.
    """

    specifications = sorted(
        set(name.strip() for name in specification_names if name.strip())
    )
    foundations = tuple(
        sorted(set(module.strip() for module in foundation_modules if module.strip()))
    )
    hash_tool_identity = _semantic_contract_closure_hash_tool_identity()
    extractor_identity = _semantic_contract_closure_extractor_identity()
    if hash_tool_identity is None or extractor_identity is None:
        return {}
    manifests = _run_semantic_contract_closure_script(
        root,
        f"import Lean\n\n{source}",
        specifications,
        (),
        (),
        foundations,
        hash_tool_path=hash_tool_identity["resolved_path"],
        inline_paper_scope=True,
        max_expansions=max_expansions,
        timeout_seconds=timeout_seconds,
    )
    context_sha256 = _closure_json_sha256(
        {
            "schema": SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "inline_source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
            "foundation_module_roots": list(foundations),
            "extractor_identity": extractor_identity,
        }
    )
    return _with_semantic_contract_closure_module_identities(
        root,
        _with_semantic_contract_closure_context(manifests, context_sha256),
        hash_tool_identity=hash_tool_identity,
        timeout_seconds=timeout_seconds,
    )


def run_lean_source_premise_false_eliminators(
    root: Path,
    import_module: str,
    reviewed_names: list[str],
    *,
    audit_modules: tuple[str, ...] | None = None,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, list[dict[str, Any]]]:
    """Find semantic routes from reviewed source inputs to ``False``.

    The candidate search is scoped to loaded repository modules.  It does not
    use candidate declaration names as evidence: Lean compares the reviewed
    input and candidate binder by definitional equality, then rejects a route
    with an additional proposition-valued premise.  Non-proposition setup is
    retained as explicit diagnostic metadata.
    """

    names = sorted(set(name.strip() for name in reviewed_names if name.strip()))
    if not names:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="source_premise_false_eliminators",
            requested_count=0,
            reused_count=0,
            fresh_count=0,
        )
        return {}
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if environment is None:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="source_premise_false_eliminators",
            requested_count=len(names),
            reused_count=0,
            fresh_count=len(names),
            missing_identities=names,
        )
        return {}
    # With no explicit scope, the Lean helper searches the reviewed input's
    # own defining module.  That is both the ordinary location of a source
    # record's eliminator/projection and materially safer than treating every
    # imported declaration without recorded module metadata as a candidate.
    modules = tuple(sorted(set(audit_modules or ())))
    cache_keys = {name: (environment, modules, name) for name in names}
    reused_names = [
        name for name in names if cache_keys[name] in _SOURCE_PREMISE_FALSE_SCAN_CACHE
    ]
    fresh_names = [name for name in names if name not in set(reused_names)]
    unexpected: set[str] = set()
    pending_receipts: dict[str, list[dict[str, Any]]] = {}
    if fresh_names:
        found = _run_source_premise_false_scan_script(
            root,
            f"import Lean\nimport {import_module}",
            fresh_names,
            modules,
            timeout_seconds,
        )
        unexpected = set(found) - set(fresh_names)
        if not unexpected:
            for name in fresh_names:
                candidates = found.get(name)
                if not isinstance(candidates, list) or any(
                    not isinstance(candidate, dict) for candidate in candidates
                ):
                    continue
                # An explicit empty list is a successful negative receipt.
                pending_receipts[name] = deepcopy(candidates)
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if current_environment != environment:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="source_premise_false_eliminators",
            requested_count=len(names),
            reused_count=len(reused_names),
            fresh_count=len(fresh_names),
            batch_count=int(bool(fresh_names)),
            missing_identities=names,
            unexpected_identities=unexpected,
            environment_changed=True,
        )
        return {}
    for name, candidates in pending_receipts.items():
        _SOURCE_PREMISE_FALSE_SCAN_CACHE[cache_keys[name]] = deepcopy(candidates)
    result = {
        name: deepcopy(_SOURCE_PREMISE_FALSE_SCAN_CACHE[cache_keys[name]])
        for name in names
        if cache_keys[name] in _SOURCE_PREMISE_FALSE_SCAN_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="source_premise_false_eliminators",
        requested_count=len(names),
        reused_count=len(reused_names),
        fresh_count=len(fresh_names),
        batch_count=int(bool(fresh_names)),
        missing_identities=set(names) - set(result),
        unexpected_identities=unexpected,
    )
    return result


def run_lean_source_premise_false_eliminators_for_source(
    root: Path,
    source: str,
    reviewed_names: list[str],
    timeout_seconds: int = 120,
) -> dict[str, list[dict[str, Any]]]:
    """Test helper for inline Lean source without a repository module scope."""

    names = sorted(set(name.strip() for name in reviewed_names if name.strip()))
    found = _run_source_premise_false_scan_script(
        root,
        f"import Lean\n\n{source}",
        names,
        (),
        timeout_seconds,
    )
    return found if set(found) == set(names) else {}


def run_lean_constructor_result_type_matches(
    root: Path,
    import_module: str,
    routes: list[tuple[str, str, str]],
    *,
    review_source_path: Path,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[tuple[str, str, str], bool]:
    """Check candidate result types against rigid elaborated reviewed binders.

    A missing, malformed, or failed Lean answer is deliberately not returned as
    a positive match.  Callers must therefore remove any static route without
    an exact Meta verdict before treating it as a constructor.  The reviewed
    module is always re-elaborated from ``review_source_path`` into an
    isolated overlay; its SHA must remain stable through the check.
    """

    canonical_routes = sorted(
        {
            (reviewed.strip(), binder.strip(), candidate.strip())
            for reviewed, binder, candidate in routes
            if reviewed.strip() and binder.strip() and candidate.strip()
        }
    )
    if not canonical_routes:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_result_type_matches",
            requested_count=0,
            reused_count=0,
            fresh_count=0,
        )
        return {}
    source_path = review_source_path.resolve()
    source_sha256 = _source_sha256(source_path)
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if (
        source_sha256 is None
        or _review_source_module_name(root, source_path) != import_module
        or environment is None
    ):
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_result_type_matches",
            requested_count=len(canonical_routes),
            reused_count=0,
            fresh_count=len(canonical_routes),
            missing_identities=(json.dumps(route) for route in canonical_routes),
        )
        return {}
    cache_keys = {
        route: (environment, str(source_path), source_sha256, route)
        for route in canonical_routes
    }
    reused_routes = [
        route
        for route in canonical_routes
        if cache_keys[route] in _CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE
    ]
    reused_route_set = set(reused_routes)
    fresh_routes = [
        route for route in canonical_routes if route not in reused_route_set
    ]
    unexpected: set[tuple[str, str, str]] = set()
    pending_verdicts: dict[tuple[str, str, str], bool] = {}
    if fresh_routes:
        with _fresh_constructor_result_type_overlay(
            root,
            import_module,
            source_path,
            build_timeout_seconds=build_timeout_seconds,
            build_input_provider=build_input_provider,
        ) as overlay:
            if overlay is None:
                extracted: dict[tuple[str, str, str], bool] = {}
            else:
                overlay_lean_path, overlay_source_sha256 = overlay
                if overlay_source_sha256 != source_sha256:
                    extracted = {}
                else:
                    extracted = _run_constructor_result_type_match_script(
                        root,
                        f"import Lean\nimport {import_module}",
                        fresh_routes,
                        timeout_seconds,
                        lean_path=overlay_lean_path,
                    )
        unexpected = set(extracted) - set(fresh_routes)
        if not unexpected:
            for route in fresh_routes:
                verdict = extracted.get(route)
                if type(verdict) is bool:
                    # `False` is a checked incompatibility, not a cache miss.
                    pending_verdicts[route] = verdict
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if (
        current_environment != environment
        or _source_sha256(source_path) != source_sha256
    ):
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_result_type_matches",
            requested_count=len(canonical_routes),
            reused_count=len(reused_routes),
            fresh_count=len(fresh_routes),
            batch_count=int(bool(fresh_routes)),
            missing_identities=(json.dumps(route) for route in canonical_routes),
            unexpected_identities=(json.dumps(route) for route in unexpected),
            environment_changed=True,
        )
        return {}
    for route, verdict in pending_verdicts.items():
        _CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE[cache_keys[route]] = verdict
    result = {
        route: bool(_CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE[cache_keys[route]])
        for route in canonical_routes
        if cache_keys[route] in _CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="constructor_result_type_matches",
        requested_count=len(canonical_routes),
        reused_count=len(reused_routes),
        fresh_count=len(fresh_routes),
        batch_count=int(bool(fresh_routes)),
        missing_identities=(
            json.dumps(route) for route in set(canonical_routes) - set(result)
        ),
        unexpected_identities=(json.dumps(route) for route in unexpected),
    )
    return result


def run_lean_constructor_result_type_matches_for_source(
    root: Path,
    source: str,
    routes: list[tuple[str, str, str]],
    *,
    timeout_seconds: int = 120,
) -> dict[tuple[str, str, str], bool]:
    """Inline-source test helper for elaborated constructor compatibility."""

    canonical_routes = sorted(
        {
            (reviewed.strip(), binder.strip(), candidate.strip())
            for reviewed, binder, candidate in routes
            if reviewed.strip() and binder.strip() and candidate.strip()
        }
    )
    found = _run_constructor_result_type_match_script(
        root,
        f"import Lean\n\n{source}",
        canonical_routes,
        timeout_seconds,
    )
    return found if set(found) == set(canonical_routes) else {}


def run_lean_recursive_field_proposition_sorts(
    root: Path,
    import_module: str,
    field_locators: list[dict[str, object]],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, dict[str, object]]:
    """Return Lean-derived sort and payload safety for exact field slots.

    The response joins through generated constructor/projection locators, not
    source field labels.  Unknown or opaque payload routes remain explicit
    fail-closed receipts for callers that need data credit.
    """

    locators: list[dict[str, object]] = []
    identities: set[str] = set()
    for raw_locator in field_locators:
        locator = canonical_recursive_field_safety_locator(raw_locator)
        if locator is None:
            return {}
        identity = str(locator["field_identity_sha256"])
        if identity in identities:
            return {}
        identities.add(identity)
        locators.append(locator)
    locators.sort(key=lambda locator: str(locator["field_identity_sha256"]))
    if not locators:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="recursive_field_proposition_sorts",
            requested_count=0,
            reused_count=0,
            fresh_count=0,
        )
        return {}
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if environment is None:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="recursive_field_proposition_sorts",
            requested_count=len(locators),
            reused_count=0,
            fresh_count=len(locators),
            missing_identities=identities,
        )
        return {}
    cache_keys = {
        str(locator["field_identity_sha256"]): (
            environment,
            json.dumps(locator, sort_keys=True, separators=(",", ":")),
        )
        for locator in locators
    }
    reused_identities = {
        identity
        for identity, key in cache_keys.items()
        if key in _RECURSIVE_FIELD_PROPOSITION_SORT_CACHE
    }
    fresh_locators = [
        locator
        for locator in locators
        if str(locator["field_identity_sha256"]) not in reused_identities
    ]
    batch_count = 0
    isolation_retry_count = 0
    unexpected: set[str] = set()
    pending_receipts: dict[str, dict[str, object]] = {}
    if fresh_locators:
        found: dict[str, dict[str, object]] = {}
        batches = _recursive_field_safety_batches(fresh_locators)
        uses_chunking = len(batches) > 1
        batch_timeout = (
            min(timeout_seconds, MAX_CHUNKED_RECURSIVE_FIELD_SAFETY_TIMEOUT_SECONDS)
            if uses_chunking
            else timeout_seconds
        )
        for batch in batches:
            # A malformed response for one exact field can make Lean omit an
            # entire multi-slot payload. Split only the missing subset, so
            # independently elaborable slots keep their receipts without
            # turning every field in a failed batch into a singleton process.
            # This partition depends solely on Lean-owned locator identities.
            pending_batches = [batch]
            while pending_batches:
                current_batch = pending_batches.pop()
                batch_count += 1
                extracted = _run_recursive_field_proposition_sort_script(
                    root,
                    f"import Lean\nimport {import_module}",
                    current_batch,
                    batch_timeout,
                )
                requested = {
                    str(locator["field_identity_sha256"]) for locator in current_batch
                }
                unexpected.update(set(extracted) - requested)
                found.update(
                    {
                        identity: receipt
                        for identity, receipt in extracted.items()
                        if identity in requested
                    }
                )
                missing = [
                    locator
                    for locator in current_batch
                    if str(locator["field_identity_sha256"]) not in found
                ]
                if len(missing) > 1:
                    midpoint = len(missing) // 2
                    pending_batches.append(missing[midpoint:])
                    pending_batches.append(missing[:midpoint])
                    isolation_retry_count += 2
        if not unexpected:
            for identity, receipt in found.items():
                key = cache_keys.get(identity)
                if key is not None and isinstance(receipt, dict):
                    pending_receipts[identity] = deepcopy(receipt)
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if current_environment != environment:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="recursive_field_proposition_sorts",
            requested_count=len(locators),
            reused_count=len(reused_identities),
            fresh_count=len(fresh_locators),
            batch_count=batch_count,
            isolation_retry_count=isolation_retry_count,
            missing_identities=identities,
            unexpected_identities=unexpected,
            environment_changed=True,
        )
        return {}
    for identity, receipt in pending_receipts.items():
        _RECURSIVE_FIELD_PROPOSITION_SORT_CACHE[cache_keys[identity]] = deepcopy(
            receipt
        )
    result = {
        identity: deepcopy(_RECURSIVE_FIELD_PROPOSITION_SORT_CACHE[key])
        for identity, key in sorted(cache_keys.items())
        if key in _RECURSIVE_FIELD_PROPOSITION_SORT_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="recursive_field_proposition_sorts",
        requested_count=len(locators),
        reused_count=len(reused_identities),
        fresh_count=len(fresh_locators),
        batch_count=batch_count,
        isolation_retry_count=isolation_retry_count,
        missing_identities=identities - set(result),
        unexpected_identities=unexpected,
    )
    return result


def run_lean_recursive_field_proposition_sorts_for_source(
    root: Path,
    source: str,
    field_locators: list[dict[str, object]],
    *,
    timeout_seconds: int = 120,
) -> dict[str, dict[str, object]]:
    """Inline-source helper for actual constructor/projection safety receipts."""

    locators: list[dict[str, object]] = []
    identities: set[str] = set()
    for raw_locator in field_locators:
        locator = canonical_recursive_field_safety_locator(raw_locator)
        if locator is None:
            return {}
        identity = str(locator["field_identity_sha256"])
        if identity in identities:
            return {}
        identities.add(identity)
        locators.append(locator)
    locators.sort(key=lambda locator: str(locator["field_identity_sha256"]))
    found = _run_recursive_field_proposition_sort_script(
        root,
        f"import Mathlib\n\n{source}",
        locators,
        timeout_seconds,
    )
    return found if set(found) == identities else {}


def run_lean_constructor_field_slot_counts(
    root: Path,
    import_module: str,
    constructor_names: list[str],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, int]:
    """Return Lean-owned stored-field counts for exact constructors."""

    names = sorted({name.strip() for name in constructor_names if name.strip()})
    if not names or len(names) != len(constructor_names):
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_field_slot_counts",
            requested_count=len(constructor_names),
            reused_count=0,
            fresh_count=len(constructor_names),
            missing_identities=constructor_names,
        )
        return {}
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if environment is None:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_field_slot_counts",
            requested_count=len(names),
            reused_count=0,
            fresh_count=len(names),
            missing_identities=names,
        )
        return {}
    cache_keys = {name: (environment, name) for name in names}
    reused_names = [
        name
        for name in names
        if cache_keys[name] in _CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE
    ]
    reused_name_set = set(reused_names)
    fresh_names = [name for name in names if name not in reused_name_set]
    unexpected: set[str] = set()
    pending_counts: dict[str, int] = {}
    if fresh_names:
        found = _run_constructor_field_slot_count_script(
            root,
            f"import Lean\nimport {import_module}",
            fresh_names,
            timeout_seconds,
        )
        unexpected = set(found) - set(fresh_names)
        if not unexpected:
            for name in fresh_names:
                count = found.get(name)
                if type(count) is int and count >= 0:
                    pending_counts[name] = count
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if current_environment != environment:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="constructor_field_slot_counts",
            requested_count=len(names),
            reused_count=len(reused_names),
            fresh_count=len(fresh_names),
            batch_count=int(bool(fresh_names)),
            missing_identities=names,
            unexpected_identities=unexpected,
            environment_changed=True,
        )
        return {}
    for name, count in pending_counts.items():
        _CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE[cache_keys[name]] = count
    result = {
        name: _CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE[cache_keys[name]]
        for name in names
        if cache_keys[name] in _CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="constructor_field_slot_counts",
        requested_count=len(names),
        reused_count=len(reused_names),
        fresh_count=len(fresh_names),
        batch_count=int(bool(fresh_names)),
        missing_identities=set(names) - set(result),
        unexpected_identities=unexpected,
    )
    return result


def run_lean_constructor_field_slot_counts_for_source(
    root: Path,
    source: str,
    constructor_names: list[str],
    *,
    timeout_seconds: int = 120,
) -> dict[str, int]:
    """Inline-source test helper for Lean constructor stored-slot counts."""

    names = sorted({name.strip() for name in constructor_names if name.strip()})
    if not names or len(names) != len(constructor_names):
        return {}
    found = _run_constructor_field_slot_count_script(
        root,
        f"import Mathlib\n\n{source}",
        names,
        timeout_seconds,
    )
    return found if set(found) == set(names) else {}


def run_lean_inductive_constructor_field_slot_counts(
    root: Path,
    import_module: str,
    inductive_names: list[str],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, dict[str, int]]:
    """Return Lean-owned constructor identities and stored-slot counts."""

    names = sorted({name.strip() for name in inductive_names if name.strip()})
    if not names or len(names) != len(inductive_names):
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="inductive_constructor_field_slot_counts",
            requested_count=len(inductive_names),
            reused_count=0,
            fresh_count=len(inductive_names),
            missing_identities=inductive_names,
        )
        return {}
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if environment is None:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="inductive_constructor_field_slot_counts",
            requested_count=len(names),
            reused_count=0,
            fresh_count=len(names),
            missing_identities=names,
        )
        return {}
    cache_keys = {name: (environment, name) for name in names}
    reused_names = [
        name
        for name in names
        if cache_keys[name] in _INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE
    ]
    reused_name_set = set(reused_names)
    fresh_names = [name for name in names if name not in reused_name_set]
    unexpected: set[str] = set()
    pending_counts: dict[str, dict[str, int]] = {}
    if fresh_names:
        found = _run_inductive_constructor_field_slot_count_script(
            root,
            f"import Lean\nimport {import_module}",
            fresh_names,
            timeout_seconds,
        )
        unexpected = set(found) - set(fresh_names)
        if not unexpected:
            for name in fresh_names:
                counts = found.get(name)
                if isinstance(counts, dict) and all(
                    isinstance(constructor, str)
                    and constructor.strip()
                    and type(count) is int
                    and count >= 0
                    for constructor, count in counts.items()
                ):
                    pending_counts[name] = deepcopy(counts)
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if current_environment != environment:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="inductive_constructor_field_slot_counts",
            requested_count=len(names),
            reused_count=len(reused_names),
            fresh_count=len(fresh_names),
            batch_count=int(bool(fresh_names)),
            missing_identities=names,
            unexpected_identities=unexpected,
            environment_changed=True,
        )
        return {}
    for name, counts in pending_counts.items():
        _INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE[cache_keys[name]] = deepcopy(
            counts
        )
    result = {
        name: deepcopy(_INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE[cache_keys[name]])
        for name in names
        if cache_keys[name] in _INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="inductive_constructor_field_slot_counts",
        requested_count=len(names),
        reused_count=len(reused_names),
        fresh_count=len(fresh_names),
        batch_count=int(bool(fresh_names)),
        missing_identities=set(names) - set(result),
        unexpected_identities=unexpected,
    )
    return result


def run_lean_inductive_constructor_field_slot_counts_for_source(
    root: Path,
    source: str,
    inductive_names: list[str],
    *,
    timeout_seconds: int = 120,
) -> dict[str, dict[str, int]]:
    """Inline-source test helper for Lean inductive constructor enumeration."""

    names = sorted({name.strip() for name in inductive_names if name.strip()})
    if not names or len(names) != len(inductive_names):
        return {}
    found = _run_inductive_constructor_field_slot_count_script(
        root,
        f"import Mathlib\n\n{source}",
        names,
        timeout_seconds,
    )
    return found if set(found) == set(names) else {}


def run_lean_type_witness_payload_safeties(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    *,
    timeout_seconds: int = 120,
    build_timeout_seconds: int = 600,
    diagnostics_out: dict[str, Any] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, list[dict[str, object]]]:
    """Return exact Lean-owned safety receipts for result Type witnesses."""

    names = sorted({name.strip() for name in declaration_names if name.strip()})
    if not names or len(names) != len(declaration_names):
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="type_witness_payload_safeties",
            requested_count=len(declaration_names),
            reused_count=0,
            fresh_count=len(declaration_names),
            missing_identities=declaration_names,
        )
        return {}
    environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        provider=build_input_provider,
    )
    if environment is None:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="type_witness_payload_safeties",
            requested_count=len(names),
            reused_count=0,
            fresh_count=len(names),
            missing_identities=names,
        )
        return {}
    cache_keys = {name: (environment, name) for name in names}
    reused_names = [
        name for name in names if cache_keys[name] in _TYPE_WITNESS_PAYLOAD_SAFETY_CACHE
    ]
    reused_name_set = set(reused_names)
    fresh_names = [name for name in names if name not in reused_name_set]
    execution_counts: dict[str, int] = {}
    unexpected: set[str] = set()
    pending_receipts: dict[str, list[dict[str, object]]] = {}
    if fresh_names:
        found = _collect_type_witness_payload_safeties(
            root,
            f"import Lean\nimport {import_module}",
            fresh_names,
            timeout_seconds,
            execution_counts=execution_counts,
        )
        unexpected = set(found) - set(fresh_names)
        if not unexpected:
            for name in fresh_names:
                receipts = found.get(name)
                if not isinstance(receipts, list) or any(
                    not isinstance(receipt, dict) for receipt in receipts
                ):
                    continue
                # A present empty list is a checked witness-free result.
                pending_receipts[name] = deepcopy(receipts)
    current_environment = _structural_scan_environment_identity(
        root,
        import_module,
        build_timeout_seconds=build_timeout_seconds,
        ensure_built=False,
        provider=build_input_provider,
    )
    if current_environment != environment:
        _publish_structural_scan_diagnostics(
            diagnostics_out,
            stage="type_witness_payload_safeties",
            requested_count=len(names),
            reused_count=len(reused_names),
            fresh_count=len(fresh_names),
            batch_count=execution_counts.get("batch_count", 0),
            isolation_retry_count=execution_counts.get("isolation_retry_count", 0),
            missing_identities=names,
            unexpected_identities=unexpected,
            environment_changed=True,
        )
        return {}
    for name, receipts in pending_receipts.items():
        _TYPE_WITNESS_PAYLOAD_SAFETY_CACHE[cache_keys[name]] = deepcopy(receipts)
    result = {
        name: deepcopy(_TYPE_WITNESS_PAYLOAD_SAFETY_CACHE[cache_keys[name]])
        for name in names
        if cache_keys[name] in _TYPE_WITNESS_PAYLOAD_SAFETY_CACHE
    }
    _publish_structural_scan_diagnostics(
        diagnostics_out,
        stage="type_witness_payload_safeties",
        requested_count=len(names),
        reused_count=len(reused_names),
        fresh_count=len(fresh_names),
        batch_count=execution_counts.get("batch_count", 0),
        isolation_retry_count=execution_counts.get("isolation_retry_count", 0),
        missing_identities=set(names) - set(result),
        unexpected_identities=unexpected,
    )
    return result


def run_lean_type_witness_payload_safeties_for_source(
    root: Path,
    source: str,
    declaration_names: list[str],
    *,
    timeout_seconds: int = 120,
) -> dict[str, list[dict[str, object]]]:
    """Inline-source variant for focused Type-witness receipt tests."""

    names = sorted({name.strip() for name in declaration_names if name.strip()})
    if not names or len(names) != len(declaration_names):
        return {}
    return _collect_type_witness_payload_safeties(
        root,
        f"import Mathlib\n\n{source}",
        names,
        timeout_seconds,
    )
