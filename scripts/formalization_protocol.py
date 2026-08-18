#!/usr/bin/env python3
"""Load and validate the authoritative formalization audit protocol."""

from __future__ import annotations

import hashlib
import json
import os
from functools import lru_cache
from pathlib import Path
from pathlib import PurePosixPath
from typing import Any, Mapping


ROOT = Path(
    os.environ.get("ECONCSLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
PROTOCOL_PATH = ROOT / "config" / "formalization_audit_protocol.json"
PROTOCOL_SCHEMA = 1
PROTOCOL_DIGEST_SCHEMA = 1
COVERAGE_PROTOCOL_DIGEST_SCHEMA = 1
REVIEW_PROTOCOL_DIGEST_SCHEMA = 1

EXPECTED_AUDIT_VERSIONS = {
    "statement_semantic_review": {
        "current": "v11",
        "prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2",
    },
    "source_record": {
        "current": "v10",
        "prompt_version": "source-record-v10-semantic-conclusion-boundary-contract",
    },
    "theorem_realization": {
        "current": "v11",
    },
}
EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT = (
    "93817f0b1a75be86bc495223c4952788f4a81df2"
)
EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF = "refs/remotes/origin/main"
TRUSTED_GIT_TREE_AUTHORITY = "trusted_git_tree"
IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY = (
    "immutable_material_identity_manifest"
)
IMMUTABLE_V10_TRUST_LEDGER_SCHEMA = 3
IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID = (
    "legacy-v10-semantic-material-trust-ledger"
)
IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA = 3
IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA = 2
MATERIAL_PROTOCOL_DIGEST_SCHEMA = 1
FORMALIZATION_COVERAGE_PROTOCOL_FIELD = (
    "formalization_coverage_protocol_sha256"
)
FORMALIZATION_REVIEW_PROTOCOL_FIELD = "formalization_review_protocol_sha256"
LEGACY_FORMALIZATION_PROTOCOL_FIELD = "formalization_protocol_sha256"
EXPECTED_REQUIRED_REUSE_IDENTITIES = frozenset(
    {
        "source_semantics",
        "byte_validated_source_quote",
        "name_independent_elaborated_statement_structure_and_semantic_proposition",
        "transitive_elaborated_semantic_dependency_graph",
        "opaque_imported_terminal_artifacts_and_toolchain_context",
        "configured_route_preflight",
        "validator_and_protocol_fingerprints",
        "correction_and_model_convention_disposition",
    }
)
EXPECTED_REUSE_FAILURES = frozenset(
    {
        "missing_identity",
        "changed_identity",
        "ambiguous_rebinding",
        "unresolved_route",
    }
)


class FormalizationProtocolError(ValueError):
    """The current policy artifact is absent, malformed, or contradictory."""


def _nonempty_string(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise FormalizationProtocolError(f"{field} must be a nonempty string")
    return value.strip()


def _string_set(value: object, field: str) -> frozenset[str]:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        raise FormalizationProtocolError(
            f"{field} must be a duplicate-free list of nonempty strings"
        )
    normalized = [item.strip() for item in value]
    if len(normalized) != len(set(normalized)):
        raise FormalizationProtocolError(
            f"{field} must be a duplicate-free list of nonempty strings"
        )
    return frozenset(normalized)


def _sha256(value: object, field: str) -> str:
    text = _nonempty_string(value, field).lower()
    if len(text) != 64 or any(character not in "0123456789abcdef" for character in text):
        raise FormalizationProtocolError(f"{field} must be a lowercase SHA-256")
    return text


def _repository_relative_json_path(value: object, field: str) -> str:
    text = _nonempty_string(value, field)
    path = PurePosixPath(text)
    if (
        path.is_absolute()
        or "\\" in text
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.suffix != ".json"
    ):
        raise FormalizationProtocolError(
            f"{field} must be a normalized repository-relative JSON path"
        )
    return text


def _validate_legacy_v10_transition_baseline(
    baseline: Mapping[str, Any],
) -> None:
    authority = baseline.get("authority")
    if authority == TRUSTED_GIT_TREE_AUTHORITY:
        if baseline.get("git_commit") != EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT:
            raise FormalizationProtocolError(
                "theorem-realization legacy baseline must remain pinned to the "
                "reviewed pre-v11 transition commit"
            )
        if baseline.get("trusted_ref") != EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF:
            raise FormalizationProtocolError(
                "theorem-realization legacy baseline must remain tied to the "
                "trusted private origin/main ref"
            )
        if baseline.get("material_identity_schema") != 1:
            raise FormalizationProtocolError(
                "trusted-git theorem-realization material identity schema must be 1"
            )
        for forbidden in (
            "manifest_path",
            "manifest_sha256",
            "manifest_schema",
            "engine_id",
            "engine_schema",
        ):
            if forbidden in baseline:
                raise FormalizationProtocolError(
                    f"trusted-git theorem-realization baseline must not set {forbidden}"
                )
        return

    if authority == IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY:
        _repository_relative_json_path(
            baseline.get("manifest_path"),
            "audit_versions.theorem_realization.legacy_v10_transition_baseline."
            "manifest_path",
        )
        _sha256(
            baseline.get("manifest_sha256"),
            "audit_versions.theorem_realization.legacy_v10_transition_baseline."
            "manifest_sha256",
        )
        if baseline.get("manifest_schema") != IMMUTABLE_V10_TRUST_LEDGER_SCHEMA:
            raise FormalizationProtocolError(
                "immutable theorem-realization manifest schema is unsupported"
            )
        if (
            baseline.get("material_identity_schema")
            != IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA
        ):
            raise FormalizationProtocolError(
                "immutable theorem-realization material identity schema is unsupported"
            )
        if baseline.get("engine_id") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID:
            raise FormalizationProtocolError(
                "immutable theorem-realization trust-ledger engine id is unsupported"
            )
        if baseline.get("engine_schema") != IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA:
            raise FormalizationProtocolError(
                "immutable theorem-realization trust-ledger engine schema is unsupported"
            )
        for forbidden in ("git_commit", "trusted_ref"):
            if forbidden in baseline:
                raise FormalizationProtocolError(
                    "immutable theorem-realization manifest authority must not depend "
                    f"on {forbidden}"
                )
        return

    raise FormalizationProtocolError(
        "theorem-realization legacy baseline authority must be trusted_git_tree "
        "or immutable_material_identity_manifest"
    )


def validate_formalization_protocol(payload: object) -> dict[str, Any]:
    """Return a validated copy of the current protocol or fail closed."""

    if not isinstance(payload, dict):
        raise FormalizationProtocolError("protocol must be a JSON object")
    if payload.get("schema") != PROTOCOL_SCHEMA:
        raise FormalizationProtocolError(
            f"protocol schema must be {PROTOCOL_SCHEMA}"
        )
    _nonempty_string(payload.get("protocol_id"), "protocol_id")
    for section in (
        "authority",
        "audit_versions",
        "coverage",
        "reuse",
        "builds",
        "classification",
        "pacing",
    ):
        if not isinstance(payload.get(section), Mapping):
            raise FormalizationProtocolError(f"{section} must be an object")

    versions = payload["audit_versions"]
    if set(versions) != set(EXPECTED_AUDIT_VERSIONS):
        raise FormalizationProtocolError(
            "audit_versions must contain exactly the authoritative audit lanes"
        )
    for lane, expected in EXPECTED_AUDIT_VERSIONS.items():
        record = versions.get(lane)
        if not isinstance(record, Mapping):
            raise FormalizationProtocolError(
                f"audit_versions.{lane} must be an object"
            )
        current = _nonempty_string(
            record.get("current"), f"audit_versions.{lane}.current"
        )
        if current != expected["current"]:
            raise FormalizationProtocolError(
                f"audit_versions.{lane}.current must be {expected['current']}"
            )
        expected_prompt = expected.get("prompt_version")
        if expected_prompt is not None:
            prompt = _nonempty_string(
                record.get("prompt_version"),
                f"audit_versions.{lane}.prompt_version",
            )
            if prompt != expected_prompt:
                raise FormalizationProtocolError(
                    f"audit_versions.{lane}.prompt_version must be {expected_prompt}"
                )
        elif "prompt_version" in record:
            raise FormalizationProtocolError(
                f"audit_versions.{lane} must not invent a prompt-version authority"
            )
        _nonempty_string(record.get("meaning"), f"audit_versions.{lane}.meaning")
    theorem_realization = versions["theorem_realization"]
    required_for = _string_set(
        theorem_realization.get("required_for"),
        "audit_versions.theorem_realization.required_for",
    )
    if required_for != frozenset({"new_paper_closeout", "explicit_v11_upgrade"}):
        raise FormalizationProtocolError(
            "theorem-realization required_for must name exactly the new-paper and explicit-upgrade cases"
        )
    _nonempty_string(
        theorem_realization.get("transition"),
        "audit_versions.theorem_realization.transition",
    )
    baseline = theorem_realization.get("legacy_v10_transition_baseline")
    if not isinstance(baseline, Mapping):
        raise FormalizationProtocolError(
            "audit_versions.theorem_realization.legacy_v10_transition_baseline "
            "must be an object"
        )
    _validate_legacy_v10_transition_baseline(baseline)

    coverage = payload["coverage"]
    normal = coverage.get("normal_mode")
    deep = coverage.get("deep_mode")
    if not isinstance(normal, Mapping) or not isinstance(deep, Mapping):
        raise FormalizationProtocolError(
            "coverage.normal_mode and coverage.deep_mode must be objects"
        )
    normal_id = _nonempty_string(normal.get("id"), "coverage.normal_mode.id")
    deep_id = _nonempty_string(deep.get("id"), "coverage.deep_mode.id")
    if normal_id == deep_id:
        raise FormalizationProtocolError("normal and deep coverage modes must differ")
    if coverage.get("default_mode") != normal_id:
        raise FormalizationProtocolError("coverage.default_mode must be the normal mode")
    included = _string_set(
        normal.get("included_source_kinds"),
        "coverage.normal_mode.included_source_kinds",
    )
    deep_only = _string_set(
        normal.get("deep_only_standalone_source_kinds"),
        "coverage.normal_mode.deep_only_standalone_source_kinds",
    )
    label_required = _string_set(
        normal.get("label_required_source_kinds"),
        "coverage.normal_mode.label_required_source_kinds",
    )
    if included & deep_only:
        raise FormalizationProtocolError(
            "normal included and deep-only standalone source kinds must be disjoint"
        )
    if not label_required <= included:
        raise FormalizationProtocolError(
            "label-required source kinds must be included normal source kinds"
        )
    required_named = {"theorem", "proposition", "lemma", "corollary", "definition"}
    if not required_named <= included:
        raise FormalizationProtocolError(
            "normal coverage must include theorem/proposition/lemma/corollary/definition"
        )
    required_deep = {"formula", "equation", "algorithm", "algorithmic_formula"}
    if not required_deep <= deep_only:
        raise FormalizationProtocolError(
            "standalone formula/equation/algorithm kinds must be deep-only"
        )

    reuse = payload["reuse"]
    required_identities = _string_set(
        reuse.get("required_unchanged_identities"),
        "reuse.required_unchanged_identities",
    )
    if required_identities != EXPECTED_REQUIRED_REUSE_IDENTITIES:
        missing = sorted(EXPECTED_REQUIRED_REUSE_IDENTITIES - required_identities)
        unexpected = sorted(required_identities - EXPECTED_REQUIRED_REUSE_IDENTITIES)
        raise FormalizationProtocolError(
            "reuse.required_unchanged_identities contradicts the authoritative "
            f"identity contract (missing={missing}, unexpected={unexpected})"
        )
    if reuse.get("granularity") != "item":
        raise FormalizationProtocolError("reuse.granularity must be item")
    if "raw_lean_statement" in required_identities:
        raise FormalizationProtocolError(
            "raw Lean spelling is trace evidence, not a semantic reuse identity"
        )
    navigation_only = _string_set(
        reuse.get("navigation_only"), "reuse.navigation_only"
    )
    for required_navigation in (
        "lean_declaration_name",
        "raw_lean_declaration_spelling_after_unique_semantic_match",
    ):
        if required_navigation not in navigation_only:
            raise FormalizationProtocolError(
                f"reuse.navigation_only must include {required_navigation}"
            )
    fail_closed_on = _string_set(
        reuse.get("fail_closed_on"), "reuse.fail_closed_on"
    )
    if fail_closed_on != EXPECTED_REUSE_FAILURES:
        missing = sorted(EXPECTED_REUSE_FAILURES - fail_closed_on)
        unexpected = sorted(fail_closed_on - EXPECTED_REUSE_FAILURES)
        raise FormalizationProtocolError(
            "reuse.fail_closed_on contradicts the authoritative failure contract "
            f"(missing={missing}, unexpected={unexpected})"
        )

    builds = payload["builds"]
    for field in ("proof_iteration", "paper_closeout", "integration_or_release"):
        _nonempty_string(builds.get(field), f"builds.{field}")
    classifications = payload["classification"]
    expected_impacts = {
        "source_condition_or_refinement": "formalized_note",
        "additional_assumption": "partially_formalized",
        "minor_source_typo_or_proof_repair": "formalized_note",
        "approved_corrected_target": "classify_by_substantive_endpoint_impact",
        "empirical_or_computational_material": "out_of_normal_theorem_scope",
    }
    for category, expected_impact in expected_impacts.items():
        record = classifications.get(category)
        if not isinstance(record, Mapping):
            raise FormalizationProtocolError(
                f"classification.{category} must be an object"
            )
        if record.get("status_impact") != expected_impact:
            raise FormalizationProtocolError(
                f"classification.{category}.status_impact must be {expected_impact}"
            )
        _nonempty_string(
            record.get("rule"), f"classification.{category}.rule"
        )
    if payload["pacing"].get("priority") != "proof_first":
        raise FormalizationProtocolError("pacing.priority must be proof_first")
    return json.loads(json.dumps(payload))


@lru_cache(maxsize=8)
def _validated_protocol_canonical_json(raw: bytes) -> str:
    """Validate one exact byte payload once and retain no mutable state."""

    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise FormalizationProtocolError(f"invalid protocol JSON: {exc}") from exc
    validated = validate_formalization_protocol(payload)
    return json.dumps(
        validated,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )


def _current_protocol_canonical_json() -> str:
    """Read current bytes on every call, caching only an exact byte identity."""

    try:
        raw = PROTOCOL_PATH.read_bytes()
    except OSError as exc:
        raise FormalizationProtocolError(
            f"could not load {PROTOCOL_PATH.relative_to(ROOT)}: {exc}"
        ) from exc
    return _validated_protocol_canonical_json(raw)


def load_formalization_protocol() -> dict[str, Any]:
    """Read the exact repository policy. Missing or invalid policy is fatal.

    Validation is content-addressed within the process. Every call still
    reads the file bytes, so an edit made during a long closeout invalidates
    immediately; callers receive a fresh object and cannot mutate the cache.
    """

    return json.loads(_current_protocol_canonical_json())


def coverage_protocol() -> dict[str, Any]:
    """Return the validated source-coverage section."""

    return load_formalization_protocol()["coverage"]


def formalization_protocol_digest(payload: object | None = None) -> str:
    """Return the canonical digest of a fully validated protocol payload.

    The digest is independent of JSON whitespace and object-key ordering. An
    invalid or contradictory payload raises instead of yielding an identity
    that could authorize cached or item-level evidence.
    """

    canonical_protocol = (
        _current_protocol_canonical_json()
        if payload is None
        else json.dumps(
            validate_formalization_protocol(payload),
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    encoded = json.dumps(
        {
            "schema": PROTOCOL_DIGEST_SCHEMA,
            "protocol": json.loads(canonical_protocol),
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _operational_coverage_protocol_projection(
    validated: Mapping[str, Any],
) -> dict[str, object]:
    """Return only policy fields that can change source-obligation selection.

    ``rule`` values are human-facing explanations of structured controls.  A
    new, unrecognized structured field is retained by default, so extending
    the protocol cannot silently preserve an extraction receipt until the new
    field has deliberately been classified as nonoperative here.
    """

    coverage = validated["coverage"]

    def without_rule(value: object) -> object:
        if isinstance(value, Mapping):
            return {
                str(key): without_rule(child)
                for key, child in value.items()
                if str(key) != "rule"
            }
        if isinstance(value, list):
            return [without_rule(child) for child in value]
        return value

    return {
        "protocol_schema": validated["schema"],
        "coverage": without_rule(coverage),
    }


def _operational_review_protocol_projection(
    validated: Mapping[str, Any],
) -> dict[str, object]:
    """Return structured policy that changes semantic review judgments.

    Build commands, pacing, transition authority coordinates, protocol IDs,
    and explanatory prose do not change what a reviewer must decide.  Coverage
    semantics remain embedded because changing the selected source obligation
    set must invalidate both extraction and every judgment over that set.
    Unknown structured fields in retained sections stay fail-closed.
    """

    versions: dict[str, object] = {}
    for lane, raw_record in validated["audit_versions"].items():
        record = {
            str(key): value
            for key, value in raw_record.items()
            if str(key)
            not in {
                "meaning",
                "transition",
                "legacy_v10_transition_baseline",
                # This selects when an optional v11 migration is scheduled. It
                # does not alter the v10 source-obligation set or the semantic
                # judgment made for an existing item.
                "required_for",
            }
        }
        if str(lane) == "theorem_realization":
            # Keep the pre-scheduling v11 lane marker in the review receipt.
            # Existing v10 sidecars were issued while ``required_for`` carried
            # this exact historical list; the actual scheduling field is now
            # deliberately nonsemantic, so canonicalizing it preserves those
            # receipts without treating either scheduling policy as evidence.
            record["required_for"] = [
                "new_paper_closeout",
                "materially_reissued_closeout",
            ]
        versions[str(lane)] = record

    reuse = {
        str(key): value
        for key, value in validated["reuse"].items()
        if str(key) != "rule"
    }
    classification = {
        str(category): {
            str(key): value
            for key, value in record.items()
            if str(key) != "rule"
        }
        for category, record in validated["classification"].items()
    }
    return {
        "protocol_schema": validated["schema"],
        "audit_versions": versions,
        **_operational_coverage_protocol_projection(validated),
        "reuse": reuse,
        "classification": classification,
    }


def _protocol_projection_digest(schema: int, projection: object) -> str:
    encoded = json.dumps(
        {"schema": schema, "protocol": projection},
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def formalization_coverage_protocol_digest(payload: object | None = None) -> str:
    """Identity of policy that can change expensive source-obligation extraction."""

    validated = (
        load_formalization_protocol()
        if payload is None
        else validate_formalization_protocol(payload)
    )
    return _protocol_projection_digest(
        COVERAGE_PROTOCOL_DIGEST_SCHEMA,
        _operational_coverage_protocol_projection(validated),
    )


def formalization_review_protocol_digest(payload: object | None = None) -> str:
    """Identity of structured policy that can change a semantic judgment."""

    validated = (
        load_formalization_protocol()
        if payload is None
        else validate_formalization_protocol(payload)
    )
    return _protocol_projection_digest(
        REVIEW_PROTOCOL_DIGEST_SCHEMA,
        _operational_review_protocol_projection(validated),
    )


def formalization_protocol_receipt_matches(
    receipt: object,
    *,
    scope: str,
    payload: object | None = None,
) -> bool:
    """Validate a scoped protocol receipt with a narrow legacy transition.

    A scoped field, once present, is authoritative and malformed/stale content
    cannot fall back to the legacy field.  Receipts created before the split
    remain usable only while their whole-protocol digest equals the exact
    current whole protocol; after any edit they fail closed and must be
    reissued with a scoped receipt.
    """

    if not isinstance(receipt, Mapping):
        return False
    if scope == "coverage":
        field = FORMALIZATION_COVERAGE_PROTOCOL_FIELD
        current = formalization_coverage_protocol_digest(payload)
    elif scope == "review":
        field = FORMALIZATION_REVIEW_PROTOCOL_FIELD
        current = formalization_review_protocol_digest(payload)
    else:
        raise ValueError(f"unsupported formalization protocol receipt scope: {scope}")

    if field in receipt:
        supplied = str(receipt.get(field) or "").strip().lower()
        return supplied == current
    supplied_legacy = str(
        receipt.get(LEGACY_FORMALIZATION_PROTOCOL_FIELD) or ""
    ).strip().lower()
    return bool(
        supplied_legacy
        and supplied_legacy == formalization_protocol_digest(payload)
    )


def formalization_judgment_review_protocol_is_current(
    raw_audit: object,
    judgment_payload: object,
    *,
    payload: object | None = None,
) -> bool:
    """Validate the review-policy receipt governing an ordinary judgment.

    Pre-split raw audits carried one whole-protocol receipt. Once that legacy
    receipt is unavailable, a coverage-scoped raw audit requires its judgment
    sidecar to carry the scoped review receipt. Authenticated item-overlay
    loaders apply their own capability checks before deciding whether this
    ordinary-sidecar predicate is relevant.
    """

    if not isinstance(raw_audit, Mapping):
        return False
    protocol_scoped = any(
        field in raw_audit
        for field in (
            FORMALIZATION_COVERAGE_PROTOCOL_FIELD,
            LEGACY_FORMALIZATION_PROTOCOL_FIELD,
        )
    )
    if not protocol_scoped:
        return True
    receipt = (
        judgment_payload
        if isinstance(judgment_payload, Mapping)
        and FORMALIZATION_REVIEW_PROTOCOL_FIELD in judgment_payload
        else raw_audit
    )
    return formalization_protocol_receipt_matches(
        receipt,
        scope="review",
        payload=payload,
    )


def formalization_material_protocol_digest(payload: object | None = None) -> str:
    """Return the semantic audit-policy identity used by portable trust ledgers.

    The transition authority, its manifest digest, Git coordinates, build
    commands, pacing prose, and generated aggregates are deliberately absent.
    This avoids a manifest/config self-hash cycle while pinning the coverage,
    classification, reuse, and validator-version rules that determine whether
    the stored material identities mean the same thing.
    """

    # Portable closeout ledgers and ordinary semantic judgments share the
    # same operational review policy.  Keeping one projection prevents prose,
    # build, pacing, or authority maintenance from producing different cache
    # behavior in the two consumers.
    return formalization_review_protocol_digest(payload)


if __name__ == "__main__":
    current = load_formalization_protocol()
    print(f"OK {current['protocol_id']}")
