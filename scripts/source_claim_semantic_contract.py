"""Authoritative API for complete source-claim semantic contracts.

The implementation remains in the legacy-named source-record module while
historical audit artifacts are supported. New audit code should import this
module: it makes clear that the gate covers every material theorem-realization
component, including model/domain data, rather than a named class of proof
restrictions.
"""

from __future__ import annotations

try:
    from source_record_operational_prop_obligations import (  # type: ignore
        APPROVED_SOURCE_CORRECTION_ROUTE,
        CHECKED_LEAN_DERIVATION_ROUTE,
        EXACT_SOURCE_CLAIM_ROUTE,
        SOURCE_CLAIM_COMPONENT_ROLE_FIELD,
        SOURCE_CLAIM_COMPONENT_SHA256_FIELD,
        SOURCE_CLAIM_COMPONENT_OCCURRENCE_FIELD,
        SOURCE_CLAIM_COMPONENT_STRUCTURAL_TYPE_SHA256_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACT_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACTS_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACT_SCHEMA,
        SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
        TRANSPARENT_SPEC_FULL_SURFACE_CORRESPONDENCE_ROUTE,
        TRUSTED_EXTERNAL_SCAFFOLDING_ROUTE,
        CheckedLeanBridgeReceipt,
        RecursiveFieldExplicitParentComponentReceipt,
        SemanticContractExecutableTerminalComponentReceipt,
        SourceDomainCorrespondenceReceipt,
        SourceClaimAtomReceipt,
        StrictSourceSpecCorrespondenceReceipt,
        TransparentSpecFullSurfaceCorrespondenceReceipt,
        complete_source_claim_semantic_contract_errors,
        source_claim_component_sha256,
        theorem_facing_obligation_items,
        theorem_facing_semantic_restriction_status,
    )
except ModuleNotFoundError:  # pragma: no cover - package-style imports.
    from scripts.source_record_operational_prop_obligations import (  # noqa: F401
        APPROVED_SOURCE_CORRECTION_ROUTE,
        CHECKED_LEAN_DERIVATION_ROUTE,
        EXACT_SOURCE_CLAIM_ROUTE,
        SOURCE_CLAIM_COMPONENT_ROLE_FIELD,
        SOURCE_CLAIM_COMPONENT_SHA256_FIELD,
        SOURCE_CLAIM_COMPONENT_OCCURRENCE_FIELD,
        SOURCE_CLAIM_COMPONENT_STRUCTURAL_TYPE_SHA256_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACT_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACTS_FIELD,
        SOURCE_CLAIM_SEMANTIC_CONTRACT_SCHEMA,
        SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
        TRANSPARENT_SPEC_FULL_SURFACE_CORRESPONDENCE_ROUTE,
        TRUSTED_EXTERNAL_SCAFFOLDING_ROUTE,
        CheckedLeanBridgeReceipt,
        RecursiveFieldExplicitParentComponentReceipt,
        SemanticContractExecutableTerminalComponentReceipt,
        SourceDomainCorrespondenceReceipt,
        SourceClaimAtomReceipt,
        StrictSourceSpecCorrespondenceReceipt,
        TransparentSpecFullSurfaceCorrespondenceReceipt,
        complete_source_claim_semantic_contract_errors,
        source_claim_component_sha256,
        theorem_facing_obligation_items,
        theorem_facing_semantic_restriction_status,
    )


def theorem_realization_component_contract_errors(*args: object, **kwargs: object) -> list[str]:
    """Validate one material realization component's provenance disposition."""

    return complete_source_claim_semantic_contract_errors(*args, **kwargs)  # type: ignore[arg-type]


def theorem_realization_components(audit_payload: object) -> tuple[tuple[str, object], ...]:
    """Return the generated component ledger through the compatibility reader."""

    if not isinstance(audit_payload, dict):
        return ()
    return theorem_facing_obligation_items(audit_payload)
