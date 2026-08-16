"""Recognize caller-supplied stochastic-process conclusions structurally.

This is deliberately a narrow fail-closed classifier.  A paper-facing theorem
may take ordinary source data such as a measure, a rate, or a measurable
function.  It may not receive formalized credit merely because a record input
also supplies the *derived* renewal-process facts needed by its proof.  In
particular, a record that simultaneously asserts an identically distributed
sequence, independence, and an integrability/expectation fact is a
construction obligation from the generative source model, not ordinary data.

The classifier reads expanded Lean type surfaces only.  It never inspects a
record, field, binder, theorem, or function name.
"""

from __future__ import annotations

import re
from typing import Any, Mapping


_IDENTICAL_DISTRIBUTION_MARKERS = (
    "ProbabilityTheory.IdentDistrib",
    "IdenticallyDistributed",
)
_INDEPENDENCE_MARKERS = (
    "\u27c2",
    "IndepFun",
    "iIndepFun",
    "Independent",
    "Independence",
)
_MOMENT_OR_EXPECTATION_MARKERS = (
    "Integrable",
    "\u222b",
    "integral",
    "Expectation",
    "expectation",
)


# These expressions only identify the *same term* across proposition shapes.
# They deliberately do not inspect Lean binder or declaration names: replacing
# ``stateTimeI`` by any fresh identifier leaves every extracted role unchanged.
_PROCESS_IDENTIFIER = r"([A-Za-z_][A-Za-z0-9_'.]*)"
_IDENT_DISTRIB_SEQUENCE_RE = re.compile(
    r"(?:ProbabilityTheory\.)?(?:IdentDistrib|IdenticallyDistributed)\s*"
    r"\(\s*" + _PROCESS_IDENTIFIER + r"\s+[^()\s]+\s*\)\s*"
    r"\(\s*\1\s+[^()\s]+\s*\)"
)
_PAIRWISE_INDEPENDENCE_SEQUENCE_RE = re.compile(
    r"\bPairwise\b.*?(?:⟂|IndepFun|iIndepFun|Independent|Independence).*?"
    r"\bon\s+" + _PROCESS_IDENTIFIER
)
_INTEGRABLE_SEQUENCE_RE = re.compile(
    r"\bIntegrable\s*\(\s*" + _PROCESS_IDENTIFIER + r"\s+[^()\s]+\s*\)"
)
_INTEGRAL_SEQUENCE_RE = re.compile(
    r"∫\s*[^,]+,\s*" + _PROCESS_IDENTIFIER + r"\s+[^()\s]+(?:\s+[^∂\s]+)?\s*∂"
)


def _shared_process_terms(types: list[str]) -> tuple[set[str], set[str], set[str]]:
    """Extract sequence terms occupying the IID/SLLN proposition positions.

    A marker alone is not sufficient evidence: a record may contain an IID
    fact for one random sequence and an integrability fact for another.  The
    shared term is taken from the proposition argument position, so the check
    survives alpha-renaming while distinguishing those two records.
    """

    identically_distributed: set[str] = set()
    independent: set[str] = set()
    moment_or_expectation: set[str] = set()
    for type_text in types:
        if any(marker in type_text for marker in _IDENTICAL_DISTRIBUTION_MARKERS):
            identically_distributed.update(
                match.group(1) for match in _IDENT_DISTRIB_SEQUENCE_RE.finditer(type_text)
            )
        if any(marker in type_text for marker in _INDEPENDENCE_MARKERS):
            independent.update(
                match.group(1)
                for match in _PAIRWISE_INDEPENDENCE_SEQUENCE_RE.finditer(type_text)
            )
        if any(marker in type_text for marker in _MOMENT_OR_EXPECTATION_MARKERS):
            moment_or_expectation.update(
                match.group(1) for match in _INTEGRABLE_SEQUENCE_RE.finditer(type_text)
            )
            moment_or_expectation.update(
                match.group(1) for match in _INTEGRAL_SEQUENCE_RE.finditer(type_text)
            )
    return identically_distributed, independent, moment_or_expectation


def caller_supplied_derived_process_basis(item: Mapping[str, Any]) -> list[str]:
    """Return semantic evidence that an input record supplies cycle consequences.

    We require all three independent type-level facts before classifying an
    input.  This deliberately avoids treating a generic probability measure,
    one integrability hypothesis, or one unrelated ``Pairwise`` relation as a
    renewal-process construction obligation.
    """

    surface = item.get("expanded_lean_surface")
    if not isinstance(surface, Mapping):
        return []
    roots = surface.get("record_roots")
    fields = surface.get("record_field_types")
    if not isinstance(roots, list) or not roots or not isinstance(fields, list):
        return []

    types = [
        str(field.get("expanded_type") or "")
        for field in fields
        if isinstance(field, Mapping) and str(field.get("expanded_type") or "").strip()
    ]
    if not types:
        return []

    (
        identically_distributed,
        independent,
        moment_or_expectation,
    ) = _shared_process_terms(types)
    if not (
        identically_distributed
        and independent
        and moment_or_expectation
        and identically_distributed & independent & moment_or_expectation
    ):
        return []

    return [
        "expanded record field types assert an identically distributed stochastic sequence",
        "expanded record field types assert independence for that same stochastic sequence",
        "expanded record field types assert an integrability or expectation fact for that same stochastic sequence",
    ]


def caller_supplied_unscoped_endpoint_calculus_basis(
    item: Mapping[str, Any],
) -> list[str]:
    """Recognize an endpoint-calculus theorem packaged as caller data.

    This targets a distinct source-fidelity failure mode: a record can quantify
    over an arbitrary policy set, insert a moving interval, and assert a
    derivative/sign equivalence for the resulting objective.  Such a field is
    not ordinary model data.  In particular, it is generally false without a
    component/separation hypothesis, since a background set may already
    contain the moving interval near the endpoint.

    The recognition uses only logical/calculus/set constructors in expanded
    types.  It intentionally ignores every record, field, binder, and
    declaration name.
    """

    surface = item.get("expanded_lean_surface")
    if not isinstance(surface, Mapping):
        return []
    roots = surface.get("record_roots")
    fields = surface.get("record_field_types")
    if not isinstance(roots, list) or not roots or not isinstance(fields, list):
        return []

    for field in fields:
        if not isinstance(field, Mapping):
            continue
        type_text = str(field.get("expanded_type") or "")
        if not type_text.strip():
            continue
        has_derivative = "HasDerivAt" in type_text or "HasDerivWithinAt" in type_text
        has_arbitrary_policy_set = "∀" in type_text and (
            "(Set (" in type_text or "(Set(" in type_text
        )
        has_moving_interval_union = (
            "∪" in type_text
            and ("Set.Ioo" in type_text or "Set.Ioi" in type_text)
        )
        if has_derivative and has_arbitrary_policy_set and has_moving_interval_union:
            return [
                "expanded record field type asserts endpoint calculus for an arbitrary policy set with a moving interval",
                "the same field supplies the derivative of the objective rather than deriving it from source primitives and component geometry",
            ]
    return []


def caller_supplied_model_construction_basis(item: Mapping[str, Any]) -> list[str]:
    """Return all structurally detected derived-model obligations on an input."""

    return (
        caller_supplied_derived_process_basis(item)
        + caller_supplied_unscoped_endpoint_calculus_basis(item)
    )
