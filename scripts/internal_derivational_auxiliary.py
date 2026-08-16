#!/usr/bin/env python3
"""Archived diagnostics for a narrowly internal PaperInterface helper.

The canonical closeout consumers no longer call this module. Its historical
lexical proof-closure receipts are retained for diagnosis and migration only;
they cannot reclassify an unresolved auxiliary or grant proof/source credit.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import sys
from collections import Counter
from collections.abc import Collection, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any

try:
    from source_record_target_disposition import (
        ValidatedAdministrativeProjectionRebind,
        approved_source_convention_antecedent_errors,
        semantic_target_disposition_errors,
        source_map_item_record_digest,
        source_input_target_disposition_errors,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_record_target_disposition import (
        ValidatedAdministrativeProjectionRebind,
        approved_source_convention_antecedent_errors,
        semantic_target_disposition_errors,
        source_map_item_record_digest,
        source_input_target_disposition_errors,
    )

try:
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import source_record_item_reuse_eligible
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import source_record_item_reuse_eligible

try:
    from source_record_integrity import source_record_audit_receipt_error
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_record_integrity import source_record_audit_receipt_error


SOURCE_RECORD_PROMPT_VERSION = "source-record-v10-semantic-conclusion-boundary-contract"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")
_EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:\b(?:page|p\.?)\s*\d+|\b[\w./-]+\.(?:tex|txt|md|pdf):\d+)",
    re.I,
)
_MISSING_CURRENT_SOURCE_CONDITION_JUDGMENT = (
    "matching parent boundary has no current source-condition judgment"
)
_FORBIDDEN_DERIVED_RESULT_RE = re.compile(r"(?:\bNonempty\b|Σ|\bSigma\b|\bSubtype\b)")
_EXISTENTIAL_BINDER_RE = re.compile(
    r"(?:∃|\bExists\b)\s*(?:\([^:()]+\s*:\s*([^()]+)\)|[^,:()]+\s*:\s*([^,]+))"
)
_SCALAR_EXISTENTIAL_HEADS = frozenset(
    {"Bool", "Char", "Fin", "Int", "Nat", "Rat", "Real", "String", "Unit", "ℕ", "ℤ", "ℚ", "ℝ"}
)
_ELEMENTARY_SCALAR_TOKENS = frozenset(
    {
        "Bool",
        "ByteArray",
        "Char",
        "Float",
        "Int",
        "Nat",
        "Rat",
        "Real",
        "String",
        "Unit",
        "ℕ",
        "ℤ",
        "ℚ",
        "ℝ",
    }
)
_SOURCE_PARSER: ModuleType | None = None
_SOURCE_PARSER_ERROR = ""
# The narrow auxiliary lane can be asked about several helpers reachable from
# one reviewed theorem.  Reparse an imported Lean closure only when one of its
# bytes changes; this is structural type-alias checking, not a source audit.
_SEMANTIC_ALIAS_CACHE: dict[
    tuple[tuple[str, str], ...], tuple[dict[str, Any], dict[str, Any]]
] = {}


@dataclass(frozen=True)
class InternalDerivationalAuxiliaryResolution:
    """One validated routing decision shared by all closeout consumers."""

    declaration: str
    accepted: bool
    reason: str


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _valid_sha256(value: object) -> str:
    normalized = str(value or "").strip().lower()
    return normalized if _SHA256_RE.fullmatch(normalized) else ""


def _canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def _read_json(path: Path) -> dict[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _source_parser() -> tuple[ModuleType | None, str]:
    """Load the existing declaration parser without invoking an audit scan."""

    global _SOURCE_PARSER, _SOURCE_PARSER_ERROR
    if _SOURCE_PARSER is not None:
        return _SOURCE_PARSER, ""
    if _SOURCE_PARSER_ERROR:
        return None, _SOURCE_PARSER_ERROR
    helper = (
        Path(__file__).resolve().parents[1]
        / "skills"
        / "econcs-formalizer"
        / "scripts"
        / "source_record_audit.py"
    )
    if not helper.is_file():
        _SOURCE_PARSER_ERROR = "source-record declaration parser is unavailable"
        return None, _SOURCE_PARSER_ERROR
    name = "_econcs_internal_derivational_source_parser"
    try:
        module = sys.modules.get(name)
        if not isinstance(module, ModuleType):
            spec = importlib.util.spec_from_file_location(name, helper)
            if spec is None or spec.loader is None:
                raise RuntimeError("could not create parser import specification")
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            spec.loader.exec_module(module)
    except Exception as exc:  # noqa: BLE001 - fail closed at the caller.
        _SOURCE_PARSER_ERROR = f"could not load source-record declaration parser: {exc}"
        return None, _SOURCE_PARSER_ERROR
    _SOURCE_PARSER = module
    return module, ""


def _input_names(parser: ModuleType, inputs: Collection[Mapping[str, object]]) -> set[str]:
    return {
        name
        for raw_input in inputs
        for name in parser.binder_names(str(raw_input.get("names") or ""))
    }


def _scoped_type_key(parser: ModuleType, type_text: object, names: set[str]) -> str:
    text = str(type_text or "").strip()
    return parser.abstract_free_identifiers(text, names) if text else ""


def _input_type_counter(
    parser: ModuleType, inputs: Collection[Mapping[str, object]]
) -> Counter[str]:
    names = _input_names(parser, inputs)
    return Counter(
        _scoped_type_key(parser, raw_input.get("type"), names)
        for raw_input in inputs
        if str(raw_input.get("type") or "").strip()
    )


def _current_interface_identity_error(
    identity: object, declarations_by_name: Mapping[str, list[Any]]
) -> str:
    """Check one exact raw declaration identity against PaperInterface bytes."""

    if not isinstance(identity, Mapping):
        return "semantic-contract endpoint has no declaration identity"
    qualified = str(identity.get("qualified_declaration") or "").strip()
    expected_hash = _valid_sha256(identity.get("declaration_sha256"))
    declarations = declarations_by_name.get(qualified, [])
    if not qualified or not expected_hash or len(declarations) != 1:
        return "semantic-contract endpoint is absent or ambiguous in current PaperInterface"
    if _sha256_bytes(declarations[0].source.encode("utf-8")) != expected_hash:
        return "semantic-contract endpoint declaration bytes changed"
    return ""


def _schema2_paired_endpoint_error(
    *,
    parent: Mapping[str, object],
    parent_association: Mapping[str, object],
    parent_qualified: str,
    declarations_by_name: Mapping[str, list[Any]],
) -> str:
    """Validate an exact semantic-contract evidence/Spec endpoint pair.

    The selected row may be the evidence theorem while its semantic review is
    recorded on the independently transparent Spec surface.  This helper
    admits that fact only when the current source map and both byte-pinned
    PaperInterface endpoints name one exact pair.  It never infers a pair from
    a declaration suffix or a conventional spelling.
    """

    role = str(parent_association.get("role") or "").strip()
    if role not in {"direct_evidence", "transparent_spec"}:
        return ""
    if parent_association.get("review_scope") != "individual_row_only":
        return "semantic-contract endpoint pair is not individually scoped"
    if not _valid_sha256(parent_association.get("semantic_association_sha256")):
        return "semantic-contract endpoint pair lacks its semantic association pin"

    pairs: set[tuple[str, str]] = set()
    source_identities = parent_association.get("source_item_identities")
    if not isinstance(source_identities, list) or not source_identities:
        return "semantic-contract endpoint pair has no source-item identity"
    for source_identity in source_identities:
        if not isinstance(source_identity, Mapping):
            return "semantic-contract endpoint pair has a malformed source identity"
        contract = source_identity.get("semantic_contract")
        if not isinstance(contract, Mapping):
            return "semantic-contract endpoint pair has no source contract"
        evidence = str(contract.get("evidence_declaration") or "").strip()
        spec = str(contract.get("spec_declaration") or "").strip()
        if not evidence or not spec or evidence == spec:
            return "semantic-contract endpoint pair is malformed"
        pairs.add((evidence, spec))
    if len(pairs) != 1:
        return "semantic-contract endpoint pair mixes source endpoints"
    evidence, spec = next(iter(pairs))
    expected_reviewed = evidence if role == "direct_evidence" else spec
    expected_paired = spec if role == "direct_evidence" else evidence
    association_identity = parent_association.get("reviewed_declaration_identity")
    parent_identity = parent.get("reviewed_declaration_identity")
    if (
        not isinstance(association_identity, Mapping)
        or str(association_identity.get("qualified_declaration") or "").strip()
        != expected_reviewed
        or str(parent_association.get("paired_qualified_declaration") or "").strip()
        != expected_paired
        or parent_qualified not in {evidence, spec}
        or not isinstance(parent_identity, Mapping)
        or str(parent_identity.get("qualified_declaration") or "").strip()
        not in {evidence, spec}
    ):
        return "semantic-contract endpoint pair does not match its exact source endpoints"
    for identity in (association_identity, parent_identity):
        identity_error = _current_interface_identity_error(identity, declarations_by_name)
        if identity_error:
            return identity_error
    return ""


def _current_semantic_aliases(
    parser: ModuleType,
    *,
    repository_root: Path,
    folder: Path,
    interface_path: Path,
    audit_payload: Mapping[str, object],
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, str]:
    """Load parser-resolved transparent aliases for the current import closure.

    Current receipts carry Lean's loaded-module graph, which is the
    authoritative declaration universe.  The diagnostic traversal is retained
    only for legacy receipts that predate that graph; it can reject such a
    receipt but cannot alter the source-facing declaration selection.
    """

    try:
        saved_closure = audit_payload.get("lean_import_closure")
        if saved_closure is not None:
            closure = parser.source_record_lean_import_closure_from_record(
                repository_root,
                interface_path,
                saved_closure,
            )
            lean_files = tuple(
                parser.paper_interface_import_closure_lean_files(
                    repository_root,
                    interface_path,
                    lean_import_closure=closure,
                )
            )
        else:
            lean_files = tuple(
                sorted(
                    {
                        interface_path.resolve(),
                        *parser.diagnostic_imported_paper_lean_files(
                            repository_root, [interface_path]
                        ),
                    },
                    key=lambda path: str(path.resolve()),
                )
            )
        fingerprint = tuple(
            (str(path.resolve()), _sha256_bytes(path.read_bytes()))
            for path in lean_files
        )
    except (OSError, ValueError) as exc:
        return None, None, f"current imported Lean closure is unavailable: {exc}"
    cached = _SEMANTIC_ALIAS_CACHE.get(fingerprint)
    if cached is None:
        try:
            declarations = parser.parse_local_declarations(
                repository_root, list(lean_files)
            )
            cached = (
                parser.parse_proposition_aliases(declarations),
                parser.parse_semantic_type_aliases(declarations),
            )
        except (OSError, ValueError) as exc:
            return None, None, f"current imported Lean closure is unreadable: {exc}"
        _SEMANTIC_ALIAS_CACHE[fingerprint] = cached
    return cached[0], cached[1], ""


def _current_expanded_binder_signature_error(
    *,
    parser: ModuleType,
    repository_root: Path,
    folder: Path,
    interface_path: Path,
    audit_payload: Mapping[str, object],
    parent: Mapping[str, object],
    raw_parent_inputs: Collection[Mapping[str, object]],
) -> str:
    """Require the issued expanded binder surface to match current aliases.

    The raw declaration signature itself is checked separately.  Here we also
    reproduce the parser's transparent proposition/type-alias expansion before
    comparing alpha-normalized domains, so an alias such as a finite candidate
    carrier cannot make a current direct signature appear stale or vice versa.
    """

    expanded_surface = parent.get("expanded_lean_surface")
    binder_domains = (
        expanded_surface.get("binder_domains")
        if isinstance(expanded_surface, Mapping)
        else None
    )
    expanded_domains = [
        str(domain.get("alpha_normalized_type") or "").strip()
        for domain in binder_domains or []
        if isinstance(domain, Mapping)
        and str(domain.get("alpha_normalized_type") or "").strip()
    ]
    if not expanded_domains:
        return "raw selected-root expanded binder signature is unavailable"
    if len(expanded_domains) != len(raw_parent_inputs):
        return "raw selected-root expanded binder arity differs from semantic-review surface"

    parent_identity = parent.get("reviewed_declaration_identity")
    if not isinstance(parent_identity, Mapping):
        return "raw selected-root review identity is unavailable for binder expansion"
    reviewed = str(parent_identity.get("qualified_declaration") or "").strip()
    if not reviewed or "." not in reviewed:
        return "raw selected-root review identity has no lexical context"
    context_namespace = reviewed.rsplit(".", 1)[0]
    proposition_aliases, type_aliases, alias_error = _current_semantic_aliases(
        parser,
        repository_root=repository_root,
        folder=folder,
        interface_path=interface_path,
        audit_payload=audit_payload,
    )
    if alias_error:
        return alias_error
    assert proposition_aliases is not None and type_aliases is not None

    bound_names: set[str] = set()
    for index, raw_input in enumerate(raw_parent_inputs):
        type_text = str(raw_input.get("type") or "").strip()
        if not type_text:
            return "raw selected-root expanded binder signature has an empty input type"
        surface = parser.semantic_model_surface_type(
            type_text,
            proposition_aliases,
            type_aliases,
            context_namespace=context_namespace,
            bound_names=bound_names,
        )
        current_domain = str(surface.get("alpha_normalized_type") or "").strip()
        if not current_domain or current_domain != expanded_domains[index]:
            return "current transparent expanded binder signature differs from raw semantic-review surface"
        bound_names.update(parser.binder_names(str(raw_input.get("names") or "")))
    return ""


def _exact_string_present(value: object, expected: str) -> bool:
    if isinstance(value, str):
        return value == expected
    if isinstance(value, Mapping):
        return any(_exact_string_present(child, expected) for child in value.values())
    if isinstance(value, list):
        return any(_exact_string_present(child, expected) for child in value)
    return False


def _current_file_pin_error(
    folder: Path, audit_payload: Mapping[str, object], item: Mapping[str, object]
) -> tuple[Path | None, str]:
    map_path = folder / "audit" / "paper_statement_map.json"
    recorded_map = _valid_sha256(audit_payload.get("paper_statement_map_sha256"))
    try:
        current_map = _sha256_bytes(map_path.read_bytes())
    except OSError:
        return None, "current paper-statement map is unavailable"
    if not recorded_map or recorded_map != current_map:
        return None, "frozen paper-statement map hash does not match current bytes"

    raw_source = audit_payload.get("review_interface_source")
    if not isinstance(raw_source, Mapping):
        return None, "raw audit lacks a review-interface source receipt"
    interface_path = folder / "PaperInterface.lean"
    try:
        expected_raw_path = str(interface_path.relative_to(folder.parent.parent)).replace("\\", "/")
    except ValueError:
        return None, "paper folder has no repository-relative source coordinate"
    raw_path = str(raw_source.get("path") or "").strip().replace("\\", "/")
    if raw_path != expected_raw_path:
        return None, "raw review-interface receipt does not point to this PaperInterface source"
    if str(item.get("source_file") or "").strip().replace("\\", "/") != raw_path:
        return None, "raw auxiliary source coordinate differs from the pinned PaperInterface source"
    recorded_source = _valid_sha256(raw_source.get("sha256"))
    try:
        current_source = _sha256_bytes(interface_path.read_bytes())
    except OSError:
        return None, "current PaperInterface source is unavailable"
    if not recorded_source or recorded_source != current_source:
        return None, "frozen PaperInterface source hash does not match current bytes"
    return interface_path, ""


def _source_identity_error(
    parser: ModuleType,
    association: Mapping[str, object],
    statement_map: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    association = _rebound_association(
        association, administrative_projection_rebind
    )
    raw_identities = association.get("source_item_identities")
    items = statement_map.get("items")
    if not isinstance(raw_identities, list) or not raw_identities or not isinstance(items, Mapping):
        return "parent direct-source association has no current source-item identity"
    expected: list[dict[str, Any]] = []
    actual: list[dict[str, Any]] = []
    for raw_identity in raw_identities:
        if not isinstance(raw_identity, Mapping):
            return "parent direct-source association has a malformed source-item identity"
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_item = items.get(source_key)
        if not source_key or not isinstance(source_item, dict):
            return "parent direct-source association targets no current source-map item"
        expected.append(parser.semantic_contract_source_identity(source_key, source_item))
        actual.append(dict(raw_identity))
    if sorted(_canonical_json(value) for value in actual) != sorted(
        _canonical_json(value) for value in expected
    ):
        return "parent direct-source association does not match the current source-map identity"
    return ""


def _schema1_source_identity_error(
    parser: ModuleType,
    association: Mapping[str, object],
    statement_map: Mapping[str, object],
) -> str:
    """Validate the legacy direct semantic-contract identity exactly.

    Schema 1 predated the extra source-semantic digest added to schema 2, but
    it still content-addresses the source-map item and records the complete
    semantic contract.  Treat it as a compatibility form only when every
    field it did record reconstructs from the current, byte-pinned map.
    """

    raw_identities = association.get("source_item_identities")
    items = statement_map.get("items")
    if not isinstance(raw_identities, list) or not raw_identities or not isinstance(items, Mapping):
        return "parent schema-1 source association has no current source-item identity"
    expected: list[dict[str, Any]] = []
    actual: list[dict[str, Any]] = []
    legacy_fields = (
        "source_key",
        "source_location",
        "source_kind",
        "source_map_item_sha256",
        "semantic_contract",
    )
    for raw_identity in raw_identities:
        if not isinstance(raw_identity, Mapping):
            return "parent schema-1 source association has a malformed source-item identity"
        if set(raw_identity) != set(legacy_fields):
            return "parent schema-1 source association has an unsupported source-item identity"
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_item = items.get(source_key)
        if not source_key or not isinstance(source_item, dict):
            return "parent schema-1 source association targets no current source-map item"
        current = parser.semantic_contract_source_identity(source_key, source_item)
        expected.append({field: current.get(field) for field in legacy_fields})
        actual.append(dict(raw_identity))
    if sorted(_canonical_json(value) for value in actual) != sorted(
        _canonical_json(value) for value in expected
    ):
        return "parent schema-1 source association does not match the current source-map identity"
    return ""


def _schema1_direct_source_association_error(
    parser: ModuleType,
    association: Mapping[str, object],
    statement_map: Mapping[str, object],
    *,
    root: str,
    root_declaration: Any,
) -> str:
    """Check one legacy direct-evidence/transparent-spec root association."""

    if association.get("schema") != 1:
        return "selected root source association is not schema 1"
    role = str(association.get("role") or "").strip()
    if role not in {"direct_evidence", "transparent_spec"}:
        return "selected root schema-1 association is not direct evidence or a transparent spec"
    if association.get("review_scope") != "individual_row_only":
        return "selected root schema-1 association is not scoped to one reviewed row"
    identity = association.get("reviewed_declaration_identity")
    if not isinstance(identity, Mapping):
        return "selected root schema-1 association lacks a declaration identity"
    if (
        identity.get("qualified_declaration") != root
        or _valid_sha256(identity.get("declaration_sha256"))
        != _sha256_bytes(root_declaration.source.encode("utf-8"))
    ):
        return "selected root schema-1 association is not pinned to the current declaration"
    association_error = _schema1_source_identity_error(
        parser, association, statement_map
    )
    if association_error:
        return association_error
    for source_identity in association.get("source_item_identities") or []:
        if not isinstance(source_identity, Mapping):  # Checked above; keeps mypy narrow.
            return "selected root schema-1 association has a malformed source item"
        contract = source_identity.get("semantic_contract")
        if not isinstance(contract, Mapping):
            return "selected root schema-1 association has no semantic contract"
        expected_declaration = (
            contract.get("evidence_declaration")
            if role == "direct_evidence"
            else contract.get("spec_declaration")
        )
        if expected_declaration != root:
            return "selected root schema-1 semantic contract does not name this root"
    paired = str(association.get("paired_qualified_declaration") or "").strip()
    if not paired or "." not in paired or paired == root:
        return "selected root schema-1 association has no distinct paired declaration"
    return ""


def _rebound_association(
    association: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> Mapping[str, object]:
    """Use only an already validated exact association transport receipt."""

    if not isinstance(
        administrative_projection_rebind, ValidatedAdministrativeProjectionRebind
    ):
        return association
    rebound = administrative_projection_rebind.association_rebinds.get(
        source_map_item_record_digest(association)
    )
    return rebound if isinstance(rebound, Mapping) else association


def _has_type_or_record_existential_binder(
    terminal: str, declarations: list[Any]
) -> bool:
    """Reject existential packaging of carriers/models, not scalar facts.

    A scalar/index existential remains an ordinary proposition.  The narrow
    routing bridge must still reject a result that manufactures a carrier,
    model, or certificate package under ``Exists``.
    """

    local_data_heads = {
        declaration.name.rsplit(".", 1)[-1]
        for declaration in declarations
        if declaration.kind in {"structure", "class", "inductive"}
    }
    for match in _EXISTENTIAL_BINDER_RE.finditer(terminal):
        binder_type = next((part.strip() for part in match.groups() if part and part.strip()), "")
        if not binder_type:
            return True
        if re.search(r"\b(?:Type|Sort|Measure|Kernel|PMF|Subtype|Sigma|Nonempty)\b", binder_type):
            return True
        head_match = re.match(r"@?([A-Za-z_][A-Za-z0-9_.']*|[ℕℤℚℝ])", binder_type)
        if head_match is None or head_match.group(1).rsplit(".", 1)[-1] not in _SCALAR_EXISTENTIAL_HEADS:
            return True
        if head_match.group(1).rsplit(".", 1)[-1] in local_data_heads:
            return True
    return False


def _is_direct_logical_proposition(parser: ModuleType, terminal: str, declarations: list[Any]) -> bool:
    if (
        not terminal
        or _FORBIDDEN_DERIVED_RESULT_RE.search(terminal)
        or _has_type_or_record_existential_binder(terminal, declarations)
    ):
        return False
    if terminal.strip() in {"True", "False"}:
        return False
    data_heads = parser.data_type_heads(declarations)
    proposition_heads = parser.proposition_type_heads(declarations)
    return bool(
        parser.is_proposition_type(
            terminal, proposition_heads=proposition_heads, data_heads=data_heads
        )
        and parser.is_logical_result_type(terminal)
    )


def _is_elementary_scalar(type_text: str) -> bool:
    if not type_text or "→" in type_text or "->" in type_text:
        return False
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|[ℕℤℚℝ]", type_text)
    return bool(tokens) and all(token in _ELEMENTARY_SCALAR_TOKENS for token in tokens)


def _current_source_condition_error(
    *,
    boundary: Mapping[str, object],
    parent: Mapping[str, object],
    parent_association: Mapping[str, object],
    parent_qualified: str,
    current_interface_declarations: Mapping[str, list[Any]],
    judgments: Mapping[str, Mapping[str, object]],
    current_judgment_keys: Collection[str],
    statement_map: Mapping[str, object],
    source_proof_fidelity: Mapping[str, object] | None,
    status: object,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    association = boundary.get("source_contract_association")
    if not isinstance(association, Mapping):
        return "matching parent boundary has no current source association"
    association = _rebound_association(association, administrative_projection_rebind)
    parent_association = _rebound_association(
        parent_association, administrative_projection_rebind
    )
    schema = association.get("schema")
    if schema == 2 and parent_association.get("schema") == 2:
        if association.get("semantic_association_sha256") != parent_association.get(
            "semantic_association_sha256"
        ):
            return "matching parent boundary is not tied to the selected root's source association"
        if _canonical_json(association.get("source_item_identities")) != _canonical_json(
            parent_association.get("source_item_identities")
        ):
            return "matching parent boundary has different source-item identities"
        # A direct source theorem can be reviewed through its exact transparent
        # Spec companion.  Boundary conditions nevertheless belong to the
        # authenticated direct-source endpoint, not necessarily the companion
        # identity held on the semantic-review row.  Require that endpoint
        # exactly and validate both source-map endpoints below; do not infer a
        # pairing from a declaration name.
        if association.get("reviewed_declaration_identity") != parent_association.get(
            "reviewed_declaration_identity"
        ):
            return "matching parent boundary is not pinned to the authenticated direct source endpoint"
        pair_error = _schema2_paired_endpoint_error(
            parent=parent,
            parent_association=parent_association,
            parent_qualified=parent_qualified,
            declarations_by_name=current_interface_declarations,
        )
        if pair_error:
            return pair_error
    elif schema == 1 and parent_association.get("schema") == 1:
        if association.get("association_mode") != "semantic_contract_group_member":
            return "matching parent schema-1 boundary is not a semantic-contract group member"
        if _canonical_json(association.get("source_item_identities")) != _canonical_json(
            parent_association.get("source_item_identities")
        ):
            return "matching parent schema-1 boundary has different source-item identities"
        root_identity = parent_association.get("reviewed_declaration_identity")
        if association.get("reviewed_declaration_identity") != root_identity:
            return "matching parent schema-1 boundary is not pinned to the selected root declaration"
        parser, parser_error = _source_parser()
        if parser is None:
            return parser_error
        association_error = _schema1_source_identity_error(
            # The root association has already made the source-map bytes and
            # declaration identity current; the boundary repeats the same
            # legacy source identity and must reconstruct exactly as well.
            parser,
            association,
            statement_map,
        )
        if association_error:
            return association_error
    else:
        return "matching parent boundary uses a different source-association schema"
    key = str(boundary.get("judgment_key") or "").strip()
    judgment = judgments.get(key)
    if not key or key not in current_judgment_keys or not isinstance(judgment, Mapping):
        return _MISSING_CURRENT_SOURCE_CONDITION_JUDGMENT
    location = str(
        judgment.get("source_location") or judgment.get("source_evidence") or ""
    ).strip()
    if not _EXACT_SOURCE_LOCATOR_RE.search(location):
        return "matching parent source-condition judgment lacks an exact source locator"
    classification = str(judgment.get("classification") or "").strip()
    if classification == "approved_source_convention":
        errors = approved_source_convention_antecedent_errors(
            boundary,
            judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
        )
    elif classification in {"validated_source_assumption", "approved_corrected_condition"}:
        errors = source_input_target_disposition_errors(
            boundary,
            judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
        )
    else:
        return "matching parent boundary is not a source condition or approved source convention"
    return "; ".join(str(error) for error in errors if str(error).strip())


def _root_semantic_review_visible_premise_error(
    *,
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    parent: Mapping[str, object],
    parent_association: Mapping[str, object],
    parser: ModuleType,
    raw_parent_inputs: Collection[Mapping[str, object]],
    helper_input_key: str,
    proposition_heads: Collection[str],
    data_heads: Collection[str],
    judgments: Mapping[str, Mapping[str, object]],
    current_judgment_keys: Collection[str],
    statement_map: Mapping[str, object],
    source_proof_fidelity: Mapping[str, object] | None,
    status: object,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    """Validate a root semantic review as one exact visible-premise receipt.

    This is a deliberately narrow substitute only for a *missing* per-input
    source-condition judgment.  It does not use a declaration, row, source-map
    item, or sidecar key as semantic evidence.  Those coordinates merely find
    the generated records whose content pins, alpha-normalized visible input,
    and expanded-binder comparison are then checked below.
    """

    parent_names = _input_names(parser, raw_parent_inputs)
    matching_root_inputs = [
        raw_input
        for raw_input in raw_parent_inputs
        if parser.is_proposition_type(
            str(raw_input.get("type") or ""),
            proposition_heads=proposition_heads,
            data_heads=data_heads,
        )
        and _scoped_type_key(parser, raw_input.get("type"), parent_names)
        == helper_input_key
    ]
    if len(matching_root_inputs) != 1:
        return "helper proposition input is not one exact current selected-root visible premise"

    # The source-record v10 semantic pin is what binds the review to both the
    # reviewed elaborated Lean surface and the source semantic identities.
    association_pin = _valid_sha256(parent_association.get("semantic_association_sha256"))
    if parent_association.get("schema") != 2 or not association_pin:
        return "selected root semantic review lacks a current schema-2 source-semantic association pin"

    review_key = str(parent.get("judgment_key") or "").strip()
    review = judgments.get(review_key)
    if (
        not review_key
        or review_key not in current_judgment_keys
        or not isinstance(review, Mapping)
    ):
        return "selected root has no current semantic-model review"
    if str(parent.get("kind") or "").strip() != "semantic_model_comparison":
        return "selected root semantic review has no semantic-model comparison receipt"
    if not source_record_item_reuse_eligible(
        parent, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return "selected root semantic review has no reusable current raw content receipt"

    raw_digest = _valid_sha256(parent.get("source_record_item_sha256"))
    audit_digest = _valid_sha256(audit_payload.get("source_record_audit_sha256"))
    if not raw_digest or not audit_digest:
        return "selected root semantic review lacks current raw content or aggregate pins"

    # Use the shared source-record currentness policy.  A schema-5 semantic
    # review can remain current across an unrelated aggregate reissue only
    # when its complete item pin set still names the current generated item.
    # The exact root-specific scalar and full-pin checks below remain stricter
    # than that general policy; this merely avoids treating an aggregate pin as
    # the sole valid form of freshness.
    try:
        try:
            from audit_repository import (
                semantic_model_review_findings,
                source_record_expected_item_digest_pins,
                source_record_expected_item_digests,
                source_record_judgment_current,
            )
        except ModuleNotFoundError:  # pragma: no cover - package-style imports.
            from scripts.audit_repository import (
                semantic_model_review_findings,
                source_record_expected_item_digest_pins,
                source_record_expected_item_digests,
                source_record_judgment_current,
            )
        expected_item_digests = source_record_expected_item_digests(
            dict(audit_payload)
        )
        expected_item_digest_pins = source_record_expected_item_digest_pins(
            dict(audit_payload)
        )
    except Exception as error:  # noqa: BLE001 - absence of the validator fails closed.
        return "could not load selected root semantic-review currentness policy: " + str(error)
    if (
        str(review.get("classification") or "").strip() != "semantic_model_review"
        or str(review.get("prompt_version") or "").strip()
        != SOURCE_RECORD_PROMPT_VERSION
        or not source_record_judgment_current(
            review_key,
            dict(review),
            digest=audit_digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        )
        or review.get("source_record_item_digest_schema")
        != SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        or _valid_sha256(review.get("source_record_item_sha256")) != raw_digest
    ):
        return "selected root semantic review is not pinned to the current raw semantic item"

    # A scalar item pin could otherwise be copied from one member of a reused
    # sidecar group.  For this root review, require its complete generated pin
    # set to name precisely the unique raw semantic-model comparison item.
    matching_raw_reviews = [
        candidate
        for candidate in audit_payload.get("semantic_model_items") or []
        if isinstance(candidate, Mapping)
        and str(candidate.get("judgment_key") or "").strip() == review_key
    ]
    expected_item_pin = (
        str(parent.get("kind") or "").strip(),
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        raw_digest,
    )
    raw_item_pins = review.get("source_record_item_sha256s")
    actual_item_pins: set[tuple[str, int, str]] = set()
    if not isinstance(raw_item_pins, list) or not raw_item_pins:
        return "selected root semantic review lacks its complete raw content pin set"
    for raw_pin in raw_item_pins:
        if not isinstance(raw_pin, Mapping):
            return "selected root semantic review has a malformed raw content pin"
        item_kind = str(raw_pin.get("kind") or "").strip()
        item_digest = _valid_sha256(raw_pin.get("source_record_item_sha256"))
        item_schema = raw_pin.get("source_record_item_digest_schema")
        if not item_kind or item_schema != SOURCE_RECORD_ITEM_DIGEST_SCHEMA or not item_digest:
            return "selected root semantic review has a malformed raw content pin"
        actual_item_pins.add((item_kind, item_schema, item_digest))
    if (
        len(matching_raw_reviews) != 1
        or len(actual_item_pins) != len(raw_item_pins)
        or actual_item_pins != {expected_item_pin}
    ):
        return "selected root semantic review content pins do not identify one exact current root review"

    raw_dimensions = parent.get("dimensions")
    expanded_dimensions = [
        dimension
        for dimension in raw_dimensions or []
        if isinstance(dimension, Mapping)
        and str(dimension.get("id") or "").strip() == "expanded_binders_and_domain"
    ]
    responses = review.get("semantic_model_dimensions")
    expanded_response = (
        responses.get("expanded_binders_and_domain")
        if isinstance(responses, Mapping)
        else None
    )
    if len(expanded_dimensions) != 1 or not isinstance(expanded_response, Mapping):
        return "selected root semantic review has no expanded-binders-and-domain response"

    # Reuse the repository's current semantic-review validator rather than
    # creating a second interpretation of verdicts or dimension obligations.
    # It performs no source or Lean scan; it only validates the already-issued
    # raw item and its sidecar against their current content pins.
    try:
        semantic_findings = semantic_model_review_findings(
            paper,
            folder,
            folder / "audit" / "source_record_match_llm.json",
            [dict(parent)],
            {key: dict(value) for key, value in judgments.items()},
            digest=audit_digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
            severity="ERROR",
            target_disposition_statement_map=dict(statement_map),
            target_disposition_source_proof_fidelity=(
                dict(source_proof_fidelity) if source_proof_fidelity else None
            ),
            target_disposition_validated_vocabulary_binding_source_item_ids=(
                audit_payload.get(
                    "source_coverage_validated_vocabulary_binding_source_items"
                )
            ),
            target_disposition_validated_vocabulary_direct_route_source_item_ids=(
                audit_payload.get(
                    "source_coverage_validated_vocabulary_direct_route_source_items"
                )
            ),
            target_disposition_administrative_projection_rebind=(
                administrative_projection_rebind
            ),
            enforce_target_disposition=False,
        )
    except Exception as error:  # noqa: BLE001 - absence of the validator fails closed.
        return "could not validate selected root semantic review: " + str(error)
    if semantic_findings:
        detail = str(getattr(semantic_findings[0], "message", "")).strip()
        return "selected root semantic review is not current and complete" + (
            ": " + detail if detail else ""
        )

    # The ordinary semantic validator checks the generated review surface. The
    # premise bridge also needs the response's exact source-association pin and
    # disposition.  This shared validator reconstructs them from the current
    # source map; it does not treat the response's source-map key as authority.
    disposition_errors = semantic_target_disposition_errors(
        parent,
        expanded_response,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        validated_vocabulary_binding_source_item_ids=(
            audit_payload.get(
                "source_coverage_validated_vocabulary_binding_source_items"
            )
        ),
        validated_vocabulary_direct_route_source_item_ids=(
            audit_payload.get(
                "source_coverage_validated_vocabulary_direct_route_source_items"
            )
        ),
        administrative_projection_rebind=administrative_projection_rebind,
    )
    if disposition_errors:
        return (
            "selected root expanded-binders response has no current source-semantic "
            "association: "
            + "; ".join(str(error) for error in disposition_errors if str(error).strip())
        )
    if str(expanded_response.get("verdict") or "").strip() not in {
        "matches_source_model",
        "matches_literal_source",
        "matches_approved_source_convention",
        "matches_approved_corrected_target",
    }:
        return "selected root expanded-binders response does not affirm the source model"
    return ""


def _internal_derivational_auxiliary_resolution_error(
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    item: Mapping[str, object],
    judgments: Mapping[str, Mapping[str, object]],
    *,
    current_judgment_keys: Collection[str],
    status: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
) -> str:
    """Return why an unresolved auxiliary cannot be treated as internal.

    An empty result is deliberately narrow authorization for an *already raw
    graph-reachable* helper.  It establishes routing only; it never infers an
    equivalence between the helper and any source statement.
    """

    # Callers receive this authority only from the receipt validator.  Ignore
    # any serialized or duck-typed value before it reaches the shared
    # target-disposition validators below.
    if not isinstance(
        administrative_projection_rebind, ValidatedAdministrativeProjectionRebind
    ):
        administrative_projection_rebind = None

    if str(audit_payload.get("prompt_version") or "").strip() != SOURCE_RECORD_PROMPT_VERSION:
        return "raw audit is not the current v10 semantic surface"
    if (
        str(item.get("disposition") or "").strip()
        != "missing_source_map_route_or_quarantine"
        or item.get("source_map_routes") != []
        or item.get("quarantined") is not False
        or str(item.get("quarantine_source_reason") or "").strip()
    ):
        return "raw auxiliary item is not the narrow unresolved helper form"
    target = str(item.get("declaration") or "").strip()
    if not target or "." not in target:
        return "raw auxiliary has no fully-qualified declaration identity"
    interface_path, pin_error = _current_file_pin_error(folder, audit_payload, item)
    if pin_error:
        return pin_error
    assert interface_path is not None
    statement_map = _read_json(folder / "audit" / "paper_statement_map.json")
    status_payload = _read_json(folder / "status.json")
    if statement_map is None or status_payload is None:
        return "current source map or status configuration is unreadable"
    if _exact_string_present(statement_map, target):
        return "helper is independently source-routed in the current source map"

    parser, parser_error = _source_parser()
    if parser is None:
        return parser_error
    repository_root = folder.parent.parent
    declarations = parser.parse_local_declarations(repository_root, [interface_path])
    by_name: dict[str, list[Any]] = {}
    for declaration in declarations:
        by_name.setdefault(declaration.name, []).append(declaration)
    raw_available = audit_payload.get("available_local_lean_declarations")
    if not isinstance(raw_available, list):
        return "raw audit lacks its local declaration completion ledger"
    if sum(str(value).strip() == target for value in raw_available) != 1:
        return "auxiliary does not have one exact fully-qualified raw completion"
    target_declarations = by_name.get(target, [])
    if len(target_declarations) != 1:
        return "current PaperInterface does not contain exactly one raw auxiliary declaration"
    target_declaration = target_declarations[0]
    if (
        target_declaration.kind not in {"theorem", "lemma"}
        or target_declaration.kind != str(item.get("kind") or "").strip()
        or target_declaration.source_file.replace("\\", "/")
        != str(item.get("source_file") or "").strip().replace("\\", "/")
        or target_declaration.line != item.get("line")
    ):
        return "current helper declaration does not match the frozen raw source coordinate"
    configured_rows = {
        (
            str(row.get("row") or "").strip()
            if isinstance(row, Mapping)
            else str(row).strip()
        )
        for row in audit_payload.get("configured_review_rows") or []
    }
    configured_rows.discard("")
    configured_declarations = {
        str(row.get("qualified_declaration") or "").strip()
        for row in audit_payload.get("configured_review_rows") or []
        if isinstance(row, Mapping)
    }
    configured_declarations.discard("")
    if target in configured_declarations:
        return "helper is independently selected as a configured review row"

    raw_dependencies = [
        dependency
        for dependency in audit_payload.get("reachable_paper_interface_auxiliary_dependencies")
        or []
        if isinstance(dependency, Mapping)
        and str(dependency.get("declaration") or "").strip() == target
    ]
    if len(raw_dependencies) != 1 or _canonical_json(raw_dependencies[0]) != _canonical_json(item):
        return "raw dependency ledger does not contain one exact helper routing item"
    transitive = item.get("transitively_referenced_from")
    if not isinstance(transitive, list) or not transitive:
        return "raw dependency ledger has no selected-root route to the helper"
    roots = {
        str(route.get("selected_declaration") or "").strip()
        for route in transitive
        if isinstance(route, Mapping)
    }
    if len(roots) != 1 or not next(iter(roots), ""):
        return "helper is not reachable solely from one exact selected root"
    parent_qualified = next(iter(roots))
    semantic_items = [
        candidate
        for candidate in audit_payload.get("semantic_model_items") or []
        if isinstance(candidate, Mapping)
        and str(candidate.get("qualified_declaration") or "").strip() == parent_qualified
    ]
    if len(semantic_items) != 1:
        return "selected root has no unique current semantic-model source row"
    if any(
        str(candidate.get("qualified_declaration") or "").strip() == target
        for candidate in audit_payload.get("semantic_model_items") or []
        if isinstance(candidate, Mapping)
    ):
        return "helper is independently selected as a semantic-model source claim"
    parent = semantic_items[0]
    parent_row = str(parent.get("row") or "").strip()
    if not parent_row or parent_row not in configured_rows:
        return "selected root lacks one current configured review-row coordinate"
    for route in transitive:
        if not isinstance(route, Mapping):
            return "raw dependency route is malformed"
        rows = route.get("selected_review_rows")
        chain = route.get("dependency_chain")
        if (
            not isinstance(rows, list)
            or set(str(row).strip() for row in rows if str(row).strip()) != {parent_row}
            or not isinstance(chain, list)
            or [str(value).strip() for value in chain if str(value).strip()][0:1]
            != [parent_qualified]
            or [str(value).strip() for value in chain if str(value).strip()][-1:] != [target]
        ):
            return "raw dependency route is not an exact selected-root-to-helper chain"

    parent_declarations = by_name.get(parent_qualified, [])
    if len(parent_declarations) != 1:
        return "selected root declaration is absent or ambiguous in current PaperInterface"
    parent_declaration = parent_declarations[0]
    association = _receipt_source_association(
        parent, administrative_projection_rebind
    )
    if not isinstance(association, Mapping):
        return "selected root lacks a direct source association"
    association_error = _terminal_root_source_association_error(
        parser=parser,
        parent=parent,
        parent_qualified=parent_qualified,
        parent_declaration=parent_declaration,
        statement_map=statement_map,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    if association_error:
        return association_error

    raw_parent_inputs = (audit_payload.get("row_visible_inputs") or {}).get(parent_row)
    if not isinstance(raw_parent_inputs, list) or not all(
        isinstance(value, Mapping) for value in raw_parent_inputs
    ):
        return "raw selected-root visible-input signature is unavailable"
    parsed_parent_inputs = parser.visible_inputs_from_declaration(parent_declaration.source)
    if _input_type_counter(parser, raw_parent_inputs) != _input_type_counter(
        parser, parsed_parent_inputs
    ):
        return "raw selected-root visible-input signature differs from current declaration"
    parent_names = _input_names(parser, raw_parent_inputs)
    # Schema 1 predates the expanded-binder receipt. Its exact raw
    # visible-input list, current declaration comparison, and whole-interface
    # byte pin remain available; do not invent a new missing field as a reason
    # to discard that otherwise auditable evidence. Schema 2 retains the
    # stronger expanded signature requirement.
    if association.get("schema") == 2:
        expanded_signature_error = _current_expanded_binder_signature_error(
            parser=parser,
            repository_root=repository_root,
            folder=folder,
            interface_path=interface_path,
            audit_payload=audit_payload,
            parent=parent,
            raw_parent_inputs=raw_parent_inputs,
        )
        if expanded_signature_error:
            return expanded_signature_error

    helper_terminal = parser.declaration_terminal_result_type(target_declaration.source)
    parent_terminal = parser.declaration_terminal_result_type(parent_declaration.source)
    if not _is_direct_logical_proposition(parser, helper_terminal, declarations):
        return "helper terminal result is not a direct non-package proposition"
    helper_inputs = parser.visible_inputs_from_declaration(target_declaration.source)
    helper_names = _input_names(parser, helper_inputs)
    if _scoped_type_key(parser, helper_terminal, helper_names) == _scoped_type_key(
        parser, parent_terminal, _input_names(parser, parsed_parent_inputs)
    ):
        return "helper terminal result duplicates the selected source-facing conclusion"

    data_heads = parser.data_type_heads(declarations)
    proposition_heads = parser.proposition_type_heads(declarations)
    parent_data = [
        raw_input
        for raw_input in raw_parent_inputs
        if not parser.is_proposition_type(
            str(raw_input.get("type") or ""),
            proposition_heads=proposition_heads,
            data_heads=data_heads,
        )
    ]
    boundary_items = [
        boundary
        for boundary in audit_payload.get("boundary_input_items") or []
        if isinstance(boundary, Mapping) and str(boundary.get("row") or "").strip() == parent_row
    ]
    source_proof_fidelity = audit_payload.get("source_proof_fidelity")
    fidelity_mapping = source_proof_fidelity if isinstance(source_proof_fidelity, Mapping) else None
    effective_status = status if status is not None else status_payload.get("status")
    for helper_input in helper_inputs:
        helper_type = str(helper_input.get("type") or "").strip()
        if not helper_type:
            return "helper has an unparseable visible input"
        helper_key = _scoped_type_key(parser, helper_type, helper_names)
        is_prop = parser.is_proposition_type(
            helper_type, proposition_heads=proposition_heads, data_heads=data_heads
        )
        if not is_prop:
            if _is_elementary_scalar(helper_type):
                continue
            data_matches = [
                parent_input
                for parent_input in parent_data
                if _scoped_type_key(parser, parent_input.get("type"), parent_names)
                == helper_key
            ]
            if len(data_matches) != 1:
                return "helper data input is not one exact current selected-root data field"
            continue
        matching_boundaries = []
        for boundary in boundary_items:
            raw_input = boundary.get("input")
            if not isinstance(raw_input, Mapping):
                continue
            if _scoped_type_key(parser, raw_input.get("type"), parent_names) == helper_key:
                matching_boundaries.append(boundary)
        if len(matching_boundaries) > 1:
            return "helper proposition input is not one exact current selected-root source condition"
        if matching_boundaries:
            condition_error = _current_source_condition_error(
                boundary=matching_boundaries[0],
                parent=parent,
                parent_association=association,
                parent_qualified=parent_qualified,
                current_interface_declarations=by_name,
                judgments=judgments,
                current_judgment_keys=current_judgment_keys,
                statement_map=statement_map,
                source_proof_fidelity=fidelity_mapping,
                status=effective_status,
                administrative_projection_rebind=administrative_projection_rebind,
            )
            if not condition_error:
                continue
            # A malformed or stale per-boundary record remains a rejection.
            # The root semantic review can replace only its genuinely absent
            # source-condition judgment, never repair a failed normal route.
            if condition_error != _MISSING_CURRENT_SOURCE_CONDITION_JUDGMENT:
                return condition_error
        root_review_error = _root_semantic_review_visible_premise_error(
            paper=paper,
            folder=folder,
            audit_payload=audit_payload,
            parent=parent,
            parent_association=association,
            parser=parser,
            raw_parent_inputs=raw_parent_inputs,
            helper_input_key=helper_key,
            proposition_heads=proposition_heads,
            data_heads=data_heads,
            judgments=judgments,
            current_judgment_keys=current_judgment_keys,
            statement_map=statement_map,
            source_proof_fidelity=fidelity_mapping,
            status=effective_status,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        if root_review_error:
            return root_review_error
    return ""


_LEGACY_AUXILIARY_RECEIPT_SCHEMA = 1
_DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA = 2
_DERIVATIONAL_AUXILIARY_RECEIPT_KIND = (
    "paper_specific_transparent_derivational_auxiliary_closure"
)
_DERIVATIONAL_AUXILIARY_RECEIPT_FILE = (
    "source_record_transparent_derivational_auxiliary_receipt.json"
)
_TRANSPARENT_TERMINAL_RECEIPT_SCHEMA = 2
_TRANSPARENT_TERMINAL_RECEIPT_KIND = "paper_specific_transparent_terminal_surface"
_TRANSPARENT_TERMINAL_RECEIPT_FILE = (
    "source_record_transparent_terminal_surface_receipt.json"
)

# Schema 1 bound an auxiliary receipt to the entire serialized raw audit.  A
# narrow, independently authenticated reissue of one source-record item can
# legitimately change that serialization without changing any proof-local
# helper route.  Schema 2 instead pins the exact raw dependency manifest that
# this receipt authorization consumes.  It is deliberately separate from
# source-record item/judgment reuse: those judgments remain subject to their
# own current semantic pins below.
_AUXILIARY_RECEIPT_RAW_BINDING_SCHEMA = 2
_AUXILIARY_RECEIPT_RAW_MANIFEST_SCHEMA = 1
_AUXILIARY_RECEIPT_RAW_MANIFEST_POLICY = (
    "paper-interface-auxiliary-receipt-dependency-manifest-v1"
)


def _canonical_sha256(value: object) -> str:
    return _sha256_bytes(_canonical_json(value).encode("utf-8"))


def _auxiliary_receipt_candidate_kind(
    receipt_kind: str,
) -> tuple[frozenset[str], bool] | None:
    """Return the narrow raw candidate domain for one receipt kind.

    These are parser-emitted declaration kinds, not suffix/name heuristics.
    The boolean records whether the receipt promises coverage of the entire
    current candidate set rather than one independently authorized terminal.
    """

    if receipt_kind == _DERIVATIONAL_AUXILIARY_RECEIPT_KIND:
        return frozenset({"theorem", "lemma"}), True
    if receipt_kind == _TRANSPARENT_TERMINAL_RECEIPT_KIND:
        return frozenset({"abbrev"}), False
    return None


def _auxiliary_receipt_candidates(
    audit_payload: Mapping[str, object], *, receipt_kind: str
) -> tuple[list[Mapping[str, object]] | None, str]:
    """Select the raw unresolved nodes authorized by one receipt kind."""

    kind_config = _auxiliary_receipt_candidate_kind(receipt_kind)
    if kind_config is None:
        return None, "receipt kind has no semantic raw-manifest policy"
    allowed_kinds, _complete_set = kind_config
    raw_candidates = audit_payload.get(
        "unresolved_reachable_paper_interface_auxiliaries"
    )
    if not isinstance(raw_candidates, list):
        return None, "raw audit has no unresolved reachable-auxiliary ledger"
    candidates = [
        candidate
        for candidate in raw_candidates
        if isinstance(candidate, Mapping)
        and str(candidate.get("kind") or "").strip() in allowed_kinds
        and str(candidate.get("disposition") or "").strip()
        == "missing_source_map_route_or_quarantine"
        and candidate.get("source_map_routes") == []
        and candidate.get("quarantined") is False
        and not str(candidate.get("quarantine_source_reason") or "").strip()
    ]
    names = [str(candidate.get("declaration") or "").strip() for candidate in candidates]
    if not candidates or not all(names) or len(set(names)) != len(names):
        return None, "raw auxiliary candidate set is empty, malformed, or ambiguous"
    return sorted(candidates, key=lambda candidate: str(candidate.get("declaration") or "")), ""


def _auxiliary_receipt_raw_manifest(
    audit_payload: Mapping[str, object], *, receipt_kind: str
) -> tuple[dict[str, object] | None, str]:
    """Return the complete raw dependency manifest for one auxiliary receipt.

    This is intentionally a compact manifest of hashes of *complete* raw
    records.  It does not infer semantics from declaration spellings: graph
    coordinates only locate the exact raw nodes whose content is hashed.  The
    selected root's complete semantic-model record, visible inputs, boundary
    records, and configured-row relation are all included because the narrow
    derivational resolver may consume each of them.
    """

    kind_config = _auxiliary_receipt_candidate_kind(receipt_kind)
    if kind_config is None:
        return None, "receipt kind has no semantic raw-manifest policy"
    _allowed_kinds, complete_set = kind_config
    candidates, candidate_error = _auxiliary_receipt_candidates(
        audit_payload, receipt_kind=receipt_kind
    )
    if candidates is None:
        return None, candidate_error

    reachable = audit_payload.get("reachable_paper_interface_auxiliary_dependencies")
    semantic_items = audit_payload.get("semantic_model_items")
    configured_rows = audit_payload.get("configured_review_rows")
    row_visible_inputs = audit_payload.get("row_visible_inputs")
    boundary_items = audit_payload.get("boundary_input_items")
    if (
        not isinstance(reachable, list)
        or not isinstance(semantic_items, list)
        or not isinstance(configured_rows, list)
        or not isinstance(row_visible_inputs, Mapping)
        or not isinstance(boundary_items, list)
    ):
        return None, "raw audit lacks a complete auxiliary dependency context"

    candidate_descriptors: list[dict[str, object]] = []
    selected_root_descriptors: dict[tuple[str, str], dict[str, object]] = {}
    for candidate in candidates:
        declaration = str(candidate.get("declaration") or "").strip()
        routes = candidate.get("transitively_referenced_from")
        if not isinstance(routes, list) or not routes:
            return None, "raw auxiliary candidate has no selected-root routes"
        matching_reachable = [
            item
            for item in reachable
            if isinstance(item, Mapping)
            and str(item.get("declaration") or "").strip() == declaration
        ]
        if len(matching_reachable) != 1:
            return None, "raw reachable-auxiliary ledger has no unique candidate record"

        route_hashes: list[str] = []
        for route in routes:
            if not isinstance(route, Mapping):
                return None, "raw auxiliary candidate has a malformed selected-root route"
            root = str(route.get("selected_declaration") or "").strip()
            selected_rows = tuple(
                sorted(
                    str(row).strip()
                    for row in route.get("selected_review_rows") or []
                    if str(row).strip()
                )
            )
            if not root or not selected_rows:
                return None, "raw auxiliary route lacks a selected root or review row"
            root_matches = [
                item
                for item in semantic_items
                if isinstance(item, Mapping)
                and str(item.get("qualified_declaration") or "").strip() == root
            ]
            if len(root_matches) != 1:
                return None, "raw auxiliary route root has no unique semantic-model record"
            parent = root_matches[0]
            parent_row = str(parent.get("row") or "").strip()
            if len(selected_rows) != 1 or selected_rows[0] != parent_row:
                return None, "raw auxiliary route is not tied to one selected semantic-model row"
            root_key = (root, parent_row)
            if root_key not in selected_root_descriptors:
                selected_root_descriptors[root_key] = {
                    "qualified_declaration": root,
                    "row": parent_row,
                    "semantic_model_record_sha256": _canonical_sha256(parent),
                    "visible_inputs_sha256": _canonical_sha256(
                        row_visible_inputs.get(parent_row)
                    ),
                    "boundary_items_sha256": _canonical_sha256(
                        [
                            item
                            for item in boundary_items
                            if isinstance(item, Mapping)
                            and str(item.get("row") or "").strip() == parent_row
                        ]
                    ),
                    "configured_row_records_sha256": _canonical_sha256(
                        [
                            item
                            for item in configured_rows
                            if (
                                isinstance(item, Mapping)
                                and str(item.get("row") or "").strip() == parent_row
                            )
                            or (isinstance(item, str) and item.strip() == parent_row)
                        ]
                    ),
                }
            route_hashes.append(_canonical_sha256(route))

        candidate_descriptors.append(
            {
                "declaration": declaration,
                "unresolved_candidate_sha256": _canonical_sha256(candidate),
                "reachable_candidate_sha256": _canonical_sha256(
                    matching_reachable[0]
                ),
                "available_local_declaration_count": sum(
                    str(value).strip() == declaration
                    for value in audit_payload.get("available_local_lean_declarations")
                    or []
                ),
                "semantic_model_declaration_count": sum(
                    isinstance(item, Mapping)
                    and str(item.get("qualified_declaration") or "").strip()
                    == declaration
                    for item in semantic_items
                ),
                "selected_route_sha256s": sorted(route_hashes),
            }
        )

    manifest: dict[str, object] = {
        "schema": _AUXILIARY_RECEIPT_RAW_MANIFEST_SCHEMA,
        "policy_version": _AUXILIARY_RECEIPT_RAW_MANIFEST_POLICY,
        "receipt_kind": receipt_kind,
        "complete_candidate_set": complete_set,
        "candidate_descriptors": sorted(
            candidate_descriptors,
            key=lambda descriptor: str(descriptor["declaration"]),
        ),
        "selected_root_descriptors": sorted(
            selected_root_descriptors.values(),
            key=lambda descriptor: (
                str(descriptor["qualified_declaration"]), str(descriptor["row"])
            ),
        ),
    }
    # The derivational route's source-condition/disposition checker can depend
    # on arbitrary fidelity records.  Pin its complete raw mapping rather
    # than attempting an unsound name-based subprojection.
    if complete_set:
        manifest["source_proof_fidelity_sha256"] = _canonical_sha256(
            audit_payload.get("source_proof_fidelity")
        )
    return manifest, ""


def auxiliary_receipt_semantic_raw_binding(
    audit_payload: Mapping[str, object], *, receipt_kind: str
) -> tuple[dict[str, object] | None, str]:
    """Build the schema-2 raw binding for a materialized auxiliary receipt."""

    prompt_version = str(audit_payload.get("prompt_version") or "").strip()
    paper = str(audit_payload.get("paper") or "").strip()
    map_sha256 = _valid_sha256(audit_payload.get("paper_statement_map_sha256"))
    interface = audit_payload.get("review_interface_source")
    interface = interface if isinstance(interface, Mapping) else {}
    interface_path = str(interface.get("path") or "").strip()
    interface_sha256 = _valid_sha256(interface.get("sha256"))
    if (
        prompt_version != SOURCE_RECORD_PROMPT_VERSION
        or not paper
        or not map_sha256
        or not interface_path
        or not interface_sha256
    ):
        return None, "raw v10 auxiliary receipt binding has incomplete source/map/interface identities"
    manifest, manifest_error = _auxiliary_receipt_raw_manifest(
        audit_payload, receipt_kind=receipt_kind
    )
    if manifest is None:
        return None, manifest_error
    return {
        "schema": _AUXILIARY_RECEIPT_RAW_BINDING_SCHEMA,
        "policy_version": _AUXILIARY_RECEIPT_RAW_MANIFEST_POLICY,
        "paper": paper,
        "prompt_version": prompt_version,
        "paper_statement_map_sha256": map_sha256,
        "paper_interface": {
            "path": interface_path.replace("\\", "/"),
            "sha256": interface_sha256,
        },
        "raw_dependency_manifest": manifest,
        "raw_dependency_manifest_sha256": _canonical_sha256(manifest),
    }, ""


def _derivational_closure_record_identity(
    parser: ModuleType,
    declaration: Any,
    direct_local_dependencies: Collection[str],
) -> dict[str, object]:
    """Return one byte-pinned node in a paper-local proof closure.

    The receipt deliberately records the whole normalized declaration, not a
    short declaration name or its terminal type.  A helper can change its
    proof body while retaining the same theorem statement, and that change is
    material to a narrowly authorized implementation-only route.
    """

    return {
        **_normalized_declaration_identity(parser, declaration),
        "direct_local_dependencies": sorted(
            str(name).strip()
            for name in direct_local_dependencies
            if str(name).strip()
        ),
    }


def derivational_auxiliary_local_closure(
    parser: ModuleType,
    declarations: Collection[Any],
    target: str,
) -> tuple[list[dict[str, object]] | None, str]:
    """Resolve and pin the complete paper-local lexical closure of ``target``.

    This is intentionally a parser-backed lexical graph, not an inference
    from declaration suffixes.  Every paper-local reference in every reached
    proof body is resolved by the same conservative helper used by the raw
    source-record routing ledger.  An ambiguous local head blocks receipt
    issuance rather than being guessed from a function name.
    """

    by_name: dict[str, Any] = {}
    for declaration in declarations:
        name = str(getattr(declaration, "name", "") or "").strip()
        if not name or name in by_name:
            return None, "paper-local declaration closure is missing or ambiguous"
        by_name[name] = declaration
    if target not in by_name:
        return None, "derivational auxiliary is absent from the current PaperInterface"
    edge_function = getattr(parser, "_local_declaration_reference_edges", None)
    if not callable(edge_function):
        return None, "source-record local dependency parser is unavailable"

    pending = [target]
    visited: set[str] = set()
    records: list[dict[str, object]] = []
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        declaration = by_name.get(name)
        if declaration is None:
            return None, "paper-local dependency closure lost a resolved declaration"
        visited.add(name)
        try:
            direct_dependencies, ambiguities = edge_function(declaration, by_name)
        except Exception as error:  # noqa: BLE001 - receipt production is fail closed.
            return None, "could not resolve paper-local dependency closure: " + str(error)
        if ambiguities:
            return None, "paper-local dependency closure has an ambiguous local reference"
        if not isinstance(direct_dependencies, list) or any(
            str(name).strip() not in by_name for name in direct_dependencies
        ):
            return None, "paper-local dependency closure has an unresolved local edge"
        records.append(
            _derivational_closure_record_identity(
                parser, declaration, direct_dependencies
            )
        )
        pending.extend(sorted(str(name).strip() for name in direct_dependencies))
    records.sort(key=lambda record: str(record["qualified_declaration"]))
    return records, ""


def derivational_auxiliary_local_closure_sha256(
    records: Collection[Mapping[str, object]],
) -> str:
    """Content-address a complete receipt closure without reordering edges."""

    return _sha256_bytes(_canonical_json(list(records)).encode("utf-8"))


def _derivational_root_path_identity(
    route: Mapping[str, object],
    parent: Mapping[str, object],
    *,
    judgment_key: str,
    association: Mapping[str, object],
) -> dict[str, object]:
    """Pin one raw selected-root route and its source association exactly."""

    return {
        "selected_declaration": str(route.get("selected_declaration") or "").strip(),
        "selected_review_rows": sorted(
            str(row).strip()
            for row in route.get("selected_review_rows") or []
            if str(row).strip()
        ),
        "dependency_chain": [
            str(value).strip()
            for value in route.get("dependency_chain") or []
            if str(value).strip()
        ],
        "semantic_model_row": str(parent.get("row") or "").strip(),
        "semantic_model_judgment_key": judgment_key,
        "reviewed_declaration_identity": parent.get(
            "reviewed_declaration_identity"
        ),
        "source_association_sha256": _sha256_bytes(
            _canonical_json(dict(association)).encode("utf-8")
        ),
        "raw_route_sha256": _sha256_bytes(
            _canonical_json(dict(route)).encode("utf-8")
        ),
    }


def _receipt_source_association(
    parent: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> Mapping[str, object] | None:
    """Return the exact direct association after an authenticated rebind only."""

    association = parent.get("source_statement_association")
    if not isinstance(association, Mapping):
        association = parent.get("semantic_contract_source_association")
    if not isinstance(association, Mapping):
        return None
    return _rebound_association(association, administrative_projection_rebind)


def _derivational_auxiliary_receipt_error(
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    item: Mapping[str, object],
    judgments: Mapping[str, Mapping[str, object]],
    *,
    current_judgment_keys: Collection[str],
    status: object | None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    """Validate a complete, paper-specific theorem-helper closure receipt.

    The ordinary helper lane proves that a theorem has no new visible source
    premise.  A closeout may opt into this stricter receipt to additionally
    pin the complete local proof closure and every selected-root route.  It
    is not a source-map route for the helper itself: its only source credit is
    the separately validated, paper-facing selected root.
    """

    target = str(item.get("declaration") or "").strip()
    receipt = _read_json(folder / "audit" / _DERIVATIONAL_AUXILIARY_RECEIPT_FILE)
    if receipt is None:
        return "no paper-specific derivational-auxiliary closure receipt is present"
    if (
        receipt.get("schema")
        not in {
            _LEGACY_AUXILIARY_RECEIPT_SCHEMA,
            _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
        }
        or receipt.get("kind") != _DERIVATIONAL_AUXILIARY_RECEIPT_KIND
        or str(receipt.get("paper") or "").strip() != paper
        or receipt.get("complete_for_current_raw") is not True
    ):
        return "derivational-auxiliary receipt has the wrong schema, kind, paper, or completeness flag"
    raw_binding_error = _current_raw_terminal_receipt_error(
        folder=folder,
        audit_payload=audit_payload,
        receipt=receipt,
        receipt_kind=_DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
    )
    if raw_binding_error:
        return raw_binding_error.replace("terminal receipt", "derivational-auxiliary receipt")

    # Retain all existing source-condition, independent-selection, and
    # non-circularity checks.  The receipt is a stricter transport, never a
    # substitute for those semantic checks.
    generic_error = _internal_derivational_auxiliary_resolution_error(
        paper,
        folder,
        audit_payload,
        item,
        judgments,
        current_judgment_keys=current_judgment_keys,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    if generic_error:
        return generic_error

    if str(item.get("kind") or "").strip() not in {"theorem", "lemma"}:
        return "derivational-auxiliary receipt permits only theorem or lemma helpers"
    entries = receipt.get("entries")
    if not isinstance(entries, list):
        return "derivational-auxiliary receipt entries are malformed"
    all_candidates = sorted(
        str(candidate.get("declaration") or "").strip()
        for candidate in audit_payload.get(
            "unresolved_reachable_paper_interface_auxiliaries"
        )
        or []
        if isinstance(candidate, Mapping)
        and str(candidate.get("kind") or "").strip() in {"theorem", "lemma"}
        and str(candidate.get("disposition") or "").strip()
        == "missing_source_map_route_or_quarantine"
        and candidate.get("source_map_routes") == []
        and candidate.get("quarantined") is False
        and not str(candidate.get("quarantine_source_reason") or "").strip()
    )
    receipt_names = sorted(
        str(entry.get("declaration") or "").strip()
        for entry in entries
        if isinstance(entry, Mapping)
    )
    if (
        not all_candidates
        or target not in all_candidates
        or receipt_names != all_candidates
        or len(set(receipt_names)) != len(receipt_names)
    ):
        return "derivational-auxiliary receipt does not cover exactly the current unresolved theorem helpers"
    matching = [
        entry
        for entry in entries
        if isinstance(entry, Mapping)
        and str(entry.get("declaration") or "").strip() == target
    ]
    if len(matching) != 1:
        return "derivational-auxiliary receipt does not authorize exactly this helper"
    entry = matching[0]

    interface_path, pin_error = _current_file_pin_error(folder, audit_payload, item)
    if pin_error:
        return pin_error
    assert interface_path is not None
    parser, parser_error = _source_parser()
    if parser is None:
        return parser_error
    declarations = parser.parse_local_declarations(folder.parent.parent, [interface_path])
    by_name = {declaration.name: declaration for declaration in declarations}
    target_declaration = by_name.get(target)
    if target_declaration is None:
        return "derivational auxiliary is absent from the current PaperInterface"
    if (
        target_declaration.kind != str(item.get("kind") or "").strip()
        or target_declaration.source_file.replace("\\", "/")
        != str(item.get("source_file") or "").strip().replace("\\", "/")
        or target_declaration.line != item.get("line")
    ):
        return "derivational auxiliary does not match the frozen raw source coordinate"
    target_identity = _normalized_declaration_identity(parser, target_declaration)
    if entry.get("target_identity") != target_identity:
        return "derivational-auxiliary receipt target declaration/body identity is not current"
    closure, closure_error = derivational_auxiliary_local_closure(
        parser, declarations, target
    )
    if closure_error:
        return closure_error
    assert closure is not None
    if entry.get("local_lexical_closure") != closure:
        return "derivational-auxiliary receipt local proof closure is not current"
    if entry.get("local_lexical_closure_sha256") != derivational_auxiliary_local_closure_sha256(
        closure
    ):
        return "derivational-auxiliary receipt local proof-closure digest is not current"

    semantic_items = audit_payload.get("semantic_model_items")
    transitive = item.get("transitively_referenced_from")
    if not isinstance(semantic_items, list) or not isinstance(transitive, list):
        return "raw audit lacks a semantic-model or selected-root route ledger"
    actual_paths: list[dict[str, object]] = []
    statement_map = _read_json(folder / "audit" / "paper_statement_map.json")
    if statement_map is None:
        return "current paper-statement map is unreadable"
    for route in transitive:
        if not isinstance(route, Mapping):
            return "raw derivational-helper route is malformed"
        parent_qualified = str(route.get("selected_declaration") or "").strip()
        chain = [
            str(value).strip()
            for value in route.get("dependency_chain") or []
            if str(value).strip()
        ]
        selected_rows = {
            str(row).strip()
            for row in route.get("selected_review_rows") or []
            if str(row).strip()
        }
        if (
            not parent_qualified
            or not chain
            or chain[0] != parent_qualified
            or chain[-1] != target
            or not selected_rows
        ):
            return "raw derivational-helper route is not a complete selected-root path"
        parents = [
            candidate
            for candidate in semantic_items
            if isinstance(candidate, Mapping)
            and str(candidate.get("qualified_declaration") or "").strip()
            == parent_qualified
        ]
        if len(parents) != 1:
            return "derivational-helper route root has no unique semantic-model item"
        parent = parents[0]
        parent_row = str(parent.get("row") or "").strip()
        if not parent_row or parent_row not in selected_rows:
            return "derivational-helper route root is not selected through its semantic-model row"
        judgment_key = f"semantic-model::{parent_row}"
        judgment = judgments.get(judgment_key)
        if (
            judgment_key not in current_judgment_keys
            or not isinstance(judgment, Mapping)
            or str(judgment.get("classification") or "").strip()
            != "semantic_model_review"
        ):
            return "derivational-helper route root lacks a current semantic-model judgment"
        parent_declaration = by_name.get(parent_qualified)
        if parent_declaration is None:
            return "derivational-helper route root is absent from the current PaperInterface"
        association_error = _terminal_root_source_association_error(
            parser=parser,
            parent=parent,
            parent_qualified=parent_qualified,
            parent_declaration=parent_declaration,
            statement_map=statement_map,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        if association_error:
            return association_error
        association = _receipt_source_association(
            parent, administrative_projection_rebind
        )
        if association is None:
            return "derivational-helper route root lacks a direct source association"
        actual_paths.append(
            _derivational_root_path_identity(
                route,
                parent,
                judgment_key=judgment_key,
                association=association,
            )
        )
    expected_paths = entry.get("root_paths")
    if not isinstance(expected_paths, list) or not expected_paths:
        return "derivational-auxiliary receipt has no complete selected-root path list"
    if sorted(_canonical_json(path) for path in actual_paths) != sorted(
        _canonical_json(path)
        for path in expected_paths
        if isinstance(path, Mapping)
    ) or len(actual_paths) != len(expected_paths):
        return "derivational-auxiliary receipt omits, adds, or changes a selected-root path"
    return ""


_TRANSPARENT_TERMINAL_REQUIRED_SEMANTIC_FLAGS = (
    "finite_carrier_construct",
    "finite_or_ordered_probability_construct",
    "integration_or_expectation_construct",
    "model_semantics",
    "nontrivial_finite_index_expression_construct",
    "probability_law_construct",
)


def _normalized_declaration_identity(
    parser: ModuleType, declaration: Any
) -> dict[str, object]:
    """Return the exact declaration/body identity emitted by the raw scan."""

    source = str(declaration.source)
    body = parser.declaration_body_text(source)
    return {
        "qualified_declaration": declaration.name,
        "kind": declaration.kind,
        "source_file": declaration.source_file.replace("\\", "/"),
        "line": declaration.line,
        "declaration_sha256": _sha256_bytes(
            parser.normalize_ws(source).encode("utf-8")
        ),
        "body_sha256": _sha256_bytes(
            parser.normalize_ws(body).encode("utf-8")
        ),
        "result_type": parser.normalize_ws(
            parser.declaration_result_type(source)
        ),
    }


def _transparent_terminal_record_identity(record: Mapping[str, object]) -> dict[str, object]:
    """Keep only the semantic body fields a terminal receipt is allowed to pin."""

    result = record.get("result_type")
    result_type = result if isinstance(result, Mapping) else {}
    semantic_flags = record.get("semantic_construct_flags")
    return {
        "qualified_declaration": str(record.get("declaration") or "").strip(),
        "kind": str(record.get("kind") or "").strip(),
        "source_file": str(record.get("source_file") or "").strip().replace("\\", "/"),
        "line": record.get("line"),
        "declaration_sha256": str(record.get("declaration_sha256") or "").strip(),
        "body_sha256": str(record.get("body_sha256") or "").strip(),
        "result_type": str(result_type.get("expanded_type") or "").strip(),
        "body_surface_inspectable": record.get("body_surface_inspectable") is True,
        "semantic_relevant": record.get("semantic_relevant") is True,
        "semantic_construct_flags": semantic_flags
        if isinstance(semantic_flags, Mapping)
        else {},
    }


def _transparent_terminal_target_closure_error(
    terminal_surface: Mapping[str, object], target: str
) -> str:
    """Reject an opaque/ambiguous path reachable from one terminal target.

    ``terminal_term_dependency_surface`` is shared by the whole selected
    theorem result, so it can legitimately contain an unrelated opaque branch.
    This receipt authorizes only one transparent ``abbrev : Prop``.  Rebuild
    the exact local dependency closure from the generated records and reject
    an unexpanded definition only when it is structurally reachable from that
    target.  Declaration strings here are graph coordinates emitted by the
    parser, never semantic evidence or a name-based exemption.
    """

    raw_records = terminal_surface.get("transparent_definitions")
    raw_unexpanded = terminal_surface.get("unexpanded_local_term_heads")
    if not isinstance(raw_records, list) or not isinstance(raw_unexpanded, list):
        return "terminal dependency surface lacks a complete local closure ledger"

    records: dict[str, Mapping[str, object]] = {}
    for record in raw_records:
        if not isinstance(record, Mapping):
            return "terminal dependency surface has a malformed transparent definition"
        name = str(record.get("declaration") or "").strip()
        dependencies = record.get("direct_local_dependencies")
        if (
            not name
            or name in records
            or not isinstance(dependencies, list)
            or any(not isinstance(dependency, str) or not dependency.strip() for dependency in dependencies)
        ):
            return "terminal dependency surface has a malformed local dependency edge"
        records[name] = record
    if target not in records:
        return "terminal dependency surface does not contain the target definition"

    unexpanded_by_parent: dict[str, list[Mapping[str, object]]] = {}
    for item in raw_unexpanded:
        if not isinstance(item, Mapping):
            return "terminal dependency surface has a malformed unexpanded local head"
        parent = str(item.get("referenced_from") or "").strip()
        declaration = str(item.get("declaration") or "").strip()
        if not parent or not declaration:
            return "terminal dependency surface has an unbound unexpanded local head"
        unexpanded_by_parent.setdefault(parent, []).append(item)

    pending = [target]
    reached: set[str] = set()
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        record = records.get(current)
        if record is None:
            return "terminal target closure lost a transparent local definition"
        reached.add(current)
        if record.get("body_surface_inspectable") is not True:
            return "terminal target closure contains a noninspectable definition body"
        dependencies = record.get("direct_local_dependencies")
        assert isinstance(dependencies, list)  # Shape-checked above.
        for dependency in dependencies:
            assert isinstance(dependency, str)
            normalized = dependency.strip()
            if normalized in records:
                pending.append(normalized)
                continue
            if any(
                str(item.get("declaration") or "").strip() == normalized
                for item in unexpanded_by_parent.get(current, [])
            ):
                return "terminal target closure reaches an unexpanded local head"
            return "terminal target closure has an unaccounted local dependency"
        if unexpanded_by_parent.get(current):
            return "terminal target closure reaches an unexpanded local head"
    return ""


def _terminal_route_identity(
    route: Mapping[str, object],
    parent: Mapping[str, object],
    *,
    judgment_key: str,
    transparent_definition_chain: list[str],
) -> dict[str, object]:
    """Bind a receipt to every raw selected-root-to-terminal route exactly."""

    rows = route.get("selected_review_rows")
    chain = route.get("dependency_chain")
    return {
        "selected_declaration": str(route.get("selected_declaration") or "").strip(),
        "selected_review_rows": sorted(
            str(row).strip() for row in rows or [] if str(row).strip()
        ),
        "dependency_chain": [
            str(value).strip() for value in chain or [] if str(value).strip()
        ],
        "semantic_model_row": str(parent.get("row") or "").strip(),
        "semantic_model_judgment_key": judgment_key,
        "raw_route_sha256": _sha256_bytes(
            _canonical_json(route).encode("utf-8")
        ),
        "transparent_definition_chain": transparent_definition_chain,
    }


def _current_raw_terminal_receipt_error(
    *,
    folder: Path,
    audit_payload: Mapping[str, object],
    receipt: Mapping[str, object],
    receipt_kind: str,
) -> str:
    """Validate a receipt's schema-specific current raw dependency binding.

    Legacy schema 1 remains byte/aggregate exact.  Schema 2 validates the
    raw audit's own integrity, then compares only the receipt-specific raw
    dependency manifest.  The latter deliberately excludes unrelated raw
    items and post-audit response summaries while retaining every raw record
    the auxiliary authorization can consume.
    """

    binding = receipt.get("raw_source_record")
    if not isinstance(binding, Mapping):
        return "terminal receipt has no raw source-record binding"
    raw_path = folder / "audit" / "source_record_audit.json"
    try:
        raw_bytes = raw_path.read_bytes()
    except OSError:
        return "current raw source-record audit is unavailable"
    raw_payload = _read_json(raw_path)
    if raw_payload is None:
        return "current raw source-record audit is unreadable"
    raw_integrity = _valid_sha256(raw_payload.get("source_record_audit_sha256"))
    payload_integrity = _valid_sha256(audit_payload.get("source_record_audit_sha256"))
    if not raw_integrity or raw_integrity != payload_integrity:
        return "receipt caller is not bound to the current raw source-record audit"
    raw_prompt = str(raw_payload.get("prompt_version") or "").strip()
    raw_map_sha256 = _valid_sha256(raw_payload.get("paper_statement_map_sha256"))
    raw_interface = raw_payload.get("review_interface_source")
    raw_interface = raw_interface if isinstance(raw_interface, Mapping) else {}
    raw_interface_path = str(raw_interface.get("path") or "").strip().replace(
        "\\", "/"
    )
    raw_interface_sha256 = _valid_sha256(raw_interface.get("sha256"))
    if raw_prompt != SOURCE_RECORD_PROMPT_VERSION:
        return "current raw source-record audit is not the v10 semantic surface"
    if not (
        raw_integrity
        and raw_map_sha256
        and raw_interface_path
        and raw_interface_sha256
    ):
        return "current raw source-record audit has an incomplete identity binding"
    receipt_schema = receipt.get("schema")
    if receipt_schema == _LEGACY_AUXILIARY_RECEIPT_SCHEMA:
        expected = {
            "source_record_audit_sha256": raw_integrity,
            "file_sha256": _sha256_bytes(raw_bytes),
            "prompt_version": raw_prompt,
            "paper_statement_map_sha256": raw_map_sha256,
            "paper_interface_sha256": raw_interface_sha256,
        }
        actual = {
            key: (
                _valid_sha256(binding.get(key))
                if key.endswith("sha256")
                else str(binding.get(key) or "").strip()
            )
            for key in expected
        }
        if actual != expected:
            return "terminal receipt raw source-record binding differs from current bytes"
        return ""

    if receipt_schema not in {
        _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
        _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
    }:
        return "terminal receipt has an unsupported schema"
    raw_receipt_error = source_record_audit_receipt_error(raw_payload)
    if raw_receipt_error:
        return "current raw source-record audit integrity is invalid: " + raw_receipt_error
    expected, expected_error = auxiliary_receipt_semantic_raw_binding(
        audit_payload, receipt_kind=receipt_kind
    )
    if expected is None:
        return "current raw auxiliary dependency manifest is unavailable: " + expected_error
    # The caller may carry only the authenticated routing-ledger augmentation;
    # its base source/map/interface identities must still be the canonical raw
    # snapshot read above.  This permits a narrow supplement without trusting
    # arbitrary caller-supplied source evidence.
    interface = expected.get("paper_interface")
    if (
        str(expected.get("paper") or "").strip()
        != str(raw_payload.get("paper") or "").strip()
        or str(expected.get("prompt_version") or "").strip() != raw_prompt
        or str(expected.get("paper_statement_map_sha256") or "").strip()
        != raw_map_sha256
        or not isinstance(interface, Mapping)
        or str(interface.get("path") or "").strip().replace("\\", "/")
        != raw_interface_path
        or _valid_sha256(interface.get("sha256")) != raw_interface_sha256
    ):
        return "receipt caller source/map/interface identities differ from canonical raw audit"
    if dict(binding) != expected:
        return "terminal receipt semantic raw dependency manifest is not current"
    return ""


def _terminal_root_source_association_error(
    *,
    parser: ModuleType,
    parent: Mapping[str, object],
    parent_qualified: str,
    parent_declaration: Any,
    statement_map: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    """Reuse the direct-source checks without treating a terminal alias as a route."""

    parent_identity = parent.get("reviewed_declaration_identity")
    association = parent.get("source_statement_association")
    if not isinstance(association, Mapping):
        association = parent.get("semantic_contract_source_association")
    if not isinstance(parent_identity, Mapping) or not isinstance(association, Mapping):
        return "terminal route root lacks a direct source association"
    association = _rebound_association(association, administrative_projection_rebind)
    if association.get("schema") == 2 and association.get("role") == "direct_source_route":
        parent_hash = _valid_sha256(parent_identity.get("declaration_sha256"))
        if (
            not parent_hash
            or parent_identity.get("qualified_declaration") != parent_qualified
            or _sha256_bytes(parent_declaration.source.encode("utf-8")) != parent_hash
            or association.get("role") != "direct_source_route"
            or association.get("reviewed_declaration_identity") != parent_identity
            or not _valid_sha256(association.get("semantic_association_sha256"))
        ):
            return "terminal route root direct source association is not pinned to its current declaration"
        return _source_identity_error(
            parser, association, statement_map, administrative_projection_rebind
        )
    if association.get("schema") == 2 and str(association.get("role") or "").strip() in {
        "direct_evidence",
        "transparent_spec",
    }:
        # A semantic-contract association can be stored once for its exact
        # direct/Spec pair while a selected row is either member.  The parent
        # row must still be one of the source map's two explicit endpoints;
        # do not recover a route from a declaration suffix or an alias name.
        role = str(association.get("role") or "").strip()
        association_identity = association.get("reviewed_declaration_identity")
        signature = association.get("reviewed_elaborated_signature_identity")
        paired = str(association.get("paired_qualified_declaration") or "").strip()
        current_parent_hash = _sha256_bytes(parent_declaration.source.encode("utf-8"))
        identities = association.get("source_item_identities")
        if (
            association.get("review_scope") != "individual_row_only"
            or not isinstance(association_identity, Mapping)
            or not isinstance(signature, Mapping)
            or not _valid_sha256(association.get("semantic_association_sha256"))
            or not isinstance(identities, list)
            or not identities
        ):
            return "terminal route root semantic-contract association is not pinned to its current declaration"
        expected_pairs: set[tuple[str, str]] = set()
        for source_identity in identities:
            if not isinstance(source_identity, Mapping):
                return "terminal route root semantic-contract association has a malformed source identity"
            contract = source_identity.get("semantic_contract")
            if not isinstance(contract, Mapping):
                return "terminal route root semantic-contract association has no source contract"
            evidence = str(contract.get("evidence_declaration") or "").strip()
            spec = str(contract.get("spec_declaration") or "").strip()
            if not evidence or not spec or evidence == spec:
                return "terminal route root semantic-contract source pair is malformed"
            expected_pairs.add((evidence, spec))
        if len(expected_pairs) != 1:
            return "terminal route root semantic-contract association mixes source endpoint pairs"
        evidence, spec = next(iter(expected_pairs))
        expected_reviewed = evidence if role == "direct_evidence" else spec
        expected_paired = spec if role == "direct_evidence" else evidence
        parent_reviewed = str(parent_identity.get("qualified_declaration") or "").strip()
        parent_reviewed_hash = _valid_sha256(parent_identity.get("declaration_sha256"))
        association_reviewed = str(
            association_identity.get("qualified_declaration") or ""
        ).strip()
        association_reviewed_hash = _valid_sha256(
            association_identity.get("declaration_sha256")
        )
        if (
            association_reviewed != expected_reviewed
            or signature.get("qualified_declaration") != expected_reviewed
            or paired != expected_paired
            or parent_qualified not in {evidence, spec}
            or parent_reviewed not in {evidence, spec}
            or not parent_reviewed_hash
            or not association_reviewed_hash
            # The selected root may be a direct row whose semantic review
            # surface is its exact Spec companion.  At least one of the two
            # raw identities must therefore pin the physically selected
            # declaration; accepting neither would detach the receipt from
            # the actual route root.
            or (
                parent_reviewed != parent_qualified
                and association_reviewed != parent_qualified
            )
            or (
                parent_reviewed == parent_qualified
                and parent_reviewed_hash != current_parent_hash
            )
            or (
                association_reviewed == parent_qualified
                and association_reviewed_hash != current_parent_hash
            )
        ):
            return "terminal route root semantic-contract association does not match its exact source endpoint pair"
        return _source_identity_error(
            parser, association, statement_map, administrative_projection_rebind
        )
    if association.get("schema") == 1:
        association_identity = association.get("reviewed_declaration_identity")
        if not isinstance(association_identity, Mapping):
            return "terminal route root schema-1 association lacks its evidence declaration identity"
        paired = str(association.get("paired_qualified_declaration") or "").strip()
        parent_hash = _valid_sha256(parent_identity.get("declaration_sha256"))
        current_parent_hash = _sha256_bytes(parent_declaration.source.encode("utf-8"))
        # Schema-1 selected roots may be the evidence declaration or its exact
        # Spec companion.  Either way, its raw declaration identity must still
        # match the parsed current source; a companion spelling alone is never
        # authority for a terminal receipt.
        association_hash = _valid_sha256(association_identity.get("declaration_sha256"))
        parent_is_evidence = parent_identity == association_identity
        parent_is_companion = (
            parent_identity.get("qualified_declaration") == paired
            and bool(paired)
            and bool(parent_hash)
        )
        selected_root_is_evidence = (
            association_identity.get("qualified_declaration") == parent_qualified
            and association_hash == current_parent_hash
        )
        selected_root_is_reviewed_surface = (
            parent_identity.get("qualified_declaration") == parent_qualified
            and parent_hash == current_parent_hash
        )
        if (
            (parent_is_evidence and parent_hash != current_parent_hash)
            or (not parent_is_evidence and not parent_is_companion)
            or not (selected_root_is_evidence or selected_root_is_reviewed_surface)
        ):
            return "terminal route root schema-1 pairing is not pinned to evidence or companion"
        return _schema1_direct_source_association_error(
            parser,
            association,
            statement_map,
            root=parent_qualified,
            root_declaration=parent_declaration,
        )
    return "terminal route root source association has an unsupported schema"


def _transparent_terminal_surface_resolution_error(
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    item: Mapping[str, object],
    judgments: Mapping[str, Mapping[str, object]],
    *,
    current_judgment_keys: Collection[str],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> str:
    """Validate one explicitly reviewed transparent terminal surface.

    This is intentionally *not* a generic ``def``/``abbrev`` exemption.  A
    receipt can authorize only its one exact declaration after proving that its
    full body was found in every raw selected-root terminal scan and that each
    such root retains a current semantic-model review.
    """

    target = str(item.get("declaration") or "").strip()
    if not target or "." not in target:
        return "terminal receipt candidate has no fully-qualified declaration identity"
    receipt = _read_json(folder / "audit" / _TRANSPARENT_TERMINAL_RECEIPT_FILE)
    if receipt is None:
        return "no paper-specific transparent-terminal receipt is present"
    if (
        receipt.get("schema")
        not in {
            _LEGACY_AUXILIARY_RECEIPT_SCHEMA,
            _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
        }
        or receipt.get("kind") != _TRANSPARENT_TERMINAL_RECEIPT_KIND
        or str(receipt.get("paper") or "").strip() != paper
    ):
        return "transparent-terminal receipt has the wrong schema, kind, or paper"
    raw_binding_error = _current_raw_terminal_receipt_error(
        folder=folder,
        audit_payload=audit_payload,
        receipt=receipt,
        receipt_kind=_TRANSPARENT_TERMINAL_RECEIPT_KIND,
    )
    if raw_binding_error:
        return raw_binding_error
    if (
        str(item.get("disposition") or "").strip()
        != "missing_source_map_route_or_quarantine"
        or item.get("source_map_routes") != []
        or item.get("quarantined") is not False
        or str(item.get("quarantine_source_reason") or "").strip()
    ):
        return "raw terminal candidate is not the narrow unresolved-helper form"

    entries = receipt.get("entries")
    if not isinstance(entries, list):
        return "transparent-terminal receipt entries are malformed"
    matching_entries = [
        entry
        for entry in entries
        if isinstance(entry, Mapping)
        and str(entry.get("declaration") or "").strip() == target
    ]
    if len(matching_entries) != 1:
        return "terminal receipt does not authorize exactly this declaration"
    entry = matching_entries[0]

    interface_path, pin_error = _current_file_pin_error(folder, audit_payload, item)
    if pin_error:
        return pin_error
    assert interface_path is not None
    parser, parser_error = _source_parser()
    if parser is None:
        return parser_error
    statement_map = _read_json(folder / "audit" / "paper_statement_map.json")
    if statement_map is None:
        return "current paper-statement map is unreadable"
    if _exact_string_present(statement_map, target):
        return "terminal candidate is independently source-routed in the current source map"
    declarations = parser.parse_local_declarations(folder.parent.parent, [interface_path])
    by_name: dict[str, list[Any]] = {}
    for declaration in declarations:
        by_name.setdefault(declaration.name, []).append(declaration)
    raw_available = audit_payload.get("available_local_lean_declarations")
    if not isinstance(raw_available, list):
        return "raw audit lacks its local declaration completion ledger"
    if sum(str(value).strip() == target for value in raw_available) != 1:
        return "terminal candidate does not have one exact raw completion"
    target_declarations = by_name.get(target, [])
    if len(target_declarations) != 1:
        return "current PaperInterface does not contain exactly one terminal declaration"
    target_declaration = target_declarations[0]
    if (
        target_declaration.kind != "abbrev"
        or str(item.get("kind") or "").strip() != "abbrev"
        or target_declaration.source_file.replace("\\", "/")
        != str(item.get("source_file") or "").strip().replace("\\", "/")
        or target_declaration.line != item.get("line")
    ):
        return "terminal receipt permits only its exact raw abbrev coordinate"
    target_identity = _normalized_declaration_identity(parser, target_declaration)
    expected_target = entry.get("target_identity")
    if not isinstance(expected_target, Mapping) or dict(expected_target) != target_identity:
        return "terminal receipt target declaration/body identity is not current"
    if target_identity["result_type"] != "Prop":
        return "terminal receipt target is not an explicit proposition surface"

    configured_declarations = {
        str(row.get("qualified_declaration") or "").strip()
        for row in audit_payload.get("configured_review_rows") or []
        if isinstance(row, Mapping)
    }
    if target in configured_declarations:
        return "terminal candidate is independently selected as a review row"
    raw_dependencies = [
        dependency
        for dependency in audit_payload.get("reachable_paper_interface_auxiliary_dependencies")
        or []
        if isinstance(dependency, Mapping)
        and str(dependency.get("declaration") or "").strip() == target
    ]
    if len(raw_dependencies) != 1 or _canonical_json(raw_dependencies[0]) != _canonical_json(item):
        return "raw dependency ledger does not contain one exact terminal routing item"
    transitive = item.get("transitively_referenced_from")
    if not isinstance(transitive, list) or not transitive:
        return "raw dependency ledger has no selected-root route to terminal surface"

    expected_terminal = entry.get("transparent_definition")
    if not isinstance(expected_terminal, Mapping):
        return "terminal receipt has no transparent-definition identity"
    expected_paths = entry.get("root_paths")
    if not isinstance(expected_paths, list) or not expected_paths:
        return "terminal receipt has no complete selected-root path list"
    semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        return "raw audit has no semantic-model item ledger"
    actual_paths: list[dict[str, object]] = []
    for route in transitive:
        if not isinstance(route, Mapping):
            return "raw terminal route is malformed"
        parent_qualified = str(route.get("selected_declaration") or "").strip()
        chain = [
            str(value).strip()
            for value in route.get("dependency_chain") or []
            if str(value).strip()
        ]
        selected_rows = {
            str(row).strip()
            for row in route.get("selected_review_rows") or []
            if str(row).strip()
        }
        if (
            not parent_qualified
            or not chain
            or chain[0] != parent_qualified
            or chain[-1] != target
            or not selected_rows
        ):
            return "raw terminal route is not a complete selected-root-to-terminal chain"
        parents = [
            candidate
            for candidate in semantic_items
            if isinstance(candidate, Mapping)
            and str(candidate.get("qualified_declaration") or "").strip()
            == parent_qualified
        ]
        if len(parents) != 1:
            return "terminal route root has no unique semantic-model item"
        parent = parents[0]
        parent_row = str(parent.get("row") or "").strip()
        if not parent_row or parent_row not in selected_rows:
            return "terminal route root is not selected through its semantic-model row"
        judgment_key = f"semantic-model::{parent_row}"
        judgment = judgments.get(judgment_key)
        if (
            judgment_key not in current_judgment_keys
            or not isinstance(judgment, Mapping)
            or str(judgment.get("classification") or "").strip()
            != "semantic_model_review"
        ):
            return "terminal route root lacks a current semantic-model judgment"
        parent_declarations = by_name.get(parent_qualified, [])
        if len(parent_declarations) != 1:
            return "terminal route root is absent or ambiguous in current PaperInterface"
        association_error = _terminal_root_source_association_error(
            parser=parser,
            parent=parent,
            parent_qualified=parent_qualified,
            parent_declaration=parent_declarations[0],
            statement_map=statement_map,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        if association_error:
            return association_error
        expanded = parent.get("expanded_lean_surface")
        terminal_surface = (
            expanded.get("terminal_term_dependency_surface")
            if isinstance(expanded, Mapping)
            else None
        )
        if not isinstance(terminal_surface, Mapping):
            return "terminal route root has no terminal dependency scan"
        if (
            terminal_surface.get("scan_complete") is not True
            or terminal_surface.get("incomplete_reasons") not in ([], None)
        ):
            return "terminal route root does not have a complete terminal dependency scan"
        target_closure_error = _transparent_terminal_target_closure_error(
            terminal_surface, target
        )
        if target_closure_error:
            return "terminal route root " + target_closure_error
        matches = [
            record
            for record in terminal_surface.get("transparent_definitions") or []
            if isinstance(record, Mapping)
            and str(record.get("declaration") or "").strip() == target
        ]
        if len(matches) != 1:
            return "terminal route root does not expose exactly one transparent terminal body"
        record = matches[0]
        actual_terminal = _transparent_terminal_record_identity(record)
        if actual_terminal != dict(expected_terminal):
            return "terminal receipt transparent-definition body identity is not current"
        if (
            actual_terminal["kind"] != "abbrev"
            or actual_terminal["result_type"] != "Prop"
            or actual_terminal["body_surface_inspectable"] is not True
            or actual_terminal["semantic_relevant"] is not True
        ):
            return "terminal receipt body is not an inspectable semantic proposition"
        flags = actual_terminal["semantic_construct_flags"]
        if (
            not isinstance(flags, Mapping)
            or any(flags.get(flag) is not True for flag in _TRANSPARENT_TERMINAL_REQUIRED_SEMANTIC_FLAGS)
        ):
            return "terminal receipt body is not a fully expanded model/payoff surface"
        transparent_chain = [
            str(value).strip()
            for value in record.get("dependency_chain") or []
            if str(value).strip()
        ]
        if not transparent_chain or transparent_chain[-1] != target:
            return "terminal receipt body lacks its complete transparent dependency chain"
        actual_paths.append(
            _terminal_route_identity(
                route,
                parent,
                judgment_key=judgment_key,
                transparent_definition_chain=transparent_chain,
            )
        )
    if sorted(_canonical_json(value) for value in actual_paths) != sorted(
        _canonical_json(value)
        for value in expected_paths
        if isinstance(value, Mapping)
    ) or len(actual_paths) != len(expected_paths):
        return "terminal receipt omits, adds, or changes a selected-root path"
    return ""


def internal_derivational_auxiliary_resolution(
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    item: Mapping[str, object],
    judgments: Mapping[str, Mapping[str, object]],
    *,
    current_judgment_keys: Collection[str],
    status: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
) -> InternalDerivationalAuxiliaryResolution:
    """Return one immutable-input routing decision for both audit consumers."""

    declaration = str(item.get("declaration") or "").strip()
    terminal_reason = _transparent_terminal_surface_resolution_error(
        paper,
        folder,
        audit_payload,
        item,
        judgments,
        current_judgment_keys=current_judgment_keys,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    if not terminal_reason:
        return InternalDerivationalAuxiliaryResolution(
            declaration=declaration,
            accepted=True,
            reason="",
        )
    terminal_receipt = _read_json(
        folder / "audit" / _TRANSPARENT_TERMINAL_RECEIPT_FILE
    )
    terminal_entry_exists = bool(
        isinstance(terminal_receipt, Mapping)
        and isinstance(terminal_receipt.get("entries"), list)
        and any(
            isinstance(entry, Mapping)
            and str(entry.get("declaration") or "").strip() == declaration
            for entry in terminal_receipt["entries"]
        )
    )
    # When a receipt explicitly claims this exact terminal surface, expose its
    # fail-closed reason rather than masking it with the ordinary theorem/lemma
    # helper lane.  An unrelated abbrev still receives no receipt authority.
    if terminal_entry_exists:
        return InternalDerivationalAuxiliaryResolution(
            declaration=declaration,
            accepted=False,
            reason="transparent-terminal receipt rejected: " + terminal_reason,
        )

    # A paper can opt into a stricter closeout receipt for every unresolved
    # theorem/lemma helper.  Once such a receipt is present, an entry may not
    # silently fall back to the generic lane: the receipt must cover the exact
    # current raw helper set and pin this proof body, local closure, and root
    # route.  Papers without this opt-in retain the older narrow resolver so
    # existing audited work is not invalidated merely by adding the procedure.
    derivational_receipt = _read_json(
        folder / "audit" / _DERIVATIONAL_AUXILIARY_RECEIPT_FILE
    )
    if isinstance(derivational_receipt, Mapping) and str(
        derivational_receipt.get("paper") or ""
    ).strip() == paper and str(item.get("kind") or "").strip() in {
        "theorem",
        "lemma",
    }:
        derivational_reason = _derivational_auxiliary_receipt_error(
            paper,
            folder,
            audit_payload,
            item,
            judgments,
            current_judgment_keys=current_judgment_keys,
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        return InternalDerivationalAuxiliaryResolution(
            declaration=declaration,
            accepted=not derivational_reason,
            reason=derivational_reason,
        )
    reason = _internal_derivational_auxiliary_resolution_error(
        paper,
        folder,
        audit_payload,
        item,
        judgments,
        current_judgment_keys=current_judgment_keys,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    return InternalDerivationalAuxiliaryResolution(
        declaration=declaration,
        accepted=not reason,
        reason=reason,
    )


def internal_derivational_auxiliary_resolution_error(
    paper: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    item: Mapping[str, object],
    judgments: Mapping[str, Mapping[str, object]],
    *,
    current_judgment_keys: Collection[str],
    status: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
) -> str:
    """Compatibility wrapper for callers that need only the rejection text."""

    return internal_derivational_auxiliary_resolution(
        paper,
        folder,
        audit_payload,
        item,
        judgments,
        current_judgment_keys=current_judgment_keys,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
    ).reason
