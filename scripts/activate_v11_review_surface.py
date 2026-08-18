#!/usr/bin/env python3
"""Select a prepared v11 PaperInterface surface in a paper's status file.

The command makes the upgrade explicit and intentionally does not certify the
paper.  Once selected, the normal closeout gate requires current raw
source-to-Spec, paper-prerequisite, library, and atom-correspondence evidence.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
V11_PROMPT = "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2"


class ActivationError(ValueError):
    """Raised when the prepared semantic surface is not well formed."""


def load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ActivationError(f"could not read {label}: {error}") from error
    if not isinstance(value, dict):
        raise ActivationError(f"{label} must be a JSON object")
    return value


def v11_contract_specs(
    source_map: Mapping[str, Any], *, namespace: str
) -> tuple[list[str], dict[str, str]]:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise ActivationError("source map has no items object")
    prefix = namespace + ".PaperInterface."
    specs: list[str] = []
    proof_endpoints: dict[str, str] = {}
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, Mapping):
            continue
        spec = str(contract.get("spec_declaration") or "").strip()
        if not spec.startswith(prefix) or not spec.endswith("Spec"):
            raise ActivationError(
                "every selected semantic contract must name a PaperInterface `...Spec`: "
                + spec
            )
        short_spec = spec[len(prefix) :]
        evidence = str(contract.get("evidence_declaration") or "").strip()
        if evidence:
            if not evidence.startswith(prefix):
                raise ActivationError(
                    "every selected semantic contract must name a PaperInterface proof "
                    "endpoint: " + evidence
                )
            short_evidence = evidence[len(prefix) :]
        else:
            # Backward-compatible handling for a pre-v11 fixture; real v11
            # maps always bind an explicit theorem endpoint.
            short_evidence = short_spec[: -len("Spec")]
        specs.append(short_spec)
        proof_endpoints[short_spec] = short_evidence
    if not specs:
        raise ActivationError("source map has no v11 semantic contracts")
    if len(specs) != len(set(specs)):
        raise ActivationError("one semantic Spec is routed by multiple source items")
    return specs, proof_endpoints


def activate(status: dict[str, Any], source_map: Mapping[str, Any], *, paper: str) -> dict[str, Any]:
    namespace = str(source_map.get("paper") or "").strip()
    if namespace != paper:
        raise ActivationError("source map paper does not match --paper")
    specs, proof_endpoints = v11_contract_specs(source_map, namespace=namespace)
    result = dict(status)
    surface = dict(result.get("review_surface") or {})
    surface["source_file"] = f"papers/{paper}/PaperInterface.lean"
    surface.pop("human_source_file", None)
    surface["include_names"] = specs
    surface["proposition_spec_proofs"] = proof_endpoints
    surface["require_v11_raw_source_spec_screening"] = True
    surface["require_source_spec_correspondence"] = True
    statement_review = dict(surface.get("llm_statement_review") or {})
    statement_review["required_prompt_version"] = V11_PROMPT
    statement_review["policy"] = (
        "For every selected source claim, compare only its exact byte-pinned raw "
        "source-anchor bundle and Lean's expanded transparent `...Spec : Prop` "
        "target. The paired proof endpoint receives separate Lean-Meta proof credit; "
        "a name, paraphrase, wrapper, or prior aggregate receipt is not a semantic "
        "match. Review every retained paper-local prerequisite and every material "
        "library prerequisite before the dependent claim."
    )
    surface["llm_statement_review"] = statement_review
    result["review_surface"] = surface
    # A new v11 claim surface is a new human-review queue.  Saved review
    # counts are displayed on the website, so retaining a legacy denominator
    # (or carry-forwarding completed rows) would falsely report review of
    # different source-to-Spec targets.
    result["human_review"] = {
        "reviewed_rows": 0,
        "total_rows": len(specs),
        "stale_rows": 0,
        "mismatch_rows": 0,
        "uncertain_rows": 0,
        "source": "v11 PaperInterface claim surface; human entries are recorded after direct review",
    }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper_dir = ROOT / "papers" / args.paper
    try:
        status = load_object(paper_dir / "status.json", label="status.json")
        source_map = load_object(
            paper_dir / "audit" / "paper_statement_map.json", label="source map"
        )
        activated = activate(status, source_map, paper=args.paper)
    except ActivationError as error:
        print(f"v11 review-surface activation refused: {error}", file=sys.stderr)
        return 1
    count = len(activated["review_surface"]["include_names"])
    if not args.write:
        print(f"{args.paper}: would select {count} v11 semantic claim Specs; rerun with --write")
        return 0
    path = paper_dir / "status.json"
    path.write_text(json.dumps(activated, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{args.paper}: selected {count} v11 semantic claim Specs in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
