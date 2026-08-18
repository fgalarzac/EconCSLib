#!/usr/bin/env python3
"""Adversarial regressions for the v11 raw semantic-review closeout gates."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

import audit_evidence_integrity as integrity  # noqa: E402
import reissue_library_semantic_review as library_reissue  # noqa: E402
import reissue_v11_raw_source_spec_screening as reissue  # noqa: E402
import review_dashboard  # noqa: E402
from scripts import review_dashboard_packet  # noqa: E402
from lean_signature_manifest import (  # noqa: E402
    DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL,
    TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL,
    TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL,
    parse_direct_library_dependency_surface_output,
    parse_transparent_paper_declaration_display_output,
    parse_transparent_library_declaration_display_output,
)


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


class _Dashboard:
    def __init__(self, *, kind: str = "def") -> None:
        self.kind = kind

    def parse_review_source_declarations(self, _path: Path) -> list[tuple[object, ...]]:
        return [
            (
                self.kind,
                "SourceSpec",
                "Fixture.SourceSpec",
                "def SourceSpec : Prop := True",
                None,
                1,
                Path("PaperInterface.lean"),
            )
        ]

    @staticmethod
    def source_semantic_input_bundle(
        _record: object, *, require_context_roles: bool
    ) -> tuple[str, str, str]:
        assert require_context_roles
        return "verbatim source", digest("verbatim source"), ""

    @staticmethod
    def source_anchor_file_error(_folder: Path, _record: object) -> str:
        return ""

    @staticmethod
    def statement_digest(value: str) -> str:
        return digest(value)

    @staticmethod
    def human_review_library_prerequisites(
        _folder: Path, _claims: object
    ) -> list[object]:
        return []


class V11RawSemanticReviewGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.item = {
            "semantic_contract": {
                "spec_declaration": "Fixture.SourceSpec",
                "evidence_declaration": "Fixture.SourceProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        }

    def _screening(self, *, judgment: str = "matches") -> dict[str, object]:
        source = "verbatim source"
        lean = "True"
        return {
            "schema": 2,
            "paper": "Fixture",
            "prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2",
            "validator": "independent semantic reviewer",
            "validated_at": "2026-08-17T00:00:00Z",
            "items": {
                "Fixture.SourceSpec": {
                    "judgment": judgment,
                    "reason": "The raw source assertion and full proposition agree.",
                    "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                    "source_input_bundle_sha256": digest(source),
                    "paper_statement_sha256": digest(source),
                    "lean_target_protocol": "lean_transparent_paper_expansion_v1",
                    "semantic_target_declaration": "Fixture.SourceSpec",
                    "lean_expanded_statement_sha256": digest(lean),
                    "paper_interface_sha256": digest(""),
                }
            },
        }

    def _findings(
        self,
        screening: dict[str, object],
        *,
        dashboard: _Dashboard | None = None,
        proof_items: dict[str, object] | None = None,
        paper_prerequisites: list[dict[str, object]] | None = None,
    ) -> list[object]:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest(""),
                            "items": {
                                "Fixture.SourceSpec": {
                                    "spec_source_sha256": digest(
                                        "def SourceSpec : Prop := True"
                                    ),
                                    "direct_library_declarations": [],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "v11_raw_source_spec_screening.json").write_text(
                json.dumps(screening), encoding="utf-8"
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=(proof_items or {"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_source_scope_dashboard_module",
                return_value=dashboard or _Dashboard(),
            ), mock.patch.object(
                review_dashboard_packet,
                "semantic_expanded_spec_targets",
                return_value={
                    "Fixture.SourceSpec": {
                        "display_sha256": digest("True"),
                        "paper_interface_sha256": digest(""),
                    }
                },
            ), mock.patch.object(
                review_dashboard_packet,
                "paper_semantic_prerequisites",
                return_value=paper_prerequisites or [],
            ):
                return integrity.v11_raw_source_spec_screening_findings(
                    folder, "formalized"
                )

    def test_current_raw_source_and_direct_spec_pass(self) -> None:
        self.assertEqual(self._findings(self._screening()), [])

    def test_current_v11_lane_supersedes_a_historical_v10_record(self) -> None:
        """The selected direct lane needs no manufactured legacy reissue."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            # This is intentionally stale/malformed.  A current direct lane
            # is what must decide whether it can still block closeout.
            (folder / "audit" / "source_record_audit.json").write_text(
                "{}", encoding="utf-8"
            )
            with mock.patch.object(
                integrity,
                "v11_direct_semantic_review_state",
                return_value=(True, ""),
            ):
                findings = integrity.check_source_record_judgments(
                    folder, "formalized"
                )
        self.assertEqual(findings, [])

    def test_incomplete_v11_lane_does_not_suppress_legacy_currentness(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            (folder / "audit" / "source_record_audit.json").write_text(
                "{}", encoding="utf-8"
            )
            with mock.patch.object(
                integrity,
                "v11_direct_semantic_review_state",
                return_value=(False, "missing raw source/Spec row"),
            ):
                findings = integrity.check_source_record_judgments(
                    folder, "formalized"
                )
        self.assertTrue(findings)

    def test_mismatch_and_stale_hash_block_closeout(self) -> None:
        screening = self._screening(judgment="mismatch")
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["lean_expanded_statement_sha256"] = digest("old statement")
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(any("stale for Lean's current expanded semantic target" in message for message in messages))
        self.assertTrue(any("judgment is `mismatch`" in message for message in messages))

    def test_approved_corrected_target_requires_an_explicit_pinned_record(self) -> None:
        screening = self._screening(judgment="matches_approved_corrected_target")
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(
            any("lacks a corrected-source map record" in message for message in messages)
        )

        corrected = dict(self.item)
        corrected["coverage_status"] = "corrected_source_statement"
        corrected["corrected_target"] = {
            "archival_equivalence_claimed": False,
            "corrected_target_sha256": "a" * 64,
        }
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["corrected_target_protocol"] = "approved_corrected_target_v1"
        row["corrected_target_sha256"] = "a" * 64
        self.assertEqual(
            self._findings(screening, proof_items={"source_claim": corrected}), []
        )

    def test_corrected_source_statement_cannot_be_relabelled_as_matches(self) -> None:
        corrected = dict(self.item)
        corrected["coverage_status"] = "corrected_source_statement"
        corrected["corrected_target"] = {
            "archival_equivalence_claimed": False,
            "corrected_target_sha256": "a" * 64,
        }
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(judgment="matches"),
                proof_items={"source_claim": corrected},
            )
        ]
        self.assertTrue(
            any("corrected_source_statement requires" in message for message in messages)
        )

    def test_wrapper_or_proof_endpoint_cannot_be_screened_as_spec(self) -> None:
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(), dashboard=_Dashboard(kind="theorem")
            )
        ]
        self.assertTrue(any("explicit `def ...Spec : Prop :=`" in message for message in messages))

    def test_two_source_claims_cannot_share_one_spec(self) -> None:
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(),
                proof_items={"first": self.item, "second": self.item},
            )
        ]
        self.assertTrue(any("one semantic Spec per source claim" in message for message in messages))

    def test_paper_prerequisite_and_its_library_cannot_bypass_review(self) -> None:
        """A retained paper model and its library meaning are both closeout gates."""

        class PrerequisiteLibraryDashboard(_Dashboard):
            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path, claims: object
            ) -> list[dict[str, object]]:
                for claim in claims:  # type: ignore[union-attr]
                    names = claim.get("library_review_owner_declarations", ())
                    if "EconCSLib.Example.onlyThroughPaperModel" in names:
                        return [
                            {
                                "lean_name": "EconCSLib.Example.onlyThroughPaperModel",
                                "semantic_current": False,
                                "semantic_judgment": "not recorded",
                                "semantic_status": "no source-to-library review",
                            }
                        ]
                return []

        messages = [
            finding.message
            for finding in self._findings(
                self._screening(),
                dashboard=PrerequisiteLibraryDashboard(),
                paper_prerequisites=[
                    {
                        "lean_name": "Fixture.SourceModel",
                        "paper_declaration_source": "def SourceModel := True",
                        "paper_semantic_target": "True",
                        "semantic_current": False,
                        "semantic_judgment": "matches",
                        "direct_library_declarations": [
                            "EconCSLib.Example.onlyThroughPaperModel"
                        ],
                    }
                ],
            )
        ]
        self.assertTrue(
            any("paper-local semantic prerequisite has no current raw-source review" in m for m in messages)
        )
        self.assertTrue(
            any("Lean-expanded semantic target has no current raw-source library review" in m for m in messages)
        )

    def test_reissue_writer_refuses_a_wrapper_target(self) -> None:
        with mock.patch.object(
            reissue.review_dashboard,
            "source_semantic_input_bundle",
            return_value=("verbatim source", digest("verbatim source"), ""),
        ), mock.patch.object(
            reissue.review_dashboard,
            "source_anchor_file_error",
            return_value="",
        ):
            with self.assertRaisesRegex(reissue.ScreeningReissueError, "explicit `def"):
                reissue.reissued_row(
                    "Fixture.SourceSpec",
                    paper_dir=Path("."),
                    record={},
                    interface_item={
                        "kind": "theorem",
                        "lean_statement": "theorem SourceSpec : True := by trivial",
                    },
                    semantic_target={
                        "display": "True",
                        "display_sha256": digest("True"),
                        "paper_interface_sha256": digest(""),
                    },
                    decision={"judgment": "matches", "reason": "not used"},
                )

    def test_unregistered_direct_library_name_is_visible(self) -> None:
        names = review_dashboard.direct_material_library_declaration_names(
            [
                {
                    "interface_source": (
                        "def SourceSpec : Prop := EconCSLib.NewLibrary.claim"
                    )
                }
            ]
        )
        self.assertEqual(names, {"EconCSLib.NewLibrary.claim"})

    def test_lean_direct_dependency_transport_rejects_partial_or_unsorted_output(
        self,
    ) -> None:
        """Python accepts only Lean's complete, canonical direct inventory."""

        requested = ["Fixture.first", "Fixture.second"]
        valid = (
            DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL
            + json.dumps(
                {
                    "schema": "1",
                    "roots": [
                        {
                            "declaration": "Fixture.first",
                            "direct_library_declarations": [
                                "EconCSLib.A.first",
                            ],
                        },
                        {
                            "declaration": "Fixture.second",
                            "direct_library_declarations": [],
                        },
                    ],
                }
            )
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(valid, requested),
            {
                "Fixture.first": ("EconCSLib.A.first",),
                "Fixture.second": (),
            },
        )
        unsorted = valid.replace(
            '["EconCSLib.A.first"]',
            '["EconCSLib.Z.last", "EconCSLib.A.first"]',
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(unsorted, requested), {}
        )
        partial = valid.replace(
            ', {"declaration": "Fixture.second", "direct_library_declarations": []}',
            '',
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(partial, requested), {}
        )

    def test_lean_library_target_transport_rejects_hidden_self_reference(self) -> None:
        """A library card cannot accept a declaration name in place of its target."""

        name = "EconCSLib.FairDivision.Bundle"
        valid = (
            TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL
            + json.dumps(
                {
                    "schema": "1",
                    "items": [
                        {
                            "declaration": name,
                            "declaration_kind": "definition",
                            "root_expanded": True,
                            "direct_library_declarations": [],
                            "display": "(Item : Type) → Finset Item",
                        }
                    ],
                }
            )
        )
        parsed = parse_transparent_library_declaration_display_output(valid, [name])
        self.assertEqual(parsed[name]["declaration_kind"], "definition")
        self.assertTrue(parsed[name]["root_expanded"])

        self_reference = valid.replace(
            '"direct_library_declarations": []',
            '"direct_library_declarations": ["EconCSLib.FairDivision.Bundle"]',
        )
        self.assertEqual(
            parse_transparent_library_declaration_display_output(self_reference, [name]),
            {},
        )

    def test_paper_prerequisite_transport_requires_lean_closure_and_target(self) -> None:
        """A paper-local wrapper cannot omit its retained semantic dependency."""

        root = "Fixture.SourceModel"
        dependency = "Fixture.SourcePolicy"
        valid = (
            TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL
            + json.dumps(
                {
                    "schema": "1",
                    "items": [
                        {
                            "declaration": root,
                            "declaration_kind": "definition",
                            "root_expanded": True,
                            "direct_paper_declarations": [dependency],
                            "direct_library_declarations": [
                                "EconCSLib.FairDivision.Bundle"
                            ],
                            "display": "∀ x, Fixture.SourcePolicy x",
                        },
                        {
                            "declaration": dependency,
                            "declaration_kind": "non_definition",
                            "root_expanded": False,
                            "direct_paper_declarations": [],
                            "direct_library_declarations": [],
                            "display": "Type → Prop",
                        },
                    ],
                }
            )
        )
        parsed = parse_transparent_paper_declaration_display_output(valid, [root])
        self.assertEqual(set(parsed), {root, dependency})
        self.assertEqual(parsed[root]["direct_paper_declarations"], (dependency,))
        self_reference = valid.replace(
            '"direct_paper_declarations": ["Fixture.SourcePolicy"]',
            '"direct_paper_declarations": ["Fixture.SourceModel"]',
        )
        self.assertEqual(
            parse_transparent_paper_declaration_display_output(self_reference, [root]),
            {},
        )

    def test_material_library_review_is_a_closeout_gate(self) -> None:
        class LibraryDashboard(_Dashboard):
            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path, _claims: object
            ) -> list[dict[str, object]]:
                return [
                    {
                        "lean_name": "EconCSLib.Example.definition",
                        "semantic_current": False,
                        "semantic_judgment": "matches",
                        "semantic_status": "stale source or library declaration",
                    }
                ]

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest(""),
                            "items": {
                                "Fixture.SourceSpec": {
                                    "spec_source_sha256": digest(
                                        "def SourceSpec : Prop := True"
                                    ),
                                    "direct_library_declarations": [],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=({"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_source_scope_dashboard_module",
                return_value=LibraryDashboard(),
            ):
                findings = integrity.material_library_semantic_review_findings(
                    folder, "formalized"
                )
        self.assertTrue(
            any("not a current `matches`" in finding.message for finding in findings)
        )

    def test_library_dependency_surface_is_bound_to_current_spec_and_owners(
        self,
    ) -> None:
        """A hand-written/old library inventory cannot silently pass closeout."""

        class CleanLibraryDashboard(_Dashboard):
            @staticmethod
            def library_review_owner_declaration(name: object) -> str:
                return str(name)

            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path, _claims: object
            ) -> list[dict[str, object]]:
                return []

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest("old interface"),
                            "items": {
                                "Fixture.SourceSpec": {
                                    "spec_source_sha256": digest("old Spec"),
                                    "direct_library_declarations": [
                                        "EconCSLib.Example.projection"
                                    ],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=({"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_source_scope_dashboard_module",
                return_value=CleanLibraryDashboard(),
            ):
                messages = [
                    finding.message
                    for finding in integrity.material_library_semantic_review_findings(
                        folder, "formalized"
                    )
                ]

        self.assertTrue(any("stale for the current PaperInterface bytes" in m for m in messages))
        self.assertTrue(any("unsupported protocol" in m for m in messages))
        self.assertTrue(any("Lean-expanded Spec library surface" in m for m in messages))

    def test_library_reissue_requires_exact_material_decision_coverage(self) -> None:
        """A reissue may not quietly omit a material reusable declaration."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            decisions = {
                "EconCSLib.Example.first": {
                    "judgment": "matches",
                    "reason": "The selected source clause has this exact meaning.",
                }
            }
            entries = [
                {
                    "lean_name": "EconCSLib.Example.first",
                    "library_definition": "def first : Prop := True",
                    "library_definition_sha256": digest("first"),
                    "verbatim_source_input": "source first",
                    "source_input_bundle_sha256": digest("source first"),
                },
                {
                    "lean_name": "EconCSLib.Example.second",
                    "library_definition": "def second : Prop := True",
                    "library_definition_sha256": digest("second"),
                    "verbatim_source_input": "source second",
                    "source_input_bundle_sha256": digest("source second"),
                },
            ]
            with mock.patch.object(
                library_reissue, "_material_entries", return_value=entries
            ):
                with self.assertRaisesRegex(
                    library_reissue.LibraryReviewReissueError,
                    "missing decisions for EconCSLib.Example.second",
                ):
                    library_reissue.reissue(
                        folder,
                        decisions,
                        validator="independent reviewer",
                        direct_dependency_surface={"items": {}},
                    )

    def test_library_reissue_refuses_unavailable_source_or_definition(self) -> None:
        """A decision cannot manufacture evidence when either input is absent."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            decisions = {
                "EconCSLib.Example.missing": {
                    "judgment": "matches",
                    "reason": "A reviewer supplied a judgment.",
                }
            }
            entries = [
                {
                    "lean_name": "EconCSLib.Example.missing",
                    "library_definition": "",
                    "library_definition_error": "not found",
                    "verbatim_source_input": "source text",
                    "source_input_bundle_sha256": digest("source text"),
                }
            ]
            with mock.patch.object(
                library_reissue, "_material_entries", return_value=entries
            ):
                with self.assertRaisesRegex(
                    library_reissue.LibraryReviewReissueError,
                    "exact bounded library declaration is unavailable",
                ):
                    library_reissue.reissue(
                        folder,
                        decisions,
                        validator="independent reviewer",
                        direct_dependency_surface={"items": {}},
                    )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
