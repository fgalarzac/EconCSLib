from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import issue_source_spec_correspondence as issuer


class SourceSpecCorrespondenceScreeningTests(unittest.TestCase):
    def setUp(self) -> None:
        self.specification = "Fixture.PaperInterface.claimSpec"
        self.source_map = {
            "items": {
                "claim": {
                    "coverage_status": "corrected_source_statement",
                    "semantic_contract": {"spec_declaration": self.specification},
                    "corrected_target": {
                        "archival_equivalence_claimed": False,
                        "corrected_target_sha256": "a" * 64,
                    },
                }
            }
        }

    def test_corrected_target_screening_can_issue_a_realization_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            with mock.patch.object(
                issuer.packet,
                "_paperinterface_items",
                return_value={self.specification: {}},
            ), mock.patch.object(
                issuer.packet,
                "semantic_expanded_spec_targets",
                return_value={self.specification: {"display": "True"}},
            ), mock.patch.object(
                issuer.packet,
                "_v11_screening_rows",
                return_value={
                    self.specification: {
                        "current": True,
                        "judgment": "matches_approved_corrected_target",
                    }
                },
            ), mock.patch.object(
                issuer.integrity,
                "corrected_source_statement_map_findings",
                return_value=[],
            ):
                self.assertEqual(
                    issuer.current_matching_screening(
                        folder, self.source_map, self.specification
                    ),
                    "",
                )

    def test_ordinary_matches_is_rejected_for_a_corrected_target(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            with mock.patch.object(
                issuer.packet,
                "_paperinterface_items",
                return_value={self.specification: {}},
            ), mock.patch.object(
                issuer.packet,
                "semantic_expanded_spec_targets",
                return_value={self.specification: {"display": "True"}},
            ), mock.patch.object(
                issuer.packet,
                "_v11_screening_rows",
                return_value={
                    self.specification: {"current": True, "judgment": "matches"}
                },
            ):
                # The issuer repeats this fail-closed check rather than
                # trusting a caller to have used the packet helper correctly.
                self.assertIn(
                    "requires approved-corrected-target",
                    issuer.current_matching_screening(
                        folder, self.source_map, self.specification
                    ),
                )


if __name__ == "__main__":
    unittest.main()
