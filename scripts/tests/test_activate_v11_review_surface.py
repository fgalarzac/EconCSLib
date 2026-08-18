"""Tests for activation of a fresh v11 human-review surface."""

from __future__ import annotations

import unittest

from scripts.activate_v11_review_surface import activate


class ActivateV11ReviewSurfaceTests(unittest.TestCase):
    def test_activation_resets_the_saved_human_review_queue(self) -> None:
        activated = activate(
            {
                "review_surface": {"include_names": ["legacy"]},
                "human_review": {"reviewed_rows": 12, "total_rows": 12},
            },
            {
                "paper": "Fixture",
                "items": {
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.firstSpec",
                            "evidence_declaration": "Fixture.PaperInterface.first_realizes_spec",
                        }
                    },
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.secondSpec",
                            "evidence_declaration": "Fixture.PaperInterface.second_proof",
                        }
                    },
                },
            },
            paper="Fixture",
        )
        self.assertEqual(activated["review_surface"]["include_names"], ["firstSpec", "secondSpec"])
        self.assertEqual(
            activated["review_surface"]["proposition_spec_proofs"],
            {"firstSpec": "first_realizes_spec", "secondSpec": "second_proof"},
        )
        self.assertEqual(activated["human_review"]["reviewed_rows"], 0)
        self.assertEqual(activated["human_review"]["total_rows"], 2)
        self.assertEqual(activated["human_review"]["mismatch_rows"], 0)


if __name__ == "__main__":
    unittest.main()
