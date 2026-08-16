#!/usr/bin/env python3
"""Python 3.10 grammar regression for the source-record audit CLI."""

from __future__ import annotations

import ast
import hashlib
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


class SourceRecordAuditPython310Tests(unittest.TestCase):
    def test_source_record_audit_uses_python310_grammar(self) -> None:
        source = HELPER.read_text(encoding="utf-8")
        ast.parse(
            source,
            filename=str(HELPER),
            mode="exec",
            feature_version=(3, 10),
        )

    def test_elaborated_witness_identity_keeps_null_delimited_digest(self) -> None:
        module_name = "source_record_audit_python310_regression"
        spec = importlib.util.spec_from_file_location(module_name, HELPER)
        assert spec is not None and spec.loader is not None
        audit = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = audit
        self.addCleanup(sys.modules.pop, module_name, None)
        spec.loader.exec_module(audit)

        normalized_sha = "a" * 64
        qualified_row = "Fixture.opaque_result"
        path = "result/opaque_witness"
        items = audit.type_valued_certificate_result_items(
            row_names=["opaque_result"],
            declarations={
                "opaque_result": "theorem opaque_result : True := by trivial"
            },
            structures={},
            aliases={},
            proposition_heads=set(),
            row_qualified_names={"opaque_result": qualified_row},
            elaborated_type_witness_receipts={
                qualified_row: [
                    {
                        "path": path,
                        "occurrence_role": "provided_result",
                        "payload_safety": "opaque_payload",
                        "normalized_type_sha256": normalized_sha,
                    }
                ]
            },
        )

        witness_identity = hashlib.sha256(
            "\0".join((qualified_row, path, normalized_sha)).encode("utf-8")
        ).hexdigest()
        self.assertEqual(len(items), 1)
        self.assertEqual(
            items[0]["judgment_key"],
            "opaque_result.type_valued_certificate_result.elaborated."
            + witness_identity,
        )


if __name__ == "__main__":
    unittest.main()
