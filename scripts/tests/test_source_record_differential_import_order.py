#!/usr/bin/env python3
"""Fresh-interpreter smoke tests for differential/current-revalidation imports."""

from __future__ import annotations

import os
import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class SourceRecordDifferentialImportOrderTests(unittest.TestCase):
    def assert_import_order(self, modules: list[str]) -> None:
        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        result = subprocess.run(
            [sys.executable, "-c", "\n".join("import " + name for name in modules)],
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            0,
            msg=(
                "fresh interpreter import order failed: "
                + " -> ".join(modules)
                + "\n"
                + result.stderr
            ),
        )

    def test_audit_repository_then_current_revalidation(self) -> None:
        self.assert_import_order(
            ["scripts.audit_repository", "scripts.source_record_current_revalidation"]
        )

    def test_current_revalidation_then_audit_repository(self) -> None:
        self.assert_import_order(
            ["scripts.source_record_current_revalidation", "scripts.audit_repository"]
        )

    def test_audit_consumers_bind_canonical_differential_module(self) -> None:
        """A prior direct-script import must not split authenticated item types."""

        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        script = f"""
import sys
sys.path.insert(0, {str(ROOT / 'scripts')!r})
import source_record_differential_revalidation
from scripts import source_record_differential_revalidation as canonical
from scripts import audit_conclusion_provenance
from scripts import audit_evidence_integrity
from scripts import audit_repository
for consumer in (audit_conclusion_provenance, audit_evidence_integrity, audit_repository):
    assert consumer.load_current_source_record_differential_revalidation_items is canonical.load_current_source_record_differential_revalidation_items
    assert consumer.is_loaded_source_record_differential_revalidation_item is canonical.is_loaded_source_record_differential_revalidation_item
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)


if __name__ == "__main__":
    unittest.main()
