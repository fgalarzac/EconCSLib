#!/usr/bin/env python3
"""Focused tests for immutable historical manifest-store recovery."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Any, Mapping, Sequence
from unittest import mock

from scripts import historical_manifest_store_recovery as RECOVERY


COMMIT = "a" * 40
SIDECAR_BLOB = "b" * 40
STATUS_BLOB = "c" * 40
INTERFACE_BLOB = "d" * 40
SIGNATURE = "e" * 64


def completed(stdout: bytes = b"", returncode: int = 0) -> subprocess.CompletedProcess[bytes]:
    return subprocess.CompletedProcess([], returncode, stdout=stdout, stderr=b"")


class FakeGit:
    """A file-creating worktree mock with immutable blob responses."""

    def __init__(self, *, blobs: Mapping[str, bytes], sources: Mapping[str, bytes]) -> None:
        self.blobs = dict(blobs)
        self.sources = dict(sources)
        self.calls: list[tuple[str, ...]] = []
        self.worktree: Path | None = None
        self.head = COMMIT
        self.status = b""

    def __call__(
        self, argv: Sequence[str], cwd: Path
    ) -> subprocess.CompletedProcess[bytes]:
        del cwd
        command = tuple(argv)
        self.calls.append(command)
        if command == ("git", "rev-parse", "--verify", f"{COMMIT}^{{commit}}"):
            return completed((COMMIT + "\n").encode("ascii"))
        if command[:3] == ("git", "rev-parse", "--verify"):
            spec = command[3]
            if not isinstance(spec, str) or ":" not in spec:
                return completed(returncode=1)
            _commit, path = spec.split(":", 1)
            object_id = {
                "papers/Fixture/audit/old.json": SIDECAR_BLOB,
                "papers/Fixture/status.json": STATUS_BLOB,
                "papers/Fixture/PaperInterface.lean": INTERFACE_BLOB,
            }.get(path)
            return completed(
                ((object_id + "\n").encode("ascii")) if object_id else b"",
                0 if object_id else 1,
            )
        if command[:3] == ("git", "cat-file", "blob"):
            content = self.blobs.get(command[3]) if len(command) == 4 else None
            return completed(content or b"", 0 if content is not None else 1)
        if command[:4] == ("git", "worktree", "add", "--detach"):
            self.worktree = Path(command[4])
            folder = self.worktree / "papers" / "Fixture"
            folder.mkdir(parents=True)
            for relative, content in self.sources.items():
                path = folder / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
            return completed()
        if command[:3] == ("git", "worktree", "remove"):
            if self.worktree is not None:
                shutil.rmtree(self.worktree, ignore_errors=True)
            return completed()
        if command[:4] == ("git", "-C", str(self.worktree), "rev-parse"):
            return completed((self.head + "\n").encode("ascii"))
        if command[:4] == ("git", "-C", str(self.worktree), "status"):
            return completed(self.status)
        raise AssertionError(f"unexpected Git command: {command}")

    def count(self, prefix: tuple[str, ...]) -> int:
        return sum(call[: len(prefix)] == prefix for call in self.calls)


class HistoricalManifestStoreRecoveryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.status_bytes = b'{"review_surface":{"source_file":"PaperInterface.lean"}}\n'
        self.interface_bytes = (
            b"namespace Fixture.PaperInterface\n"
            b"theorem archived : True := by trivial\n"
            b"end Fixture.PaperInterface\n"
        )
        self.sidecar_bytes = b'{"paper":"Fixture","items":[]}\n'
        self.sources = {
            "status.json": self.status_bytes,
            "PaperInterface.lean": self.interface_bytes,
        }
        self.blobs = {
            SIDECAR_BLOB: self.sidecar_bytes,
            STATUS_BLOB: self.status_bytes,
            INTERFACE_BLOB: self.interface_bytes,
        }

    def _root(self) -> tempfile.TemporaryDirectory[str]:
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        (root / ".git").mkdir()
        folder = root / "papers" / "Fixture"
        (folder / "audit").mkdir(parents=True)
        # The surviving input deliberately has a different live filename than
        # the immutable historical path but identical bytes.
        (folder / "audit" / "survives.json").write_bytes(self.sidecar_bytes)
        for relative in (
            "scripts/historical_manifest_store_recovery.py",
            "scripts/lean_signature_manifest.py",
            "scripts/lean_signature_manifest_helper.lean",
            "scripts/authenticated_manifest_store.py",
            "scripts/review_dashboard.py",
        ):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"fixture {relative}\n", encoding="utf-8")
        return temporary

    def _config(self, root: Path) -> RECOVERY.HistoricalManifestStoreRecoveryConfig:
        return RECOVERY.HistoricalManifestStoreRecoveryConfig(
            root=root,
            paper="Fixture",
            historical_commit=COMMIT,
            historical_sidecar_path="audit/survives.json",
            historical_sidecar_git_path="audit/old.json",
            authority_output_path="audit/recovered.authority.json",
            carrier_output_path="audit/recovered.carrier.json.gz",
            receipt_output_path="audit/recovered.receipt.json",
        )

    def _surface(self, worktree: Path, paper: str) -> RECOVERY.HistoricalReviewSurface:
        self.assertEqual(paper, "Fixture")
        folder = worktree / "papers" / paper
        return RECOVERY.HistoricalReviewSurface(
            import_module="Fixture.PaperInterface",
            declarations=(
                RECOVERY.HistoricalReviewDeclaration(
                    qualified_declaration="Fixture.PaperInterface.archived",
                    source_file="PaperInterface.lean",
                    lean_source_declaration="theorem archived : True",
                    line_number=2,
                    declaration_kind="theorem",
                ),
            ),
            source_files=(
                RECOVERY.HistoricalReviewSource(
                    "status.json", (folder / "status.json").read_bytes()
                ),
                RECOVERY.HistoricalReviewSource(
                    "PaperInterface.lean",
                    (folder / "PaperInterface.lean").read_bytes(),
                ),
            ),
        )

    @staticmethod
    def _context(*args: object, **kwargs: object) -> Mapping[str, Any]:
        del args, kwargs
        return {
            "audit_modules": ["Fixture.PaperInterface"],
            "canonical_representation": "lean_compact_canonical_v2",
            "semantic_hash_tool_identity": {"resolved_path": "fixture"},
        }

    @staticmethod
    def _manifest(*args: object, **kwargs: object) -> Mapping[str, Mapping[str, Any]]:
        del args, kwargs
        return {
            "Fixture.PaperInterface.archived": {
                "sha256": SIGNATURE,
                "elaborated_proposition_graph": {"schema": 1, "nodes": []},
            }
        }

    @staticmethod
    def _store_builder(
        paper: str, candidates: Sequence[Mapping[str, Any]]
    ) -> tuple[dict[str, Any], dict[str, Any], set[str]]:
        if paper != "Fixture" or len(candidates) != 1:
            raise AssertionError("unexpected store candidates")
        candidate = candidates[0]
        binding = candidate["authority_binding"]
        assert isinstance(binding, Mapping)
        if binding.get("source_file") != "PaperInterface.lean":
            raise AssertionError("candidate source binding was not preserved")
        name = str(candidate["qualified_declaration"])
        authority = {
            "schema": 1,
            "paper": paper,
            "contexts": [],
            "contexts_sha256": "0" * 64,
            "entries": [],
            "entries_sha256": "0" * 64,
        }
        carrier = {"schema": 1, "paper": paper, "entries": []}
        return authority, carrier, {name}

    def _recover(
        self,
        root: Path,
        fake_git: FakeGit,
        *,
        manifest_producer=None,
        store_builder=None,
    ) -> RECOVERY.RecoveredHistoricalManifestStore:
        with mock.patch.object(
            RECOVERY.manifest_tools,
            "signature_manifest_digest",
            return_value=SIGNATURE,
        ):
            return RECOVERY.recover_historical_manifest_store(
                self._config(root),
                command_runner=fake_git,
                review_surface_extractor=self._surface,
                manifest_context_producer=self._context,
                manifest_producer=manifest_producer or self._manifest,
                store_payload_builder=store_builder or self._store_builder,
            )

    def test_recovery_is_in_memory_then_writes_pinned_compressed_artifacts(self) -> None:
        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            recovered = self._recover(root, fake_git)

            folder = root / "papers" / "Fixture" / "audit"
            self.assertFalse((folder / "recovered.authority.json").exists())
            self.assertFalse((folder / "recovered.carrier.json.gz").exists())
            self.assertFalse((folder / "recovered.receipt.json").exists())
            self.assertEqual(fake_git.count(("git", "worktree", "add")), 1)
            self.assertEqual(fake_git.count(("git", "worktree", "remove")), 1)
            self.assertIsNotNone(fake_git.worktree)
            assert fake_git.worktree is not None
            self.assertFalse(fake_git.worktree.exists())

            carrier_metadata = recovered.receipt["recovered_store"]["carrier"]
            assert isinstance(carrier_metadata, Mapping)
            self.assertEqual(
                RECOVERY.verified_deterministic_gzip_decompress(
                    recovered.carrier_compressed_bytes,
                    expected_compressed_sha256=str(
                        carrier_metadata["compressed_bytes_sha256"]
                    ),
                    expected_uncompressed_sha256=str(
                        carrier_metadata["uncompressed_bytes_sha256"]
                    ),
                    expected_uncompressed_byte_length=int(
                        carrier_metadata["uncompressed_byte_length"]
                    ),
                ),
                recovered.carrier_uncompressed_bytes,
            )
            self.assertEqual(
                recovered.receipt["historical_statement_sidecar"]["git_path"],
                "papers/Fixture/audit/old.json",
            )
            coordinates = recovered.receipt["historical_review_surface"][
                "selected_declaration_coordinates"
            ]
            self.assertEqual(coordinates[0]["source_file"], "PaperInterface.lean")
            authority, carrier, raw_carrier = (
                RECOVERY.verified_recovered_manifest_store_artifacts(
                    paper="Fixture",
                    receipt=recovered.receipt,
                    receipt_bytes=recovered.receipt_bytes,
                    authority_bytes=recovered.authority_bytes,
                    carrier_compressed_bytes=recovered.carrier_compressed_bytes,
                )
            )
            self.assertEqual(authority, recovered.authority)
            self.assertEqual(carrier, recovered.carrier)
            self.assertEqual(raw_carrier, recovered.carrier_uncompressed_bytes)

            RECOVERY.write_recovered_manifest_store(self._config(root), recovered)
            self.assertEqual(
                (folder / "recovered.authority.json").read_bytes(),
                recovered.authority_bytes,
            )
            self.assertEqual(
                (folder / "recovered.carrier.json.gz").read_bytes(),
                recovered.carrier_compressed_bytes,
            )
            self.assertEqual(
                (folder / "recovered.receipt.json").read_bytes(),
                recovered.receipt_bytes,
            )
            self.assertFalse(
                (folder / "lean_signature_manifest_cache_authority.json").exists()
            )

    def test_sidecar_blob_mismatch_fails_before_worktree_creation(self) -> None:
        with self._root() as temporary:
            root = Path(temporary)
            (root / "papers/Fixture/audit/survives.json").write_bytes(
                b'{"paper":"Fixture","items":["changed"]}\n'
            )
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            with self.assertRaisesRegex(
                RECOVERY.HistoricalManifestStoreRecoveryError,
                "surviving historical statement sidecar bytes",
            ):
                self._recover(root, fake_git)
            self.assertEqual(fake_git.count(("git", "worktree", "add")), 0)

    def test_missing_manifest_fails_closed_and_removes_worktree(self) -> None:
        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            with self.assertRaisesRegex(
                RECOVERY.HistoricalManifestStoreRecoveryError,
                "did not return exactly the configured review surface",
            ):
                self._recover(root, fake_git, manifest_producer=lambda *args, **kwargs: {})
            self.assertEqual(fake_git.count(("git", "worktree", "add")), 1)
            self.assertEqual(fake_git.count(("git", "worktree", "remove")), 1)
            self.assertFalse(
                (root / "papers/Fixture/audit/recovered.receipt.json").exists()
            )

    def test_uses_current_producer_checkpoint_context_without_a_second_context_build(self) -> None:
        def producer(*args: object, **kwargs: object) -> Mapping[str, Mapping[str, Any]]:
            checkpoint = kwargs.get("manifest_checkpoint")
            assert callable(checkpoint)
            checkpoint(self._context(), {})
            return self._manifest()

        def unexpected_context(*args: object, **kwargs: object) -> Mapping[str, Any]:
            del args, kwargs
            raise AssertionError("checkpoint context should avoid a second build")

        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            with mock.patch.object(
                RECOVERY.manifest_tools,
                "signature_manifest_digest",
                return_value=SIGNATURE,
            ):
                recovered = RECOVERY.recover_historical_manifest_store(
                    self._config(root),
                    command_runner=fake_git,
                    review_surface_extractor=self._surface,
                    manifest_context_producer=unexpected_context,
                    manifest_producer=producer,
                    store_payload_builder=self._store_builder,
                )
            self.assertEqual(recovered.accepted_declarations, ("Fixture.PaperInterface.archived",))

    def test_rejected_store_entry_fails_closed_and_removes_worktree(self) -> None:
        def rejects(
            paper: str, candidates: Sequence[Mapping[str, Any]]
        ) -> tuple[dict[str, Any], dict[str, Any], set[str]]:
            authority, carrier, _accepted = self._store_builder(paper, candidates)
            return authority, carrier, set()

        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            with self.assertRaisesRegex(
                RECOVERY.HistoricalManifestStoreRecoveryError,
                "rejected part of the historical review surface",
            ):
                self._recover(root, fake_git, store_builder=rejects)
            self.assertEqual(fake_git.count(("git", "worktree", "remove")), 1)

    def test_head_mismatch_fails_before_current_manifest_producer(self) -> None:
        calls: list[object] = []

        def producer(*args: object, **kwargs: object) -> Mapping[str, Mapping[str, Any]]:
            calls.append((args, kwargs))
            return self._manifest()

        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            fake_git.head = "f" * 40
            with self.assertRaisesRegex(
                RECOVERY.HistoricalManifestStoreRecoveryError,
                "not at the requested commit",
            ):
                self._recover(root, fake_git, manifest_producer=producer)
            self.assertEqual(calls, [])
            self.assertEqual(fake_git.count(("git", "worktree", "remove")), 1)

    def test_rejects_non_audit_or_uncompressed_carrier_paths_before_git(self) -> None:
        with self._root() as temporary:
            root = Path(temporary)
            fake_git = FakeGit(blobs=self.blobs, sources=self.sources)
            bad = RECOVERY.HistoricalManifestStoreRecoveryConfig(
                **{
                    **self._config(root).__dict__,
                    "carrier_output_path": "audit/not-compressed.json",
                }
            )
            with self.assertRaisesRegex(
                RECOVERY.HistoricalManifestStoreRecoveryError,
                "carrier_output_path must end in .json.gz",
            ):
                RECOVERY.recover_historical_manifest_store(bad, command_runner=fake_git)
            self.assertEqual(fake_git.calls, [])

    def test_compressed_carrier_requires_the_canonical_representation(self) -> None:
        raw = json.dumps({"paper": "Fixture", "entries": []}, sort_keys=True).encode()
        compressed = RECOVERY.deterministic_gzip_compress(raw)
        self.assertEqual(compressed, RECOVERY.deterministic_gzip_compress(raw))
        decoded = RECOVERY.verified_deterministic_gzip_decompress(
            compressed,
            expected_compressed_sha256=hashlib.sha256(compressed).hexdigest(),
            expected_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),
            expected_uncompressed_byte_length=len(raw),
        )
        self.assertEqual(decoded, raw)
        noncanonical = bytearray(compressed)
        noncanonical[9] = 3 if noncanonical[9] != 3 else 255
        noncanonical_bytes = bytes(noncanonical)
        with self.assertRaisesRegex(
            RECOVERY.HistoricalManifestStoreRecoveryError,
            "canonical gzip representation",
        ):
            RECOVERY.verified_deterministic_gzip_decompress(
                noncanonical_bytes,
                expected_compressed_sha256=hashlib.sha256(
                    noncanonical_bytes
                ).hexdigest(),
                expected_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),
                expected_uncompressed_byte_length=len(raw),
            )

    def test_default_surface_extractor_uses_archived_paperinterface_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_bytes(self.status_bytes)
            (folder / "PaperInterface.lean").write_bytes(self.interface_bytes)
            surface = RECOVERY._default_historical_review_surface(root, "Fixture")
            self.assertEqual(surface.import_module, "Fixture.PaperInterface")
            self.assertEqual(
                [item.qualified_declaration for item in surface.declarations],
                ["Fixture.PaperInterface.archived"],
            )
            self.assertEqual(
                [item.paper_relative_path for item in surface.source_files],
                ["PaperInterface.lean", "status.json"],
            )


if __name__ == "__main__":  # pragma: no cover - direct test convenience.
    unittest.main()
