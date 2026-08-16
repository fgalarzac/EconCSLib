#!/usr/bin/env python3
"""Focused tests for the no-``preexec_fn`` Lean closure trampoline."""

from __future__ import annotations

import sys
import unittest
from contextlib import redirect_stderr
from io import StringIO
from unittest import mock

from scripts import lean_closure_subprocess as trampoline


class LeanClosureSubprocessTests(unittest.TestCase):
    def test_address_space_limit_is_applied_before_exec(self) -> None:
        class FakeResource:
            RLIMIT_AS = 17
            RLIM_INFINITY = -1

            def __init__(self) -> None:
                self.updated: tuple[int, tuple[int, int]] | None = None

            def getrlimit(self, resource_kind: int) -> tuple[int, int]:
                if resource_kind != self.RLIMIT_AS:
                    raise AssertionError("unexpected resource limit")
                return self.RLIM_INFINITY, self.RLIM_INFINITY

            def setrlimit(
                self, resource_kind: int, limits: tuple[int, int]
            ) -> None:
                self.updated = (resource_kind, limits)

        fake_resource = FakeResource()
        with mock.patch.dict(sys.modules, {"resource": fake_resource}):
            trampoline.apply_posix_address_space_limit(12345)

        self.assertEqual(
            fake_resource.updated,
            (fake_resource.RLIMIT_AS, (12345, fake_resource.RLIM_INFINITY)),
        )

    def test_main_passes_the_exact_command_to_exec(self) -> None:
        with (
            mock.patch.object(trampoline, "apply_posix_address_space_limit") as cap,
            mock.patch.object(trampoline.os, "execvp", side_effect=OSError("missing")) as execvp,
            redirect_stderr(StringIO()),
        ):
            result = trampoline.main(
                ["--address-space-bytes", "12345", "--", "lake", "env", "lean"]
            )

        cap.assert_called_once_with(12345)
        execvp.assert_called_once_with("lake", ["lake", "env", "lean"])
        self.assertEqual(result, 127)


if __name__ == "__main__":
    unittest.main()
