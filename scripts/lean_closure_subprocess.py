#!/usr/bin/env python3
"""Exec one command beneath a POSIX address-space ceiling.

This is a deliberately small process trampoline for Lean semantic-closure
extraction.  Using a standalone executable avoids ``preexec_fn`` in the
potentially threaded audit coordinator: the coordinator starts this process
normally, and this process installs the limit before replacing itself with
``lake``.
"""

from __future__ import annotations

import argparse
import os
import sys


def apply_posix_address_space_limit(limit_bytes: int) -> None:
    """Apply ``RLIMIT_AS`` before exec, or raise an actionable runtime error."""

    if limit_bytes <= 0:
        raise RuntimeError("address-space limit must be positive")
    if os.name != "posix":
        return
    try:
        import resource
    except ImportError as error:  # pragma: no cover - unavailable on non-POSIX.
        raise RuntimeError("POSIX resource limits are unavailable") from error
    try:
        address_space = resource.RLIMIT_AS
    except AttributeError as error:  # pragma: no cover - uncommon POSIX port.
        raise RuntimeError("POSIX RLIMIT_AS is unavailable") from error
    soft_limit, hard_limit = resource.getrlimit(address_space)
    infinity = resource.RLIM_INFINITY
    next_soft_limit = limit_bytes
    if soft_limit != infinity:
        next_soft_limit = min(next_soft_limit, soft_limit)
    if hard_limit != infinity:
        next_soft_limit = min(next_soft_limit, hard_limit)
    resource.setrlimit(address_space, (next_soft_limit, hard_limit))


def main(argv: list[str] | None = None) -> int:
    """Parse a bounded command and replace this process with it."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--address-space-bytes", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    parsed = parser.parse_args(argv)
    command = list(parsed.command)
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        parser.error("a command is required after --")
    try:
        apply_posix_address_space_limit(parsed.address_space_bytes)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"lean closure trampoline: {error}", file=sys.stderr)
        return 126
    try:
        os.execvp(command[0], command)
    except OSError as error:
        print(f"lean closure trampoline: could not exec {command[0]}: {error}", file=sys.stderr)
        return 127
    return 127  # pragma: no cover - os.execvp never returns on success.


if __name__ == "__main__":  # pragma: no cover - exercised through subprocess.
    raise SystemExit(main())
