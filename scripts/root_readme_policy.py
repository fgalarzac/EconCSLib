#!/usr/bin/env python3
"""Keep generators away from the hand-written root README.

Human edits to README.md are allowed directly. This module intentionally does
not inspect README prose. It only blocks generator output maps that would write
the root README; agent-facing documentation still requires express user
instructions in the current task before an LLM edits any README file.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
ROOT_README = ROOT / "README.md"

def root_relative(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def validate_root_readme() -> list[str]:
    """Return policy violations for the non-content README policy.

    Kept for backward compatibility with older CI commands. Human README edits
    should not make CLI checks fail, so content validation is deliberately empty.
    """

    return []


def assert_root_readme_policy() -> None:
    messages = validate_root_readme()
    if messages:
        raise ValueError("root README policy failed:\n- " + "\n- ".join(messages))


def assert_root_readme_locked() -> None:
    """Backward-compatible name for the non-locking README policy."""

    assert_root_readme_policy()


def assert_no_root_readme_outputs(paths: Iterable[Path]) -> None:
    root_readme = ROOT_README.resolve()
    offenders = [root_relative(path) for path in paths if path.resolve() == root_readme]
    if offenders:
        raise ValueError(
            "generators must not write the hand-written root README: "
            + ", ".join(offenders)
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-lock",
        action="store_true",
        help="deprecated no-op; human README edits no longer require a hash lock",
    )
    args = parser.parse_args()

    if args.write_lock:
        print("root README hash locks are no longer used; nothing to write")
        return 0

    messages = validate_root_readme()
    if messages:
        print("root README policy failed:")
        for message in messages:
            print(f"- {message}")
        return 1
    print("root README policy passed; README prose was not inspected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
