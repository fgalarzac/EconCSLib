#!/usr/bin/env python3
"""Protect the hand-written root README from generated or accidental edits."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
ROOT_README = ROOT / "README.md"
LOCK_FILE = ROOT / "docs" / "root_readme_lock.json"
LOCK_SCHEMA = 1

GENERATED_MARKERS = (
    "<!-- BEGIN GENERATED",
    "<!-- END GENERATED",
)


def root_relative(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def readme_sha256() -> str:
    return hashlib.sha256(ROOT_README.read_bytes()).hexdigest()


def load_lock() -> dict[str, object] | None:
    if not LOCK_FILE.exists():
        return None
    payload = json.loads(LOCK_FILE.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{root_relative(LOCK_FILE)} should contain a JSON object")
    return payload


def validate_root_readme() -> list[str]:
    """Return policy violations for the protected root README."""

    messages: list[str] = []
    if not ROOT_README.exists():
        return [f"{root_relative(ROOT_README)} is missing"]

    text = ROOT_README.read_text(encoding="utf-8")
    for marker in GENERATED_MARKERS:
        if marker in text:
            messages.append(
                f"{root_relative(ROOT_README)} contains generated-output marker `{marker}`"
            )

    lock = load_lock()
    if lock is None:
        messages.append(f"{root_relative(LOCK_FILE)} is missing")
        return messages

    if lock.get("schema") != LOCK_SCHEMA:
        messages.append(f"{root_relative(LOCK_FILE)} should use schema {LOCK_SCHEMA}")
    if lock.get("path") != "README.md":
        messages.append(f"{root_relative(LOCK_FILE)} should protect README.md")

    expected = lock.get("sha256")
    actual = readme_sha256()
    if not isinstance(expected, str) or expected != actual:
        messages.append(
            f"{root_relative(ROOT_README)} does not match {root_relative(LOCK_FILE)}; "
            "only update the root README after explicit user instructions, then "
            "refresh the lock with `python3 scripts/root_readme_policy.py --write-lock`"
        )
    return messages


def assert_root_readme_locked() -> None:
    messages = validate_root_readme()
    if messages:
        raise ValueError("root README policy failed:\n- " + "\n- ".join(messages))


def assert_no_root_readme_outputs(paths: Iterable[Path]) -> None:
    root_readme = ROOT_README.resolve()
    offenders = [root_relative(path) for path in paths if path.resolve() == root_readme]
    if offenders:
        raise ValueError(
            "generators must not write the protected root README: "
            + ", ".join(offenders)
        )


def write_lock() -> None:
    payload = {
        "schema": LOCK_SCHEMA,
        "path": "README.md",
        "sha256": readme_sha256(),
        "policy": (
            "README.md is hand-written human-facing project prose. Do not edit it "
            "or generate it unless Nikhil gives specific root-README instructions."
        ),
    }
    LOCK_FILE.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {root_relative(LOCK_FILE)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-lock",
        action="store_true",
        help="refresh the protected README hash after an explicitly requested root README edit",
    )
    args = parser.parse_args()

    if args.write_lock:
        write_lock()
        return 0

    messages = validate_root_readme()
    if messages:
        print("root README policy failed:")
        for message in messages:
            print(f"- {message}")
        return 1
    print("root README policy passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
