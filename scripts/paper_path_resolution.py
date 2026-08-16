#!/usr/bin/env python3
"""Platform-neutral paper-folder path validation for workflow entrypoints."""

from __future__ import annotations

from pathlib import Path


def resolve_paper_folder(root: Path, paper: str) -> Path | None:
    """Resolve one existing paper basename without accepting path expressions."""

    if not paper or paper in {".", ".."} or Path(paper).name != paper:
        return None
    papers_root = (root / "papers").resolve()
    folder = (papers_root / paper).resolve()
    try:
        folder.relative_to(papers_root)
    except ValueError:
        return None
    return folder if folder.is_dir() else None
