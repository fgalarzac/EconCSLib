#!/usr/bin/env python3
"""Migrate an archive-backed source map to a canonical text audit surface.

The command is intentionally narrow.  It accepts an explicit correspondence
from each legacy paper-local ``file:line`` source path to one regular archive
member, reconstructs a byte-pinned text surface, rewrites only structured map
``source_location`` spans, and materializes the exact anchor quotes.  It does
not reissue a semantic review, source-record audit, or closure receipt: those
remain stale until the ordinary review pipeline has considered the new surface.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tarfile
from pathlib import Path
from typing import Any, Mapping

try:
    from scripts.audit_evidence_integrity import ROOT, SOURCE_FILE_LINE_RE
    from scripts.source_archive_surface import (
        SOURCE_ARCHIVE_SURFACE_FIELD,
        SOURCE_ARCHIVE_SURFACE_GENERATOR,
        SOURCE_ARCHIVE_SURFACE_SCHEMA,
        archive_surface_member_line_offsets,
        render_archive_surface,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script imports.
    from audit_evidence_integrity import ROOT, SOURCE_FILE_LINE_RE
    from source_archive_surface import (
        SOURCE_ARCHIVE_SURFACE_FIELD,
        SOURCE_ARCHIVE_SURFACE_GENERATOR,
        SOURCE_ARCHIVE_SURFACE_SCHEMA,
        archive_surface_member_line_offsets,
        render_archive_surface,
    )


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


ARCHIVE_MEMBER_EXTRACTED_LINE_RE = re.compile(
    r"(?P<archive>[A-Za-z0-9_./-]+\.tar(?:\.gz)?)\s+member\s+"
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md))\s*,\s*"
    r"extracted\s+lines\s+(?P<start>\d+)(?:-(?P<end>\d+))?",
    re.I,
)


def parse_member_mapping(raw_values: list[str]) -> dict[str, str]:
    """Parse strict ``paper-local-path=archive-member`` correspondences."""

    mapping: dict[str, str] = {}
    for raw in raw_values:
        local, separator, member = raw.partition("=")
        local = local.strip().replace("\\", "/")
        member = member.strip().replace("\\", "/")
        if not separator or not local or not member:
            raise ValueError("--member must have the form paper-local-path=archive-member")
        if local.startswith("/") or member.startswith("/") or ".." in local.split("/") or ".." in member.split("/"):
            raise ValueError("--member paths must be relative and cannot contain `..`")
        if local in mapping:
            raise ValueError(f"duplicate --member source path: {local}")
        mapping[local] = member
    if not mapping:
        raise ValueError("at least one --member correspondence is required")
    return mapping


def _archive_member_texts(
    archive_path: Path, mapping: Mapping[str, str]
) -> tuple[list[tuple[str, str]], dict[str, str]]:
    """Read explicit ordered archive members, rejecting binary or absent input."""

    try:
        with tarfile.open(archive_path, "r:*") as archive:
            known = {entry.name: entry for entry in archive.getmembers()}
            outputs: list[tuple[str, str]] = []
            digests: dict[str, str] = {}
            for member in dict.fromkeys(mapping.values()):
                entry = known.get(member)
                if entry is None or not entry.isfile():
                    raise ValueError(f"archive has no regular member `{member}`")
                handle = archive.extractfile(entry)
                raw = handle.read() if handle is not None else None
                if raw is None:
                    raise ValueError(f"could not read archive member `{member}`")
                try:
                    text = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
                except UnicodeDecodeError as exc:
                    raise ValueError(f"archive member `{member}` is not UTF-8 text") from exc
                outputs.append((member, text))
                digests[member] = sha256(raw)
    except (OSError, tarfile.TarError) as exc:
        raise ValueError(f"could not read source archive `{archive_path}`: {exc}") from exc
    return outputs, digests


def _walk_source_location_nodes(value: Any):
    if isinstance(value, dict):
        if isinstance(value.get("source_location"), str):
            yield value
        for child in value.values():
            yield from _walk_source_location_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk_source_location_nodes(child)


def rewrite_locator(
    location: str,
    *,
    member_mapping: Mapping[str, str],
    offsets: Mapping[str, int],
    surface_path: str,
    archive_name: str,
) -> tuple[str, set[str]]:
    """Translate every recognized legacy source span into the text surface."""

    unmatched: set[str] = set()

    replaced = 0

    def translated_span(source_path: str, start_text: str, end_text: str | None) -> str:
        nonlocal replaced
        member = member_mapping.get(source_path)
        if member is None:
            unmatched.add(source_path)
            return ""
        start = int(start_text) + offsets[member] - 1
        end = int(end_text) + offsets[member] - 1 if end_text is not None else None
        replaced += 1
        return f"{surface_path}:{start}" + (f"-{end}" if end is not None else "")

    def replace(match: re.Match[str]) -> str:
        source_path = match.group("path").replace("\\", "/")
        translated = translated_span(
            source_path, match.group("start"), match.group("end")
        )
        return translated or match.group(0)

    rewritten = SOURCE_FILE_LINE_RE.sub(replace, location)

    def replace_archive_member(match: re.Match[str]) -> str:
        if Path(match.group("archive")).name != Path(archive_name).name:
            unmatched.add(match.group("archive"))
            return match.group(0)
        source_path = match.group("path").replace("\\", "/")
        translated = translated_span(
            source_path, match.group("start"), match.group("end")
        )
        return translated or match.group(0)

    rewritten = ARCHIVE_MEMBER_EXTRACTED_LINE_RE.sub(replace_archive_member, rewritten)
    if replaced == 0:
        unmatched.add("<no recognized source span>")
    return rewritten, unmatched


def _surface_anchor_entries(location: str, *, surface_path: str, surface_text: str) -> list[dict[str, object]]:
    """Construct exact quote anchors after every legacy span was translated."""

    lines = surface_text.split("\n")
    if surface_text.endswith("\n"):
        lines.pop()
    entries: list[dict[str, object]] = []
    for match in SOURCE_FILE_LINE_RE.finditer(location):
        if match.group("path") != surface_path:
            raise ValueError(
                "rewritten source location still does not identify the canonical archive surface"
            )
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if start < 1 or end < start or end > len(lines):
            raise ValueError(
                f"rewritten source location `{surface_path}:{start}-{end}` is outside the generated surface"
            )
        quote = "\n".join(lines[start - 1 : end])
        entries.append(
            {
                "path": surface_path,
                "line_start": start,
                "line_end": end,
                "quoted_text": quote,
                "quoted_text_sha256": sha256(quote.encode("utf-8")),
            }
        )
    if not entries:
        raise ValueError("rewritten source_location has no file:line span")
    return entries


def migrate_payload(
    folder: Path,
    payload: dict[str, Any],
    *,
    member_mapping: Mapping[str, str],
    surface_path: str,
) -> tuple[str, int]:
    """Return generated surface text and update map paths/byte anchors in memory."""

    raw_archive = payload.get("source_artifact_path")
    archive_name = raw_archive.strip() if isinstance(raw_archive, str) else ""
    if not archive_name:
        raise ValueError("paper map has no source_artifact_path")
    archive_relative = Path(archive_name)
    if archive_relative.is_absolute():
        raise ValueError("source_artifact_path must be relative")
    archive_path = (
        (ROOT / archive_relative).resolve()
        if archive_relative.parts[:1] == ("papers",)
        else (folder / archive_relative).resolve()
    )
    try:
        archive_path.relative_to(folder.resolve())
    except ValueError as exc:
        raise ValueError("source_artifact_path must remain inside the paper folder") from exc
    if not archive_path.is_file():
        raise ValueError(f"source archive does not exist: {archive_name}")
    archive_raw = archive_path.read_bytes()
    pinned_archive_sha = str(payload.get("source_artifact_sha256") or "").lower()
    if sha256(archive_raw) != pinned_archive_sha:
        raise ValueError("source archive bytes do not match the current map pin")

    member_texts, member_digests = _archive_member_texts(archive_path, member_mapping)
    offsets = archive_surface_member_line_offsets(member_texts)
    surface_text = render_archive_surface(member_texts)
    unmatched: set[str] = set()
    location_nodes = list(_walk_source_location_nodes(payload))
    if not location_nodes:
        raise ValueError("paper map has no structured source_location nodes")
    for node in location_nodes:
        rewritten, unsupported = rewrite_locator(
            node["source_location"],
            member_mapping=member_mapping,
            offsets=offsets,
            surface_path=surface_path,
            archive_name=archive_name,
        )
        node["source_location"] = rewritten
        unmatched.update(unsupported)
    if unmatched:
        raise ValueError(
            "source locations reference paths without an explicit --member mapping: "
            + ", ".join(sorted(unmatched))
        )

    surface_raw = surface_text.encode("utf-8")
    payload["source_artifact_path"] = surface_path
    payload["source_artifact_sha256"] = sha256(surface_raw)
    payload[SOURCE_ARCHIVE_SURFACE_FIELD] = {
        "schema": SOURCE_ARCHIVE_SURFACE_SCHEMA,
        "generator": SOURCE_ARCHIVE_SURFACE_GENERATOR,
        "archive": {"path": archive_name, "sha256": sha256(archive_raw)},
        "members": [
            {
                "path": member,
                "sha256": member_digests[member],
            }
            for member, text in member_texts
        ],
    }
    payload["source_anchor_evidence_required"] = True
    changed_anchors = 0
    for node in location_nodes:
        expected = _surface_anchor_entries(
            node["source_location"],
            surface_path=surface_path,
            surface_text=surface_text,
        )
        existing = node.get("source_anchor_evidence")
        if existing == expected:
            continue
        if existing is not None:
            raise ValueError(
                "existing source_anchor_evidence differs from generated archive-surface "
                "evidence; review it before replacing"
            )
        node["source_anchor_evidence"] = expected
        changed_anchors += 1
    return surface_text, changed_anchors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument(
        "--member",
        action="append",
        default=[],
        help="paper-local legacy source path=archive member; repeat for each member",
    )
    parser.add_argument(
        "--surface-path",
        default="audit/source_archive_surface.tex",
        help="paper-local canonical generated text surface",
    )
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    folder = (ROOT / "papers" / args.paper).resolve()
    try:
        folder.relative_to((ROOT / "papers").resolve())
    except ValueError:
        parser.error("--paper must name a paper directory")
    map_path = folder / "audit" / "paper_statement_map.json"
    try:
        payload = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        parser.error(f"could not read {map_path}: {exc}")
    if not isinstance(payload, dict):
        parser.error("paper statement map must be a JSON object")
    try:
        mapping = parse_member_mapping(args.member)
        surface_text, changed_anchors = migrate_payload(
            folder,
            payload,
            member_mapping=mapping,
            surface_path=args.surface_path,
        )
    except ValueError as exc:
        parser.error(str(exc))
    output_path = folder / args.surface_path
    try:
        output_path.resolve().relative_to(folder.resolve())
    except ValueError:
        parser.error("--surface-path must stay within the paper directory")
    if args.write:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(surface_text, encoding="utf-8")
        map_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        f"{args.paper}: {len(mapping)} archive member(s), {changed_anchors} source anchor(s) "
        f"{'written' if args.write else 'would write'}"
    )
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI wrapper.
    raise SystemExit(main())
