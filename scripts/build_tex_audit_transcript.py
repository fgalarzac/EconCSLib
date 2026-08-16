#!/usr/bin/env python3
"""Build a deterministic, source-pinned TeX audit transcript.

This is deliberately *not* a TeX interpreter.  It follows only literal,
active ``\\input{...}`` and ``\\include{...}`` commands selected by an
explicit profile, after stripping TeX comments and applying a likewise
explicit redline policy.  Every other file-read mechanism is either declared
with a supported behavior or fails closed.  The resulting UTF-8 transcript is
therefore suitable as a canonical source artifact for semantic review without
quietly treating a compilation side effect, a macro expansion, or a deleted
redline as source text.

The tool has three deterministic commands:

``snapshot``
    Copy the full configured input graph, including explicitly
    ``read_not_rendered`` files, into a private source snapshot.
``build``
    Produce the comment-free, redline-resolved audit transcript and a
    line-provenance manifest.
``verify``
    Rebuild in memory and reject any source/profile/transcript/manifest drift.

Profiles are intentionally narrow.  They must explicitly state behavior for
``input``, ``include``, and any active supported file-read command such as
``CatchFileDef``.  ``CatchFileDef`` may be recorded as ``read_not_rendered``;
its bytes then remain in the raw snapshot and graph manifest but never enter
the semantic transcript.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
from typing import Mapping, Sequence


PROFILE_SCHEMA = 1
MANIFEST_SCHEMA = 1
SNAPSHOT_MANIFEST_SCHEMA = 1
TOOL_NAME = "scripts/build_tex_audit_transcript.py"

_PROFILE_FIELDS = frozenset(
    {
        "schema",
        "entrypoint",
        "path_resolution",
        "file_reads",
        "redlines",
        "unknown_file_read",
        "unknown_redline",
    }
)
_REDLINE_FIELDS = frozenset({"commands", "spans"})
_SUPPORTED_FILE_READS = frozenset({"input", "include", "CatchFileDef"})
_KNOWN_UNSUPPORTED_FILE_READS = frozenset(
    {
        "InputIfFileExists",
        "IfFileExists",
        "@@input",
        "import",
        "subfile",
        "includepdf",
    }
)
_FILE_READ_BEHAVIORS = frozenset({"render", "read_not_rendered"})
_COMMAND_REDACTIONS = frozenset({"keep_argument", "drop_argument"})
_SPAN_REDACTIONS = frozenset({"keep", "drop"})
_COMMAND_NAME_RE = re.compile(r"[A-Za-z@]+")
_PROFILE_NAME_RE = re.compile(r"[A-Za-z@][A-Za-z0-9@]*\Z")


class TranscriptError(RuntimeError):
    """A source/profile ambiguity that must not receive audit credit."""


@dataclass(frozen=True)
class RedlineProfile:
    commands: Mapping[str, str]
    spans: Mapping[str, str]


@dataclass(frozen=True)
class TranscriptProfile:
    entrypoint: str
    path_resolution: str
    file_reads: Mapping[str, str]
    redlines: RedlineProfile
    profile_sha256: str


@dataclass(frozen=True)
class SourceFile:
    path: str
    sha256: str
    byte_length: int
    line_count: int
    rendered: bool


@dataclass(frozen=True)
class FileReadEdge:
    parent: str
    parent_line: int
    command: str
    target: str
    behavior: str


@dataclass(frozen=True)
class RedlineEvent:
    source_path: str
    source_line: int
    command: str
    behavior: str


@dataclass(frozen=True)
class Origin:
    """One provenance label for emitted transcript characters."""

    kind: str
    source_path: str | None = None
    source_line: int | None = None
    boundary: str | None = None

    def payload(self) -> dict[str, object]:
        if self.kind == "source":
            assert self.source_path is not None and self.source_line is not None
            return {
                "kind": "source",
                "source_path": self.source_path,
                "source_line": self.source_line,
            }
        assert self.kind == "boundary"
        assert self.source_path is not None and self.boundary is not None
        return {
            "kind": "boundary",
            "boundary": self.boundary,
            "source_path": self.source_path,
        }


@dataclass(frozen=True)
class BuiltTranscript:
    text: str
    source_files: tuple[SourceFile, ...]
    file_reads: tuple[FileReadEdge, ...]
    redline_events: tuple[RedlineEvent, ...]
    line_provenance: tuple[dict[str, object], ...]
    profile: TranscriptProfile


def _sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_text(text: str) -> str:
    return _sha256_bytes(text.encode("utf-8"))


def _logical_line_count(text: str) -> int:
    if not text:
        return 0
    return len(text.splitlines())


def _normalize_newlines(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")


def _strict_object(value: object, *, where: str, fields: frozenset[str]) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TranscriptError(f"{where} must be a JSON object")
    keys = {str(key) for key in value}
    missing = sorted(fields - keys)
    unknown = sorted(keys - fields)
    if missing:
        raise TranscriptError(f"{where} is missing required field(s): {', '.join(missing)}")
    if unknown:
        raise TranscriptError(f"{where} has unknown field(s): {', '.join(unknown)}")
    return value


def _string_mapping(value: object, *, where: str) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise TranscriptError(f"{where} must be a JSON object")
    result: dict[str, str] = {}
    for raw_name, raw_behavior in value.items():
        name = str(raw_name)
        if not _PROFILE_NAME_RE.fullmatch(name):
            raise TranscriptError(f"{where} has invalid command name: {name!r}")
        if not isinstance(raw_behavior, str):
            raise TranscriptError(f"{where}.{name} must be a string")
        result[name] = raw_behavior
    return result


def load_profile(path: Path) -> TranscriptProfile:
    """Load a closed, explicit transcript profile from JSON."""

    try:
        raw = path.read_bytes()
    except OSError as error:
        raise TranscriptError(f"cannot read profile {path}: {error}") from error
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise TranscriptError(f"profile {path} is not valid UTF-8 JSON: {error}") from error
    profile = _strict_object(payload, where="profile", fields=_PROFILE_FIELDS)
    if profile.get("schema") != PROFILE_SCHEMA:
        raise TranscriptError(
            f"profile.schema must be {PROFILE_SCHEMA}, found {profile.get('schema')!r}"
        )
    entrypoint = profile.get("entrypoint")
    if not isinstance(entrypoint, str) or not entrypoint.strip():
        raise TranscriptError("profile.entrypoint must be a nonempty string")
    entrypoint = entrypoint.strip()
    if Path(entrypoint).is_absolute() or ".." in Path(entrypoint).parts:
        raise TranscriptError("profile.entrypoint must be a root-relative safe path")
    if profile.get("path_resolution") != "source_root_tex_extension":
        raise TranscriptError(
            "profile.path_resolution must be 'source_root_tex_extension'; "
            "the audit tool never guesses TeX search paths"
        )
    if profile.get("unknown_file_read") != "error":
        raise TranscriptError("profile.unknown_file_read must be 'error'")
    if profile.get("unknown_redline") != "error":
        raise TranscriptError("profile.unknown_redline must be 'error'")

    file_reads = _string_mapping(profile.get("file_reads"), where="profile.file_reads")
    unsupported = sorted(set(file_reads) - _SUPPORTED_FILE_READS)
    if unsupported:
        raise TranscriptError(
            "profile.file_reads configures unsupported command(s): "
            f"{', '.join(unsupported)}"
        )
    for command, behavior in file_reads.items():
        if behavior not in _FILE_READ_BEHAVIORS:
            raise TranscriptError(
                f"profile.file_reads.{command} has unknown behavior {behavior!r}"
            )

    redlines = _strict_object(
        profile.get("redlines"), where="profile.redlines", fields=_REDLINE_FIELDS
    )
    redline_commands = _string_mapping(
        redlines.get("commands"), where="profile.redlines.commands"
    )
    redline_spans = _string_mapping(redlines.get("spans"), where="profile.redlines.spans")
    required_redline_bases = {"DIFadd", "DIFdel"}
    if set(redline_commands) != required_redline_bases:
        raise TranscriptError(
            "profile.redlines.commands must explicitly configure exactly "
            "DIFadd and DIFdel"
        )
    if set(redline_spans) != required_redline_bases:
        raise TranscriptError(
            "profile.redlines.spans must explicitly configure exactly "
            "DIFadd and DIFdel"
        )
    for command, behavior in redline_commands.items():
        if behavior not in _COMMAND_REDACTIONS:
            raise TranscriptError(
                f"profile.redlines.commands.{command} has unknown behavior {behavior!r}"
            )
    for command, behavior in redline_spans.items():
        if behavior not in _SPAN_REDACTIONS:
            raise TranscriptError(
                f"profile.redlines.spans.{command} has unknown behavior {behavior!r}"
            )

    return TranscriptProfile(
        entrypoint=entrypoint,
        path_resolution="source_root_tex_extension",
        file_reads=dict(sorted(file_reads.items())),
        redlines=RedlineProfile(
            commands=dict(sorted(redline_commands.items())),
            spans=dict(sorted(redline_spans.items())),
        ),
        profile_sha256=_sha256_bytes(raw),
    )


def strip_tex_comments(text: str) -> str:
    """Remove unescaped TeX comments while preserving every physical newline."""

    text = _normalize_newlines(text)
    output: list[str] = []
    index = 0
    while index < len(text):
        character = text[index]
        if character == "\\":
            command = _COMMAND_NAME_RE.match(text, index + 1)
            if command is not None and command.group(0) == "verb":
                # ``\\verb`` changes TeX's ordinary catcodes until its next
                # delimiter, so a literal percent sign there is not a comment.
                # Handle this one lexical exception rather than pretending the
                # transcript builder can expand arbitrary macros.
                verb_end = command.end()
                if verb_end < len(text) and text[verb_end] == "*":
                    verb_end += 1
                if verb_end < len(text) and text[verb_end] != "\n":
                    delimiter = text[verb_end]
                    closing = text.find(delimiter, verb_end + 1)
                    if closing < 0:
                        raise TranscriptError("unterminated \\verb construct")
                    output.append(text[index : closing + 1])
                    index = closing + 1
                    continue
        if character != "%":
            output.append(character)
            index += 1
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and text[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2:
            output.append(character)
            index += 1
            continue
        newline = text.find("\n", index)
        if newline < 0:
            break
        output.append("\n")
        index = newline + 1
    return "".join(output)


def _line_at(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def _skip_space(text: str, index: int) -> int:
    while index < len(text) and text[index].isspace():
        index += 1
    return index


def _matching_brace(text: str, opening: int, *, source_path: str, line: int) -> int:
    if opening >= len(text) or text[opening] != "{":
        raise TranscriptError(f"{source_path}:{line}: expected '{{'")
    depth = 0
    index = opening
    while index < len(text):
        character = text[index]
        if character == "\\":
            index += 2
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    raise TranscriptError(f"{source_path}:{line}: unterminated braced argument")


def _newline_only(text: str) -> str:
    return "".join(character for character in text if character == "\n")


class _RedlineTransformer:
    """Resolve the small explicit DIF profile without interpreting TeX."""

    def __init__(self, text: str, profile: RedlineProfile, source_path: str):
        self.text = text
        self.profile = profile
        self.source_path = source_path
        self.events: list[RedlineEvent] = []
        self.span_stack: list[tuple[str, str]] = []

    def _suppressed(self) -> bool:
        return any(behavior == "drop" for _, behavior in self.span_stack)

    def _emit_plain(self, value: str) -> str:
        return _newline_only(value) if self._suppressed() else value

    def _record(self, index: int, command: str, behavior: str) -> None:
        self.events.append(
            RedlineEvent(
                source_path=self.source_path,
                source_line=_line_at(self.text, index),
                command=command,
                behavior=behavior,
            )
        )

    def transform(self) -> tuple[str, tuple[RedlineEvent, ...]]:
        output = self._transform_range(0, len(self.text))
        if self.span_stack:
            names = ", ".join(name for name, _ in self.span_stack)
            raise TranscriptError(f"{self.source_path}: unclosed redline span(s): {names}")
        return output, tuple(self.events)

    def _transform_range(self, start: int, end: int) -> str:
        output: list[str] = []
        index = start
        while index < end:
            if self.text[index] != "\\":
                output.append(self._emit_plain(self.text[index]))
                index += 1
                continue
            name_match = _COMMAND_NAME_RE.match(self.text, index + 1)
            if name_match is None:
                output.append(self._emit_plain(self.text[index]))
                index += 1
                continue
            name = name_match.group(0)
            command_end = name_match.end()
            line = _line_at(self.text, index)
            if name in self.profile.commands:
                argument_start = _skip_space(self.text, command_end)
                if argument_start >= end or self.text[argument_start] != "{":
                    # A macro declaration (``\\providecommand{\\DIFadd}``) is
                    # not a redline invocation.  Any other occurrence is
                    # ambiguous and must not silently survive the audit view.
                    if command_end < end and self.text[command_end] == "}":
                        output.append(self._emit_plain(self.text[index:command_end]))
                        index = command_end
                        continue
                    raise TranscriptError(
                        f"{self.source_path}:{line}: {name} must use one literal braced argument"
                    )
                argument_end = _matching_brace(
                    self.text, argument_start, source_path=self.source_path, line=line
                )
                full_call = self.text[index : argument_end + 1]
                behavior = self.profile.commands[name]
                self._record(index, name, behavior)
                if self._suppressed() or behavior == "drop_argument":
                    output.append(_newline_only(full_call))
                else:
                    output.append(_newline_only(self.text[index:argument_start + 1]))
                    output.append(self._transform_range(argument_start + 1, argument_end))
                index = argument_end + 1
                continue

            span_base: str | None = None
            span_edge: str | None = None
            for candidate in self.profile.spans:
                if name == f"{candidate}begin":
                    span_base, span_edge = candidate, "begin"
                    break
                if name == f"{candidate}end":
                    span_base, span_edge = candidate, "end"
                    break
            if span_base is not None and span_edge is not None:
                # Like command forms, leave a declaration's macro-name token
                # alone.  Real span markers do not have a closing brace
                # immediately after the control word.
                if command_end < end and self.text[command_end] == "}":
                    output.append(self._emit_plain(self.text[index:command_end]))
                    index = command_end
                    continue
                behavior = self.profile.spans[span_base]
                self._record(index, name, behavior)
                output.append(_newline_only(self.text[index:command_end]))
                if span_edge == "begin":
                    self.span_stack.append((span_base, behavior))
                else:
                    if not self.span_stack:
                        raise TranscriptError(
                            f"{self.source_path}:{line}: {name} has no matching begin marker"
                        )
                    opened, _ = self.span_stack.pop()
                    if opened != span_base:
                        raise TranscriptError(
                            f"{self.source_path}:{line}: {name} closes {opened}, not {span_base}"
                        )
                index = command_end
                continue

            if name.startswith("DIF"):
                # This does not infer a local convention from a macro name.
                # The profile must account for every live DIF redline form.
                if command_end < end and self.text[command_end] == "}":
                    output.append(self._emit_plain(self.text[index:command_end]))
                    index = command_end
                    continue
                raise TranscriptError(
                    f"{self.source_path}:{line}: unknown live redline command {name}"
                )
            output.append(self._emit_plain(self.text[index:command_end]))
            index = command_end
        return "".join(output)


def resolve_redlines(
    text: str, profile: RedlineProfile, source_path: str
) -> tuple[str, tuple[RedlineEvent, ...]]:
    """Strip comments then apply the closed DIF redline profile."""

    return _RedlineTransformer(strip_tex_comments(text), profile, source_path).transform()


def _resolve_target(root: Path, raw_target: str, *, parent: str, line: int) -> tuple[Path, str]:
    target = raw_target.strip()
    if not target:
        raise TranscriptError(f"{parent}:{line}: empty file-read target")
    if any(token in target for token in ("\\", "#", "~")):
        raise TranscriptError(
            f"{parent}:{line}: nonliteral file-read target {target!r} is unsupported"
        )
    relative = Path(target)
    if relative.is_absolute() or ".." in relative.parts:
        raise TranscriptError(
            f"{parent}:{line}: file-read target escapes source root: {target!r}"
        )
    candidate = root / relative
    if not candidate.suffix:
        candidate = candidate.with_suffix(".tex")
    try:
        resolved = candidate.resolve(strict=True)
        relative_path = resolved.relative_to(root.resolve())
    except (FileNotFoundError, OSError, RuntimeError, ValueError) as error:
        raise TranscriptError(
            f"{parent}:{line}: cannot resolve file-read target {target!r} under source root"
        ) from error
    if not resolved.is_file():
        raise TranscriptError(f"{parent}:{line}: file-read target is not a regular file: {target!r}")
    return resolved, relative_path.as_posix()


def _parse_braced_group(
    text: str, index: int, *, parent: str, line: int
) -> tuple[str, int]:
    opening = _skip_space(text, index)
    if opening >= len(text) or text[opening] != "{":
        raise TranscriptError(f"{parent}:{line}: expected a literal braced file-read argument")
    closing = _matching_brace(text, opening, source_path=parent, line=line)
    return text[opening + 1 : closing], closing + 1


@dataclass(frozen=True)
class _CommandOccurrence:
    command: str
    start: int
    end: int
    target: str
    line: int


def _file_read_occurrences(text: str, *, parent: str, configured: Mapping[str, str]) -> tuple[_CommandOccurrence, ...]:
    """Find literal supported file reads and reject all ambiguous variants."""

    found: list[_CommandOccurrence] = []
    index = 0
    while index < len(text):
        if text[index] != "\\":
            index += 1
            continue
        match = _COMMAND_NAME_RE.match(text, index + 1)
        if match is None:
            index += 1
            continue
        command = match.group(0)
        command_end = match.end()
        if command in _KNOWN_UNSUPPORTED_FILE_READS:
            line = _line_at(text, index)
            raise TranscriptError(
                f"{parent}:{line}: encountered unsupported file-read command {command}; "
                "the profile must not silently approximate it"
            )
        if command not in _SUPPORTED_FILE_READS:
            index = command_end
            continue
        line = _line_at(text, index)
        if command not in configured:
            raise TranscriptError(
                f"{parent}:{line}: active {command} has no configured file-read behavior"
            )
        if command in {"input", "include"}:
            target, end = _parse_braced_group(text, command_end, parent=parent, line=line)
        else:
            # \CatchFileDef{\macro}{path}{options}; it reads its second
            # braced argument.  The options are parsed only to prove that this
            # is the literal, closed form the profile selected.
            _, after_macro = _parse_braced_group(text, command_end, parent=parent, line=line)
            target, after_target = _parse_braced_group(
                text, after_macro, parent=parent, line=line
            )
            _, end = _parse_braced_group(text, after_target, parent=parent, line=line)
        found.append(
            _CommandOccurrence(
                command=command,
                start=index,
                end=end,
                target=target,
                line=line,
            )
        )
        index = end
    return tuple(found)


class _Emitter:
    """Collect transcript characters and derive line-level provenance."""

    def __init__(self) -> None:
        self.characters: list[tuple[str, Origin]] = []

    def emit_text(self, text: str, *, source_path: str, source_line: int) -> None:
        line = source_line
        for character in text:
            self.characters.append(
                (character, Origin("source", source_path=source_path, source_line=line))
            )
            if character == "\n":
                line += 1

    def emit_boundary(self, *, boundary: str, source_path: str, text: str) -> None:
        origin = Origin("boundary", source_path=source_path, boundary=boundary)
        self.characters.extend((character, origin) for character in text)

    def finish(self) -> tuple[str, tuple[dict[str, object], ...]]:
        text = "".join(character for character, _ in self.characters)
        records: list[dict[str, object]] = []
        origins: list[Origin] = []
        line_number = 1
        for character, origin in self.characters:
            if origin not in origins:
                origins.append(origin)
            if character != "\n":
                continue
            records.append(
                {
                    "transcript_line": line_number,
                    "origins": [item.payload() for item in origins],
                }
            )
            line_number += 1
            origins = []
        if self.characters and self.characters[-1][0] != "\n":
            records.append(
                {
                    "transcript_line": line_number,
                    "origins": [item.payload() for item in origins],
                }
            )
        return text, tuple(records)


class _Builder:
    def __init__(self, source_root: Path, profile: TranscriptProfile):
        try:
            self.root = source_root.resolve(strict=True)
        except (FileNotFoundError, OSError) as error:
            raise TranscriptError(f"cannot access source root {source_root}: {error}") from error
        if not self.root.is_dir():
            raise TranscriptError(f"source root is not a directory: {source_root}")
        self.profile = profile
        self.emitter = _Emitter()
        self.source_files: dict[str, SourceFile] = {}
        self.file_reads: list[FileReadEdge] = []
        self.redline_events: list[RedlineEvent] = []
        self._render_stack: list[str] = []

    def _read_source(self, path: Path, relative_path: str, *, rendered: bool) -> str:
        try:
            raw = path.read_bytes()
        except OSError as error:
            raise TranscriptError(f"cannot read source file {relative_path}: {error}") from error
        try:
            text = _normalize_newlines(raw.decode("utf-8"))
        except UnicodeDecodeError as error:
            raise TranscriptError(f"source file {relative_path} is not UTF-8: {error}") from error
        source_file = SourceFile(
            path=relative_path,
            sha256=_sha256_bytes(raw),
            byte_length=len(raw),
            line_count=_logical_line_count(text),
            rendered=rendered,
        )
        prior = self.source_files.get(relative_path)
        if prior is None:
            self.source_files[relative_path] = source_file
        elif prior.sha256 != source_file.sha256 or prior.rendered != source_file.rendered:
            # A file first seen through a non-rendered read can subsequently be
            # rendered.  Its final node must truthfully say rendered=true.
            self.source_files[relative_path] = SourceFile(
                path=relative_path,
                sha256=source_file.sha256,
                byte_length=source_file.byte_length,
                line_count=source_file.line_count,
                rendered=prior.rendered or rendered,
            )
        return text

    def build(self) -> BuiltTranscript:
        entry_path, entry_relative = _resolve_target(
            self.root, self.profile.entrypoint, parent="profile.entrypoint", line=1
        )
        self._render_file(entry_path, entry_relative)
        text, line_provenance = self.emitter.finish()
        return BuiltTranscript(
            text=text,
            source_files=tuple(
                self.source_files[path] for path in sorted(self.source_files)
            ),
            file_reads=tuple(self.file_reads),
            redline_events=tuple(self.redline_events),
            line_provenance=line_provenance,
            profile=self.profile,
        )

    def _render_file(self, path: Path, relative_path: str) -> None:
        if relative_path in self._render_stack:
            cycle = " -> ".join([*self._render_stack, relative_path])
            raise TranscriptError(f"literal input/include cycle: {cycle}")
        self._render_stack.append(relative_path)
        try:
            raw_text = self._read_source(path, relative_path, rendered=True)
            text, events = resolve_redlines(raw_text, self.profile.redlines, relative_path)
            self.redline_events.extend(events)
            self.emitter.emit_boundary(
                boundary="begin_source",
                source_path=relative_path,
                text=(
                    f"% <<< AUDIT SOURCE BEGIN path={relative_path} "
                    f"sha256={self.source_files[relative_path].sha256} >>>\n"
                ),
            )
            reads = _file_read_occurrences(
                text, parent=relative_path, configured=self.profile.file_reads
            )
            cursor = 0
            for occurrence in reads:
                self._emit_source_slice(text, cursor, occurrence.start, relative_path)
                target_path, target_relative = _resolve_target(
                    self.root,
                    occurrence.target,
                    parent=relative_path,
                    line=occurrence.line,
                )
                behavior = self.profile.file_reads[occurrence.command]
                self.file_reads.append(
                    FileReadEdge(
                        parent=relative_path,
                        parent_line=occurrence.line,
                        command=occurrence.command,
                        target=target_relative,
                        behavior=behavior,
                    )
                )
                if behavior == "render":
                    self._render_file(target_path, target_relative)
                elif behavior == "read_not_rendered":
                    # Read and pin the raw bytes, but do not parse its body or
                    # emit a source boundary.  This makes a CatchFileDef-style
                    # input visible to the audit graph without treating it as
                    # semantic source text.
                    self._read_source(target_path, target_relative, rendered=False)
                    self.emitter.emit_boundary(
                        boundary="read_not_rendered",
                        source_path=target_relative,
                        text=(
                            "% <<< AUDIT FILE READ NOT RENDERED "
                            f"command={occurrence.command} target={target_relative} "
                            f"from={relative_path}:{occurrence.line} >>>\n"
                        ),
                    )
                else:  # Defensive: profile validation has already closed this.
                    raise TranscriptError(
                        f"{relative_path}:{occurrence.line}: unknown configured behavior {behavior!r}"
                    )
                cursor = occurrence.end
            self._emit_source_slice(text, cursor, len(text), relative_path)
            self.emitter.emit_boundary(
                boundary="end_source",
                source_path=relative_path,
                text=f"% <<< AUDIT SOURCE END path={relative_path} >>>\n",
            )
        finally:
            self._render_stack.pop()

    def _emit_source_slice(
        self, text: str, start: int, end: int, source_path: str
    ) -> None:
        if start >= end:
            return
        self.emitter.emit_text(
            text[start:end], source_path=source_path, source_line=_line_at(text, start)
        )


def build_transcript(source_root: Path, profile_path: Path) -> BuiltTranscript:
    """Build a transcript in memory; useful for both CLI and focused tests."""

    return _Builder(source_root, load_profile(profile_path)).build()


def _manifest_payload(result: BuiltTranscript, transcript_path: str) -> dict[str, object]:
    transcript_bytes = result.text.encode("utf-8")
    return {
        "schema": MANIFEST_SCHEMA,
        "tool": TOOL_NAME,
        "profile": {
            "schema": PROFILE_SCHEMA,
            "entrypoint": result.profile.entrypoint,
            "sha256": result.profile.profile_sha256,
        },
        "source_files": [
            {
                "path": source.path,
                "sha256": source.sha256,
                "byte_length": source.byte_length,
                "line_count": source.line_count,
                "rendered": source.rendered,
            }
            for source in result.source_files
        ],
        "file_reads": [
            {
                "parent": edge.parent,
                "parent_line": edge.parent_line,
                "command": edge.command,
                "target": edge.target,
                "behavior": edge.behavior,
            }
            for edge in result.file_reads
        ],
        "redline_events": [
            {
                "source_path": event.source_path,
                "source_line": event.source_line,
                "command": event.command,
                "behavior": event.behavior,
            }
            for event in result.redline_events
        ],
        "transcript": {
            "path": transcript_path,
            "sha256": _sha256_bytes(transcript_bytes),
            "byte_length": len(transcript_bytes),
            "line_count": _logical_line_count(result.text),
        },
        "line_provenance": list(result.line_provenance),
    }


def _write_json(path: Path, payload: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _display_path(path: Path, *, anchor: Path) -> str:
    try:
        return path.resolve().relative_to(anchor.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return path.name


def command_build(arguments: argparse.Namespace) -> int:
    result = build_transcript(arguments.source_root, arguments.profile)
    transcript = arguments.transcript
    manifest = arguments.manifest
    transcript.parent.mkdir(parents=True, exist_ok=True)
    transcript.write_text(result.text, encoding="utf-8")
    payload = _manifest_payload(
        result, _display_path(transcript, anchor=manifest.parent)
    )
    _write_json(manifest, payload)
    print(
        json.dumps(
            {
                "transcript": str(transcript),
                "transcript_sha256": payload["transcript"]["sha256"],
                "manifest": str(manifest),
                "source_file_count": len(result.source_files),
                "file_read_count": len(result.file_reads),
            },
            sort_keys=True,
        )
    )
    return 0


def command_verify(arguments: argparse.Namespace) -> int:
    try:
        manifest_payload = json.loads(arguments.manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise TranscriptError(f"cannot read manifest {arguments.manifest}: {error}") from error
    if not isinstance(manifest_payload, Mapping):
        raise TranscriptError("manifest must be a JSON object")
    transcript_payload = manifest_payload.get("transcript")
    if not isinstance(transcript_payload, Mapping):
        raise TranscriptError("manifest.transcript must be a JSON object")
    stored_path = transcript_payload.get("path")
    if not isinstance(stored_path, str) or not stored_path:
        raise TranscriptError("manifest.transcript.path must be a nonempty string")
    try:
        actual = arguments.transcript.read_bytes()
    except OSError as error:
        raise TranscriptError(f"cannot read transcript {arguments.transcript}: {error}") from error
    actual_sha = _sha256_bytes(actual)
    if transcript_payload.get("sha256") != actual_sha:
        raise TranscriptError(
            "stored transcript SHA-256 does not match current bytes: "
            f"expected {transcript_payload.get('sha256')!r}, found {actual_sha}"
        )
    result = build_transcript(arguments.source_root, arguments.profile)
    expected = _manifest_payload(result, stored_path)
    expected_bytes = result.text.encode("utf-8")
    if actual != expected_bytes:
        raise TranscriptError("current transcript bytes differ from deterministic rebuild")
    if manifest_payload != expected:
        raise TranscriptError("manifest differs from deterministic rebuild")
    print(
        json.dumps(
            {
                "manifest": str(arguments.manifest),
                "status": "verified",
                "transcript_sha256": actual_sha,
            },
            sort_keys=True,
        )
    )
    return 0


def command_snapshot(arguments: argparse.Namespace) -> int:
    result = build_transcript(arguments.source_root, arguments.profile)
    destination = arguments.destination
    if destination.exists() and any(destination.iterdir()):
        if not arguments.overwrite:
            raise TranscriptError(
                f"snapshot destination {destination} is nonempty; use --overwrite only after reviewing it"
            )
        expected_paths = {
            *(source.path for source in result.source_files),
            "source_graph_manifest.json",
        }
        existing_paths = {
            path.relative_to(destination).as_posix()
            for path in destination.rglob("*")
            if path.is_file()
        }
        unexpected = sorted(existing_paths - expected_paths)
        if unexpected:
            raise TranscriptError(
                "snapshot destination contains stale/unconfigured file(s): "
                f"{', '.join(unexpected)}; refuse to retain an ambiguous graph"
            )
    destination.mkdir(parents=True, exist_ok=True)
    root = arguments.source_root.resolve()
    for source in result.source_files:
        source_path = root / source.path
        target_path = destination / source.path
        target_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, target_path)
        copied_sha = _sha256_bytes(target_path.read_bytes())
        if copied_sha != source.sha256:
            raise TranscriptError(
                f"snapshot copy hash mismatch for {source.path}: {copied_sha} != {source.sha256}"
            )
    snapshot_manifest = {
        "schema": SNAPSHOT_MANIFEST_SCHEMA,
        "tool": TOOL_NAME,
        "profile": {
            "schema": PROFILE_SCHEMA,
            "entrypoint": result.profile.entrypoint,
            "sha256": result.profile.profile_sha256,
        },
        "source_revision": arguments.source_revision or "",
        "source_files": [
            {
                "path": source.path,
                "sha256": source.sha256,
                "byte_length": source.byte_length,
                "line_count": source.line_count,
                "rendered": source.rendered,
            }
            for source in result.source_files
        ],
        "file_reads": [
            {
                "parent": edge.parent,
                "parent_line": edge.parent_line,
                "command": edge.command,
                "target": edge.target,
                "behavior": edge.behavior,
            }
            for edge in result.file_reads
        ],
    }
    _write_json(destination / "source_graph_manifest.json", snapshot_manifest)
    print(
        json.dumps(
            {
                "destination": str(destination),
                "manifest": str(destination / "source_graph_manifest.json"),
                "source_file_count": len(result.source_files),
                "source_revision": arguments.source_revision or "",
            },
            sort_keys=True,
        )
    )
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subcommands = result.add_subparsers(dest="command", required=True)

    def shared(command: argparse.ArgumentParser) -> None:
        command.add_argument("--source-root", type=Path, required=True)
        command.add_argument("--profile", type=Path, required=True)

    build = subcommands.add_parser("build", help="build transcript and provenance manifest")
    shared(build)
    build.add_argument("--transcript", type=Path, required=True)
    build.add_argument("--manifest", type=Path, required=True)
    build.set_defaults(handler=command_build)

    verify = subcommands.add_parser("verify", help="verify transcript and manifest by rebuilding")
    shared(verify)
    verify.add_argument("--transcript", type=Path, required=True)
    verify.add_argument("--manifest", type=Path, required=True)
    verify.set_defaults(handler=command_verify)

    snapshot = subcommands.add_parser("snapshot", help="copy the configured raw input graph")
    shared(snapshot)
    snapshot.add_argument("--destination", type=Path, required=True)
    snapshot.add_argument("--source-revision", default="")
    snapshot.add_argument("--overwrite", action="store_true")
    snapshot.set_defaults(handler=command_snapshot)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    arguments = parser().parse_args(argv)
    try:
        return int(arguments.handler(arguments))
    except TranscriptError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
