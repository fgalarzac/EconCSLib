#!/usr/bin/env python3
"""Index named theoretical source presentations without Lean-route heuristics.

This module deliberately operates only on canonical UTF-8 text/TeX artifacts.
It does not read files, inspect source-map keys, or inspect Lean declarations.
Callers supply source text and a source-map ``items`` object, then use the
reconciliation result to decide whether every discovered named presentation is
anchored by source location metadata or by an exact byte-pinned quote.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import posixpath
import re
from typing import Any, Iterable, Mapping


NAMED_RESULT_KINDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "definition",
        "equation",
        "formula",
        "algorithm",
        "assumption",
        # A named conjecture or open question is source-visible but has an
        # explicit non-proof disposition.  It is never silently ignored just
        # because it cannot receive theorem-proof credit.
        "open_problem",
    }
)

OPEN_NAMED_PRESENTATION_KIND = "open_problem"
UNCLASSIFIED_NAMED_PRESENTATION_KIND = "unclassified"

# A PDF/text extraction can conservatively retain explanatory prose or a proof
# after a visible theorem heading.  A source map may therefore attach a
# separately reviewed, byte-pinned statement core to that heading.  This is a
# source-only reconciliation aid: it cannot name a Lean declaration, choose a
# map key, or replace the ordinary exact-full-span rule for items that do not
# opt in.
SOURCE_PRESENTATION_RECONCILIATION_FIELD = "source_presentation_reconciliation"
SOURCE_PRESENTATION_RECONCILIATION_SCHEMA = 1
SOURCE_PRESENTATION_RECONCILIATION_RELATION = "conservative_text_span_core"
SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD = "core_anchor"
SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS = frozenset(
    {"completed_statement_then_explanation"}
)

# These are visible source titles, not source-map keys or Lean identifiers.
# The second group deliberately remains unclassified until the curator records
# a source-pinned ``environment_kinds``/``heading_kinds`` interpretation.  A
# generic audit must not assume that a paper's local "Property" or "Case"
# environment means the same thing as a theorem in another paper.
_STANDARD_NAMED_TITLE_WORDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "definition",
        "equation",
        "formula",
        "algorithm",
        "assumption",
        "conjecture",
    }
)
_UNCLASSIFIED_NAMED_TITLE_WORDS = frozenset(
    {
        "fact",
        "property",
        "condition",
        "model",
        "desideratum",
        "setup",
        "axiom",
        "postulate",
        "observation",
        "result",
    }
)
_NON_THEORETICAL_TITLE_WORDS = frozenset(
    {
        "example",
        "remark",
        "comment",
        "note",
        "discussion",
    }
)
_TEXT_TITLE_PATTERN = "|".join(
    [
        r"open\s+(?:question|problem)",
        # ``Eq. (1)`` is a common source presentation for a numbered equation.
        # Treat it as a visible source title, not as a source-map or Lean name.
        r"eq(?:uation)?\.?",
        *sorted(_STANDARD_NAMED_TITLE_WORDS, key=len, reverse=True),
        *sorted(_UNCLASSIFIED_NAMED_TITLE_WORDS, key=len, reverse=True),
    ]
)
_TEX_ENV_RE = re.compile(
    r"\\(?P<action>begin|end)\s*\{\s*(?P<environment>[A-Za-z@][A-Za-z0-9_@-]*)(?P<star>\*)?\s*\}",
    re.IGNORECASE,
)
_TEX_RESTATABLE_ENVIRONMENT = "restatable"
_TEX_ENVIRONMENT_NAME_RE = re.compile(r"[A-Za-z@][A-Za-z0-9_@-]*\Z")
_TEX_NEW_THEOREM_RE = re.compile(
    r"""
    \\newtheorem\*?\s*
    \{\s*(?P<environment>[A-Za-z@][A-Za-z0-9_@-]*)\s*\}
    (?:\s*\[[^\]]+\])?
    \s*\{\s*(?P<title>[^{}]+)\s*\}
    """,
    re.IGNORECASE | re.VERBOSE,
)
_TEX_LABEL_RE = re.compile(r"\\label\s*\{\s*(?P<label>[^{}\s][^{}]*)\s*\}")
_TEX_CAPTION_RE = re.compile(r"\\caption(?:\[[^\]]*\])?\s*\{(?P<caption>[^{}]+)\}")
_TEX_TAG_RE = re.compile(r"\\tag\*?\s*\{(?P<tag>[^{}]+)\}")
_TEX_ROW_BREAK_RE = re.compile(r"(?<!\\)\\\\(?!\\)")
_TEX_ROW_BREAK_SUFFIX_RE = re.compile(r"\s*(?:\[[^\]]*\])?\s*$")
_TEX_NONNUMBER_RE = re.compile(r"\\(?:notag|nonumber)\b", re.IGNORECASE)
_TEX_UNSUPPORTED_MULTIROW_RE = re.compile(
    r"\\(?:begin|end|intertext|shortintertext|displaybreak|allowdisplaybreaks)\b",
    re.IGNORECASE,
)
_TEX_LEADING_COMMAND_RE = re.compile(
    r"^\s*\\(?:noindent|smallskip|medskip|bigskip|paragraph)\b\s*",
    re.IGNORECASE,
)
_TEX_INLINE_STYLE_RE = re.compile(r"\\(?:textbf|textit|emph)\s*\{")
_TEXT_HEADING_RE = re.compile(
    rf"""
    ^\s*
    (?P<title>{_TEXT_TITLE_PATTERN})\s+
    (?P<label>
        (?:\(\s*(?:[A-Za-z]+\.)?\d+(?:\.\d+)*\s*\)|\d+(?:\.\d+)*|[A-Za-z]+(?:\.\d+)*)
        (?:\s*\(\s*(?:[ivxlcdm]+|[a-z]|\d+)\s*\))?
    )
    (?!\.\d)
    (?:
        (?=\s*(?:$|[.:)\]\-\N{{EN DASH}}\N{{EM DASH}}]))
      # A parenthesized subtitle is part of a visibly titled result even when
      # it begins with mathematical notation or a lowercase word, e.g.
      # ``Definition 1 (gamma-homogeneity)``.  The title/label still have to
      # begin the line, so ordinary inline cross-references remain excluded.
      | (?=\s+\()
      | (?=\s+(?-i:[A-Z]))
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# Some scanned PDFs visibly head a standalone definition as ``DEFINITION.``
# without a number.  It is a source presentation, unlike an ordinary sentence
# mentioning a definition, only when the all-caps heading begins its own line.
# The extractor below gives this narrow form a bounded first-sentence span; it
# never uses a source-map key, a Lean declaration, or a local paper convention
# to infer that boundary.
_TEXT_UNNUMBERED_DEFINITION_HEADING_RE = re.compile(
    r"^\s*(?P<title>DEFINITION)\s*\.\s*(?=\S|$)"
)
_TEXT_UNNUMBERED_DEFINITION_MAX_LINES = 8
# PDF-to-text extraction can interleave two columns onto one line.  When the
# right column begins a decimal-numbered result and its conclusion starts with
# an uppercase token, recover that presentation without treating ordinary
# lower-case cross-references (for example, "Lemma 9.2 we use below") as a
# heading.  The rule is deliberately limited to decimal labels because a
# bare-number title embedded in prose is too ambiguous to index safely.
_TEXT_EMBEDDED_DECIMAL_HEADING_RE = re.compile(
    rf"""
    \b
    (?P<title>{_TEXT_TITLE_PATTERN})\s+
    (?P<label>(?:(?:[A-Za-z]+\.)?\d+\.\d+(?:\.\d+)*))
    (?!\.\d)
    (?=\s+(?-i:[A-Z]))
    """,
    re.IGNORECASE | re.VERBOSE,
)
_TEXT_SUBPART_MARKER_RE = re.compile(
    r"""
    ^\s*
    \(\s*(?P<label>i|ii|iii|iv|v|vi|vii|viii|ix|x|xi|xii)\s*\)
    """,
    re.IGNORECASE | re.VERBOSE,
)
_PROOF_START_RE = re.compile(r"^\s*(?:proof\.?|\\begin\s*\{\s*proof\*?\s*\})", re.I)
_TEXT_PROOF_NARRATIVE_RE = re.compile(
    r"""
    ^\s*(?:
        proof\s+of\b
      | we\s+(?:now\s+|next\s+|then\s+)?(?:prove|show)\b
      | we\s+spend\b.*\bproving\b
      | we\s+turn\s+to\s+(?:the\s+)?proof\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# A text/PDF transcript can defer a proof, so proof markers alone cannot stop
# a named result from absorbing a later paper section. Keep this intentionally
# narrow: standalone closing/back-matter titles and visibly numbered/lettered
# title lines are source-presentation boundaries, while ordinary narrative
# prose (including blank lines inside a displayed conclusion) is not guessed
# to be a boundary.
_TEXT_SECTION_BOUNDARY_RE = re.compile(
    r"""
    ^\s*(?:
        (?i:abstract|introduction|background|conclusion(?:s)?|references|
            acknowledg(?:e)?ments|appendix(?:\s+[A-Z])?)
      |
        (?:\d+(?:\.\d+)*|[A-Z])(?:\s*[.:])?\s+
        (?-i:[A-Z])[A-Za-z0-9][A-Za-z0-9 &'(),/\-]{0,100}
    )\s*$
    """,
    re.VERBOSE,
)
# Some PDF transcripts split a visible section header across two lines, for
# example ``2.4`` followed by ``A Preference for Independence``.  That pair
# is a source-presentation boundary, not part of the preceding theorem.
_TEXT_STANDALONE_DECIMAL_SECTION_RE = re.compile(r"^\s*\d+\.\d+(?:\.\d+)*\s*$")
_TEXT_SECTION_TITLE_LINE_RE = re.compile(
    r"^\s*(?-i:[A-Z])[A-Za-z0-9 &'(),/\-]{0,101}\s*$"
)
_TEXT_REFERENCE_CONTINUATION_RE = re.compile(
    r"^\s*[.:)]?\s*(?:thus|therefore|hence|consequently|similarly|moreover|however|indeed)\b",
    re.IGNORECASE,
)
# PDF extraction can wrap the object of a prose reference onto a fresh line,
# making ``Theorem 2: ...`` look like a heading at column zero.  These are
# source-grammar leads whose unfinished sentence expects a referenced result;
# they do not depend on paper-specific labels, map keys, or Lean names.
_TEXT_PRIOR_NAMED_REFERENCE_LEAD_RE = re.compile(
    r"""
    (?:
        \b(?:see|cf\.?|compare(?:\s+with)?|invoke(?:s|d)?|use(?:s|d)?|using|
            appl(?:y|ies|ied)|illustrat(?:e|es|ed)|summari[sz](?:e|es|ed)|
            confirm(?:s|ed)?|support(?:s|ed)?)
      | \b(?:according\s+to|as\s+(?:shown|stated|proved)\s+in|
            follow(?:s|ed)?\s+from)
    )\s*$
    """,
    re.IGNORECASE | re.VERBOSE,
)
# Captions and labelled deep-only presentations are likewise visible source
# boundaries. They are not theorem obligations in ordinary mode, but a result
# span must not silently absorb one after a transcript blank line.
_TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE = re.compile(
    r"""
    ^\s*(?:figure|table|remark|example|caption)\s+
    (?:\(?[A-Za-z]?\d+(?:\.\d+)*\)?|[A-Z])\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
_ROMAN_SUBPART_LABELS = (
    "i",
    "ii",
    "iii",
    "iv",
    "v",
    "vi",
    "vii",
    "viii",
    "ix",
    "x",
    "xi",
    "xii",
)
_SOURCE_LOCATION_RE = re.compile(
    r"(?P<path>[^\s,:]+):(?P<start>[1-9]\d*)(?:-(?P<end>[1-9]\d*))?"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_ISO_LIKE_UTC_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)
_SOURCE_STATEMENT_TERMINAL_RE = re.compile(r"[.!?](?:[\]\)}\"']*)\s*$")
_SOURCE_STATEMENT_CONTINUATION_RE = re.compile(
    r"^\s*(?:then|and|or|where|provided(?:\s+that)?|if|for\s+(?:every|all))\b",
    re.IGNORECASE,
)

# These are standard AMS/LaTeX display environments.  Their ordinary rendered
# numbers and ``\\label`` keys are cross-reference mechanics, not named
# theoretical source presentations.  They are only indexed when the source
# visibly calls the display a Formula/Equation, for example through a matching
# tag or a source-declared theorem-style title.
_STANDARD_NUMBERED_DISPLAY_ENVIRONMENTS = frozenset(
    {
        "equation",
        "align",
        "alignat",
        "flalign",
        "gather",
        "multline",
    }
)
_STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS = frozenset({"align", "gather"})
_STANDARD_VISIBLE_TITLE_ALIASES = {"eq": "equation", "eqn": "equation"}


@dataclass(frozen=True)
class SourceLineSpan:
    """One source-relative inclusive line span."""

    path: str
    line_start: int
    line_end: int


@dataclass(frozen=True)
class NamedResultPresentation:
    """A named source result discovered from source presentation, not metadata."""

    kind: str
    label: str
    line_start: int
    line_end: int
    presentation: str


@dataclass(frozen=True)
class NamedResultCoverageMatch:
    """One opaque source-map item matched by source-only anchor evidence."""

    item_id: str
    evidence: tuple[str, ...]


@dataclass(frozen=True)
class NamedResultReconciliation:
    """The source-only coverage result for one discovered presentation."""

    presentation: NamedResultPresentation
    matches: tuple[NamedResultCoverageMatch, ...]

    @property
    def covered(self) -> bool:
        return bool(self.matches)


def _normalized_source_text(source_text: str) -> str:
    return source_text.replace("\r\n", "\n").replace("\r", "\n")


def _source_lines(source_text: str) -> list[str]:
    normalized = _normalized_source_text(source_text)
    lines = normalized.split("\n")
    if normalized.endswith("\n"):
        lines.pop()
    return lines


def _strip_tex_comment(line: str) -> str:
    """Remove an unescaped TeX comment while preserving ordinary text."""

    for index, character in enumerate(line):
        if character != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return line[:index]
    return line


def _skip_tex_whitespace_and_comments(source_text: str, cursor: int) -> int:
    """Advance past TeX spacing and whole-line/comment-tail comments."""

    while cursor < len(source_text):
        while cursor < len(source_text) and source_text[cursor].isspace():
            cursor += 1
        if cursor >= len(source_text) or source_text[cursor] != "%":
            return cursor
        newline = source_text.find("\n", cursor)
        if newline < 0:
            return len(source_text)
        cursor = newline + 1
    return cursor


def _parse_tex_delimited_argument(
    source_text: str,
    cursor: int,
    *,
    opening: str,
    closing: str,
) -> tuple[str, int] | None:
    """Parse one balanced, non-verbatim TeX argument from ``cursor``.

    The source indexer is intentionally not a general TeX parser.  This small
    reader is limited to the standard optional and mandatory arguments which
    immediately follow ``\\begin{restatable}``, while still accepting ordinary
    whitespace, comments, nested groups, and escaped delimiters.
    """

    if cursor >= len(source_text) or source_text[cursor] != opening:
        return None
    depth = 1
    content_start = cursor + 1
    cursor += 1
    while cursor < len(source_text):
        character = source_text[cursor]
        if character == "\\":
            # A command or escaped delimiter cannot close this argument.
            cursor += 2
            continue
        if character == "%":
            newline = source_text.find("\n", cursor)
            if newline < 0:
                return None
            cursor = newline + 1
            continue
        if character == opening:
            depth += 1
        elif character == closing:
            depth -= 1
            if depth == 0:
                return source_text[content_start:cursor], cursor + 1
        cursor += 1
    return None


def _restatable_inner_environment(
    source_text: str, cursor: int
) -> str | None:
    """Read the semantic inner environment of a standard ``restatable``.

    ``thmtools`` writes a result as
    ``\\begin{restatable}[optional title]{theorem}{macroName}``.  The first
    mandatory argument controls the rendered theorem-like result; the second
    names a TeX macro and is deliberately not used by the audit index.
    """

    cursor = _skip_tex_whitespace_and_comments(source_text, cursor)
    if cursor < len(source_text) and source_text[cursor] == "[":
        optional_argument = _parse_tex_delimited_argument(
            source_text, cursor, opening="[", closing="]"
        )
        if optional_argument is None:
            return None
        _optional_title, cursor = optional_argument
        cursor = _skip_tex_whitespace_and_comments(source_text, cursor)

    inner_argument = _parse_tex_delimited_argument(
        source_text, cursor, opening="{", closing="}"
    )
    if inner_argument is None:
        return None
    raw_environment, cursor = inner_argument
    cursor = _skip_tex_whitespace_and_comments(source_text, cursor)
    macro_argument = _parse_tex_delimited_argument(
        source_text, cursor, opening="{", closing="}"
    )
    if macro_argument is None or not macro_argument[0].strip():
        return None

    environment = raw_environment.strip().lower()
    if not _TEX_ENVIRONMENT_NAME_RE.fullmatch(environment):
        return None
    return environment


def _presentation_label(kind: str, label: str, line_start: int) -> str:
    text = label.strip()
    return text or f"{kind}@{line_start}"


def _is_numbered_algorithm_label(label: str) -> bool:
    return bool(re.fullmatch(r"(?:\d+(?:\.\d+)*|[A-Za-z]+\.\d+(?:\.\d+)*)", label))


def _normalized_visible_title(title: str) -> str:
    """Normalize a rendered source presentation title for declaration lookup."""

    cleaned = re.sub(r"\\[A-Za-z@]+\*?", " ", title)
    words = re.findall(r"[A-Za-z]+", cleaned.lower())
    return " ".join(words)


def _visible_title_result_kind(title: str) -> str:
    """Return a canonical kind only for an unambiguous visible source title.

    Local environment names are intentionally irrelevant here.  A generic
    source title such as ``Fact`` or ``Property`` may be a theorem-like claim,
    a model axiom, or an empirical observation depending on the paper.  Those
    titles are discovered below but remain unclassified until the source-pinned
    inventory receipt records a declarative classification.
    """

    normalized = _normalized_visible_title(title)
    if normalized in {"open question", "open problem", "conjecture"}:
        return OPEN_NAMED_PRESENTATION_KIND
    if normalized in _STANDARD_VISIBLE_TITLE_ALIASES:
        return _STANDARD_VISIBLE_TITLE_ALIASES[normalized]
    words = normalized.split()
    for word in words:
        singular = word[:-1] if word.endswith("s") else word
        if singular in NAMED_RESULT_KINDS and singular != OPEN_NAMED_PRESENTATION_KIND:
            return singular
    return ""


def _visible_title_is_non_theoretical(title: str) -> bool:
    """Whether a declared source title is a routine non-theory presentation."""

    normalized = _normalized_visible_title(title)
    words = normalized.split()
    return bool(words and words[0] in _NON_THEORETICAL_TITLE_WORDS)


def _declared_tex_environment_titles(source_text: str) -> dict[str, str]:
    """Return visible titles for source-declared theorem-like environments."""

    declaration_text = "\n".join(
        _strip_tex_comment(line) for line in _source_lines(source_text)
    )
    return {
        match.group("environment").strip().lower(): match.group("title").strip()
        for match in _TEX_NEW_THEOREM_RE.finditer(declaration_text)
    }


def _validated_kind_mapping(
    value: Mapping[str, str] | None,
    *,
    field_name: str,
) -> dict[str, str]:
    """Validate a declarative source-presentation classification table."""

    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise ValueError(
            f"{field_name} must be a mapping of source presentation to result kind"
        )
    result: dict[str, str] = {}
    for raw_key, raw_kind in value.items():
        if not isinstance(raw_key, str) or not raw_key.strip():
            raise ValueError(f"{field_name} keys must be nonempty strings")
        if (
            not isinstance(raw_kind, str)
            or raw_kind.strip().lower() not in NAMED_RESULT_KINDS
        ):
            raise ValueError(
                f"{field_name} values must be supported named result kinds"
            )
        result[raw_key.strip().lower()] = raw_kind.strip().lower()
    return result


def _tex_environment_kind_map(
    source_text: str, environment_kinds: Mapping[str, str] | None
) -> tuple[dict[str, str], dict[str, str], frozenset[str]]:
    """Return source-declared and caller-declared TeX environment meanings.

    A declarative mapping resolves only an ambiguous local presentation.  It
    cannot reinterpret a source-visible ``Theorem`` as a definition (or any
    other different kind), since that would weaken the source obligation merely
    through audit metadata.
    """

    result = {kind: kind for kind in NAMED_RESULT_KINDS}
    result.update(
        {
            environment: "equation"
            for environment in _STANDARD_NUMBERED_DISPLAY_ENVIRONMENTS
        }
    )
    declarations = _declared_tex_environment_titles(source_text)
    for environment, title in declarations.items():
        kind = _visible_title_result_kind(title)
        if kind:
            result[environment] = kind
    configured = _validated_kind_mapping(
        environment_kinds, field_name="environment_kinds"
    )
    for environment, configured_kind in configured.items():
        visible_kind = (
            _visible_title_result_kind(declarations[environment])
            if environment in declarations
            else ""
        )
        canonical_kind = visible_kind or result.get(environment, "")
        if canonical_kind and configured_kind != canonical_kind:
            raise ValueError(
                "environment_kinds cannot override unambiguous source presentation "
                f"`{environment}` ({canonical_kind}) as `{configured_kind}`"
            )
        result[environment] = configured_kind
    return result, declarations, frozenset(configured)


def _tex_equation_or_formula_is_named(
    entry: Mapping[str, object], declared_environment_titles: Mapping[str, str]
) -> bool:
    """Whether a display visibly presents itself as a Formula or Equation."""

    tag_kind = _visible_title_result_kind(str(entry.get("tag") or ""))
    if tag_kind in {"equation", "formula"}:
        return True
    environment = str(entry.get("environment") or "")
    declared_kind = _visible_title_result_kind(
        str(declared_environment_titles.get(environment) or "")
    )
    # A ``newtheorem``-style source declaration supplies the visible title
    # even when the author omits a local ``\\label``.
    return declared_kind in {"equation", "formula"}


def _tex_tag_formula_or_equation_kind(tag: str) -> str:
    """Return a Formula/Equation kind only for a visibly titled tag."""

    kind = _visible_title_result_kind(tag)
    return kind if kind in {"equation", "formula"} else ""


def _multiline_display_visible_formula_or_equation_tag(
    source_lines: list[str], entry: Mapping[str, object], line_end: int
) -> tuple[str, str] | None:
    """Return the first explicitly titled Formula/Equation tag in a display."""

    line_start = entry.get("line_start")
    if not isinstance(line_start, int) or line_start < 1 or line_end < line_start:
        return None
    display_text = "\n".join(
        _strip_tex_comment(source_lines[line_number - 1])
        for line_number in range(line_start, line_end + 1)
    )
    for match in _TEX_TAG_RE.finditer(display_text):
        tag = match.group("tag").strip()
        kind = _tex_tag_formula_or_equation_kind(tag)
        if kind:
            return kind, tag
    return None


def _simple_multiline_equation_rows(
    source_lines: list[str], entry: Mapping[str, object], line_end: int
) -> list[NamedResultPresentation] | None:
    """Extract clear physical-line rows from an unstarred ``align``/``gather``.

    This deliberately accepts only the ordinary one-row-per-source-line form.
    Nested displays, multi-line rows, and special alignment commands are left
    unparsed instead of guessing which rendered rows have a visible Formula or
    Equation title. A caller can then retain only an explicit titled tag for
    the enclosing display.
    """

    line_start = entry.get("line_start")
    environment = str(entry.get("environment") or "")
    if (
        not isinstance(line_start, int)
        or line_start < 1
        or line_end <= line_start
        or environment not in _STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS
    ):
        return None

    # A label/tag on the same physical line as ``\\begin`` belongs to the
    # enclosing display rather than an unambiguously identified numbered row.
    opening_line = _strip_tex_comment(source_lines[line_start - 1])
    opening_match = next(
        (
            match
            for match in _TEX_ENV_RE.finditer(opening_line)
            if match.group("action").lower() == "begin"
            and match.group("environment").strip().lower() == environment
        ),
        None,
    )
    if opening_match is None:
        return None
    if _TEX_LABEL_RE.search(opening_line[opening_match.end() :]) or _TEX_TAG_RE.search(
        opening_line[opening_match.end() :]
    ):
        return None

    body_lines = [
        (line_number, _strip_tex_comment(source_lines[line_number - 1]).strip())
        for line_number in range(line_start + 1, line_end)
    ]
    rows = [(line_number, line) for line_number, line in body_lines if line]
    if not rows:
        return None

    presentations: list[NamedResultPresentation] = []
    for index, (row_line, row_text) in enumerate(rows):
        if _TEX_UNSUPPORTED_MULTIROW_RE.search(row_text):
            return None
        row_breaks = list(_TEX_ROW_BREAK_RE.finditer(row_text))
        is_last_row = index == len(rows) - 1
        if len(row_breaks) > 1:
            return None
        if not is_last_row and len(row_breaks) != 1:
            return None
        if row_breaks:
            row_break = row_breaks[0]
            if not _TEX_ROW_BREAK_SUFFIX_RE.fullmatch(row_text[row_break.end() :]):
                return None
            row_body = row_text[: row_break.start()]
        else:
            row_body = row_text
        if not row_body.strip():
            return None

        labels = list(_TEX_LABEL_RE.finditer(row_body))
        tags = list(_TEX_TAG_RE.finditer(row_body))
        if (
            len(labels) > 1
            or len(tags) > 1
            or (r"\label" in row_body and not labels)
            or (r"\tag" in row_body and not tags)
        ):
            return None
        if _TEX_NONNUMBER_RE.search(row_body):
            continue
        tag = tags[0].group("tag").strip() if tags else ""
        visible_kind = _tex_tag_formula_or_equation_kind(tag)
        if not visible_kind:
            continue
        presentations.append(
            NamedResultPresentation(
                kind=visible_kind,
                label=_presentation_label(visible_kind, tag, row_line),
                line_start=row_line,
                line_end=row_line,
                presentation="tex_multiline_display_row",
            )
        )
    return presentations


def extract_tex_named_result_presentations(
    source_text: str, *, environment_kinds: Mapping[str, str] | None = None
) -> list[NamedResultPresentation]:
    """Extract standard named TeX environments with inclusive source spans.

    The TeX environment itself is the source presentation.  Numbered theorem
    environments need not have a ``\\label`` because their rendered number is
    supplied by the document class; a label is retained when present for useful
    diagnostics.  Standard ``\\newtheorem`` declarations are read from the
    source so aliases such as ``thm`` and ``prop`` remain source-visible rather
    than being silently ignored.  ``thmtools`` ``restatable`` wrappers are
    classified from their first inner environment argument, not the outer
    wrapper or its TeX macro identifier.  ``environment_kinds`` permits a
    declarative caller-supplied mapping for document-class-generated aliases.
    Ordinary numbered equation/alignment displays and ``\\label`` keys do not
    enter ordinary named-theory coverage. A Formula/Equation display needs a
    source-visible Formula/Equation title (a matching tag or source-declared
    theorem-style title). Algorithm environments require a caption or label so
    an unnumbered algorithmic implementation block cannot become an obligation.
    """

    (
        resolved_environment_kinds,
        declared_environment_titles,
        _explicitly_configured_environments,
    ) = _tex_environment_kind_map(source_text, environment_kinds)
    active: list[dict[str, Any]] = []
    presentations: list[NamedResultPresentation] = []
    normalized_source_text = _normalized_source_text(source_text)
    source_lines = _source_lines(normalized_source_text)
    source_offset = 0
    for line_number, raw_line in enumerate(source_lines, start=1):
        line = _strip_tex_comment(raw_line)
        events: list[tuple[int, str, re.Match[str]]] = [
            (match.start(), "environment", match)
            for match in _TEX_ENV_RE.finditer(line)
        ]
        events.extend(
            (match.start(), "label", match) for match in _TEX_LABEL_RE.finditer(line)
        )
        events.extend(
            (match.start(), "caption", match)
            for match in _TEX_CAPTION_RE.finditer(line)
        )
        events.extend(
            (match.start(), "tag", match) for match in _TEX_TAG_RE.finditer(line)
        )
        for _offset, event_kind, match in sorted(events, key=lambda event: event[0]):
            if event_kind == "label":
                if active and not active[-1]["label"]:
                    active[-1]["label"] = match.group("label").strip()
                continue
            if event_kind == "caption":
                if active and active[-1]["kind"] == "algorithm":
                    active[-1]["caption"] = match.group("caption").strip()
                continue
            if event_kind == "tag":
                if active and not active[-1]["tag"]:
                    active[-1]["tag"] = match.group("tag").strip()
                continue

            environment = match.group("environment").strip().lower()
            action = match.group("action").lower()
            if action == "begin":
                is_restatable = environment == _TEX_RESTATABLE_ENVIRONMENT
                semantic_environment = environment
                if is_restatable:
                    parsed_environment = _restatable_inner_environment(
                        normalized_source_text, source_offset + match.end()
                    )
                    if parsed_environment is None:
                        # A malformed wrapper has no reliable inner source
                        # presentation. Do not classify it from the wrapper or
                        # from the macro identifier that follows it.
                        continue
                    semantic_environment = parsed_environment

                kind = resolved_environment_kinds.get(semantic_environment)
                if not kind and is_restatable:
                    # The first ``restatable`` argument is a source-visible
                    # theorem-like title. It can therefore carry a standard
                    # meaning even if this file omits the preamble declaration.
                    kind = _visible_title_result_kind(semantic_environment)
                if not kind:
                    declared_title = declared_environment_titles.get(
                        semantic_environment
                    )
                    if declared_title is None:
                        if not is_restatable or _visible_title_is_non_theoretical(
                            semantic_environment
                        ):
                            continue
                        # A restatable wrapper visibly contains a named result,
                        # but its inner source title has no generic meaning.
                        # Preserve it as a source-first closeout blocker rather
                        # than guessing from the inner local environment name.
                        kind = UNCLASSIFIED_NAMED_PRESENTATION_KIND
                        display_kind = (
                            _normalized_visible_title(semantic_environment)
                            or semantic_environment
                        )
                    elif _visible_title_is_non_theoretical(declared_title):
                        continue
                    else:
                        # The source itself visibly declares a named
                        # presentation, but its title has no generic semantic
                        # interpretation. Preserve it as an explicit closeout
                        # blocker rather than guessing from its local
                        # environment name.
                        kind = UNCLASSIFIED_NAMED_PRESENTATION_KIND
                        display_kind = (
                            _normalized_visible_title(declared_title)
                            or semantic_environment
                        )
                else:
                    display_kind = kind
                active.append(
                    {
                        "kind": kind,
                        "display_kind": display_kind,
                        "environment": environment,
                        "semantic_environment": semantic_environment,
                        "line_start": line_number,
                        "label": "",
                        "caption": "",
                        "tag": "",
                        "starred": bool(match.group("star")),
                        "restatable": is_restatable,
                    }
                )
                continue

            matching_index = next(
                (
                    index
                    for index in range(len(active) - 1, -1, -1)
                    if active[index]["environment"] == environment
                ),
                None,
            )
            if matching_index is None:
                continue
            entry = active.pop(matching_index)
            entry_kind = str(entry["kind"])
            if (
                entry_kind == "equation"
                and environment in _STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS
                and not bool(entry["starred"])
            ):
                row_presentations = _simple_multiline_equation_rows(
                    source_lines, entry, line_number
                )
                if row_presentations is not None:
                    presentations.extend(row_presentations)
                    continue
                visible_tag = _multiline_display_visible_formula_or_equation_tag(
                    source_lines, entry, line_number
                )
                if visible_tag is None:
                    # Ordinary alignment row numbers and labels are not named
                    # theoretical presentations. Leave them to deep review.
                    continue
                visible_kind, visible_label = visible_tag
                # The source explicitly names this display Formula/Equation,
                # but its row syntax cannot be safely split. Keep the complete
                # display as one named presentation instead of inventing rows.
                presentations.append(
                    NamedResultPresentation(
                        kind=visible_kind,
                        label=_presentation_label(
                            visible_kind,
                            visible_label,
                            int(entry["line_start"]),
                        ),
                        line_start=int(entry["line_start"]),
                        line_end=line_number,
                        presentation="tex_multiline_named_display",
                    )
                )
                continue
            label = _presentation_label(
                str(entry["display_kind"]),
                str(entry["label"] or entry["tag"]),
                int(entry["line_start"]),
            )
            if (
                not bool(entry.get("restatable"))
                and entry_kind == "algorithm"
                and not (entry["label"] or entry["caption"])
            ):
                continue
            if not bool(entry.get("restatable")) and entry_kind in {
                "equation",
                "formula",
            } and not _tex_equation_or_formula_is_named(
                entry, declared_environment_titles
            ):
                continue
            presentations.append(
                NamedResultPresentation(
                    kind=entry_kind,
                    label=label,
                    line_start=int(entry["line_start"]),
                    line_end=line_number,
                    presentation="tex_environment",
                )
            )
        source_offset += len(raw_line) + 1
    return sorted(
        presentations,
        key=lambda item: (item.line_start, item.line_end, item.kind, item.label),
    )


def _clean_text_heading_line(line: str) -> str:
    cleaned = _TEX_LEADING_COMMAND_RE.sub("", _strip_tex_comment(line))
    cleaned = _TEX_INLINE_STYLE_RE.sub("", cleaned)
    return cleaned.replace("}", "")


def _unclassified_heading_has_formal_label(title: str, label: str) -> bool:
    """Whether an ambiguous source title has a result-like label.

    A numbered or capital-letter ``Model``/``Condition`` may be a paper's
    explicitly named mathematical setup.  An ordinary prose heading such as
    ``Model generalizations`` is not.  This distinction is based only on the
    rendered source title and label, never map keys or Lean declarations.
    Proof-internal ``Case`` headings are deliberately not indexed at all: they
    are neither named source results nor named governing conditions.
    """

    if _visible_title_result_kind(title):
        return True
    normalized_title = _normalized_visible_title(title)
    if normalized_title not in _UNCLASSIFIED_NAMED_TITLE_WORDS:
        return True
    normalized_label = label.strip()
    if re.fullmatch(
        r"\(\s*(?:[A-Za-z]+\.)?\d+(?:\.\d+)*\s*\)|"
        r"(?:[A-Za-z]+\.)?\d+(?:\.\d)*",
        normalized_label,
    ):
        return True
    return bool(re.fullmatch(r"[A-Z](?:\.\d+)*", normalized_label))


def _text_heading_is_sentence_continuation(line: str, match: re.Match[str]) -> bool:
    """Reject a line-broken cross-reference followed by discourse prose.

    A transcript can place ``Definition 1. Thus, ...`` at a fresh line even
    though it continues the preceding proof paragraph.  The visible discourse
    connective is source grammar; no map or Lean identifier participates.
    """

    return bool(_TEXT_REFERENCE_CONTINUATION_RE.match(line[match.end() :]))


def _text_heading_continues_prior_reference(
    lines: list[str], line_number: int
) -> bool:
    """Reject a heading-shaped line that completes unfinished reference prose."""

    if line_number <= 1:
        return False
    prior = _clean_text_heading_line(lines[line_number - 2]).strip()
    if not prior or _SOURCE_STATEMENT_TERMINAL_RE.search(prior):
        return False
    return bool(_TEXT_PRIOR_NAMED_REFERENCE_LEAD_RE.search(prior))


def _text_two_line_section_boundary(lines: list[str], line_number: int) -> bool:
    """Recognize a decimal section number followed by a rendered title line."""

    if not _TEXT_STANDALONE_DECIMAL_SECTION_RE.match(lines[line_number - 1]):
        return False
    next_line = line_number + 1
    while next_line <= len(lines) and not lines[next_line - 1].strip():
        next_line += 1
    return (
        next_line <= len(lines)
        and _TEXT_SECTION_TITLE_LINE_RE.match(lines[next_line - 1]) is not None
    )


def _text_heading_matches(
    lines: list[str], heading_kinds: Mapping[str, str] | None
) -> list[tuple[int, str, str, str]]:
    configured_heading_kinds = _validated_kind_mapping(
        heading_kinds, field_name="heading_kinds"
    )
    headings: list[tuple[int, str, str, str]] = []
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        match = _TEXT_HEADING_RE.match(cleaned)
        if match is None:
            continue
        if _text_heading_is_sentence_continuation(cleaned, match):
            continue
        if _text_heading_continues_prior_reference(lines, line_number):
            continue
        title = match.group("title").strip()
        title_key = _normalized_visible_title(title)
        visible_kind = _visible_title_result_kind(title)
        configured_kind = configured_heading_kinds.get(title_key)
        if visible_kind and configured_kind and configured_kind != visible_kind:
            raise ValueError(
                "heading_kinds cannot override unambiguous source presentation "
                f"`{title}` ({visible_kind}) as `{configured_kind}`"
            )
        kind = visible_kind or configured_kind or UNCLASSIFIED_NAMED_PRESENTATION_KIND
        label = match.group("label").strip()
        if not _unclassified_heading_has_formal_label(title, label):
            continue
        if kind == "algorithm" and not _is_numbered_algorithm_label(label):
            continue
        headings.append((line_number, kind, label, title))
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        for match in _TEXT_EMBEDDED_DECIMAL_HEADING_RE.finditer(cleaned):
            # A start-of-line presentation was already handled by the strict
            # heading matcher above.  This path is only for column-interleaved
            # PDF transcripts.
            if match.start() == 0:
                continue
            title = match.group("title").strip()
            title_key = _normalized_visible_title(title)
            visible_kind = _visible_title_result_kind(title)
            configured_kind = configured_heading_kinds.get(title_key)
            if visible_kind and configured_kind and configured_kind != visible_kind:
                raise ValueError(
                    "heading_kinds cannot override unambiguous source presentation "
                    f"`{title}` ({visible_kind}) as `{configured_kind}`"
                )
            kind = visible_kind or configured_kind or UNCLASSIFIED_NAMED_PRESENTATION_KIND
            label = match.group("label").strip()
            if not _unclassified_heading_has_formal_label(title, label):
                continue
            if kind == "algorithm" and not _is_numbered_algorithm_label(label):
                continue
            headings.append((line_number, kind, label, title))
    # This is intentionally separate from the general heading grammar.  A
    # visible all-caps ``DEFINITION.`` block is a conventional unnumbered
    # source result; broadening the regular expression to arbitrary
    # unnumbered title words would turn ordinary prose into theorem coverage.
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        if _TEXT_UNNUMBERED_DEFINITION_HEADING_RE.match(cleaned) is None:
            continue
        if _text_unnumbered_definition_sentence_end(lines, line_number) is None:
            continue
        headings.append((line_number, "definition", f"@{line_number}", "definition"))
    return sorted(set(headings))


def _text_unnumbered_definition_sentence_end(
    lines: list[str], line_start: int
) -> int | None:
    """Find the bounded terminal line of a visible ``DEFINITION.`` block.

    Source line anchors cannot express a character-range endpoint, so this
    recognizes only a terminal sentence ending within a short consecutive run
    of nonblank source lines.  If a scan/OCR transcript does not expose that
    boundary, no unnumbered result is manufactured from it.
    """

    limit = min(len(lines), line_start + _TEXT_UNNUMBERED_DEFINITION_MAX_LINES - 1)
    for line_number in range(line_start, limit + 1):
        candidate = _clean_text_heading_line(lines[line_number - 1])
        if line_number > line_start and not candidate.strip():
            return None
        if line_number > line_start and (
            _TEXT_HEADING_RE.match(candidate)
            or _PROOF_START_RE.match(candidate)
            or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
            or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
            or _text_two_line_section_boundary(lines, line_number)
        ):
            return None
        heading = _TEXT_UNNUMBERED_DEFINITION_HEADING_RE.match(candidate)
        # A standalone heading's period is punctuation for the visible title,
        # not the terminal punctuation of its definition sentence.
        if (
            _SOURCE_STATEMENT_TERMINAL_RE.search(candidate)
            and not (
                line_number == line_start
                and heading is not None
                and not candidate[heading.end() :].strip()
            )
        ):
            return line_number
    return None


def _text_heading_presentation_label(title: str, label: str) -> str:
    """Render a stable visible label, including unnumbered source headings."""

    if label.startswith("@"):
        return f"{title.title()}{label}"
    return f"{title.title()} {label}"


def _text_subpart_markers(
    lines: list[str],
    headings: list[tuple[int, str, str, str]],
) -> dict[int, list[tuple[int, str]]]:
    """Find visibly enumerated leaves below a named result heading.

    A paper can present one named theorem/lemma followed by several numbered
    conclusion parts.  Those leaves are independent review obligations even
    when the PDF transcript does not repeat ``Theorem`` before every part.
    Detection is source-only: it begins at an actual named heading and accepts
    only an initial sequence of at least two Roman-numeral markers before the
    next named heading or proof.  Ordinary parenthesized model notation such
    as ``(t) iid`` and equation tags such as ``(7)`` are excluded.
    """

    markers_by_heading: dict[int, list[tuple[int, str]]] = {}
    heading_starts = [line_start for line_start, _kind, _label, _title in headings]
    for heading_index, (line_start, _kind, _label, _title) in enumerate(headings):
        next_heading = (
            heading_starts[heading_index + 1]
            if heading_index + 1 < len(heading_starts)
            else len(lines) + 1
        )
        markers: list[tuple[int, str]] = []
        for line_number in range(line_start + 1, next_heading):
            candidate = _clean_text_heading_line(lines[line_number - 1])
            if _PROOF_START_RE.match(candidate) or _TEXT_PROOF_NARRATIVE_RE.match(
                candidate
            ) or _TEXT_SECTION_BOUNDARY_RE.match(candidate) or _text_two_line_section_boundary(
                lines, line_number
            ):
                break
            marker = _TEXT_SUBPART_MARKER_RE.match(candidate)
            if marker is None:
                continue
            label = marker.group("label").strip().lower()
            expected_index = len(markers)
            if (
                expected_index >= len(_ROMAN_SUBPART_LABELS)
                or label != _ROMAN_SUBPART_LABELS[expected_index]
            ):
                if markers:
                    break
                continue
            markers.append((line_number, label))
        # A single enumerated parenthetical phrase is too ambiguous to replace
        # the named parent result.  Multiple sibling markers are a visible
        # source presentation of distinct theorem/lemma parts.
        if len(markers) >= 2:
            markers_by_heading[line_start] = markers
    return markers_by_heading


def _subparts_are_explicit_conditional_antecedents(
    lines: list[str],
    *,
    heading_start: int,
    markers: list[tuple[int, str]],
) -> bool:
    """Recognize a visibly conditional result whose list supplies premises.

    Enumerated leaves normally deserve separate source obligations.  A result
    of the form ``Proposition N. Suppose/Assume ... (i) ... (ii) ... Then
    ...`` is different: the leaves are one conditional statement's
    antecedents, not independent proposition conclusions.  Retain the parent
    presentation in that case.  The test uses only the printed connective
    grammar and never source-map or Lean names.
    """

    if not markers:
        return False
    lead = " ".join(lines[heading_start - 1 : markers[0][0] - 1]).casefold()
    tail_lines: list[str] = []
    for line_number in range(
        markers[-1][0], min(len(lines) + 1, markers[-1][0] + 80)
    ):
        candidate = _clean_text_heading_line(lines[line_number - 1])
        if line_number > markers[-1][0] and (
            _TEXT_HEADING_RE.match(candidate)
            or _PROOF_START_RE.match(candidate)
            or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
            or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
            or _text_two_line_section_boundary(lines, line_number)
        ):
            break
        tail_lines.append(candidate)
    # A bare word occurrence is too weak: an independently claim-bearing
    # subpart can itself say, for example, ``if x, then y``.  Only a printed
    # statement-level `Then` line licenses treating the preceding enumerated
    # leaves as one result's antecedents.  This remains deliberately
    # conservative: an unfamiliar consequent connective leaves the parts
    # separate rather than hiding a paper-facing conclusion.
    has_statement_level_then = any(
        re.match(r"^\s*then\b", line, flags=re.IGNORECASE)
        for line in tail_lines
    )
    return bool(
        re.search(r"\b(?:suppose|assume|assuming)\b", lead)
        and has_statement_level_then
    )


def source_text_uses_conditional_antecedent_subpart_selection(
    source_text: str, *, heading_kinds: Mapping[str, str] | None = None
) -> bool:
    """Whether text exercises conditional-subpart source selection.

    This is intentionally a printed-source grammar predicate.  Callers use it
    only to attach a feature-scoped raw-surface producer identity, so a parser
    repair refreshes papers whose selected source presentation can actually
    change without invalidating unrelated current audit receipts.
    """

    lines = _source_lines(source_text)
    headings = _text_heading_matches(lines, heading_kinds)
    subparts_by_heading = _text_subpart_markers(lines, headings)
    return any(
        _subparts_are_explicit_conditional_antecedents(
            lines,
            heading_start=heading_start,
            markers=markers,
        )
        for heading_start, markers in subparts_by_heading.items()
        if markers
    )


def extract_text_named_result_presentations(
    source_text: str, *, heading_kinds: Mapping[str, str] | None = None
) -> list[NamedResultPresentation]:
    """Extract visible text/PDF-transcript heading presentations by line.

    A heading must begin its own line and use an explicit delimiter or line end
    after its label.  That intentionally excludes ordinary prose such as
    ``Theorem 2 proves ...`` from becoming a new source obligation.
    """

    lines = _source_lines(source_text)
    headings = _text_heading_matches(lines, heading_kinds)
    starts = {line_number for line_number, _kind, _label, _title in headings}
    unnumbered_definition_ends = {
        line_start: _text_unnumbered_definition_sentence_end(lines, line_start)
        for line_start, _kind, label, _title in headings
        if label.startswith("@")
    }
    subparts_by_heading = _text_subpart_markers(lines, headings)
    presentations: list[NamedResultPresentation] = []
    for line_start, kind, label, title in headings:
        unnumbered_definition_end = unnumbered_definition_ends.get(line_start)
        if unnumbered_definition_end is not None:
            presentations.append(
                NamedResultPresentation(
                    kind=kind,
                    label=_text_heading_presentation_label(title, label),
                    line_start=line_start,
                    line_end=unnumbered_definition_end,
                    presentation="text_unnumbered_definition",
                )
            )
            continue
        subparts = subparts_by_heading.get(line_start)
        if subparts and _subparts_are_explicit_conditional_antecedents(
            lines, heading_start=line_start, markers=subparts
        ):
            subparts = None
        if subparts:
            for subpart_index, (subpart_start, subpart_label) in enumerate(subparts):
                next_subpart_start = (
                    subparts[subpart_index + 1][0]
                    if subpart_index + 1 < len(subparts)
                    else len(lines) + 1
                )
                subpart_end = next_subpart_start - 1
                for line_number in range(subpart_start + 1, next_subpart_start):
                    candidate = lines[line_number - 1]
                    if (
                        line_number in starts
                        or _PROOF_START_RE.match(candidate)
                        or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
                        or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
                        or _text_two_line_section_boundary(lines, line_number)
                        or _TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE.match(candidate)
                    ):
                        subpart_end = line_number - 1
                        break
                # Keep the source span complete while avoiding trailing blank
                # transcript lines that carry no part of the visible result.
                while subpart_end > subpart_start and not lines[subpart_end - 1].strip():
                    subpart_end -= 1
                presentations.append(
                    NamedResultPresentation(
                        kind=kind,
                        label=f"{_text_heading_presentation_label(title, label)}({subpart_label})",
                        line_start=subpart_start,
                        line_end=subpart_end,
                        presentation="text_heading_subpart",
                    )
                )
            continue
        line_end = line_start
        for line_number in range(line_start + 1, len(lines) + 1):
            if line_number in starts:
                break
            candidate = lines[line_number - 1]
            if (
                _PROOF_START_RE.match(candidate)
                or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
                or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
                or _text_two_line_section_boundary(lines, line_number)
                or _TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE.match(candidate)
            ):
                break
            # PDF/transcript extraction often inserts blank lines inside a
            # displayed definition or conclusion. A blank line is not source
            # evidence that the named result has ended: retain scanning until
            # the next visible result/proof boundary, but exclude trailing
            # blank lines from the presentation's exact anchor span.
            if candidate.strip():
                line_end = line_number
        presentations.append(
            NamedResultPresentation(
                kind=kind,
                label=_text_heading_presentation_label(title, label),
                line_start=line_start,
                line_end=line_end,
                presentation="text_heading",
            )
        )
    return presentations


def _deduplicate_presentations(
    presentations: Iterable[NamedResultPresentation],
) -> list[NamedResultPresentation]:
    """Collapse text renderings nested inside the same TeX environment."""

    deduplicated: list[NamedResultPresentation] = []
    for candidate in sorted(
        presentations,
        key=lambda item: (
            item.line_start,
            0 if item.presentation == "tex_environment" else 1,
            item.line_end,
            item.kind,
            item.label,
        ),
    ):
        duplicate_index = next(
            (
                index
                for index, existing in enumerate(deduplicated)
                if existing.kind == candidate.kind
                and max(existing.line_start, candidate.line_start)
                <= min(existing.line_end, candidate.line_end)
            ),
            None,
        )
        if duplicate_index is None:
            deduplicated.append(candidate)
        elif candidate.presentation == "tex_environment":
            deduplicated[duplicate_index] = candidate
    return sorted(
        deduplicated,
        key=lambda item: (item.line_start, item.line_end, item.kind, item.label),
    )


def extract_named_result_presentations(
    source_text: str,
    *,
    source_format: str = "auto",
    environment_kinds: Mapping[str, str] | None = None,
    heading_kinds: Mapping[str, str] | None = None,
) -> list[NamedResultPresentation]:
    """Extract named source results from canonical text or TeX source.

    ``source_format`` may be ``"text"``, ``"tex"``, or ``"auto"``.  TeX
    and auto mode both retain visible text headings because some TeX sources use
    manually styled headings rather than theorem environments.
    ``environment_kinds`` classifies document-class/local TeX environments;
    ``heading_kinds`` classifies visible transcript heading titles.  Both are
    declarative source-presentation mappings, never Lean aliases or map keys.
    """

    if source_format not in {"auto", "text", "tex"}:
        raise ValueError("source_format must be one of: auto, text, tex")
    if source_format == "text":
        return extract_text_named_result_presentations(
            source_text, heading_kinds=heading_kinds
        )
    return _deduplicate_presentations(
        [
            *extract_tex_named_result_presentations(
                source_text, environment_kinds=environment_kinds
            ),
            *extract_text_named_result_presentations(
                source_text, heading_kinds=heading_kinds
            ),
        ]
    )


def source_line_spans(source_location: object) -> tuple[SourceLineSpan, ...]:
    """Parse concrete ``path:start[-end]`` spans from source metadata."""

    if not isinstance(source_location, str):
        return ()
    spans: list[SourceLineSpan] = []
    for match in _SOURCE_LOCATION_RE.finditer(source_location):
        line_start = int(match.group("start"))
        line_end = int(match.group("end") or line_start)
        if line_end < line_start:
            continue
        spans.append(
            SourceLineSpan(
                path=match.group("path").strip(),
                line_start=line_start,
                line_end=line_end,
            )
        )
    return tuple(spans)


def _normalized_path(path: str) -> str:
    return posixpath.normpath(path.replace("\\", "/").strip()).lstrip("./")


def source_paths_match(declared_path: object, source_path: object) -> bool:
    """Compare canonical source paths without basename fallback."""

    declared = _normalized_path(str(declared_path or ""))
    expected = _normalized_path(str(source_path or ""))
    return bool(declared and expected and declared == expected)


def _span_contains_presentation(
    line_start: int, line_end: int, presentation: NamedResultPresentation
) -> bool:
    return line_start <= presentation.line_start and presentation.line_end <= line_end


def source_location_covers_presentation(
    source_location: object,
    presentation: NamedResultPresentation,
    *,
    source_path: str = "",
) -> bool:
    """Return whether a concrete source-location range contains the result.

    A heading-only range is not enough to certify the statement below it: the
    source location must cover the complete discovered presentation span.
    """

    return any(
        source_paths_match(span.path, source_path)
        and _span_contains_presentation(span.line_start, span.line_end, presentation)
        for span in source_line_spans(source_location)
    )


def _byte_pinned_anchor_line_span(
    anchor: object,
    *,
    source_text: str,
    source_path: str = "",
) -> tuple[int, int] | None:
    """Return an exact current anchor's inclusive source span, if valid."""

    if not isinstance(anchor, Mapping):
        return None
    line_start = anchor.get("line_start")
    line_end = anchor.get("line_end")
    anchor_path = anchor.get("path")
    quote = anchor.get("quoted_text")
    quote_digest = anchor.get("quoted_text_sha256")
    if (
        not isinstance(anchor_path, str)
        or not anchor_path.strip()
        or not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
        or not isinstance(quote, str)
        or not quote
        or not isinstance(quote_digest, str)
        or not _SHA256_RE.fullmatch(quote_digest.strip())
        or not source_paths_match(anchor_path, source_path)
    ):
        return None
    normalized_quote = _normalized_source_text(quote)
    if (
        hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != quote_digest.strip().lower()
    ):
        return None
    lines = _source_lines(source_text)
    if line_end > len(lines):
        return None
    if normalized_quote != "\n".join(lines[line_start - 1 : line_end]):
        return None
    return line_start, line_end


def byte_pinned_anchor_covers_presentation(
    anchor: object,
    presentation: NamedResultPresentation,
    *,
    source_text: str,
    source_path: str = "",
) -> bool:
    """Validate one exact source quote and test whether it contains a result.

    The required shape matches the repository's source-anchor contract:
    ``path``, integer line bounds, ``quoted_text``, and the SHA-256 of that
    normalized quote.  The quote must equal the exact canonical source line
    slice, and it must span the whole discovered presentation. A source-map
    item therefore cannot claim coverage merely by quoting a heading or one
    convenient line of a longer source statement.
    """

    span = _byte_pinned_anchor_line_span(
        anchor, source_text=source_text, source_path=source_path
    )
    return span is not None and _span_contains_presentation(*span, presentation)


def source_presentation_reconciliation_errors(
    item: object,
    presentations: Iterable[NamedResultPresentation],
    *,
    source_text: str,
    source_path: str = "",
) -> tuple[str, ...]:
    """Validate an optional source-only core for a conservative text span.

    Text/PDF extraction deliberately makes a heading's span conservative when
    it cannot establish where a displayed statement ends.  This opt-in record
    permits a curator to pin a shorter complete statement core, but only when
    the core starts at an independently extracted visible heading, has the
    same visible kind and label, is contained in the item's pre-existing exact
    source evidence, and contains at least one nonblank continuation line.
    It never reads an item key, map summary, or Lean route.
    """

    if not isinstance(item, Mapping):
        return ()
    relation = item.get(SOURCE_PRESENTATION_RECONCILIATION_FIELD)
    if relation is None:
        return ()
    errors: list[str] = []
    if not isinstance(relation, Mapping):
        return (f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD} must be an object",)
    allowed_fields = {
        "schema",
        "relation",
        "presentation_kind",
        "presentation_label",
        SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD,
        "boundary_reason",
        "semantic_basis",
        "validator",
        "validated_at",
    }
    unexpected = sorted(str(key) for key in relation if str(key) not in allowed_fields)
    if unexpected:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if relation.get("schema") != SOURCE_PRESENTATION_RECONCILIATION_SCHEMA:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.schema must be "
            f"{SOURCE_PRESENTATION_RECONCILIATION_SCHEMA}"
        )
    if relation.get("relation") != SOURCE_PRESENTATION_RECONCILIATION_RELATION:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.relation must be "
            f"`{SOURCE_PRESENTATION_RECONCILIATION_RELATION}`"
        )
    boundary_reason = relation.get("boundary_reason")
    if (
        not isinstance(boundary_reason, str)
        or boundary_reason not in SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS
    ):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.boundary_reason must be one of: "
            + ", ".join(sorted(SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS))
        )
    kind = relation.get("presentation_kind")
    label = relation.get("presentation_label")
    if not isinstance(kind, str) or not kind.strip():
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.presentation_kind is required"
        )
    if not isinstance(label, str) or not label.strip():
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.presentation_label is required"
        )
    for field in ("semantic_basis", "validator"):
        value = relation.get(field)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.{field} is required")
    validated_at = str(relation.get("validated_at") or "").strip()
    if not _ISO_LIKE_UTC_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.validated_at must be an ISO-like UTC timestamp"
        )

    core_anchor = relation.get(SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD)
    core_span = _byte_pinned_anchor_line_span(
        core_anchor, source_text=source_text, source_path=source_path
    )
    if core_span is None:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must be an exact current source anchor"
        )
        return tuple(errors)
    core_start, core_end = core_span
    lines = _source_lines(source_text)
    if core_end <= core_start or not any(
        line.strip() for line in lines[core_start:core_end]
    ):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must include a nonblank continuation beyond the heading line"
        )
    elif not _SOURCE_STATEMENT_TERMINAL_RE.search(lines[core_end - 1]):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must end at a complete source-statement terminal"
        )
    elif (
        core_end < len(lines)
        and _SOURCE_STATEMENT_CONTINUATION_RE.match(lines[core_end])
    ):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor stops before a visible statement continuation"
        )

    current_presentations = tuple(presentations)
    candidates = [
        presentation
        for presentation in current_presentations
        if presentation.line_start == core_start
        and presentation.kind == str(kind or "").strip()
        and presentation.label == str(label or "").strip()
    ]
    if len(candidates) != 1:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must begin at exactly one independently extracted presentation with the declared kind and label"
        )
    else:
        candidate = candidates[0]
        if core_end > candidate.line_end:
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must remain inside the independently extracted presentation span"
            )
        nested = [
            presentation
            for presentation in current_presentations
            if presentation != candidate
            and core_start <= presentation.line_start <= core_end
        ]
        if nested:
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor spans another independently extracted presentation"
            )

    anchors = item.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD} requires this item's pre-existing source_anchor_evidence"
        )
    elif not any(
        (span := _byte_pinned_anchor_line_span(
            anchor, source_text=source_text, source_path=source_path
        )) is not None
        and span[0] <= core_start
        and core_end <= span[1]
        for anchor in anchors
    ):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must be contained in an exact current source_anchor_evidence span on the same item"
        )
    return tuple(errors)


def source_presentation_reconciliation_covers_presentation(
    item: object,
    presentation: NamedResultPresentation,
    presentations: Iterable[NamedResultPresentation],
    *,
    source_text: str,
    source_path: str = "",
) -> bool:
    """Whether a valid curated source core is this visible presentation."""

    if not isinstance(item, Mapping) or item.get(
        SOURCE_PRESENTATION_RECONCILIATION_FIELD
    ) is None:
        return False
    if source_presentation_reconciliation_errors(
        item,
        presentations,
        source_text=source_text,
        source_path=source_path,
    ):
        return False
    relation = item[SOURCE_PRESENTATION_RECONCILIATION_FIELD]
    assert isinstance(relation, Mapping)
    core_anchor = relation[SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD]
    core_span = _byte_pinned_anchor_line_span(
        core_anchor, source_text=source_text, source_path=source_path
    )
    assert core_span is not None
    return (
        presentation.kind == relation["presentation_kind"].strip()
        and presentation.label == relation["presentation_label"].strip()
        and presentation.line_start == core_span[0]
    )


def map_item_coverage_match(
    item: object,
    presentation: NamedResultPresentation,
    *,
    source_text: str,
    source_path: str = "",
    presentations: Iterable[NamedResultPresentation] | None = None,
) -> tuple[str, ...]:
    """Return source-only evidence fields by which one map item covers a result."""

    if not isinstance(item, Mapping):
        return ()
    # A dedicated statement-core reconciliation is intentionally exclusive.
    # Its purpose is to keep a broad context/proof anchor from being mistaken
    # for every named heading it happens to contain.  Maps without that opt-in
    # record retain the established exact-full-span behavior below.
    if item.get(SOURCE_PRESENTATION_RECONCILIATION_FIELD) is not None:
        if presentations is None:
            return ()
        return (
            (SOURCE_PRESENTATION_RECONCILIATION_FIELD,)
            if source_presentation_reconciliation_covers_presentation(
                item,
                presentation,
                presentations,
                source_text=source_text,
                source_path=source_path,
            )
            else ()
        )
    evidence: list[str] = []
    if source_location_covers_presentation(
        item.get("source_location"), presentation, source_path=source_path
    ):
        evidence.append("source_location")
    anchors = item.get("source_anchor_evidence")
    if isinstance(anchors, list):
        for index, anchor in enumerate(anchors):
            if byte_pinned_anchor_covers_presentation(
                anchor,
                presentation,
                source_text=source_text,
                source_path=source_path,
            ):
                evidence.append(f"source_anchor_evidence[{index}]")
    return tuple(evidence)


def reconcile_named_result_presentations(
    presentations: Iterable[NamedResultPresentation],
    source_items: object,
    *,
    source_text: str,
    source_path: str = "",
) -> list[NamedResultReconciliation]:
    """Match discovered source presentations to opaque source-map items.

    Map object keys are retained only as report identifiers.  Matching uses no
    key, alias, title, source kind, or Lean-route spelling: it is determined
    solely by source path, source line span, and exact source-anchor evidence.
    """

    items = source_items if isinstance(source_items, Mapping) else {}
    current_presentations = tuple(presentations)
    reconciliations: list[NamedResultReconciliation] = []
    for presentation in current_presentations:
        matches: list[NamedResultCoverageMatch] = []
        for raw_item_id, item in items.items():
            evidence = map_item_coverage_match(
                item,
                presentation,
                source_text=source_text,
                source_path=source_path,
                presentations=current_presentations,
            )
            if evidence:
                matches.append(
                    NamedResultCoverageMatch(
                        item_id=str(raw_item_id), evidence=evidence
                    )
                )
        reconciliations.append(
            NamedResultReconciliation(
                presentation=presentation,
                matches=tuple(sorted(matches, key=lambda match: match.item_id)),
            )
        )
    return reconciliations


def uncovered_named_result_presentations(
    reconciliations: Iterable[NamedResultReconciliation],
) -> list[NamedResultPresentation]:
    """Return discovered presentations that have no source-only map evidence."""

    return [
        reconciliation.presentation
        for reconciliation in reconciliations
        if not reconciliation.covered
    ]


def named_result_presentations_sha256(
    presentations: Iterable[NamedResultPresentation],
) -> str:
    """Return a stable source-only receipt for a discovered presentation set.

    This is deliberately derived from visible source spans and labels, never
    from source-map keys, source kinds, Lean names, or audit routes.  A
    closeout attestation records this receipt alongside the pinned source
    artifact so a stale manual inventory cannot silently survive a source-text
    change.
    """

    payload = [
        {
            "kind": presentation.kind,
            "label": presentation.label,
            "line_start": presentation.line_start,
            "line_end": presentation.line_end,
            "presentation": presentation.presentation,
        }
        for presentation in sorted(
            presentations,
            key=lambda item: (
                item.line_start,
                item.line_end,
                item.kind,
                item.label,
                item.presentation,
            ),
        )
    ]
    encoded = json.dumps(
        payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


__all__ = [
    "NAMED_RESULT_KINDS",
    "OPEN_NAMED_PRESENTATION_KIND",
    "SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS",
    "SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD",
    "SOURCE_PRESENTATION_RECONCILIATION_FIELD",
    "SOURCE_PRESENTATION_RECONCILIATION_RELATION",
    "SOURCE_PRESENTATION_RECONCILIATION_SCHEMA",
    "UNCLASSIFIED_NAMED_PRESENTATION_KIND",
    "NamedResultCoverageMatch",
    "NamedResultPresentation",
    "NamedResultReconciliation",
    "SourceLineSpan",
    "byte_pinned_anchor_covers_presentation",
    "extract_named_result_presentations",
    "extract_tex_named_result_presentations",
    "extract_text_named_result_presentations",
    "map_item_coverage_match",
    "named_result_presentations_sha256",
    "reconcile_named_result_presentations",
    "source_presentation_reconciliation_covers_presentation",
    "source_presentation_reconciliation_errors",
    "source_line_spans",
    "source_location_covers_presentation",
    "source_paths_match",
    "uncovered_named_result_presentations",
]
