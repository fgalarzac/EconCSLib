#!/usr/bin/env python3
"""Run an exact historical statement-manifest serializer against live Lean.

``historical_statement_manifest_replay`` deliberately has no filesystem or
subprocess authority.  This module is its production runner: it verifies the
historical Git commit and the exact serializer/helper blobs, pins the live
PaperInterface/toolchain/Lake inputs and the full Lean-owned import closure
named by the recipe, and invokes the historical serializer once for the
requested current declarations.

Declaration strings are routing coordinates only.  They are used transiently
to request Lean's elaborated types and are not returned in the observation
payload.  The payload is therefore suitable for the replay bridge, which pairs
receipts solely by source/translation hashes and serializer-owned manifests.

Compatibility boundary: a historical serializer must be self-contained with
its adjacent helper and expose ``run_lean_signature_manifests(root,
import_module, declaration_names, timeout_seconds, build_timeout_seconds)``.
Older serializers that import removed project-local Python modules or require a
different callable convention fail closed rather than receiving a compatibility
shim that could change their output.
"""

from __future__ import annotations

import ast
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Callable, Mapping, Sequence

try:  # Supports package imports and direct focused-test imports.
    from scripts import historical_statement_manifest_replay as replay
    from scripts import lean_import_closure
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import historical_statement_manifest_replay as replay
    import lean_import_closure


DEFAULT_HISTORICAL_SERIALIZER_PATH = "scripts/lean_signature_manifest.py"
DEFAULT_HISTORICAL_HELPER_PATH = "scripts/lean_signature_manifest_helper.lean"
DEFAULT_LEAN_TOOLCHAIN_PATH = "lean-toolchain"
DEFAULT_LAKE_MANIFEST_PATH = "lake-manifest.json"
DEFAULT_NAVIGATION_FIELD = "declaration"
ISOLATED_SERIALIZER_RESULT_SENTINEL = "HISTORICAL_STATEMENT_MANIFEST_RESULT:"

# A historical serializer is executable evidence, not an arbitrary compatibility
# hook.  The only supported legacy surface is a self-contained stdlib Python
# script plus the separately pinned sibling Lean helper.  This is deliberately
# narrower than ``sys.stdlib_module_names``: a stable explicit set makes a
# dependency expansion visible in code review and prevents a project-local
# module from being picked up through an ambient import path.
HISTORICAL_SERIALIZER_STDLIB_IMPORT_ROOTS = frozenset(
    {
        "__future__",
        "contextlib",
        "hashlib",
        "json",
        "os",
        "pathlib",
        "shutil",
        "signal",
        "subprocess",
        "sys",
        "tempfile",
        "typing",
    }
)
_DYNAMIC_IMPORT_CALL_NAMES = frozenset({"__import__", "compile", "eval", "exec"})
_SYS_PATH_MUTATOR_NAMES = frozenset(
    {"append", "clear", "extend", "insert", "pop", "remove", "reverse", "sort"}
)


# The bootstrap is part of this runner's implementation identity.  It receives
# only the verified historical bytes and a JSON request, runs Python in isolated
# mode, and imports the serializer by an explicit file spec rather than through
# ``sys.path``.  The AST gate below admits no project-local Python imports, so
# an old serializer cannot acquire mutable repository Python code through this
# bootstrap.
_ISOLATED_SERIALIZER_BOOTSTRAP = r'''from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


SENTINEL = "HISTORICAL_STATEMENT_MANIFEST_RESULT:"


def _request() -> dict[str, object]:
    value = json.loads(sys.stdin.buffer.read().decode("utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError("historical serializer request is not an object")
    return value


def main() -> int:
    if not sys.flags.isolated:
        raise RuntimeError("historical serializer bootstrap requires python -I")
    request = _request()
    serializer_path = Path(__file__).with_name("lean_signature_manifest.py")
    spec = importlib.util.spec_from_file_location(
        "_econcs_pinned_historical_statement_manifest", serializer_path
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the historical serializer module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    runner = getattr(module, "run_lean_signature_manifests", None)
    if not callable(runner):
        raise RuntimeError("historical serializer has no run_lean_signature_manifests callable")
    result = runner(
        Path(str(request["root"])),
        str(request["import_module"]),
        list(request["declarations"]),
        timeout_seconds=int(request["timeout_seconds"]),
        build_timeout_seconds=int(request["build_timeout_seconds"]),
    )
    if not isinstance(result, dict):
        raise RuntimeError("historical serializer did not return a mapping")
    print(SENTINEL + json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''


class HistoricalStatementManifestRunnerError(RuntimeError):
    """Raised when a recipe-pinned historical serializer cannot be replayed."""


CommandRunner = Callable[[Sequence[str], Path], subprocess.CompletedProcess[bytes]]
HistoricalSerializerExecutor = Callable[
    [
        bytes,
        bytes,
        Path,
        str,
        Sequence[str],
        int,
        int,
    ],
    Mapping[str, Mapping[str, object]],
]
CurrentLeanImportClosureVerifier = Callable[
    [Path, str, Mapping[str, object]], str | None
]


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _module_file_sha256() -> str:
    """Return the runner implementation identity bound by a replay recipe."""

    return _sha256_bytes(Path(__file__).read_bytes())


def historical_statement_manifest_runner_identity_sha256() -> str:
    """Expose the production runner code identity for serializer recipes."""

    return _module_file_sha256()


def _normalized_repo_relative_path(value: str | Path, *, label: str) -> str:
    text = str(value).strip().replace("\\", "/")
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise HistoricalStatementManifestRunnerError(
            f"{label} must be a normalized project-relative path"
        )
    return pure.as_posix()


def current_lean_import_closure_payload_sha256(value: Mapping[str, object]) -> str:
    """Return the canonical digest for a Lean-authored current closure.

    The digest is an execution-input pin only.  Callers must separately obtain
    the full closure from a byte-pinned current audit/cache authority before
    passing it to this runner; this helper deliberately does not treat an
    arbitrary mapping as such authority.
    """

    try:
        return lean_import_closure.lean_import_closure_payload_sha256(value)
    except (TypeError, ValueError) as exc:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure payload is invalid"
        ) from exc


def current_lean_import_closure_canonical_bytes(value: Mapping[str, object]) -> bytes:
    """Encode one validated Lean closure for the runner's exact-byte input."""

    try:
        closure = lean_import_closure.validated_lean_import_closure_payload(value)
    except (TypeError, ValueError) as exc:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure payload is invalid"
        ) from exc
    return json.dumps(
        closure, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def _default_current_lean_import_closure_verifier(
    root: Path,
    paper_interface_path: str,
    closure: Mapping[str, object],
) -> str | None:
    """Validate a saved Lean-owned closure without re-elaborating it."""

    expected = current_lean_import_closure_payload_sha256(closure)
    provider = lean_import_closure.WorktreeImportClosureProvider(
        root,
        eager_source_snapshot=False,
        # The external bridge authenticates the saved closure against a
        # byte-pinned current authority.  Here we need exact current bytes,
        # including a locally edited proof state, not a Git-staging policy.
        allow_dirty_worktree_sources=True,
    )
    try:
        actual, problem = provider.identity_from_saved_closure(
            paper_interface_path, closure
        )
    except Exception as exc:  # pragma: no cover - defensive provider boundary.
        return "could not validate saved Lean import-closure: " + type(exc).__name__
    if problem is not None:
        return problem.format()
    if actual != expected:
        return "saved Lean import-closure digest mismatch"
    finalization = provider.finalization_problems()
    if finalization:
        return "saved Lean import-closure changed during validation: " + finalization[0].format()
    return None


def _validated_current_lean_import_closure(
    value: Mapping[str, object],
    raw_bytes: bytes,
    *,
    paper_interface_path: str,
    import_module: str | None,
) -> dict[str, object]:
    """Validate one caller-carried exact closure payload for this interface."""

    try:
        decoded = json.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure bytes are not a JSON object"
        ) from exc
    if not isinstance(decoded, Mapping) or dict(decoded) != dict(value):
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure bytes do not equal the supplied payload"
        )
    try:
        closure = lean_import_closure.validated_lean_import_closure_payload(value)
    except ValueError as exc:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure payload is invalid"
        ) from exc
    if closure["entrypoint"] != paper_interface_path:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure belongs to a different PaperInterface"
        )
    expected_module = lean_import_closure.module_name_for_path(paper_interface_path)
    if not expected_module or closure["entry_module"] != expected_module:
        raise HistoricalStatementManifestRunnerError(
            "current Lean import-closure has an invalid PaperInterface module binding"
        )
    if import_module is not None and import_module != expected_module:
        raise HistoricalStatementManifestRunnerError(
            "import_module does not match the configured PaperInterface path"
        )
    # Keep an immutable JSON-shaped copy rather than retaining caller-owned
    # nested mappings that could mutate between the pre- and post-execution
    # checks.
    return json.loads(
        json.dumps(closure, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    )


@dataclass(frozen=True)
class HistoricalStatementManifestRunnerConfig:
    """Project-local runtime coordinates, none of which become bridge identity."""

    root: Path
    paper_interface_path: str | Path
    # A static recipe verifier needs only repository paths.  The Lean import
    # module is required exclusively by ``__call__``, which runs the historical
    # serializer.  Keeping it optional here lets evidence/materialization
    # validate Git and current-file pins without inventing a module name.
    import_module: str | None = None
    lean_toolchain_path: str | Path = DEFAULT_LEAN_TOOLCHAIN_PATH
    lake_manifest_path: str | Path = DEFAULT_LAKE_MANIFEST_PATH
    historical_serializer_path: str | Path = DEFAULT_HISTORICAL_SERIALIZER_PATH
    historical_helper_path: str | Path = DEFAULT_HISTORICAL_HELPER_PATH
    navigation_field: str = DEFAULT_NAVIGATION_FIELD
    timeout_seconds: int = 120
    build_timeout_seconds: int = 600
    # A production caller obtains this exact closure payload from a separately
    # byte-pinned current audit/cache authority.  The runner checks only its
    # live execution identity; it never self-attests that provenance.
    current_lean_import_closure: Mapping[str, object] | None = None
    current_lean_import_closure_bytes: bytes | None = None
    # Tests may inject a fixture identity. Production callers leave this unset
    # and recipes are bound to this module's exact bytes.
    runner_identity_sha256: str | None = None

    def __post_init__(self) -> None:
        root = Path(self.root).resolve()
        if not root.is_dir():
            raise HistoricalStatementManifestRunnerError(
                f"runner root does not exist: {root}"
            )
        object.__setattr__(self, "root", root)
        import_module = str(self.import_module or "").strip()
        object.__setattr__(self, "import_module", import_module or None)
        for field_name in (
            "paper_interface_path",
            "lean_toolchain_path",
            "lake_manifest_path",
            "historical_serializer_path",
            "historical_helper_path",
        ):
            object.__setattr__(
                self,
                field_name,
                _normalized_repo_relative_path(
                    getattr(self, field_name), label=field_name
                ),
            )
        navigation_field = str(self.navigation_field or "").strip()
        if not navigation_field:
            raise HistoricalStatementManifestRunnerError("navigation_field is required")
        object.__setattr__(self, "navigation_field", navigation_field)
        if self.timeout_seconds <= 0 or self.build_timeout_seconds <= 0:
            raise HistoricalStatementManifestRunnerError(
                "historical serializer timeouts must be positive"
            )
        closure = self.current_lean_import_closure
        closure_bytes = self.current_lean_import_closure_bytes
        if (closure is None) != (closure_bytes is None):
            raise HistoricalStatementManifestRunnerError(
                "current Lean import-closure payload and exact bytes must be supplied together"
            )
        if closure is not None:
            if not isinstance(closure, Mapping) or not isinstance(closure_bytes, bytes):
                raise HistoricalStatementManifestRunnerError(
                    "current Lean import-closure payload and exact bytes are malformed"
                )
            normalized_closure = _validated_current_lean_import_closure(
                closure,
                closure_bytes,
                paper_interface_path=str(self.paper_interface_path),
                import_module=self.import_module,
            )
            object.__setattr__(
                self, "current_lean_import_closure", normalized_closure
            )
            object.__setattr__(
                self, "current_lean_import_closure_bytes", bytes(closure_bytes)
            )
        if self.runner_identity_sha256 is not None:
            identity = str(self.runner_identity_sha256).strip().lower()
            if len(identity) != 64 or any(char not in "0123456789abcdef" for char in identity):
                raise HistoricalStatementManifestRunnerError(
                    "runner_identity_sha256 must be a SHA-256 digest"
                )
            object.__setattr__(self, "runner_identity_sha256", identity)


def _default_command_runner(
    argv: Sequence[str], cwd: Path
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        list(argv),
        cwd=str(cwd),
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def _is_sys_path_expression(value: ast.AST) -> bool:
    return (
        isinstance(value, ast.Attribute)
        and value.attr == "path"
        and isinstance(value.value, ast.Name)
        and value.value.id == "sys"
    )


def _literal_text(value: ast.AST) -> str | None:
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return value.value
    return None


def historical_serializer_dependency_error(serializer_bytes: bytes) -> str | None:
    """Return why a historical serializer is not self-contained, if any.

    This intentionally checks imports in every lexical scope.  A local import
    inside the serializer's callable is just as capable of resolving mutable
    repository code as a top-level one.  The check is a compatibility gate,
    not a sandbox for hostile code: exact historical bytes remain reviewed and
    Git-pinned separately.
    """

    try:
        source = serializer_bytes.decode("utf-8")
    except UnicodeDecodeError:
        return "historical serializer is not valid UTF-8 Python source"
    try:
        tree = ast.parse(source, filename="pinned_historical_serializer.py")
    except SyntaxError:
        return "historical serializer is not syntactically valid Python"

    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".", 1)[0]
                if root not in HISTORICAL_SERIALIZER_STDLIB_IMPORT_ROOTS:
                    return (
                        "historical serializer imports a non-self-contained "
                        f"module: {root}"
                    )
        elif isinstance(node, ast.ImportFrom):
            if node.level != 0 or not node.module:
                return "historical serializer uses a relative import"
            root = node.module.split(".", 1)[0]
            if root not in HISTORICAL_SERIALIZER_STDLIB_IMPORT_ROOTS:
                return (
                    "historical serializer imports a non-self-contained "
                    f"module: {root}"
                )
        elif isinstance(node, ast.Call):
            function = node.func
            if isinstance(function, ast.Name):
                if function.id in _DYNAMIC_IMPORT_CALL_NAMES:
                    return (
                        "historical serializer uses a dynamic code/import "
                        f"primitive: {function.id}"
                    )
                if function.id == "getattr" and any(
                    _literal_text(argument) == "__import__" for argument in node.args
                ):
                    return "historical serializer dynamically accesses __import__"
            if isinstance(function, ast.Attribute):
                if function.attr == "__import__":
                    return "historical serializer dynamically accesses __import__"
                if (
                    _is_sys_path_expression(function.value)
                    and function.attr in _SYS_PATH_MUTATOR_NAMES
                ):
                    return "historical serializer mutates sys.path"
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets: list[ast.AST]
            if isinstance(node, ast.Assign):
                targets = list(node.targets)
            else:
                targets = [node.target]
            if any(_is_sys_path_expression(target) for target in targets):
                return "historical serializer mutates sys.path"
    return None


def _historical_serializer_subprocess_timeout_seconds(
    declaration_names: Sequence[str],
    *,
    timeout_seconds: int,
    build_timeout_seconds: int,
) -> int:
    """Bound the isolated host process around the legacy per-call limits."""

    # The legacy serializer may build once and issue one bounded helper command
    # per requested declaration.  This outer limit permits that documented
    # behavior while still preventing an orphaned isolated Python process.
    return build_timeout_seconds + timeout_seconds * max(1, len(declaration_names)) + 60


def _isolated_serializer_failure_excerpt(result: subprocess.CompletedProcess[bytes]) -> str:
    raw = result.stderr if isinstance(result.stderr, bytes) else b""
    text = raw.decode("utf-8", errors="replace").strip()
    if not text:
        return ""
    return " (" + " ".join(text.splitlines()[-3:])[-1200:] + ")"


def _default_historical_serializer_executor(
    serializer_bytes: bytes,
    helper_bytes: bytes,
    root: Path,
    import_module: str,
    declaration_names: Sequence[str],
    timeout_seconds: int,
    build_timeout_seconds: int,
) -> Mapping[str, Mapping[str, object]]:
    """Run a self-contained historical serializer in isolated Python.

    No current repository directory is placed on the child module path.  The
    pinned serializer is loaded only by an explicit file spec inside ``python
    -I`` after its AST has established that it has no project-local Python
    imports.  The sibling Lean helper remains adjacent because that is the
    historic serializer's documented data dependency.
    """

    if error := historical_serializer_dependency_error(serializer_bytes):
        raise HistoricalStatementManifestRunnerError(error)

    with tempfile.TemporaryDirectory(
        prefix="econcs-historical-statement-manifest-"
    ) as temp_dir:
        directory = Path(temp_dir)
        serializer_path = directory / "lean_signature_manifest.py"
        helper_path = directory / "lean_signature_manifest_helper.lean"
        bootstrap_path = directory / "historical_serializer_bootstrap.py"
        serializer_path.write_bytes(serializer_bytes)
        helper_path.write_bytes(helper_bytes)
        bootstrap_path.write_text(_ISOLATED_SERIALIZER_BOOTSTRAP, encoding="utf-8")
        request = {
            "schema": 1,
            "root": str(root),
            "import_module": import_module,
            "declarations": list(declaration_names),
            "timeout_seconds": timeout_seconds,
            "build_timeout_seconds": build_timeout_seconds,
        }
        try:
            completed = subprocess.run(
                [sys.executable, "-I", str(bootstrap_path)],
                cwd=str(root),
                input=json.dumps(
                    request, ensure_ascii=True, sort_keys=True, separators=(",", ":")
                ).encode("utf-8"),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=_historical_serializer_subprocess_timeout_seconds(
                    declaration_names,
                    timeout_seconds=timeout_seconds,
                    build_timeout_seconds=build_timeout_seconds,
                ),
            )
        except subprocess.TimeoutExpired as exc:
            raise HistoricalStatementManifestRunnerError(
                "historical serializer isolated subprocess timed out"
            ) from exc
        except OSError as exc:
            raise HistoricalStatementManifestRunnerError(
                "could not start historical serializer isolated subprocess"
            ) from exc
    if completed.returncode != 0:
        raise HistoricalStatementManifestRunnerError(
            "historical serializer isolated subprocess failed"
            + _isolated_serializer_failure_excerpt(completed)
        )
    raw_output = completed.stdout
    if not isinstance(raw_output, bytes):
        raise HistoricalStatementManifestRunnerError(
            "historical serializer isolated subprocess had non-byte output"
        )
    try:
        output_lines = [line for line in raw_output.decode("utf-8").splitlines() if line]
    except UnicodeDecodeError as exc:
        raise HistoricalStatementManifestRunnerError(
            "historical serializer isolated subprocess emitted non-UTF-8 output"
        ) from exc
    if len(output_lines) != 1 or not output_lines[0].startswith(
        ISOLATED_SERIALIZER_RESULT_SENTINEL
    ):
        raise HistoricalStatementManifestRunnerError(
            "historical serializer isolated subprocess did not emit one result"
        )
    try:
        result = json.loads(output_lines[0][len(ISOLATED_SERIALIZER_RESULT_SENTINEL) :])
    except json.JSONDecodeError as exc:
        raise HistoricalStatementManifestRunnerError(
            "historical serializer isolated subprocess emitted malformed JSON"
        ) from exc
    if not isinstance(result, Mapping):
        raise HistoricalStatementManifestRunnerError(
            "historical serializer did not return a mapping"
        )
    return result


@dataclass
class HistoricalStatementManifestRunner:
    """A cached verifier plus callable for one recipe-pinned historical replay."""

    config: HistoricalStatementManifestRunnerConfig
    command_runner: CommandRunner = _default_command_runner
    serializer_executor: HistoricalSerializerExecutor = (
        _default_historical_serializer_executor
    )
    # Test-only injection seam. Production factories retain the default,
    # which checks every saved Lean-owned closure source and artifact.
    current_lean_import_closure_verifier: CurrentLeanImportClosureVerifier = (
        _default_current_lean_import_closure_verifier
    )
    # Git objects are immutable, so their exact byte verification may be
    # retained for this process. Current project files are intentionally not
    # cached: they are checked before and after every serializer execution.
    _verified_git_recipes: dict[str, tuple[dict[str, object], bytes, bytes]] = field(
        default_factory=dict, init=False, repr=False
    )

    def _command_output(self, argv: Sequence[str], *, label: str) -> bytes:
        try:
            result = self.command_runner(tuple(argv), self.config.root)
        except Exception as exc:  # pragma: no cover - defensive injection boundary.
            raise HistoricalStatementManifestRunnerError(
                f"{label} could not start"
            ) from exc
        if not isinstance(result, subprocess.CompletedProcess):
            raise HistoricalStatementManifestRunnerError(
                f"{label} runner did not return a completed process"
            )
        if result.returncode != 0:
            raise HistoricalStatementManifestRunnerError(f"{label} failed")
        stdout = result.stdout
        if isinstance(stdout, str):
            return stdout.encode("utf-8")
        if isinstance(stdout, bytes):
            return stdout
        raise HistoricalStatementManifestRunnerError(f"{label} had non-byte output")

    def _git_text(self, args: Sequence[str], *, label: str) -> str:
        output = self._command_output(("git", *args), label=label)
        try:
            text = output.decode("ascii").strip().lower()
        except UnicodeDecodeError as exc:
            raise HistoricalStatementManifestRunnerError(
                f"{label} had non-ASCII Git output"
            ) from exc
        if not text or "\n" in text:
            raise HistoricalStatementManifestRunnerError(f"{label} had malformed Git output")
        return text

    def _git_blob_bytes(self, object_id: str, *, label: str) -> bytes:
        # ``cat-file blob`` simultaneously checks the exact object id and its
        # object type.  The content hash is checked separately below.
        return self._command_output(
            ("git", "cat-file", "blob", object_id), label=label
        )

    def _configured_path(self, relative_path: str, *, label: str) -> Path:
        path = (self.config.root / relative_path).resolve()
        try:
            path.relative_to(self.config.root)
        except ValueError as exc:
            raise HistoricalStatementManifestRunnerError(
                f"{label} escapes the project root"
            ) from exc
        return path

    def _pinned_file_bytes(self, relative_path: str, expected: str, *, label: str) -> bytes:
        path = self._configured_path(relative_path, label=label)
        try:
            contents = path.read_bytes()
        except OSError as exc:
            raise HistoricalStatementManifestRunnerError(
                f"could not read current {label}"
            ) from exc
        actual = _sha256_bytes(contents)
        if actual != expected:
            raise HistoricalStatementManifestRunnerError(
                f"current {label} bytes do not match the historical serializer recipe"
            )
        return contents

    def _verify_current_lean_import_closure(self, expected: str) -> None:
        """Check the authority-supplied Lean closure against this live worktree.

        ``identity_from_saved_closure`` intentionally does not rerun Lean: the
        bridge has already tied this exact full closure to a byte-pinned
        current authority.  It does recheck every closure source association
        and byte sequence, Lake routing/build controls, and external ``.olean``
        artifact identity.  Any source import edit therefore fails before the
        historical serializer can be credited.
        """

        closure = self.config.current_lean_import_closure
        if not isinstance(closure, Mapping):
            raise HistoricalStatementManifestRunnerError(
                "historical serializer recipe requires a caller-supplied current Lean import-closure payload"
            )
        configured_digest = current_lean_import_closure_payload_sha256(closure)
        if configured_digest != expected:
            raise HistoricalStatementManifestRunnerError(
                "current Lean import-closure payload does not match the historical serializer recipe"
            )
        try:
            error = self.current_lean_import_closure_verifier(
                self.config.root, self.config.paper_interface_path, closure
            )
        except Exception as exc:  # pragma: no cover - defensive injection boundary.
            raise HistoricalStatementManifestRunnerError(
                "could not validate current Lean import-closure payload"
            ) from exc
        if error is not None and not isinstance(error, str):
            raise HistoricalStatementManifestRunnerError(
                "current Lean import-closure verifier returned an invalid result"
            )
        if isinstance(error, str) and error:
            raise HistoricalStatementManifestRunnerError(
                "current Lean import-closure no longer matches the historical serializer recipe: "
                + str(error)
            )

    def _normalized_recipe(self, recipe: Mapping[str, object]) -> dict[str, object]:
        try:
            normalized = replay._serializer_recipe_payload(recipe)
        except replay.HistoricalStatementManifestReplayError as exc:
            raise HistoricalStatementManifestRunnerError(str(exc)) from exc
        configured_identity = (
            self.config.runner_identity_sha256
            or historical_statement_manifest_runner_identity_sha256()
        )
        if normalized["runner_identity_sha256"] != configured_identity:
            raise HistoricalStatementManifestRunnerError(
                "historical serializer recipe names a different runner implementation"
            )
        return normalized

    def _verify_current_execution_inputs(
        self, normalized: Mapping[str, object]
    ) -> None:
        execution = normalized["current_execution_inputs"]
        assert isinstance(execution, Mapping)
        self._pinned_file_bytes(
            self.config.paper_interface_path,
            str(execution["paper_interface_bytes_sha256"]),
            label="PaperInterface",
        )
        self._pinned_file_bytes(
            self.config.lean_toolchain_path,
            str(execution["lean_toolchain_bytes_sha256"]),
            label="lean-toolchain",
        )
        self._pinned_file_bytes(
            self.config.lake_manifest_path,
            str(execution["lake_manifest_bytes_sha256"]),
            label="lake-manifest",
        )
        closure_digest = str(execution.get("lean_import_closure_sha256") or "")
        if len(closure_digest) != 64 or any(
            character not in "0123456789abcdef" for character in closure_digest
        ):
            raise HistoricalStatementManifestRunnerError(
                "historical serializer recipe has no current Lean import-closure digest"
            )
        self._verify_current_lean_import_closure(closure_digest)

    def _verify_recipe(
        self, recipe: Mapping[str, object]
    ) -> tuple[dict[str, object], bytes, bytes]:
        normalized = self._normalized_recipe(recipe)
        recipe_sha = replay.historical_serializer_recipe_sha256(normalized)
        cached = self._verified_git_recipes.get(recipe_sha)
        if cached is not None:
            self._verify_current_execution_inputs(normalized)
            return cached

        commit = str(normalized["historical_git_commit"])
        resolved_commit = self._git_text(
            ("rev-parse", "--verify", f"{commit}^{{commit}}"),
            label="historical Git commit verification",
        )
        if resolved_commit != commit:
            raise HistoricalStatementManifestRunnerError(
                "historical Git commit does not resolve to the pinned object id"
            )

        blob_bytes: dict[str, bytes] = {}
        for blob_field, configured_path in (
            ("historical_serializer_blob", self.config.historical_serializer_path),
            ("historical_helper_blob", self.config.historical_helper_path),
        ):
            blob = normalized[blob_field]
            assert isinstance(blob, Mapping)  # Normalized by the replay module.
            object_id = str(blob["git_object_id"])
            tree_object = self._git_text(
                ("rev-parse", "--verify", f"{commit}:{configured_path}"),
                label=f"historical {blob_field} tree verification",
            )
            if tree_object != object_id:
                raise HistoricalStatementManifestRunnerError(
                    f"historical {blob_field} is not the pinned blob in the pinned commit"
                )
            contents = self._git_blob_bytes(
                object_id, label=f"historical {blob_field} byte verification"
            )
            if _sha256_bytes(contents) != str(blob["bytes_sha256"]):
                raise HistoricalStatementManifestRunnerError(
                    f"historical {blob_field} bytes do not match the recipe"
                )
            blob_bytes[blob_field] = contents

        if dependency_error := historical_serializer_dependency_error(
            blob_bytes["historical_serializer_blob"]
        ):
            raise HistoricalStatementManifestRunnerError(dependency_error)

        # Current source files are an execution precondition, not historic
        # matching data.  Pinning them prevents a replay that happened to run
        # after the source or toolchain moved from being mistaken for old work.
        self._verify_current_execution_inputs(normalized)
        verified = (
            normalized,
            blob_bytes["historical_serializer_blob"],
            blob_bytes["historical_helper_blob"],
        )
        self._verified_git_recipes[recipe_sha] = verified
        return verified

    def verify_recipe(self, recipe: Mapping[str, object]) -> str | None:
        """Return a bridge-compatible error string after validating all pins."""

        try:
            self._verify_recipe(recipe)
        except HistoricalStatementManifestRunnerError as exc:
            return str(exc)
        return None

    def _current_routes(
        self, current_targets: Sequence[Mapping[str, object]]
    ) -> tuple[list[str], dict[str, list[Mapping[str, object]]]]:
        declarations: list[str] = []
        targets_by_declaration: dict[str, list[Mapping[str, object]]] = {}
        seen_target_identity: set[str] = set()
        for position, target in enumerate(current_targets):
            if not isinstance(target, Mapping):
                raise HistoricalStatementManifestRunnerError(
                    f"current target {position + 1} is not an object"
                )
            declaration = str(target.get(self.config.navigation_field) or "").strip()
            if not declaration:
                raise HistoricalStatementManifestRunnerError(
                    f"current target {position + 1} has no navigation declaration"
                )
            try:
                identity = replay.current_target_identity(target)
                target_identity = replay.current_target_identity_sha256(identity)
            except replay.HistoricalStatementManifestReplayError as exc:
                raise HistoricalStatementManifestRunnerError(
                    f"current target {position + 1}: {exc}"
                ) from exc
            if target_identity in seen_target_identity:
                raise HistoricalStatementManifestRunnerError(
                    "current targets have duplicate name-free content identities"
                )
            evidence, evidence_error = replay._current_manifest_evidence(
                target.get("lean_signature_manifest")
            )
            if evidence_error:
                raise HistoricalStatementManifestRunnerError(
                    f"current target {position + 1}: {evidence_error}"
                )
            # Several paper/source target triples may legitimately elaborate
            # through one Lean declaration (for example a component route and
            # its visible statement route).  Routing is not matching: execute
            # that declaration once, then fan its observation out to the
            # separately content-addressed targets below.
            if declaration not in targets_by_declaration:
                declarations.append(declaration)
                targets_by_declaration[declaration] = []
            targets_by_declaration[declaration].append(target)
            seen_target_identity.add(target_identity)
        if not declarations:
            raise HistoricalStatementManifestRunnerError("current target set is empty")
        return declarations, targets_by_declaration

    def __call__(
        self,
        historical_serializer_recipe: Mapping[str, object],
        current_targets: Sequence[Mapping[str, object]],
    ) -> Mapping[str, object]:
        """Return name-free historic observations for the replay bridge.

        The serializer executor is intentionally invoked exactly once, with the
        full declaration list.  A historical implementation may use its own
        bounded internal batching, but this runner never reroutes a failure by
        declaration name or silently falls back to a current serializer.
        """

        import_module = self.config.import_module
        if not import_module:
            raise HistoricalStatementManifestRunnerError(
                "import_module is required to execute the historical serializer"
            )
        normalized, serializer_bytes, helper_bytes = self._verify_recipe(
            historical_serializer_recipe
        )
        declarations, targets_by_declaration = self._current_routes(current_targets)
        try:
            raw_manifests = self.serializer_executor(
                serializer_bytes,
                helper_bytes,
                self.config.root,
                import_module,
                tuple(declarations),
                self.config.timeout_seconds,
                self.config.build_timeout_seconds,
            )
        except HistoricalStatementManifestRunnerError:
            raise
        except Exception as exc:  # pragma: no cover - defensive executor boundary.
            raise HistoricalStatementManifestRunnerError(
                f"historical serializer executor failed: {type(exc).__name__}"
            ) from exc
        if not isinstance(raw_manifests, Mapping):
            raise HistoricalStatementManifestRunnerError(
                "historical serializer did not return a mapping"
            )
        # Detect an edit that raced the historical Lean execution.  The second
        # check is cheap and means the returned observation is pinned to the
        # environment that still exists at return, not merely at launch.
        self._verify_current_execution_inputs(normalized)
        expected_routes = set(declarations)
        returned_routes = set(str(route) for route in raw_manifests)
        if returned_routes != expected_routes:
            missing = len(expected_routes - returned_routes)
            extra = len(returned_routes - expected_routes)
            raise HistoricalStatementManifestRunnerError(
                "historical serializer did not return exactly the requested "
                f"manifest routes (missing={missing}, extra={extra})"
            )

        observations: list[dict[str, object]] = []
        for declaration in declarations:
            historical_manifest = raw_manifests.get(declaration)
            compact_historical, compact_error = replay._compact_historical_outer_manifest(
                historical_manifest
            )
            if compact_error:
                raise HistoricalStatementManifestRunnerError(
                    "historical serializer returned an invalid manifest: "
                    + compact_error
                )
            for target in targets_by_declaration[declaration]:
                evidence, evidence_error = replay._current_manifest_evidence(
                    target.get("lean_signature_manifest")
                )
                if evidence_error:  # Already checked before Lean; keep construction local.
                    raise HistoricalStatementManifestRunnerError(evidence_error)
                observations.append(
                    {
                        "current_target_identity": replay.current_target_identity(target),
                        "historical_manifest_signature_sha256": compact_historical[
                            "sha256"
                        ],
                        "historical_manifest": compact_historical,
                        **evidence,
                    }
                )
        return {
            "historical_serializer_recipe_sha256": replay.historical_serializer_recipe_sha256(
                normalized
            ),
            "verified_historical_git_blobs": {
                "historical_git_commit": normalized["historical_git_commit"],
                "historical_serializer_blob": normalized[
                    "historical_serializer_blob"
                ],
                "historical_helper_blob": normalized["historical_helper_blob"],
            },
            "current_execution_inputs": normalized["current_execution_inputs"],
            "observations": observations,
        }


def make_historical_statement_manifest_runner(
    config: HistoricalStatementManifestRunnerConfig,
    *,
    command_runner: CommandRunner = _default_command_runner,
    serializer_executor: HistoricalSerializerExecutor = _default_historical_serializer_executor,
    current_lean_import_closure_verifier: CurrentLeanImportClosureVerifier = (
        _default_current_lean_import_closure_verifier
    ),
) -> HistoricalStatementManifestRunner:
    """Construct a bridge-compatible, recipe-pinned historic runner."""

    return HistoricalStatementManifestRunner(
        config=config,
        command_runner=command_runner,
        serializer_executor=serializer_executor,
        current_lean_import_closure_verifier=current_lean_import_closure_verifier,
    )


def make_historical_statement_manifest_recipe_verifier(
    *,
    root: Path,
    paper_interface_path: str | Path,
    lean_toolchain_path: str | Path = DEFAULT_LEAN_TOOLCHAIN_PATH,
    lake_manifest_path: str | Path = DEFAULT_LAKE_MANIFEST_PATH,
    historical_serializer_path: str | Path = DEFAULT_HISTORICAL_SERIALIZER_PATH,
    historical_helper_path: str | Path = DEFAULT_HISTORICAL_HELPER_PATH,
    current_lean_import_closure: Mapping[str, object] | None = None,
    current_lean_import_closure_bytes: bytes | None = None,
    runner_identity_sha256: str | None = None,
    command_runner: CommandRunner = _default_command_runner,
    current_lean_import_closure_verifier: CurrentLeanImportClosureVerifier = (
        _default_current_lean_import_closure_verifier
    ),
) -> Callable[[Mapping[str, object]], str | None]:
    """Construct a no-Lean verifier for one exact historic recipe.

    This is deliberately separate from the executable runner.  It validates
    the recipe's Git commit/blob tree, current PaperInterface/toolchain pins,
    and caller-supplied saved Lean closure, but it has neither an import-module
    name nor a serializer executor and therefore cannot route or elaborate any
    Lean declaration.  The caller must obtain that closure from a separately
    byte-pinned current audit/cache authority.
    """

    runner = make_historical_statement_manifest_runner(
        HistoricalStatementManifestRunnerConfig(
            root=root,
            paper_interface_path=paper_interface_path,
            lean_toolchain_path=lean_toolchain_path,
            lake_manifest_path=lake_manifest_path,
            historical_serializer_path=historical_serializer_path,
            historical_helper_path=historical_helper_path,
            current_lean_import_closure=current_lean_import_closure,
            current_lean_import_closure_bytes=current_lean_import_closure_bytes,
            runner_identity_sha256=runner_identity_sha256,
        ),
        command_runner=command_runner,
        current_lean_import_closure_verifier=current_lean_import_closure_verifier,
    )
    return runner.verify_recipe
