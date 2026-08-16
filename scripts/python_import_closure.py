#!/usr/bin/env python3
"""Resolve a repository-local Python import closure for advisory cache keys.

This helper is deliberately not an audit authority.  It makes an ignored
planner cache fail closed when a transitive local implementation dependency
changes, without turning workflow code into paper evidence.
"""

from __future__ import annotations

import ast
from pathlib import Path
from typing import Iterable


class PythonImportClosureError(ValueError):
    """A local entrypoint could not be read or parsed coherently."""


def _module_candidates(root: Path, module: str) -> tuple[Path, ...]:
    if not module:
        return ()
    relative = Path(*module.split("."))
    return (root / relative.with_suffix(".py"), root / relative / "__init__.py")


def _local_module_path(root: Path, module: str) -> Path | None:
    matches = [
        path.resolve() for path in _module_candidates(root, module) if path.is_file()
    ]
    if len(matches) > 1:
        raise PythonImportClosureError(
            f"local Python module ownership is ambiguous: {module}"
        )
    return matches[0] if matches else None


def _package_initializers(root: Path, module: str) -> set[Path]:
    initializers: set[Path] = set()
    parts = module.split(".")
    for index in range(1, len(parts)):
        candidate = root.joinpath(*parts[:index]) / "__init__.py"
        if candidate.is_file():
            initializers.add(candidate.resolve())
    return initializers


def _module_name(root: Path, path: Path) -> str:
    relative = path.resolve().relative_to(root.resolve())
    parts = list(relative.with_suffix("").parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def _imported_local_paths(root: Path, path: Path, tree: ast.AST) -> set[Path]:
    current_module = _module_name(root, path)
    current_package = (
        current_module
        if path.name == "__init__.py"
        else current_module.rpartition(".")[0]
    )
    imported: set[Path] = set()
    for node in ast.walk(tree):
        names: list[str] = []
        if isinstance(node, ast.Import):
            for alias in node.names:
                names.append(alias.name)
                if path.parent == root / "scripts" and not alias.name.startswith(
                    "scripts."
                ):
                    names.append(f"scripts.{alias.name}")
        elif isinstance(node, ast.ImportFrom):
            base_parts = current_package.split(".") if current_package else []
            if node.level:
                drop = node.level - 1
                if drop > len(base_parts):
                    continue
                base_parts = base_parts[: len(base_parts) - drop]
            elif node.module and not node.module.startswith("scripts"):
                # Direct-script fallbacks such as ``from helper import x`` live
                # beside files under scripts/.  Prefer that local candidate.
                base_parts = ["scripts"] if path.parent == root / "scripts" else []
            else:
                base_parts = []
            module_parts = list(base_parts)
            if node.module:
                module_parts.extend(node.module.split("."))
            base = ".".join(part for part in module_parts if part)
            if base:
                names.append(base)
            for alias in node.names:
                if alias.name == "*":
                    continue
                names.append(".".join(part for part in (base, alias.name) if part))
        elif (
            isinstance(node, ast.Call)
            and node.args
            and isinstance(node.args[0], ast.Constant)
            and isinstance(node.args[0].value, str)
            and (
                isinstance(node.func, ast.Name)
                and node.func.id == "__import__"
                or isinstance(node.func, ast.Attribute)
                and node.func.attr == "import_module"
            )
        ):
            names.append(node.args[0].value)
        for name in names:
            candidate = _local_module_path(root, name)
            if candidate is not None:
                imported.add(candidate)
                imported.update(_package_initializers(root, name))
    return imported


def repository_python_import_closure(
    root: Path,
    entrypoints: Iterable[Path],
) -> tuple[Path, ...]:
    """Return the transitive local module files selected by Python imports."""

    root = root.resolve()
    pending = [path.resolve() for path in entrypoints]
    seen: set[Path] = set()
    while pending:
        path = pending.pop()
        try:
            path.relative_to(root)
        except ValueError as exc:
            raise PythonImportClosureError(
                f"Python advisory entrypoint escapes the repository: {path}"
            ) from exc
        if path in seen:
            continue
        try:
            source = path.read_text(encoding="utf-8")
            tree = ast.parse(source, filename=str(path))
        except (OSError, UnicodeError, SyntaxError) as exc:
            raise PythonImportClosureError(
                f"could not parse advisory Python dependency {path}: {exc}"
            ) from exc
        seen.add(path)
        pending.extend(_imported_local_paths(root, path, tree) - seen)
    return tuple(sorted(seen, key=str))
