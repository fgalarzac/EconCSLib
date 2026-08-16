#!/usr/bin/env python3
"""Focused tests for loader-owned current overlay unioning."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_authenticated_overlay_union as UNION  # noqa: E402


class _LoadedItem(dict[str, object]):
    pass


def _module(
    loader_name: str,
    capability_name: str,
    items: dict[str, object],
) -> SimpleNamespace:
    def load(*_args: object, **_kwargs: object) -> dict[str, object]:
        return items

    return SimpleNamespace(
        **{
            loader_name: load,
            capability_name: lambda value: isinstance(value, _LoadedItem),
        }
    )


def _modules(
    *,
    differential: dict[str, object] | None = None,
    historical: dict[str, object] | None = None,
    semantic_rebind: dict[str, object] | None = None,
    semantic_receipt_exists: bool = False,
    semantic_prepare: object | None = None,
    component_projection: dict[str, object] | None = None,
    component_receipt_exists: bool = False,
) -> dict[str, SimpleNamespace]:
    component_path = SimpleNamespace(is_file=lambda: component_receipt_exists)
    semantic_path = SimpleNamespace(is_file=lambda: semantic_receipt_exists)
    semantic = _module(
        "load_current_source_record_semantic_rebind_items",
        "is_loaded_source_record_semantic_rebind_item",
        semantic_rebind or {},
    )
    semantic.source_record_semantic_rebind_overlay_path = lambda _paper_dir: semantic_path
    semantic.prepare_current_source_record_semantic_rebind_identity_context = (
        semantic_prepare if semantic_prepare is not None else lambda *_args: object()
    )
    return {
        "scoped_receipt": _module(
            "load_current_source_record_scoped_receipt_rebind_items",
            "is_loaded_source_record_scoped_receipt_rebind_item",
            {},
        ),
        "attested_selected": _module(
            "load_current_attested_selected_semantic_reuse_items",
            "is_loaded_source_record_attested_selected_reuse_item",
            {},
        ),
        "schema4_to5": _module(
            "load_current_source_record_schema4_to5_migration_items",
            "is_loaded_source_record_schema4_to5_migration_item",
            {},
        ),
        "differential": _module(
            "load_current_source_record_differential_revalidation_items",
            "is_loaded_source_record_differential_revalidation_item",
            differential or {},
        ),
        # The historical-descriptor capability intentionally accepts this
        # fixture item: in production it is also the public transport through
        # which the semantic-rebind loader exposes its private item token.
        "historical_descriptor": _module(
            "load_current_source_record_historical_descriptor_migration_items",
            "is_loaded_source_record_historical_descriptor_migration_item",
            historical or {},
        ),
        "semantic_rebind": semantic,
        "component_projection": SimpleNamespace(
            component_projection_artifact_path=lambda _paper_dir: component_path,
            load_current_source_record_component_projection_items=(
                lambda *_args, **_kwargs: component_projection or {}
            ),
            is_loaded_source_record_component_projection_item=(
                lambda value: isinstance(value, _LoadedItem)
            ),
        ),
    }


def _identity_evidence(
    *,
    context: object | None = None,
    prepare: object | None = None,
) -> SimpleNamespace:
    """Minimal neutral issuer fixture for synthetic overlay-lane tests."""

    issued = context if context is not None else object()

    def issue(*_args: object, **_kwargs: object) -> object:
        if callable(prepare):
            return prepare(*_args, **_kwargs)
        return issued

    return SimpleNamespace(
        prepare_current_source_record_identity_context=issue,
        current_source_record_identity_context_error=(
            lambda *_args, **_kwargs: ""
        ),
    )


class SourceRecordAuthenticatedOverlayUnionTests(unittest.TestCase):
    def test_strict_union_includes_distinct_semantic_rebind_lane(self) -> None:
        differential = {"current differential group": _LoadedItem({"id": 1})}
        semantic_rebind = {"current semantic rebind group": _LoadedItem({"id": 2})}
        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(
                    differential=differential,
                    semantic_rebind=semantic_rebind,
                    semantic_receipt_exists=True,
                ),
            ),
            patch.object(UNION, "_evidence_module", return_value=_identity_evidence()),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
            actual = UNION.strict_authenticated_current_overlay_union(lanes)
        self.assertEqual(set(actual), set(differential) | set(semantic_rebind))
        self.assertEqual(
            [lane.label for lane in lanes],
            [
                "scoped_receipt",
                "attested_selected",
                "semantic_rebind",
                "schema4_to5",
                "differential",
                "historical_descriptor",
            ],
        )

    def test_strict_union_rejects_cross_lane_collision(self) -> None:
        shared = "one current semantic group"
        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(
                    differential={shared: _LoadedItem({"id": 1})},
                    semantic_rebind={shared: _LoadedItem({"id": 2})},
                    semantic_receipt_exists=True,
                ),
            ),
            patch.object(UNION, "_evidence_module", return_value=_identity_evidence()),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
            with self.assertRaisesRegex(
                UNION.SourceRecordAuthenticatedOverlayUnionError,
                "overlap at current semantic group",
            ):
                UNION.strict_authenticated_current_overlay_union(lanes)

    def test_union_rejects_a_plain_serialized_provenance_mapping(self) -> None:
        with patch.object(
            UNION,
            "_overlay_modules",
            return_value=_modules(
                differential={"current group": {"provenance": "forged"}},
            ),
        ), self.assertRaisesRegex(
            UNION.SourceRecordAuthenticatedOverlayUnionError,
            "without its private capability",
        ):
            UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )

    def test_strict_union_rejects_a_caller_constructed_lane(self) -> None:
        forged = UNION.AuthenticatedCurrentOverlayLane(
            label="differential",
            items={"current group": _LoadedItem({"id": 1})},
            _loader_token=object(),
        )
        with self.assertRaisesRegex(
            UNION.SourceRecordAuthenticatedOverlayUnionError,
                "without loader authority",
            ):
                UNION.strict_authenticated_current_overlay_union((forged,))

    def test_optional_component_lane_is_absent_without_a_receipt(self) -> None:
        with patch.object(UNION, "_overlay_modules", return_value=_modules()):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
        self.assertEqual(
            [lane.label for lane in lanes],
            [
                "scoped_receipt",
                "attested_selected",
                "schema4_to5",
                "differential",
                "historical_descriptor",
            ],
        )

    def test_neutral_identity_context_is_prepared_once_and_not_replayed_by_legacy_lane(
        self,
    ) -> None:
        context = object()
        calls: list[object] = []

        def prepare(*_args: object, **_kwargs: object) -> object:
            calls.append("prepare")
            return context

        modules = _modules(
            semantic_rebind={"exact rebound group": _LoadedItem({"id": 2})},
            semantic_receipt_exists=True,
        )
        semantic = modules["semantic_rebind"]
        original_load = semantic.load_current_source_record_semantic_rebind_items

        def load(*args: object, **kwargs: object) -> object:
            calls.append(kwargs.get("source_record_identity_context"))
            return original_load(*args, **kwargs)

        semantic.load_current_source_record_semantic_rebind_items = load
        historical = modules["historical_descriptor"]
        original_historical_load = (
            historical.load_current_source_record_historical_descriptor_migration_items
        )

        def load_historical(*args: object, **kwargs: object) -> object:
            calls.append(kwargs.get("include_semantic_rebind"))
            return original_historical_load(*args, **kwargs)

        historical.load_current_source_record_historical_descriptor_migration_items = (
            load_historical
        )
        with (
            patch.object(UNION, "_overlay_modules", return_value=modules),
            patch.object(
                UNION,
                "_evidence_module",
                return_value=_identity_evidence(context=context, prepare=prepare),
            ),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
        self.assertEqual(calls.count("prepare"), 1)
        self.assertIn(context, calls)
        self.assertIn(False, calls)
        self.assertEqual(
            set(UNION.strict_authenticated_current_overlay_union(lanes)),
            {"exact rebound group"},
        )

    def test_unselected_semantic_lane_does_not_prepare_an_identity_context(self) -> None:
        calls: list[str] = []

        def prepare(*_args: object) -> object:
            calls.append("prepare")
            return object()

        with patch.object(
            UNION,
            "_overlay_modules",
            return_value=_modules(
                semantic_receipt_exists=True,
                semantic_prepare=prepare,
            ),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"),
                "FixturePaper",
                {"paper": "FixturePaper"},
                lane_labels=("differential",),
            )
        self.assertEqual([lane.label for lane in lanes], ["differential"])
        self.assertEqual(calls, [])

    def test_deferred_semantic_identity_refuses_the_entire_overlay_union(self) -> None:
        """A busy identity gate must not look like an empty optional lane."""

        def deferred(*_args: object, **_kwargs: object) -> object:
            raise RuntimeError(
                "source-record identity revalidation deferred: source-record scan busy"
            )

        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(semantic_receipt_exists=True),
            ),
            patch.object(
                UNION,
                "_evidence_module",
                return_value=_identity_evidence(prepare=deferred),
            ),
            self.assertRaisesRegex(
                UNION.SourceRecordAuthenticatedOverlayUnionError,
                "identity revalidation deferred",
            ),
        ):
            UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )

    def test_component_projection_is_a_new_lane_only_when_its_receipt_exists(self) -> None:
        projected = {"derived child component": _LoadedItem({"id": 3})}
        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(
                    component_projection=projected,
                    component_receipt_exists=True,
                ),
            ),
            patch.object(UNION, "_evidence_module", return_value=_identity_evidence()),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
            actual = UNION.strict_authenticated_current_overlay_union(lanes)
        self.assertEqual(actual, projected)
        self.assertEqual(lanes[-1].label, "component_projection")

    def test_semantic_and_component_lanes_share_one_neutral_identity_context(
        self,
    ) -> None:
        context = object()
        received: list[object] = []
        modules = _modules(
            semantic_rebind={"semantic current group": _LoadedItem({"id": 1})},
            semantic_receipt_exists=True,
            component_projection={"component current group": _LoadedItem({"id": 2})},
            component_receipt_exists=True,
        )
        semantic = modules["semantic_rebind"]
        semantic_load = semantic.load_current_source_record_semantic_rebind_items

        def load_semantic(*args: object, **kwargs: object) -> object:
            received.append(kwargs.get("source_record_identity_context"))
            return semantic_load(*args, **kwargs)

        semantic.load_current_source_record_semantic_rebind_items = load_semantic
        component = modules["component_projection"]
        component_load = component.load_current_source_record_component_projection_items

        def load_component(*args: object, **kwargs: object) -> object:
            received.append(kwargs.get("source_record_identity_context"))
            return component_load(*args, **kwargs)

        component.load_current_source_record_component_projection_items = load_component
        with (
            patch.object(UNION, "_overlay_modules", return_value=modules),
            patch.object(
                UNION,
                "_evidence_module",
                return_value=_identity_evidence(context=context),
            ),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"),
                "FixturePaper",
                {"paper": "FixturePaper"},
            )
        self.assertEqual(received, [context, context])
        self.assertEqual(
            set(UNION.strict_authenticated_current_overlay_union(lanes)),
            {"semantic current group", "component current group"},
        )


if __name__ == "__main__":
    unittest.main()
