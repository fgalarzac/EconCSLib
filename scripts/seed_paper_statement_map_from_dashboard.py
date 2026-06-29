#!/usr/bin/env python3
"""Create a self-contained paper_statement_map.json from dashboard rows.

This is a seeding helper, not a substitute for source reading.  It makes the
coverage audit concrete by materializing the current paper-facing review target
inventory with direct statement text, source URL metadata, and row-name aliases.
Agents should then compare this inventory against the actual paper source and
add missing source statements or mark out-of-scope items explicitly.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import date
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

sys.path.insert(0, str(ROOT / "scripts"))
from review_dashboard import PAPER_STATEMENT_MAP_FILE, review_items_for_paper  # noqa: E402

SOURCE_URLS = {
    "DSWG24DiscretizationBias": "https://arxiv.org/pdf/2405.16762",
    "GCG24UserItemFairness": "https://openreview.net/pdf?id=ZOZjMs3JTs; https://arxiv.org/pdf/2412.04466",
    "GGSG19TopThree": "https://arxiv.org/pdf/1906.08160",
    "GHW01DigitalGoods": "http://www.eecs.northwestern.edu/~hartline/papers/auctions-SODA-01.pdf; journal cross-check: http://www.eecs.northwestern.edu/~hartline/papers/auctions-journal.pdf; https://doi.org/10.1016/j.geb.2006.02.003",
    "GJ18InformativeRatingSystems": "https://arxiv.org/pdf/1810.13028",
    "GKGMM19IterativeLocalVoting": "https://arxiv.org/pdf/1702.07984; published article: https://doi.org/10.1613/jair.1.11358",
    "GN21DriverSurgePricing": "https://arxiv.org/pdf/1905.07544; published article: https://doi.org/10.1287/mnsc.2021.4058",
    "GS62CollegeAdmissions": "https://doi.org/10.1080/00029890.1962.11989827; https://www.jstor.org/stable/2312726",
    "LBG24SpatialUnderreporting": "https://arxiv.org/pdf/2204.08620; published article: https://doi.org/10.1038/s43588-023-00572-6",
    "LG21TestOptionalPolicies": "https://arxiv.org/pdf/2107.08922; published proceedings: https://doi.org/10.1145/3465416.3483293",
    "LMMS04FairDivision": "https://www.stat.berkeley.edu/~mossel/publications/happy.pdf; https://doi.org/10.1145/988772.988792",
    "LOS02CombinatorialAuctions": "https://arxiv.org/pdf/cs/0202017v1; https://doi.org/10.1145/585265.585266",
    "MBJG25ProducerFairness": "https://arxiv.org/pdf/2207.04369; published article: https://doi.org/10.1609/icwsm.v19i1.35865",
    "MSVV07AdWords": "https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf; https://doi.org/10.1145/1284320.1284321",
    "PKG25NoFreeLunch": "https://ojs.aaai.org/index.php/AAAI/article/view/33574/35729; https://arxiv.org/pdf/2411.15230",
    "PRPKG24AccuracyDiversity": "https://arxiv.org/pdf/2307.15142",
    "Roth82StableMatching": "https://web.stanford.edu/~alroth/papers/1982_MOR_EconomicsOfMatching.pdf; https://doi.org/10.1287/moor.7.4.617",
}


def load_status_title(folder: Path) -> str:
    path = folder / "status.json"
    if not path.exists():
        return folder.name
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return folder.name
    return str(payload.get("title") or folder.name)


def item_statement(item: Any) -> str:
    for value in (item.paper_statement, item.source_note, item.agent_statement, item.lean_statement):
        text = str(value or "").strip()
        if text:
            return text
    return f"Paper-facing dashboard statement for `{item.name}`."


def map_payload(folder: Path) -> dict[str, Any]:
    items = review_items_for_paper(folder, use_cache=True)
    source_url = SOURCE_URLS.get(folder.name, "")
    return {
        "schema": 1,
        "paper": folder.name,
        "title": load_status_title(folder),
        "generated_at": date.today().isoformat(),
        "source_inventory_kind": "dashboard_seeded_preliminary",
        "source_curated": False,
        "source_inventory_policy": (
            "Self-contained source-statement inventory seeded from the current "
            "paper-facing review dashboard after source PDF/text acquisition. "
            "Each row remains subject to the paper-level coverage LLM audit; "
            "add source statements not represented by dashboard rows or mark "
            "them out of scope explicitly. Do not treat this as a source-curated "
            "claim that every named paper statement has been found."
        ),
        "source_url": source_url,
        "items": {
            item.name: {
                "statement": item_statement(item),
                "source_url": source_url,
                "source_location": (
                    item.source_status
                    or item.source_note
                    or "paper-facing review target; exact source location to be refined"
                ),
                "aliases": [item.name],
            }
            for item in items
        },
    }


def paper_folders(paper: str | None) -> list[Path]:
    if paper:
        folder = PAPERS_DIR / paper
        if not folder.is_dir():
            raise SystemExit(f"unknown paper folder: {paper}")
        return [folder]
    return sorted(
        folder
        for folder in PAPERS_DIR.iterdir()
        if folder.is_dir() and folder.name != "TEMPLATE" and (folder / "PaperInterface.lean").exists()
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", default="", help="Optional paper folder to seed.")
    parser.add_argument("--write", action="store_true", help="Write paper_statement_map.json.")
    parser.add_argument("--force", action="store_true", help="Overwrite an existing map.")
    args = parser.parse_args()
    for folder in paper_folders(args.paper or None):
        payload = map_payload(folder)
        path = folder / PAPER_STATEMENT_MAP_FILE
        print(f"{folder.name}: dashboard_rows={len(payload['items'])} map_exists={path.exists()}")
        if not args.write:
            continue
        if path.exists() and not args.force:
            continue
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
