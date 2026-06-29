# Paper Coverage Audit Workflow

This audit is separate from Lean compilation. A paper can compile while still
having an incomplete or poorly matched human review surface.

## Required Lanes

1. Source inventory.

   Read the source PDF, TeX, or extracted text and build
   `paper_statement_map.json` from the paper itself. Do not build this inventory
   from Lean declaration names. Include theorem/equation numbers, source
   locations, and compact source evidence. Mark final inventories with
   `"source_inventory_kind": "source_curated"` and `"source_curated": true`.

2. Source-to-dashboard matching.

   A separate LLM judge compares each source inventory item with the human
   dashboard rows from `PaperInterface.lean`. Save the result in
   `paper_coverage_llm.json` with:

   - `audit_kind: "source_to_dashboard_llm"` or `"source_to_dashboard_agent"`
   - `source_grounded: true`
   - `review_rows` naming the Lean dashboard rows
   - `source_evidence` from the paper
   - a nontrivial reason explaining why the row covers the source item

   Exact key matching from `scripts/seed_paper_coverage.py` is only a scaffold
   and must not be treated as a completed audit.

3. Row-local statement translation.

   Generate `lean_to_tex_llm.json` from Lean statements alone. Then compare
   that translation against the source statement in `statement_match_llm.json`.
   This checks whether existing rows say what the paper says; it does not check
   whether all paper statements are present.

## Checks

Run:

```bash
python3 scripts/review_dashboard.py --paper <paper-id> --paper-coverage-check
python3 scripts/review_dashboard.py --paper <paper-id> --statement-check
python3 scripts/review_dashboard.py --paper <paper-id> --assumption-check
```

For public-facing papers, all three lanes should be current or the status should
explicitly describe what is missing.
