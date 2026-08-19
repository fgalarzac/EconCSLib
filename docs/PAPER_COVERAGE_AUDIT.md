# Paper Coverage Audit Workflow

This audit is separate from Lean compilation. A paper can compile while its
paper-facing surface is incomplete, weakened, or matched only by names. The
source, not a declaration, map key, or dashboard-row name, determines what
needs coverage.

## Audit Modes

The default mode is `named_theoretical_statements`. Its surface is every
independently source-presented named definition, theorem, proposition, lemma,
corollary, theorem-like labelled claim, explicit named assumption or model,
and named appendix theoretical result. It also includes an unlabelled
condition only when that condition is a dependency of a selected item. A
standalone formula, equation, algorithm, computational claim, or complexity
claim is deep-only unless it is needed to state or prove a selected named
theoretical item.

Figures, tables, captions, numerical examples, simulations, empirical
material, and other unlabelled prose are outside this default surface. Audit
those only under the explicit
`deep_paper_with_all_prose_claims` mode. Do not quietly expand normal mode
because an item looks mathematically interesting, and do not quietly exclude a
selected named item because it looks computational or informal.

## Required Evidence

1. **Independent source presentation receipt.**

   Build a source-only named-presentation index from a canonical text or TeX
   artifact. Pin that artifact's path and SHA-256 in the receipt, along with the
   index digest. A PDF or archive may be provenance, but normal-mode indexing
   must use a stable, reviewable text/TeX transcript.

   In the current map, the receipt is
   `source_named_result_inventory_review`: schema, `complete: true`, validator,
   method, timestamp, current `source_artifact_sha256`, and
   `discovered_named_result_sha256` are all required. Put custom source
   classification tables in its `environment_kinds` and `heading_kinds` fields.

   The receipt must also explicitly enumerate every definition-shaped prose
   presentation in `prose_definition_presentations`, even when the list is
   empty, and pin the complete list digest. Each entry records the exact
   defined object or predicate, full byte-pinned definitional clause, and a
   source-only `scope_disposition`. Normal named-theory definitions reconcile
   one-to-one to source-map items. Local proof notation, computational
   definitions, and other deep-only definitions remain in the complete ledger
   with content-pinned independent scope judgments and cannot acquire normal
   coverage credit. A catch-all deep-only exclusion additionally requires an
   explicit user approval; a reason alone cannot hide a paper-facing
   definition or mechanism. A repeated presentation remains byte-pinned in the ledger and may
   point to one canonical normal definition only through its own independently
   reviewed, content-pinned semantic-restatement receipt; it does not create a
   duplicate proof obligation.

   The index must not read the Lean interface, map routes, or Lean declaration
   names. Map custom source environments or headings to presentation kinds
   declaratively in the receipt; do not infer their meaning from a matching Lean
   name. An unclassified named presentation blocks closeout until it is
   classified or explicitly mapped. A named open problem is retained in the
   receipt with an explicit source-declared-open, nonproof disposition rather
   than being silently dropped or treated as a theorem target. Its source-map
   item uses `source_kind: "open_problem"`, `claim_bearing: false`,
   `source_scope_classification: "source_declared_open_nonresult_observation"`, and
   `coverage_status`/`protocol_role: "source_declared_open"`, with a pinned
   anchor, source evidence, and scope reason.

   A prose-definition reconciliation is a semantic judgment, not an anchor
   overlap. It pins both the complete source presentation and the exact current
   source-map statement, records an explicit semantic-equivalence verdict and
   reviewer identity, and fails closed if either side changes. Map keys,
   `source_kind`, Lean routes, and a free-text note cannot establish the
   correspondence.

   Semantic reuse retains the immutable presentation, disposition, alias,
   relation, and map-statement pins. Reviewer identity, timestamp, and
   explanatory prose remain mandatory audit evidence but are not mathematical
   identity, so refreshing those credentials does not rerun unchanged work.

2. **Source inventory and semantic coverage.**

   Build `audit/paper_statement_map.json` from that source surface. Each
   selected item needs source evidence, a source semantic identity, and a
   byte-pinned locator. The map may use aliases and Lean declaration routes for
   navigation only.

   A covered item must match a unique, current, fully elaborated Lean
   signature and explain the semantic correspondence: assumptions,
   quantifiers, domains, representations, output, algorithm semantics, and
   advertised complexity where applicable. Matching a source number, map key,
   theorem name, or final prose is never coverage. A noncomputable existence
   wrapper does not cover an advertised algorithm or runtime result.

3. **Row-local statement and premise audit.**

   Audit each selected Lean statement against its source item, then audit
   source premises at their actual granularity. An added Lean premise may be a
   documented boundary only when it is genuinely a source condition or an
   explicitly accepted additional assumption. A weakened or missing source
   conclusion is a coverage failure, not a conditional boundary.

4. **Joined validation.**

   A source item is clean only when its source receipt, semantic coverage
   record, current elaborated Lean signature, and row-local judgment all agree.
   Conditional rows must be visible as conditional in the source coverage
   record. A blank or seeded sidecar is pending evidence, not passing evidence.

## Item-Level Reuse

Reuse is an optimization, never evidence. Cache validity is evaluated per item
using the current source-semantic digest schema, the item's source semantic
digest, and a unique current fully elaborated Lean signature/dependency
identity. A map-key, route, declaration-name, source-file, or line-number
rename can rebind only when those semantic identities are unchanged and the
rebind is unique.

Moving a canonical artifact without changing its item semantics may preserve an
item's semantic cache entry. Every normal source check still byte-validates each
reused anchor against the current artifact, so a moved locator cannot bypass
the semantic digest; changed artifact bytes are therefore caught immediately.
Ambiguous rebinding, missing pins, changed quoted text, or a changed elaborated
signature fails closed. Normal reads and checks write no cache files; an
explicit refresh is the only operation that writes updated receipts or sidecars.

## Proof-First Operation

During a proof campaign, establish the source mode, source receipt, selected
item/dependency map, audited `PaperInterface.lean` skeleton, and next proof
seam. Then work on proofs. Update documentation only at material boundaries:
changed source scope, a resolved/created proof obligation, a status transition,
or final closeout. Do not turn routine proof iterations into repeated broad
audits or documentation churn.

## Checks

Run the targeted paper lanes after their inputs are stable:

```bash
python3 scripts/review_dashboard.py --paper <paper-id> --paper-coverage-check
python3 scripts/review_dashboard.py --paper <paper-id> --source-to-lean-check
python3 scripts/review_dashboard.py --paper <paper-id> --statement-check
python3 scripts/review_dashboard.py --paper <paper-id> --assumption-check
```

For public-facing papers, all required lanes must be current or the paper's
status must accurately describe the remaining boundary. A check that cannot
confirm current evidence is failing until it is repaired or refreshed.
