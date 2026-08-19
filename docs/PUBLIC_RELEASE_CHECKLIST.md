# Public Release Checklist

Use this checklist before announcing a public release or inviting broad
external contributions. Checked boxes record the 2026-06-03 release only; a
new release must rerun every applicable item against its exact candidate.

## Repository State

- [x] The intended public branch is clear. Public release docs, the Pages site
      source, and the Pages workflow live on `main`.
- [x] Non-public development work is not converted into the public repository.
- [ ] The candidate was created on a `release/` branch in a separate clean
      worktree from the recorded public base. Only reviewed current-tree
      artifacts are included in the release.
- [ ] The complete export is one squashed release commit whose sole parent is
      the exact recorded public base; there are no stacked or merge commits.
- [ ] Every paper status explicitly sets `repository_visibility` to `public`
      or `private_only`; the public candidate contains only `public` paper
      records. Academic publication metadata was not used as export authority.
- [ ] The release allowlist records one exact file path, source commit,
      rationale, and affirmative public-safety review for every exported path,
      with no directory or unused entries.
- [ ] The deterministic release preflight passes for the clean one-commit
      candidate and exact allowlist. All reported problems were resolved before
      human approval was requested; preflight is not publication authorization.
- [ ] A human reviewer records approval outside the candidate, binding the exact
      candidate and public-base commits, allowlist, guard, reviewed tooling
      provenance, and source-provenance commits. The approval is reviewer-owned
      and is not a repository artifact.
- [ ] `python3 scripts/lean_import_closure.py --candidate index` passes after
      staging, so no tracked entrypoint imports an untracked or unstaged Lean
      module.
- [ ] From the clean committed candidate, run the reviewed release guard with
      its reviewed allowlist. Every included candidate blob has its recorded
      provenance; deletions and generated aggregate files use their explicit
      non-copy provenance modes.
- [x] `lake build EconCSLib` passes from a clean public checkout.
- [x] The top-level `README.md` describes the public repository, not a development
      workspace.
- [x] `docs/PAPER_STATUS.md` matches the paper folders included in the public
      repository.
- [x] Each public `papers/<PaperName>/status.json` is current, and
      `python3 scripts/sync_paper_status.py --check` confirms that the generated
      `papers/status.json`, `papers/human_status.json`, and
      `docs/PAPER_STATUS.md` and `site/index.html` are in sync. Paper-local
      README files are human-owned and are refreshed only with explicit README
      instructions.
- [x] The generated `docs/PAPER_STATUS.md` and site status tables
      summarize the same public paper set, statuses, review counts, Lean LOC,
      and sparse notes as `papers/human_status.json`.
- [x] Status labels use `Formalized`, `Formalized with caveat`, or
      `Partially formalized`; do not publish `Verified in Lean` as a separate
      status category.
- [x] `python3 scripts/audit_repository.py` reports 0 errors. Public-release
      warnings for omitted source PDFs are acceptable when licensing requires
      source PDFs to stay out of the repository.
- [x] `CONTRIBUTING.md` states the current contribution policy and contact
      email.
- [x] `CITATION.cff` has the current repository title, author, and release date.
- [x] A repository license has been chosen and added as `LICENSE` before
      soliciting broad external code contributions.
- [x] The GitHub repository description is set. The homepage field points to
      `https://gargnikhil.com/EconCSLib/`.

## Paper Folder Readiness

Each public paper folder should have:

- [ ] `PaperInterface.lean` as the compact human-facing theorem surface;
- [ ] `Assumptions.lean` if any paper-facing theorem premise remains as an
      explicit source/model assumption;
- [ ] `FINAL_VALIDATION_REPORT.md` or an equivalent validation summary;
- [ ] `docs/DependencyDAG.tex` and a rendered `docs/DependencyDAG.pdf`;
- [ ] checked-in `docs/HUMAN_REVIEW_PACKET.tex` and rendered
      `docs/HUMAN_REVIEW_PACKET.pdf` as the reviewer artifacts. A clean public
      clone may perform only this presentation-only rebuild of existing TeX:
      `python3 scripts/review_dashboard_packet.py --paper <Paper>
      --sanitize-existing --compile`. It rewrites public presentation locators
      and compiles the PDF; it does not recompute semantic Lean displays,
      source excerpts, or audit evidence without the approved review inputs.
      The packet is a review aid, not a substitute for saved human dashboard
      judgments.
- [ ] a current `status.json`, including human-review row counts,
      `review_surface` rows/slices, `assumption_names` for any paper-model
      assumptions, artifact paths, and any PaperInterface maintenance issue;
- [ ] `audit/assumption_match_llm.json` whenever paper-facing theorem premises remain
      as source/model assumptions rather than derived Lean facts;
- [ ] a passing `lake build <PaperTarget>` command; and
- [ ] no tracked source PDFs, extracted source-paper text caches,
      review-dashboard caches, internal planning markdown, or generated
      build artifacts other than intentional public proof/DAG PDFs in `docs/`.
      The sole source exception is a canonical official arXiv `.tex` artifact
      at `papers/<Paper>/source/<file>.tex`, whose candidate bytes exactly
      match the source-map SHA-256 and whose source URL is an arXiv `abs` or
      `e-print` URL. The release guard verifies this exception; archives,
      scans, PDFs, and other extracted source files are excluded from the public release.

## Preparing A Completed Paper For Public Release

- [ ] Confirm the paper is ready for public review.
- [ ] Confirm its status explicitly says `repository_visibility: public`.
- [ ] Select its current-tree files and reusable library changes through the
      reviewed release allowlist. Do not export unreviewed development history.
- [ ] Apply only the reviewed current-tree patch to a clean branch based on
      the recorded public base.
- [ ] Update paper-local `status.json`, run `python3 scripts/sync_paper_status.py`,
      and then update surrounding site prose, roadmap, or release notes only if
      needed. Do not edit the root `README.md` unless the user gives specific
      root-README instructions.

## GitHub Pages Readiness

- [ ] Decide whether the reviewed workshop paper PDF should be linked
      externally or added as a final public artifact.
- [x] Run `python3 scripts/sync_paper_status.py --check` to confirm the site
      status table matches `papers/human_status.json` and
      `docs/PAPER_STATUS.md`.
- [x] The Pages workflow is tracked as `.github/workflows/pages.yml`.
- [x] Confirm the Pages workflow completes and the Pages URL serves the site.
- [x] Enable HTTPS enforcement for GitHub Pages.
