# GitHub Pages Publishing Plan

This document records how to publish the project site when the paper and public
repository are ready.

## Current State

- The public GitHub repository `nikhgarg/EconCSLib` exists and is public.
- The workflow file is tracked as `.github/workflows/pages.yml` and deploys
  from `site/` on pushes to `main` that touch the site or workflow.
- The workflow uses `actions/configure-pages` with `enablement: true`, so the
  first successful deployment should configure Pages for GitHub Actions.
- GitHub Pages is deployed at `https://gargnikhil.com/EconCSLib/`.
- No paper PDF is checked into this public repository yet.
- The default branch is `main`; broad announcement should wait until final
  paper/status review.

## Before Publishing

1. Decide whether the paper PDF should be linked externally or added as a final
   reviewed public artifact.
2. Review `site/index.html` for accurate contact text and non-generated prose.
3. Run `python3 scripts/sync_paper_status.py --check` to confirm
   `papers/status.json`, `papers/human_status.json`, `docs/PAPER_STATUS.md`,
   per-paper `README.md` files, and the generated site status table are in sync. Use
   `papers/status.json` for detailed audit metadata.
4. Confirm no agent or generator edited the root `README.md` unless the user
   gave specific root-README instructions. Human README edits are allowed
   directly and do not require a lock-file refresh.
5. Run `python3 scripts/audit_repository.py` and confirm there are 0 errors.
6. Preview the static site locally, for example:

   ```bash
   python3 -m http.server 8765 --directory site
   ```

   Then check the home page.
6. Push the branch or merge it into `main`.
7. Confirm the Pages workflow deploys successfully.
8. Set the repository homepage URL to the Pages URL once the first deploy
   succeeds.

## Updating After Publication

Treat the site as a summary layer. The source of truth remains:

- paper-local `papers/<PaperName>/status.json` files for status and review
  metadata;
- generated `papers/human_status.json` for compact public status;
- generated `papers/status.json` for detailed aggregate status;
- generated status tables in `docs/PAPER_STATUS.md` and `site/index.html` for
  human summaries;
- paper-local `FINAL_VALIDATION_REPORT.md` files for detailed caveats; and
- `CONTRIBUTING.md` for the contribution policy.

When a paper status changes, update the paper-local `status.json`, run
`python3 scripts/sync_paper_status.py`, then update site prose only if
surrounding non-generated text needs to change. Agents should not update root
README prose unless the user gives specific root-README instructions.
