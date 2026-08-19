# EconCSLib

EconCSLib is a Lean 4 project research in Economics and
Computation and related applied math fields.  The goal of EconCSLib is to enable researchers to formalize their papers in Lean without knowing Lean themselves. The central design principle is a human-AI-Lean formalization workflow: an LLM writes Lean code, Lean checks formal statements and proofs, and both humans and LLM-as-judge processes can verify that the paper's statements were translated into Lean correctly. We develop agent skills, human-facing reporting, a review dashboard, and auditing procedures to support this workflow.

Links:
- [Project website](https://gargnikhil.com/EconCSLib/)
- [Paper describing project](https://arxiv.org/abs/2606.13306)
- [Slack workspace for applied math modeling in Lean](https://join.slack.com/t/appliedmodelinglib/shared_invite/zt-42slirzxx-rEO8eEns7~4~i3Lbu7N~lA)

If you use this project, please cite the following paper

```
@article{garg2026econcslib,
  title={EconCSLib: AI-Assisted Lean Formalization for Economics \& Computation research},
  author={Garg, Nikhil},
  journal={arXiv preprint arXiv:2606.13306},
  year={2026}
}
```

## Contribute A Paper Formalization

A one-paper contribution has a scoped path: it builds and audits only the paper
being contributed. It does not refresh aggregate status files or audit existing
papers.

```bash
python3 scripts/paper_contribution.py doctor
PAPER=ABC24ShortTitle
PAPER_URL=https://arxiv.org/abs/2401.01234
SOURCE_VERSION='arXiv v2'
WORK_DIR="${HOME}/econcslib-review/$PAPER"
SOURCE_ARTIFACT="$WORK_DIR/paper.pdf"
STATEMENT_SPEC="$WORK_DIR/statement-spec.json"
mkdir -p "$WORK_DIR"
# Copy or download the exact v2 source bytes here before continuing.
test -f "$SOURCE_ARTIFACT"
python3 scripts/paper_contribution.py init-spec \
  "$SOURCE_ARTIFACT" \
  --version "$SOURCE_VERSION" \
  --output "$STATEMENT_SPEC"
```

**STOP before `new`:** edit `$STATEMENT_SPEC`, replace every `REPLACE ...`
value and `replace_with_lean_name`, and add all named theoretical targets in
scope. This guard must print nothing and succeed:

```bash
! grep -nE 'REPLACE|replace_with_lean_name' "$STATEMENT_SPEC"
```

Then scaffold the paper:

```bash
python3 scripts/paper_contribution.py new "$PAPER_URL" \
  --folder "$PAPER" --title "A Short Formalization Example" \
  --authors "Ada Author and Bao Collaborator" \
  --version "$SOURCE_VERSION" \
  --statement-spec "$STATEMENT_SPEC"
```

Keep both inputs outside the repository. Do not stage or commit the source
artifact or statement spec.

Develop in `papers/ABC24ShortTitle/`, then use:

```bash
python3 scripts/paper_contribution.py check ABC24ShortTitle --fast
python3 scripts/paper_contribution.py prepare-pr ABC24ShortTitle --base upstream/main
```

After publication is approved, set the paper-local
`repository_visibility` to `public`, synchronize only that paper, and commit
the candidate before `prepare-pr`. That command runs the full local,
source-present acceptance check. Pull-request CI verifies the same paper in
public-checkout mode but does not replace that source-grounded closeout. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for the short path and
[`docs/NEW_CONTRIBUTOR_WORKFLOW.md`](docs/NEW_CONTRIBUTOR_WORKFLOW.md) for
details.

When using a coding agent, give it the paper URL, exact source version, and
folder name, and ask it to follow the repository's paper-formalization skill
through source inventory, proofs, and paper-scoped closeout.

## How The Repository Is Organized

- `EconCSLib/` is the reusable library. Code here should be paper-independent
  and useful across more than one formalization.
- `papers/` contains one folder per source paper. These folders preserve the
  paper's notation, theorem numbering, proof DAG, validation report, and
  human-facing Lean interface.
- `docs/` contains project documentation. Some files are human-facing strategy
  and status documents; others are detailed conventions for agents and
  maintainers.
- `skills/econcs-formalizer/` contains the agent workflow instructions used to
  formalize papers consistently.

## Human understanding of a Formalized Paper

Start in the paper folder under `papers/<PaperName>/`.

For a completed or nearly completed paper, read these files in this order:

1. `FINAL_VALIDATION_REPORT.md`: source checked, theorem inventory, proof
   deviations, remaining assumptions, and final status.
2. `PaperInterface.lean`: readable definitions and theorem statements matching
   the paper. This is the main human-facing Lean file.
3. Dependency graph: visual map of named definitions, lemmas, theorems, and
   remaining caveats. Some paper folders keep only the source graph tracked and
   render the PDF locally.
4. `README.md`: paper metadata and theorem-status ledger.

Implementation-level proof files are for maintainers and agents. They should
not be necessary for a first human audit of what the paper claims and what Lean
proves.

## Development

This project is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

Maintainer and integration commands:

```bash
lake build EconCSLib
python3 scripts/audit_repository.py
```

`lake build EconCSLib` is the reusable-library check and should pass for the
public repository. `python3 scripts/audit_repository.py` is a maintainer audit.
One-paper contributors should use `scripts/paper_contribution.py check` instead;
they are not expected to run either repository-wide command.
In a fresh clone it may report missing ignored local artifacts such as source
PDFs, rendered dependency-graph PDFs, or review-dashboard caches; those are not
Lean verification failures.

## License

Unless otherwise noted, the Lean source, scripts, documentation, and site source
are licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE).
Source-paper PDFs and extracted text caches are not included in the public
repository unless redistribution rights have been checked separately.

## Separate Library Also Called EconCSLib

See also [this paper](https://arxiv.org/abs/2606.16144) and
[Lean Project](https://github.com/gametheoryinlean/EconCSLib), also called
EconCSLib. The two projects are separate and independently (and concurrently)
developed, with different focuses: our project focuses on automated
formalization of research papers (with human-in-the-loop translation
validation), while their project focuses on human curation (with LLM support)
of a library of concepts for Economics and Computation.

## More documentation for agents

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/NEW_CONTRIBUTOR_WORKFLOW.md](docs/NEW_CONTRIBUTOR_WORKFLOW.md): public repository and contribution workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
