# EconCSLib

EconCSLib is a Lean 4 project for checking results in Economics and
Computation. The repository has two roles:

- Build a reusable library of mathematical tools for EC: probability,
  optimization, matching, auctions, online algorithms, fair division, learning,
  and related foundations.
- Keep a paper-by-paper audit trail showing which source definitions and
  theorems have been formalized, which assumptions remain, and where the proof
  deviates from an informal paper argument.

The project is meant to support both formalization work and human review. A
human reader should be able to open a completed paper folder and understand
what was proved without reading the full Lean implementation.

Links:
- [Project website](https://gargnikhil.com/EconCSLib/)
- [Paper describing project](https://arxiv.org/abs/2606.13306)
- [Human quick start guide](docs/paper-formalization-quickstart/README.md)

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

## Reviewing A Formalized Paper

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

## Current Status

See the [project website](https://gargnikhil.com/EconCSLib/) for the current
public paper table. Each paper folder also has a paper-local `status.json`.

Paper IDs and folder names are stable artifact identifiers and may track an
arXiv, conference, or original working-paper year. Public status tables use the
published citation title and year.

For more detail, use:

- `papers/<PaperName>/status.json` for the paper-local source of truth.
- [`papers/human_status.json`](papers/human_status.json) for the compact
  public-facing status summary.
- [`papers/status.json`](papers/status.json) for the generated aggregate
  status, review counts, and interface metadata.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) for the generated public paper
  status table.
- [`site/index.html`](site/index.html) for the generated public website status
  table.
- Individual `papers/<PaperName>/README.md` files for paper-specific caveats.

Partial public formalizations are included when the remaining assumption seam is
explicit and useful to expose. LMMS04 and LOS02 are the current examples:
LMMS04's final complexity claim is held behind an explicit fixed-dimension IP
runtime boundary, and LOS02's final NP-hardness/`NP = ZPP` consequences are
held behind external machine-level complexity facts.

## Starting A New Paper With An Agent

To get started in formalizing your own paper, clone the repository and open an
LLM agent tool (I use Codex with GPT 5.5 in xhigh thinking mode). Give the
agent the paper link, and ask it to formalize the paper using the skill and
workflow in the repository. (And please let me know what your experience is
like!).

Use [docs/AGENT_FORMALIZATION_WORKFLOW.md](docs/AGENT_FORMALIZATION_WORKFLOW.md).
That file is intentionally agent-facing and includes the expected prompts,
artifact checklist, validation commands, and workflow rules.

For a concise prompt template, see
[`docs/paper-formalization-quickstart/README.md`](docs/paper-formalization-quickstart/README.md).

## Development

This project is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

Useful commands:

```bash
lake build EconCSLib
python3 scripts/audit_repository.py
```

`lake build EconCSLib` is the first fresh-clone check and should pass for the
public repository. `python3 scripts/audit_repository.py` is a maintainer audit.
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

## More Documentation

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/PRIVATE_DEVELOPMENT_WORKFLOW.md](docs/PRIVATE_DEVELOPMENT_WORKFLOW.md): private development and public PR workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
