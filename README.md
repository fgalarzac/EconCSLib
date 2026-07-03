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

# Paper Formalization Quickstart guide for humans

To get started in formalizing your own paper, clone the repository. Give the agent (I use Codex with GPT 5.5 in xhigh thinking mode) an arXiv link or paper pdf/source, and also mention where the published version is for its records.

```text
Get context on this repo and skills and formalize
<paper link>.
```
Set a durable goal:
```text
/goal fully formalize <PaperFolder> until full done, and then run the post formalization audit.
```

I often queue up a bunch of
```text
keep going until closeout
```
commands in Codex, but this is increasingly not needed given a goal.

Useful steering advice:
- I often ask it for the status and steer it into proving one thing or another first.
- Often it will state something is a caveat/error in the paper, but I ask it to look for the source assumptions carefully and usually it'll find it.

(And please let me know what your experience is like!).

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

## More documentation for agents

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/PRIVATE_DEVELOPMENT_WORKFLOW.md](docs/PRIVATE_DEVELOPMENT_WORKFLOW.md): private development and public PR workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
