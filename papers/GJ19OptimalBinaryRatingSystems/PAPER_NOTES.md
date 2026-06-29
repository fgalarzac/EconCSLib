# Designing Optimal Binary Rating Systems Formalization Notes

This is a lightweight source-to-Lean mapping note.

- Namespace: `GJ19OptimalBinaryRatingSystems`
- Official URL: https://proceedings.mlr.press/v89/garg19a.html
- Source PDFs: `source/garg19a.pdf`, `source/garg19a-supp.pdf`
- Local source text cache: `source/garg19a.txt`, `source/garg19a-supp.txt`
  (ignored by Git in public workspaces)
- Local arXiv TeX cache, when present: `source_tex/arxiv_1806.06908`
  (ignored by Git)

## Closeout

- Date reviewed: 2026-06-28
- Status: formalized.
- Build target: `lake build GJ19OptimalBinaryRatingSystems`
- Final validation report: `FINAL_VALIDATION_REPORT.md`
- Detailed audit: `POST_FORMALIZATION_AUDIT.md`

The formalization covers the finite binary-rating large-deviation layer,
Theorem 3.1, Lemma C.3, Lemma C.4, Lemmas C.5-C.12, Theorem 3.2 certificate
rows, Appendix B.1/B.2/B.3, and the Kendall/Spearman examples.

## Maintenance Notes

- Use `README.md` and `status.json` as the current human- and machine-readable
  status sources.
- Use `POST_FORMALIZATION_AUDIT.md` for agent-facing details about proof
  interface reducers and source-condition packages.
- Do not convert proof-interface reducers in `Assumptions.lean` into public
  status qualifications unless a future source audit identifies a genuine
  source discrepancy.
