# Final Validation Report: Gale-Shapley 1962
Updated: 2026-08-16

## 1. Human Verdict

**Formalized.** The two displayed college definitions, the Section 3 definition
of unstable marriage, Theorem 1, and Theorem 2 have source-faithful statements
and closed proofs. No source-paper caveat is needed. Independent human review
has not yet been recorded.

## 2. Closeout Status

- Completion status: Formalized.
- Normal scope: five source items, comprising three definitions and two named
  theorems.
- Source coverage: five of five normal-scope items covered.
- All five items have current formalization evidence. Independent human review
  has not yet been recorded.

## 3. Source and Scope

The source is D. Gale and L. S. Shapley, *College Admissions and the
Stability of Marriage*, *American Mathematical Monthly* 69(1), 1962, printed
pages 9--15 ([public record](https://www.jstor.org/stable/2312726)).

Normal scope includes the
paper's displayed Definitions on printed page 10, the result-bearing Section 3
prose definition, and Theorems 1--2. The three numerical examples and
unnumbered procedure consequences are outside this theorem surface.

## 4. Researcher Summary of Checked Results

The marriage definition says an assignment is unstable exactly when a man and
woman prefer one another to their actual mates. Theorem 1 is formalized for two
distinct finite sides of equal cardinality with complete strict preferences;
it returns a complete assignment with no such pair.

For college admissions, the formalized surface includes the literal displayed
replacement-pair instability definition and the literal applicant-optimality
definition over fixed-quota feasible assignments. The Theorem 2 route makes
the paper's intended completed stability convention explicit: quota
feasibility, individual rationality, and no mutually acceptable block through
either a vacancy or replacement of a current assignee.

Theorem 2 formalizes the Section 4 applicant-proposing procedure: its outcome
is stable and every applicant weakly prefers it to any other stable assignment.

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

The finite rejection argument is a reusable route to applicant optimality for
many-to-one deferred-acceptance procedures.

## 9. Generalizations, Conjectures, and Extensions

The finite applicant-optimality argument may extend to other many-to-one
deferred-acceptance settings; no additional paper claim is made here.

## 10. Source Clarifications and Exact Readings

None found. The stability completion discussed below is an interpretation made
explicit by the paper's procedure and proof, not a proposed change to its main
result.

## 11. Paper Issues or Caveats

None.
