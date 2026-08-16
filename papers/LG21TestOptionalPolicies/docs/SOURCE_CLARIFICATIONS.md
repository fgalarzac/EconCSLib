# Source Clarifications: LG21 Test-Optional Policies

This note gives the source-level detail behind Section 10 of the final
validation report.  The anchors refer to the private pinned source surface.
It distinguishes local corrections from the approved Theorem 3.2 reading and
does not claim a broader archival equivalence than stated below.

| Source anchor | Clarification or correction | Effect |
| --- | --- | --- |
| Theorem 3.1, `source.txt:1134-1172; 1233-1267` | The no-report mixture uses the below-cutoff mass `C Pr(score < c) = C(1-A(c))`, not the printed reporting mass. | The fixed-point calculation uses the intended mixture. |
| Theorem 3.1, `source.txt:1268-1390` | The cutoff argument requires lower-tail mass and first-moment continuity, positive denominator, and endpoint signs; pointwise finiteness alone is insufficient. | The fixed-point step has the analytic premises it uses. |
| Theorem 3.2, `source.txt:199-218; 256-395; 455-461; 1614-1778` | The approved reading uses deterministic output after a reported score, an arbitrary common law on no-report/no-take, finite expectations, and separate optional-reporting and report-required schedules. | This is the stated approved corrected target; it does not assert equivalence with the archival arbitrary-randomized-policy statement. |
| Theorem 3.2 summary, `source.txt:1770-1782` | The final reference is read as `observable`, not `demographic`, consistently with the theorem's argument. | The local word choice does not change the result's mathematical content. |
| Lemma 4.1, `source.txt:2183-2220; 2262-2310` | The score cutoff is the affine inverse solving `intercept + slope * score = qTilde`. | The threshold calculation uses the displayed equation. |
| Proposition 4.3, `source.txt:2495-2505` | The relevant comparison is unconditional Gaussian precision, not an inference from a conditional comparison to a marginal one. | The precision conclusion is checked on the appropriate probability law. |
