# Source Clarifications: PKG25 No Free Lunch for Human--AI Collaboration

This note supplies the source-level detail for Section 10 of the final
validation report.  The anchors identify the byte-pinned cited publication
record used for review.
The entries are local corrections or clarified mathematical readings; the
forward no-free-lunch result is unchanged.

| Source anchor | Clarification or correction | Effect |
| --- | --- | --- |
| `cited publication:27-30` | The opening expectation of absolute prediction error is a 0--1 loss, not accuracy.  Accuracy is expected correctness as used in the later agent formula and proof. | The two quantities are not conflated. |
| `cited publication:31-35` | Point-conditioned calibration on a zero-probability prediction fiber is read as an equality for measurable prediction events. | Calibration is defined for atomic and atomless prediction laws without choosing a null-fiber conditional probability. |
| `cited publication:104-117` | A single positive-mass point where one classifier is correct and another is incorrect does not by itself make the former strictly more accurate; the total accuracy difference must be positive. | The strict comparison is used only with its required aggregate inequality. |
| `cited publication:123-144` | Proposition 6 samples component `m` with weight `lambda_m`, not the free-index weight `lambda_ell` in the prose. | The finite mixture has its intended normalization. |
| `cited publication:151-156` | The partition construction needs finite measurable cells and a stated value for a null cell. | The calibrated-predictor construction is well-defined on the stated class of partitions. |
| `cited publication:159-172` | The proof discussion's converse at a boundary profile is not implied by the interior fixed-agent/fixed-tie condition in Definition 4. | Only the forward no-free-lunch theorem is claimed. |
| `cited publication:280-288` | The first Proposition 9 construction requires `0 < epsilon < 1/2`, not only `epsilon < 1/2`. | Both induced profiles are interior probability vectors. |
| `cited publication:300-340` | The second Proposition 9 mass normalizes over both odds families; the printed denominator leaves one index free. | The displayed construction defines one probability distribution. |
