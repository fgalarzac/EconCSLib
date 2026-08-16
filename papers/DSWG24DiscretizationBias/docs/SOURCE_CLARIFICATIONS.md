# Source Clarifications and Proof-Route Note

## Theorem 1 proof route

The paper sketches a continuous source-transformation argument for the
argmax-bias bound. Its measurable-transformation step and the multiclass
`S_b`/`S_d` mass accounting are not specified enough to serve as a complete
proof route. The checked argument derives the same paper-facing bound directly
from calibration. This changes neither the theorem statement nor the model.

## Theorem 2(iii) weighted-objective wording

The main-text phrase around `gamma = 1` is too broad if read as requiring that
value even when an independent rule already agrees with argmax. Appendix B.1's
switch argument gives the needed statement: a positive disagreement has a
strict improvement for every weighted objective with `0 <= gamma < 1`.

The reference distribution remains the paper's dataset-dependent map, with its
specified mass condition on the selected aggregate-max class. This
clarification preserves the Pareto and weighted-objective endpoint.
