# Theorem 2 Probability-Model Clarification

Theorem 2 describes rank coordinates as iid Bernoulli variables while assigning
the rank-dependent probabilities

```text
q_i = c (i + d)^(-alpha).
```

Except in a constant or degenerate case, rank-dependent probabilities are not
identically distributed. The precise reading is that the rank coordinates are
independent Bernoulli variables with the displayed rank-dependent marginal
schedule.

For the decreasing schedule, every displayed probability must lie in `[0,1]`.
The universal top-one statements also require a nondegenerate first-rank
probability: `c > 0` and `q_1 < 1`. At `c = 0` or `q_1 = 1`, the relevant
objective can be flat and need not force a homogeneous optimum. The
positive-`alpha` all-consumed calculation uses the same independent
rank-varying model; its zero-exponent endpoint is handled separately rather
than by the undefined `1 / alpha` display.

These conditions preserve Theorem 2's displayed rank-dependent model and its
positive-parameter conclusions. They are a correction to the incompatible
"iid" wording, not a change to the theorem's intended result.
