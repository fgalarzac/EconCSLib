# Equation (8) Conditional-Model Clarification

The Appendix calculation behind Equation (8) has two algebraic corrections: it
uses the first post-start gap `t_(m+1) - s` and the residual multiplier
`M! / (e-s)^M`.

Those corrections establish the displayed likelihood factorization only under
a specified conditional observation model. The paper's stated marginal
rate-independence conditions do not themselves determine the live-history
transition law needed to connect the next report with an immediate stopping
response. They also do not by themselves provide a likelihood-preserving bridge
from the paper variables to the conditional model.

Thus the corrected calculation is useful but does not close the full source
observation-model boundary. This is why the paper remains partially formalized;
it is not merely a typographical issue in Equation (8).
