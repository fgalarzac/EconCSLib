# Source clarifications

## Lemma 1 and Proposition 1: calendar-time first reports

For the steady-state results, an observed incident is one whose **first report
time** lies in the calendar-time observation interval. It is not an incident
whose birth lies in that interval and which will eventually be reported. Thus
an incident born before the left endpoint can contribute to the observed count
when its first report occurs inside the interval.

The formal model uses a stationary Poisson process of incident births. Each
incident has an iid duration with the source density on nonnegative durations.
Up to its first report, its homogeneous Poisson report clock is independent of
that duration. Equivalently, conditional on duration `t`, its probability of
no report before the duration ends is `exp (-lambda * t)`. Consequently the
retention probability in Lemma 1 is

\[
  p = \int_0^\infty \bigl(1-\exp(-\lambda t)\bigr) f(t)\,dt.
\]

The calendar-time first-report process is the image of the retained marked
birth process under `birth time + first-report delay`. The required result is
therefore the stationary marked-displacement theorem: this image is a
homogeneous Poisson process with rate `Lambda p`. Proposition 1's unit-window
law of large numbers and its nonidentifiability conclusion use that same
calendar-time process.

This clarification concerns the pre-first-report duration/report relation. It
does not require later response or observation-end behavior to be independent
of the report history.

Source anchors: Lemma 1 and Proposition 1 (Appendix B.1; `cited publication:1433-1542`),
and the paper's incident, reporting, and observed-data model
(`cited publication:194-220`).

## Theorem 1 and Appendix Theorem 2: causal endpoint policy

The endpoint is one realized stopping time. Given the visible report history,
the policy may react to that history, but it does not inspect the next
unobserved report time or depend directly on the reporting-rate parameter. At
each live history, the next report clock and the immediate endpoint response
are combined causally; the earlier event either produces the next report or
sets the unique endpoint. A fixed cap, an inspection, or a work order is
covered by this policy. The scalar endpoint density in the source is the
absolutely continuous branch of the underlying endpoint kernel.

The full theorem permits a selected start after the first report. Its
selection is rate-free conditional on the retained pre-start report history;
the formal result keeps that history in the conditioning state rather than
specializing the theorem to the first report.

Source anchors: Theorem 1 and Appendix Theorem 2 (`cited publication:254-300;1565-1590`),
and the NYC observation-window application (`cited publication:2086-2110`).

## Equation (3): rate-estimation convention

The maximum-likelihood statement is read on nonnegative reporting rates with
strictly positive total observation exposure. At zero total report count, the
estimator is zero and is a maximizer on that nonnegative domain.

Source anchor: Equation (3), `cited publication:279-291`.
