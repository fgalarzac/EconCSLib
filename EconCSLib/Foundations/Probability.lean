import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.Averaging
import EconCSLib.Foundations.Probability.Bernoulli
import EconCSLib.Foundations.Probability.BinaryRatingLDP
import EconCSLib.Foundations.Probability.BoundedDensity
import EconCSLib.Foundations.Probability.BivariateGaussian
import EconCSLib.Foundations.Probability.CTMC
import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.Foundations.Probability.ContinuousReward
import EconCSLib.Foundations.Probability.Exponential
import EconCSLib.Foundations.Probability.ExponentialMemoryless
import EconCSLib.Foundations.Probability.ExponentialInterarrival
import EconCSLib.Foundations.Probability.ExponentialInterarrivalBoundedStopping
import EconCSLib.Foundations.Probability.ExponentialInterarrivalBoundedStoppingBlock
import EconCSLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import EconCSLib.Foundations.Probability.ExponentialInterarrivalFuture
import EconCSLib.Foundations.Probability.ExponentialInterarrivalPostArrival
import EconCSLib.Foundations.Probability.ExponentialInterarrivalIncrementBoundary
import EconCSLib.Foundations.Probability.ExponentialInterarrivalDeterministicNoArrival
import EconCSLib.Foundations.Probability.ExponentialInterarrivalResidualTail
import EconCSLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail
import EconCSLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import EconCSLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import EconCSLib.Foundations.Probability.ExponentialInterarrivalRenewalCount
import EconCSLib.Foundations.Probability.ExponentialInterarrivalErlang
import EconCSLib.Foundations.Probability.ExponentialGammaConvolution
import EconCSLib.Foundations.Probability.ExponentialGammaCDF
import EconCSLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import EconCSLib.Foundations.Probability.EquilibriumPoissonBase
import EconCSLib.Foundations.Probability.PoissonEquilibriumHalves
import EconCSLib.Foundations.Probability.PoissonSuspensionProductFactors
import EconCSLib.Foundations.Probability.FairCoin
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts
import EconCSLib.Foundations.Probability.FiniteLabel
import EconCSLib.Foundations.Probability.FiniteMixture
import EconCSLib.Foundations.Probability.FiniteMeasurablePartition
import EconCSLib.Foundations.Probability.FiniteMultinomialEntropy
import EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import EconCSLib.Foundations.Probability.FiniteProductTernaryCounts
import EconCSLib.Foundations.Probability.FiniteKernelProduct
import EconCSLib.Foundations.Probability.FiniteRatingComparison
import EconCSLib.Foundations.Probability.FiniteRankingEvents
import EconCSLib.Foundations.Probability.FiniteSupportMGF
import EconCSLib.Foundations.Probability.FiniteTypeLogMass
import EconCSLib.Foundations.Probability.FinsetVariance
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Probability.GaussianDerivatives
import EconCSLib.Foundations.Probability.GaussianHazardInverse
import EconCSLib.Foundations.Probability.GaussianMathlib
import EconCSLib.Foundations.Probability.GaussianMills
import EconCSLib.Foundations.Probability.GaussianQuantile
import EconCSLib.Foundations.Probability.InformationOrder
import EconCSLib.Foundations.Probability.IIDLargeDeviations
import EconCSLib.Foundations.Probability.IndependentProduct
import EconCSLib.Foundations.Probability.IntegralLargeDeviations
import EconCSLib.Foundations.Probability.Kernel
import EconCSLib.Foundations.Probability.LargeDeviations
import EconCSLib.Foundations.Probability.MarkovChain
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.Foundations.Probability.MeasureAtoms
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.Occupancy
import EconCSLib.Foundations.Probability.OrderStatistics
import EconCSLib.Foundations.Probability.Pareto
import EconCSLib.Foundations.Probability.PoissonProcess
import EconCSLib.Foundations.Probability.ForwardPoisson
import EconCSLib.Foundations.Probability.ForwardPoissonStopping
import EconCSLib.Foundations.Probability.ForwardStoppedPoisson
import EconCSLib.Foundations.Probability.PoissonStopping
import EconCSLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import EconCSLib.Foundations.Probability.Queueing
import EconCSLib.Foundations.Probability.QueueingRenewalFCFS
import EconCSLib.Foundations.Probability.QueueingGeometric
import EconCSLib.Foundations.Probability.QueueingGPS
import EconCSLib.Foundations.Probability.QueueingGPSAERateFloor
import EconCSLib.Foundations.Probability.QueueingGPSAENormalizedAllocation
import EconCSLib.Foundations.Probability.QueueingMM1Stationary
import EconCSLib.Foundations.Probability.QueueingMM1Uniformization
import EconCSLib.Foundations.Probability.QueueingMM1Kernel
import EconCSLib.Foundations.Probability.QueueingMM1Trajectory
import EconCSLib.Foundations.Probability.QueueingMM1TrajectoryTransition
import EconCSLib.Foundations.Probability.QueueingMM1MarkedUniformization
import EconCSLib.Foundations.Probability.QueueingMM1MarkedStateTrajectory
import EconCSLib.Foundations.Probability.QueueingMM1MarkedSuspension
import EconCSLib.Foundations.Probability.QueueingMM1TwoSidedTrajectory
import EconCSLib.Foundations.Probability.QueueingTwoSidedPathCylinder
import EconCSLib.Foundations.Probability.QueueingTwoSidedReverseTrajectory
import EconCSLib.Foundations.Probability.QueueingTwoSidedReverseFiniteWindows
import EconCSLib.Foundations.Probability.QueueingTwoSidedFullStationarity
import EconCSLib.Foundations.Probability.QueueingMM1TwoSidedTrajectoryShift
import EconCSLib.Foundations.Probability.QueueingMM1TwoSidedMarkedFactor
import EconCSLib.Foundations.Probability.QueueingMM1TwoSidedMarkedSuspension
import EconCSLib.Foundations.Probability.QueueingMM1ForwardReverseMarkedSuspension
import EconCSLib.Foundations.Probability.QueueingMM1ForwardReverseMarkedPalm
import EconCSLib.Foundations.Probability.QueueingPostTagFalseMarkCount
import EconCSLib.Foundations.Probability.QueueingMM1ForwardReverseMarkedPalmPostTagCount
import EconCSLib.Foundations.Probability.QueueingSelectedMarkedPalm
import EconCSLib.Foundations.Probability.QueueingTimedEmbeddedCampbell
import EconCSLib.Foundations.Probability.QueueingTimedEmbeddedMarkedPointSet
import EconCSLib.Foundations.Probability.QueueingMM1TrajectoryTimeChange
import EconCSLib.Foundations.Probability.QueueingMM1TrajectoryPoissonClock
import EconCSLib.Foundations.Probability.QueueingMM1
import EconCSLib.Foundations.Probability.PalmArrivalPath
import EconCSLib.Foundations.Probability.PalmArrivalPathNonexplosion
import EconCSLib.Foundations.Probability.PoissonSuspensionFlow
import EconCSLib.Foundations.Probability.PoissonSuspensionExponentialSplit
import EconCSLib.Foundations.Probability.PalmPASTA
import EconCSLib.Foundations.Probability.PoissonSuspensionStationaryBase
import EconCSLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import EconCSLib.Foundations.Probability.PoissonSuspensionMarkedTransport
import EconCSLib.Foundations.Probability.PoissonSuspensionCampbellBridge
import EconCSLib.Foundations.Probability.PalmCampbell
import EconCSLib.Foundations.Probability.PalmMarkedCampbell
import EconCSLib.Foundations.Probability.PalmProductTaggedArrival
import EconCSLib.Foundations.Probability.PalmFiniteTaggedArrival
import EconCSLib.Foundations.Probability.PalmRenewalService
import EconCSLib.Foundations.Probability.PalmPASTAMM1
import EconCSLib.Foundations.Probability.NormalizedKernelDensity
import EconCSLib.Foundations.Probability.RandomUtility
import EconCSLib.Foundations.Probability.RandomUtilityDensity
import EconCSLib.Foundations.Probability.RealDistribution
import EconCSLib.Foundations.Probability.RealIntervalPartition
import EconCSLib.Foundations.Probability.RenewalReward
import EconCSLib.Foundations.Probability.StochasticDominance
import EconCSLib.Foundations.Probability.Symmetry
import EconCSLib.Foundations.Probability.Weighted
import EconCSLib.Foundations.Probability.WithoutReplacement
import EconCSLib.Foundations.Probability.EventuallyStableFiniteReplay
import EconCSLib.Foundations.Probability.ExponentialInterarrivalTwoStreamHeadTail
import EconCSLib.Foundations.Probability.ExponentialRateScaling
import EconCSLib.Foundations.Probability.ExponentialUnequalRateConvolution
import EconCSLib.Foundations.Probability.FiniteHorizonGPSBatchTraceProgress
import EconCSLib.Foundations.Probability.FiniteHorizonGPSBlockDominance
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSCompletionEventRefinement
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSCompletionTemporalSeparation
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSDeadline
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSEmptyFenceFixedScriptMeasurability
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSKeyAbsence
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSKeyAccounting
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSSemanticProjection
import EconCSLib.Foundations.Probability.FiniteHorizonGPSFCFSZeroDelayFence
import EconCSLib.Foundations.Probability.FiniteHorizonGPSPreBatchReset
import EconCSLib.Foundations.Probability.FiniteHorizonGPSSegmentComposition
import EconCSLib.Foundations.Probability.FiniteHorizonGPSSuffixCreditReset
import EconCSLib.Foundations.Probability.LindleyRemotePastCausalUniqueness
import EconCSLib.Foundations.Probability.LindleyRemotePastMonotonicity
import EconCSLib.Foundations.Probability.LindleyRemotePastShift
import EconCSLib.Foundations.Probability.MeasurableCountableEvaluation
import EconCSLib.Foundations.Probability.MulticlassGPSFiniteHorizon
import EconCSLib.Foundations.Probability.MulticlassStationaryPoisson
import EconCSLib.Foundations.Probability.MulticlassStationaryPoissonAdmissionWork
import EconCSLib.Foundations.Probability.PalmCampbellProductLift
import EconCSLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import EconCSLib.Foundations.Probability.StationaryPoissonWorkPastRate
import EconCSLib.Foundations.Probability.TwoSidedMarkedRenewalPredecessorStateFactors

/-!
# Probability Foundations

Aggregate import for reusable probability infrastructure.

## Main declarations

- Finite PMF expectation/probability APIs:
  `EconCSLib.Foundations.Probability.FiniteExpectation`,
  `EconCSLib.Foundations.Probability.Conditional`,
  `EconCSLib.Foundations.Probability.Kernel`,
  `EconCSLib.Foundations.Probability.FiniteMixture`, and
  `EconCSLib.Foundations.Probability.FiniteLabel`.
  `FiniteExpectation` includes iid finite-product PMFs, coordinate-dependent
  product-event factorization, option-extension product decompositions, and
  finite-product reindexing/binomial success-count formulas.
- Continuous measure and concentration helpers:
  `EconCSLib.Foundations.Probability.Averaging`,
  `EconCSLib.Foundations.Probability.Bernoulli`,
  `EconCSLib.Foundations.Probability.BoundedDensity`,
  `EconCSLib.Foundations.Probability.ContinuousReward`,
  `EconCSLib.Foundations.Probability.MeasureInequalities`,
  `EconCSLib.Foundations.Probability.FairCoin`, and
  `EconCSLib.Foundations.Probability.FinsetVariance`.
- Large-deviation scaffolding:
  `EconCSLib.Foundations.Probability.FiniteSupportMGF`,
  `EconCSLib.Foundations.Probability.FiniteMultinomialEntropy`,
  `EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts`,
  `EconCSLib.Foundations.Probability.IIDLargeDeviations`,
  `EconCSLib.Foundations.Probability.IntegralLargeDeviations`, and
  `EconCSLib.Foundations.Probability.LargeDeviations`.
- Finite information orders:
  `EconCSLib.Foundations.Probability.InformationOrder`.
- Order-statistic interfaces:
  `EconCSLib.Foundations.Probability.OrderStatistics`.
  This includes finite at-most-`k` top-sum maximization and tuple-level
  order-statistic integration interfaces, plus pointwise top-k sample-extension
  and two-level top-mass marginal bounds. It also provides the bridge from an
  upper-order-statistic threshold event to an iid strict-success count, finite
  iid expected top-k wrappers, and option-step marginal identities for adding
  one iid draw.
- Real distribution tail/CDF helpers:
  `EconCSLib.Foundations.Probability.RealDistribution`.
- Continuous heavy-tail distribution helpers:
  `EconCSLib.Foundations.Probability.Pareto`, including finite iid
  product-measure wrappers, closed-form Pareto upper-tail/CDF mass, and
  threshold-count and upper-order-statistic survival binomial formulas, plus
  support-scale tail-integral reductions.
- Dynamic and stochastic-process support:
  `EconCSLib.Foundations.Probability.MarkovChain`,
  `EconCSLib.Foundations.Probability.MDP`,
  `EconCSLib.Foundations.Probability.CTMC`, and
  `EconCSLib.Foundations.Probability.RenewalReward`.
  `EconCSLib.Foundations.Probability.PoissonProcess` includes reusable
  Poisson count likelihoods, no-arrival and interarrival-tail kernels, ordered
  observation windows, thinning-count algebra, homogeneous process-law
  interfaces, and finite-product likelihood collapses for event-count
  observation models. `ExponentialInterarrival` constructs the canonical iid
  exponential product space and a first-arrival natural-filtration/stopping
  certificate. `ExponentialInterarrivalForwardPoisson` builds its canonical
  renewal count into a concrete forward-time Poisson process with finite
  independent increments; it intentionally makes no all-times, stationary,
  or Palm-process claim.
  `Queueing` supplies deterministic FCFS comparator transfers, while
  `QueueingGeometric` proves the exact geometric state tail and independent
  product-space coupling used by the M/M/1 calculation. `QueueingMM1` proves
  the analytic stationary-M/M/1 count mixture conditional on an explicit
  stationary/Palm tagged-arrival coupling and records the no-atom strict-to-
  weak tail bridge.  These modules do not derive a queue's geometric
  stationarity, construct the Palm law, or derive the fluid-GPS recurrence.
  `QueueingPostTagFalseMarkCount` names the actual false-edge potential-service
  count on a tagged gap/marked path and proves its structural measurability,
  bounds, and monotonicity.  On the direct selected marked-Palm M/M/1 path,
  `QueueingMM1ForwardReverseMarkedPalmPostTagCount` now proves its fixed-
  horizon marked-thinning Poisson law and its independence from the selected
  pre-arrival queue state; it does not construct response dynamics or GPS.
  `ForwardPoisson` supplies a probability-law interface for forward
  nonnegative-time Poisson counts after a tag, and `PalmArrivalPath` constructs
  a two-sided iid-exponential-gap candidate tagged path with its arrival at
  time zero. `PalmProductTaggedArrival` independently adjoins that path to a
  supplied base law, proves exponential tagged-gap laws and base/gap
  independence, and proves the resulting product PASTA queue-state
  certificate. It can also adjoin a stationary embedded trajectory while
  retaining its coordinate marginal, while explicitly not calling any of
  these product laws a Campbell/Palm transform. `PalmFiniteTaggedArrival`
  identifies every finite block of post-tag gaps and cumulative epochs with
  the corresponding iid exponential and finite-arrival density laws.
  `PalmPASTA` makes the remaining stationary-base versus Palm-tagged-law
  distinction explicit and derives tagged queue-state tails from a supplied
  PASTA identity. `PalmCampbell` now states a verifiable finite-window
  Campbell/Palm certificate, including recentering and locally finite arrival
  enumeration, so a paper-facing theorem can require genuine Palm provenance.
  `EquilibriumPoissonBase` constructs the correct origin-split equilibrium
  configuration, finite exact window enumerators, and unmarked intensity
  calibration, while `PoissonSuspensionFlow` constructs and normalizes the
  measurable exponential special flow. Its countable good-carrier partition
  now proves the real-time action and measure preservation, and
  `PoissonSuspensionStationaryBase` packages it as a genuine
  `ShiftInvariantProbabilityLaw`. `PoissonSuspensionBaseArrivals` supplies
  its concrete arrivals, recentering, exact finite enumerators, and every
  non-mass-transport field of the Campbell certificate.
  `PoissonSuspensionExponentialSplit` proves the local exponential
  residual/age split for the origin-straddling Palm gap.
  `PoissonSuspensionMarkedTransport` proves the fixed-index branch transport
  and already packages the resulting genuine stationary Campbell/Palm
  certificate. Independently, `PoissonEquilibriumHalves`,
  `PoissonSuspensionProductFactors`, and
  `PoissonSuspensionCampbellBridge` now prove the full
  suspension-to-equilibrium measure identity by tensorizing the central-gap
  residual/age split with the two iid tails. The direct marked certificate and
  this equilibrium-coordinate identity are separate from PASTA, which remains
  a separate queue-state theorem.
  `PalmRenewalService` independently adjoins a concrete canonical
  iid-exponential renewal-service path to an already tagged arrival law and
  derives the fixed-horizon Poisson completion-count law and queue/count
  independence needed by the M/M/1 calculation. For the canonical renewal
  time at a measurable queue index, it also derives measurability, the a.e.
  response/count event identity, and atomlessness, yielding a fully concrete
  count-level certificate once the inherited queue tail is supplied. This
  product construction is intentionally not a stationary Campbell/Palm
  construction and makes no independent-increments claim.
  `ForwardStoppedPoisson` precisely packages the still-needed strong-Markov
  conditional law for a count increment after a forward stopping time and
  derives its exponential survival consequence; fixed-time independent
  increments alone do not imply that field.
  `ForwardPoissonStopping` supplies the compatible forward natural filtration
  and native first-count-arrival stopping-time certificate needed to connect a
  concrete post-tag or post-incident count path to that stopped-law boundary.
  `QueueingGPS` proves the deterministic integrated-fluid GPS service
  floor and its transfer to an FCFS recurrence, including the comparator
  initial-workload coupling needed at a Palm tag. `QueueingGPSAERateFloor`
  gives the same FCFS transfer from an almost-everywhere rate floor on each
  physical job interval, appropriate when endpoint allocation values are not
  semantically meaningful. `QueueingGPSAENormalizedAllocation` derives that
  a.e. floor from the normalized GPS allocation identity and the a.e. active-
  weight-sum bounds on each actual job interval.
  `ExponentialMemoryless` proves the full measure-level deterministic
  residual law for a positive-rate exponential variable: after survival past
  a fixed elapsed time, its shifted residual is the original exponential
  measure scaled by the survival mass.
  `ExponentialInterarrivalResidualTail` lifts that identity to an iid
  interarrival path after a fixed first-gap survival event, preserving the
  entire residual path law up to its survival mass.
  `ExponentialInterarrivalFuture` proves deterministic-index regeneration of
  the iid exponential path and its next-gap stopping-time bridge; it does not
  promote that fact to a conditional or infinite-tail strong-Markov law.
  `ExponentialInterarrivalBoundedStopping` proves that the first uninspected
  coordinate after a bounded prefix-measurable discrete stopping index retains
  the exponential law, while keeping the conditional and whole-future-tail
  strong-Markov upgrades explicit.
  `ExponentialInterarrivalBoundedStoppingBlock` extends this to every finite
  post-stop block, with its full iid exponential product law, but remains a
  bounded-index finite-horizon result.
  `ExponentialInterarrivalUnboundedStopping` removes the bounded-index
  condition for every total prefix-measurable discrete index and proves the
  same finite post-stop iid block law.  It does not assert an infinite shifted
  tail, a conditional law, or a continuous-time strong-Markov theorem.
  `ExponentialInterarrivalNonexplosion` proves almost-sure divergence of the
  canonical one-sided renewal epochs and finiteness of the arrivals before
  every finite time, but does not turn those epochs into an all-times Poisson
  count process.
  `ExponentialInterarrivalRenewalCount` supplies that measurable one-sided
  renewal count, its threshold/cardinality identities, and its natural
  filtration, while leaving Poisson increment and strong-Markov laws open.
  `ExponentialInterarrivalErlang` proves that each finite arrival epoch has
  the repeated exponential-convolution law. `ExponentialGammaConvolution`
  identifies every canonical `arrivalTime n` and positive
  `postTagArrival (n + 1)` with its positive-integer Gamma law, while
  `ExponentialGammaCDF` proves the corresponding finite Erlang CDF series.
  `ExponentialInterarrivalRenewalCountMarginal` combines these results to
  prove the canonical renewal count's full fixed-time Poisson PMF and
  `HasLaw` statement. It still does not establish Poisson increments,
  stationary two-sided counts, or a continuous-time strong-Markov theorem.
  `ExponentialInterarrivalPostArrival` upgrades that fixed-time statement at
  every deterministic arrival index: the post-arrival count is a fresh-tail
  count and has the Poisson law. It also exposes the full finite pre-arrival
  prefix as independent of the entire future tail. It is not a
  deterministic-clock increment theorem.
  `ExponentialInterarrivalIncrementBoundary` then proves the exact
  a.e. pathwise deterministic-clock increment identity in terms of a
  residual tail. `ExponentialInterarrivalDeterministicNoArrival` discharges
  the zero-increment consequence at every deterministic nonnegative clock by
  summing the countable straddling-gap fibers, proving the exact no-arrival
  exponential tail. `ExponentialInterarrivalDeterministicResidualTail` then
  proves that the complete residual path at any nonnegative deterministic
  clock has the original iid exponential law and consequently that every
  deterministic nonnegative-time increment has its Poisson law. It also
  proves that the accumulated count is independent of that residual path and
  of the immediately following deterministic increment.
  `ExponentialInterarrivalForwardPoisson` recursively upgrades this to finite
  joint independent increments and constructs the canonical forward
  `ForwardHomogeneousPoissonCountingProcessByLaw`. It does not establish a
  stationary two-sided count or a random/stopping-time result.
  `QueueingMM1Stationary` proves that the normalized geometric mass satisfies
  detailed and global generator balance for stable M/M/1 rates, while leaving
  the countable nonexplosive-CTMC and generator-to-semigroup construction
  explicit.
  `QueueingMM1Uniformization` upgrades that mass to an invariant PMF for the
  reflected countable uniformized birth--death jump kernel through detailed
  balance and identifies that PMF exactly with Mathlib's geometric measure,
  but does not yet construct its continuous-time Poisson-clock path.
  `QueueingMM1Kernel` lifts countable PMF kernels (including augmented
  state/mark spaces) to Mathlib's `Kernel.Invariant` interface and proves
  invariance for every finite kernel power.
  `QueueingMM1Trajectory` constructs the stationary Ionescu--Tulcea embedded
  trajectory and proves all of its marginals geometric, while leaving the
  continuous-time Poisson-clock time change explicit.
  `QueueingMM1TrajectoryTransition` proves its full finite-prefix-to-next
  recurrence, stationary consecutive-pair law, and exact initial/`n`-step pair
  law `π ⊗ₘ K^n`. `PoissonFiniteHorizonMarkedThinning` constructs a literal
  finite-horizon Poisson count with an iid finite Boolean mark vector and
  proves the exact product-of-Poisson law for its retained and discarded mark
  counts. This is a count-and-mark construction, not yet a point-process path,
  Palm law, or PASTA theorem. `QueueingMM1MarkedUniformization` makes each reflected
  M/M/1 edge an explicit Bernoulli arrival/potential-service mark and proves
  that the stationary pre-edge state and recovered mark have the product law;
  its marked tail event consequently factors as well. This is embedded-time
  only, not thinning or PASTA.
  `QueueingMM1MarkedStateTrajectory` upgrades this to a literal augmented
  state `(Q_n, M_n)` chain: it proves the geometric-state/Bernoulli-mark PMF
  is invariant, its state/current-mark coordinate has the exact product law,
  and two consecutive marks on its stationary Ionescu--Tulcea trajectory have
  the Bernoulli product law. `QueueingMM1MarkedSuspension` then defines the
  pathwise real-time action that couples a good Poisson suspension to a
  two-sided embedded path, synchronizing event relabeling with its clock
  crossing index. Its checked skew-product transfer now proves real-time
  measure preservation, and packages a `ShiftInvariantProbabilityLaw`, for
  any embedded path law invariant under every integer relabeling. Supplying
  that full invariant M/M/1 path law remains separate, so neither module yet
  claims thinning, Palm, or PASTA semantics.
  `QueueingMM1TwoSidedMarkedFactor` gives a compatible route to that path: it
  recovers every mark from a reversible unmarked trajectory edge, proves that
  edge-marking commutes with integer reindexing, and gives the exact
  state/current-mark product law at every integer index. It likewise stops
  short of full path shift invariance.
  `QueueingMM1TwoSidedMarkedSuspension` forms the resulting two-sided marked
  M/M/1 path together with the good Poisson suspension, yielding the concrete
  product measure on which the timed action is defined and retaining every
  coordinate's state/mark law. The generic invariant skew-product bridge is
  now available. `QueueingTwoSidedFullStationarity` supplies the required
  full integer-shift invariant law for the forward/reverse carrier.
  `QueueingMM1ForwardReverseMarkedSuspension` additionally supplies the
  stationarity-facing carrier: it edge-marks the generic forward/reverse
  two-sided M/M/1 construction, records the detailed-balance reverse-pair
  condition and its time-zero geometric/Bernoulli law, and packages the exact
  route from a full unmarked shift theorem to a real-time stationary marked
  suspension. Its product suspension also retains the embedded time-zero
  geometric/Bernoulli marginal and its elementary arrival-mark/state-tail
  factorization. Conditioning its true embedded mark gives a probability
  path with the same geometric pre-arrival tail, and pairing that path with a
  tagged Poisson-gap path gives a literal `TaggedArrivalAtZero` candidate.
  `QueueingMM1ForwardReverseMarkedPalm` now invokes the full shift theorem,
  the product Campbell lift, and selected-point covariance to construct a
  genuine stationary Palm certificate for true M/M/1 arrivals; at the
  uniformization clock its intensity is exactly the physical arrival rate.
  It also packages the matching geometric law of the base and selected-tag
  embedded coordinate-zero queue statistic as a PASTA certificate.  Its
  direct selected tag additionally has verified finite iid mark prefixes and,
  through the path-derived false-mark count, fixed-horizon marked thinning
  and queue/service-count independence. This is not yet a real-time
  queue-occupancy construction: response dynamics and GPS
  response dynamics remain separate obligations.
  `QueueingSelectedMarkedPalm` supplies the checked selection algebra once a
  marked all-event Campbell certificate is available: conditioning preserves
  the tag-at-zero and strict-arrival facts, a true-zero-mark slice factors
  exactly, and the selected Campbell count has intensity `rate * p`.
  `QueueingTimedEmbeddedCampbell` now proves that all-event certificate for
  a Poisson suspension with any independent embedded path law invariant under
  every integer relabeling, and `QueueingTimedEmbeddedMarkedPointSet` proves
  that its selected marked point set covaries under the real-time flow.
  `PalmMarkedCampbell` packages these facts as a genuine selected marked
  Campbell/Palm certificate using the all-event enumeration plus a covariant
  Boolean selector, avoiding a noncanonical separate re-enumeration of the
  surviving true points.
  `QueueingMM1TwoSidedTrajectory` constructs a state-anchored
  integer-indexed embedded trajectory and, under detailed balance, proves its
  cross-zero pair has the stationary transition law. The generic
  `QueueingTwoSidedReverseTrajectory` instead accepts a forward and reverse
  kernel with an explicit pair-balance condition, proving the same one-edge
  shift consistency without assuming reversibility. It also exposes exact
  cross-zero and forward triple and four-coordinate laws and derives their
  one-step shift equalities from pair balance by conditional-Fubini
  reordering. Neither construction
  claims full integer-shift invariance or Palm semantics.
  `QueueingTwoSidedReverseFiniteWindows` extends that generic construction to
  arbitrary cross-zero windows and arbitrary pure-past reverse prefixes, each
  with an explicit finite-dimensional law under pair balance.
  `QueueingTwoSidedFullStationarity` completes the mixed-window recurrence,
  reindexes finite integer intervals, and applies the cylinder criterion to
  prove full integer-shift measure preservation.
  `QueueingTwoSidedPathCylinder` proves the generic final extension principle:
  equality of every finite contiguous integer-window restriction determines a
  two-sided product-path probability law, and hence establishes a measurable
  integer relabeling as measure-preserving; it is now used by the full
  forward/reverse stationarity proof.
  `QueueingMM1TwoSidedTrajectoryShift` proves that every adjacent embedded
  window has the stationary transition law under detailed balance; the
  forward/reverse construction's full path invariance is now supplied by
  `QueueingTwoSidedFullStationarity`.
  `QueueingMM1TrajectoryTimeChange` turns the `n`-step law into the exact
  mixture for an exogenous measurable index on a separate product-space
  clock factor. `QueueingMM1TrajectoryPoissonClock` specializes that mixture
  to a supplied forward Poisson clock and proves the fixed-time joint
  state--external-clock-count product law for uniformized M/M/1, including
  the rate-aligned clock marginal. These remain fixed-time independent-product
  results: they do not prove marked thinning, a CTMC semigroup, a Palm law, or
  PASTA.
  `PalmArrivalPathNonexplosion` transfers canonical renewal nonexplosion to
  both gap directions of the candidate tagged path, without claiming a
  Campbell/Palm identity or stationary Poisson increments.
  `PalmPASTAMM1` turns a supplied geometric stationary base-state law into the
  pre-arrival tagged tail needed by the M/M/1 response certificate through the
  explicit PASTA state-law bridge.
- Finite sampling and occupancy tools:
  `EconCSLib.Foundations.Probability.Weighted`,
  `EconCSLib.Foundations.Probability.WithoutReplacement`, and
  `EconCSLib.Foundations.Probability.Occupancy`.
- Admissions/testing and stochastic-order wrappers:
  `EconCSLib.Foundations.Probability.Admissions`,
  `EconCSLib.Foundations.Probability.BivariateGaussian`,
  `EconCSLib.Foundations.Probability.Gaussian`,
  `EconCSLib.Foundations.Probability.GaussianMathlib`,
  `EconCSLib.Foundations.Probability.GaussianMills`,
  `EconCSLib.Foundations.Probability.GaussianDerivatives`,
  `EconCSLib.Foundations.Probability.GaussianQuantile`,
  `EconCSLib.Foundations.Probability.GaussianHazardInverse`, and
  `EconCSLib.Foundations.Probability.StochasticDominance`.
  `BivariateGaussian` includes correlated standard-Gaussian laws and
  independent two-coordinate Gaussian product/variance-scaling bridges for
  RUM-style conditional winner-ratio proofs.
- Random-utility noise, contraction, and density-product inequalities:
  `EconCSLib.Foundations.Probability.RandomUtility` and
  `EconCSLib.Foundations.Probability.RandomUtilityDensity`.
-/
