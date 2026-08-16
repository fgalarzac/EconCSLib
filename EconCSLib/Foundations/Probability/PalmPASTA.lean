import EconCSLib.Foundations.Probability.QueueingMM1

/-!
# Stationary base laws and Palm/PASTA queue-state interfaces

This module does not construct a Palm measure.  It gives the explicit
mathematical interface a future construction must satisfy: a shift-invariant
untagged stationary probability law, a separately tagged-at-zero probability
law, and a PASTA distributional identity for the pre-arrival queue state.
-/

namespace EconCSLib
namespace Probability
namespace Palm

open MeasureTheory ProbabilityTheory

/-- A probability law invariant under a measurable real-time shift action. -/
structure ShiftInvariantProbabilityLaw
    (Ω : Type*) [MeasurableSpace Ω] where
  Pbase : Measure Ω
  isProbability : IsProbabilityMeasure Pbase
  shift : ℝ → Ω → Ω
  shift_zero : shift 0 = id
  shift_add : ∀ s t : ℝ, shift (s + t) = shift s ∘ shift t
  shift_preserving : ∀ t : ℝ, MeasurePreserving (shift t) Pbase Pbase

/--
The queue-state consequence of a stationary Palm/PASTA construction.

`base` is the shift-invariant untagged system law.  `tagged` is a different
probability law in which an arrival has been pinned at time zero.  The field
`pasta_queue_length` says precisely that the tagged pre-arrival queue-length
distribution agrees with the base stationary queue-length distribution.  It
is deliberately a conclusion-to-be-proved, not an automatic property of a
Poisson rate declaration.
-/
structure PalmPASTAQueueLengthCertificate
    (Ωbase Ωtag : Type*) [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (base : ShiftInvariantProbabilityLaw Ωbase)
    (tagged : Queueing.TaggedArrivalAtZero Ωtag) where
  stationaryQueueLength : Ωbase → ℕ
  preArrivalQueueLength : Ωtag → ℕ
  stationaryQueueLength_measurable : Measurable stationaryQueueLength
  preArrivalQueueLength_measurable : Measurable preArrivalQueueLength
  pasta_queue_length : HasLaw preArrivalQueueLength
    (base.Pbase.map stationaryQueueLength) tagged.Ptag

namespace PalmPASTAQueueLengthCertificate

/-- PASTA transfers every queue-length upper tail from the base law to the tag. -/
theorem real_preArrivalQueueLength_tail_eq_stationary
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (k : ℕ) :
    tagged.Ptag.real {ω | k ≤ H.preArrivalQueueLength ω} =
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} := by
  change (tagged.Ptag {ω | k ≤ H.preArrivalQueueLength ω}).toReal =
    (base.Pbase {ω | k ≤ H.stationaryQueueLength ω}).toReal
  rw [show tagged.Ptag {ω | k ≤ H.preArrivalQueueLength ω} =
      (tagged.Ptag.map H.preArrivalQueueLength) (Set.Ici k) by
        simpa only [Set.preimage_setOf_eq] using
          (Measure.map_apply H.preArrivalQueueLength_measurable measurableSet_Ici).symm]
  rw [H.pasta_queue_length.map_eq]
  congr 1
  simpa only [Set.preimage_setOf_eq] using
    (Measure.map_apply H.stationaryQueueLength_measurable measurableSet_Ici)

/--
Combine an explicit stationary-base/PASTA queue-state certificate with a
forward potential-service process to obtain the count certificate consumed by
the M/M/1 response-tail proof.  The base stationary geometric law, post-tag
independence, response event identity, and no-atom property remain explicit
inputs; unlike the lower-level constructor, the tagged queue tail is derived
from the PASTA identity rather than supplied directly.
-/
def toTaggedPASTAMM1CountCertificate
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofForwardServiceProcess
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

/--
Forward-service version of the PASTA-to-count-certificate bridge with an
almost-everywhere response event identity.  The stationary base law, Palm
tagged law, PASTA identity, future-service independence, and no-atom condition
remain explicit inputs.
-/
def toTaggedPASTAMM1CountCertificateAE
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw
      Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.count z.toNNReal) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
        {ω | service.count z.toNNReal ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofForwardServiceProcessAE
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

/--
Combine an explicit stationary-base/PASTA queue-state certificate with just
the fixed-horizon post-tag completion-count facts consumed by the M/M/1 tail
mixture.  Unlike `toTaggedPASTAMM1CountCertificate`, this makes no assertion
about chronological sample paths or independent increments of the supplied
counts.
-/
noncomputable def toTaggedPASTAMM1CountCertificateOfPostTagPoissonCompletionCountMarginals
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (service : Queueing.PostTagPoissonCompletionCountMarginals Ωtag tagged.Ptag)
    (hstable : arrivalRate < service.rate)
    (response : Ωtag → ℝ)
    (hresponse_measurable : Measurable response)
    (hstationary_queue_tail : ∀ k : ℕ,
      base.Pbase.real {ω | k ≤ H.stationaryQueueLength ω} =
        (arrivalRate / service.rate) ^ k)
    (hpreArrivalQueueLength_indep_service : ∀ z : ℝ, 0 ≤ z →
      IndepFun H.preArrivalQueueLength (service.completionCount z) tagged.Ptag)
    (hstrict_response_event : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[tagged.Ptag]
      {ω | service.completionCount z ω ≤ H.preArrivalQueueLength ω})
    (hresponse_atom_zero : ∀ z : ℝ,
      tagged.Ptag.real {ω | response ω = z} = 0) :
    Queueing.TaggedPASTAMM1CountCertificate Ωtag :=
  Queueing.TaggedPASTAMM1CountCertificate.ofPostTagPoissonCompletionCountMarginals
    tagged arrivalRate harrivalRate service hstable H.preArrivalQueueLength response
    H.preArrivalQueueLength_measurable hresponse_measurable
    hpreArrivalQueueLength_indep_service
    (fun k => (H.real_preArrivalQueueLength_tail_eq_stationary k).trans
      (hstationary_queue_tail k))
    hstrict_response_event hresponse_atom_zero

end PalmPASTAQueueLengthCertificate

end Palm
end Probability
end EconCSLib
