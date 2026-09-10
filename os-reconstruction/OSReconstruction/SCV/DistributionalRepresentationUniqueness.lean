/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.DistributionalRepresentationGluing
import OSReconstruction.SCV.DistributionalUniqueness










noncomputable section

open MeasureTheory Topology

namespace SCV

variable {E ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasureSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]
variable [IsLocallyFiniteMeasure (volume : Measure E)]
variable [Measure.IsOpenPosMeasure (volume : Measure E)]

/-- Continuous local representatives of the same distribution agree on the
overlap of their open carriers. -/
theorem eqOn_inter_of_representsDistributionOn
    (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    (U V : Set E)
    (g h : E → ℂ)
    (hU_open : IsOpen U)
    (hV_open : IsOpen V)
    (hg_cont : ContinuousOn g U)
    (hh_cont : ContinuousOn h V)
    (hg_rep : RepresentsDistributionOn T g U)
    (hh_rep : RepresentsDistributionOn T h V) :
    Set.EqOn g h (U ∩ V) := by
  apply
    eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      (hU_open.inter hV_open)
      (hg_cont.mono Set.inter_subset_left)
      (hh_cont.mono Set.inter_subset_right)
  intro f hf_compact hf_support
  have hg_support : SupportsInOpen (f : E → ℂ) U :=
    ⟨hf_compact, hf_support.trans Set.inter_subset_left⟩
  have hh_support : SupportsInOpen (f : E → ℂ) V :=
    ⟨hf_compact, hf_support.trans Set.inter_subset_right⟩
  exact (hg_rep f hg_support).symm.trans (hh_rep f hh_support)

end SCV
