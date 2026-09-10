/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.ConnectedNeighborhood
import Init
import OSReconstruction.SCV.LocalContinuousEOW
import OSReconstruction.SCV.DistributionalEOWSupport










noncomputable section

open MeasureTheory Topology

namespace SCV

variable {E ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasureSpace E]

/-- Restrict a distributional representative to a smaller carrier and replace it
there by an equal kernel.

This is used after local EOW/Malgrange-Zerner recovery: the recovered
representative may be named `H`, while the OS semigroup branch is a separately
defined kernel that agrees with `H` on the side window. -/
theorem representsDistributionOn_congr_on_subset
    (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    {H H' : E → ℂ} {U V : Set E}
    (hRep : RepresentsDistributionOn T H U)
    (hEq : Set.EqOn H H' V)
    (hVU : V ⊆ U) :
    RepresentsDistributionOn T H' V := by
  intro φ hφ
  have hφU : SupportsInOpen (φ : E → ℂ) U :=
    ⟨hφ.1, hφ.2.trans hVU⟩
  calc
    T φ = ∫ x : E, H x * φ x := hRep φ hφU
    _ = ∫ x : E, H' x * φ x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hxφ : x ∈ tsupport (φ : E → ℂ)
      · have hxV : x ∈ V := hφ.2 hxφ
        rw [hEq hxV]
      · have hφ_zero : φ x = 0 :=
          image_eq_zero_of_notMem_tsupport hxφ
        simp [hφ_zero]

variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasureSpace F] [BorelSpace E] [BorelSpace F]

variable [FiniteDimensional ℝ E]
variable [IsLocallyFiniteMeasure (volume : Measure E)]

/-- Distributional half of the Malgrange-Zerner gluing step.

This is independent of QFT-specific data: local kernels that represent the same
distribution and agree on overlaps glue to a kernel representing that
distribution on any covered set. -/
theorem representsDistributionOn_glued_iUnion
    (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    (N : ι → Set E)
    (D : ι → E → ℂ)
    (U : Set E)
    (hcover : U ⊆ ⋃ i, N i)
    (hN_open : ∀ i, IsOpen (N i))
    (hD_cont : ∀ i, ContinuousOn (D i) (N i))
    (hD_rep : ∀ i, RepresentsDistributionOn T (D i) (N i))
    (hEq : ∀ i j, Set.EqOn (D i) (D j) (N i ∩ N j)) :
    RepresentsDistributionOn T (glued_iUnion N D) U := by
  intro φ hφ
  refine
    distribution_representation_of_local_representations_for_test
      (T := T) (H := glued_iUnion N D) φ hφ.1 ?_
  intro x hxφ
  have hxU : x ∈ U := hφ.2 hxφ
  rcases Set.mem_iUnion.mp (hcover hxU) with ⟨i, hxi⟩
  refine ⟨N i, hN_open i, hxi, ?_, ?_⟩
  · exact (hD_cont i).congr fun y hy =>
      glued_iUnion_eqOn (N := N) (D := D) hEq i hy
  · intro ψ hψ
    calc
      T ψ = ∫ y : E, D i y * ψ y := hD_rep i ψ hψ
      _ = ∫ y : E, glued_iUnion N D y * ψ y := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hyψ : y ∈ tsupport (ψ : E → ℂ)
        · have hyN : y ∈ N i := hψ.2 hyψ
          have hglue :
              glued_iUnion N D y = D i y :=
            glued_iUnion_eqOn (N := N) (D := D) hEq i hyN
          rw [hglue]
        · have hψ_zero : ψ y = 0 :=
            image_eq_zero_of_notMem_tsupport hyψ
          simp [hψ_zero]

/-- Translating a local representative back by the same vector removes a
translated test action from the represented distribution. -/
theorem representsDistributionOn_of_translate
    {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (F : (Fin m → ℝ) → ℂ)
    (U : Set (Fin m → ℝ))
    (a : Fin m → ℝ)
    (hrep : RepresentsDistributionOn
      (T.comp (translateSchwartzCLM (-a))) F U) :
    RepresentsDistributionOn T (fun y ↦ F (y - a))
      {y | y - a ∈ U} := by
  intro ψ hψ
  let φ : SchwartzMap (Fin m → ℝ) ℂ :=
    translateSchwartz a ψ
  have hφ : SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U := by
    constructor
    · exact hψ.1.comp_homeomorph (Homeomorph.addRight a)
    · intro x hx
      have hxψ : x + a ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) := by
        rw [show φ = translateSchwartz a ψ by rfl] at hx
        exact (tsupport_comp_subset_preimage
          (ψ : (Fin m → ℝ) → ℂ)
          (Homeomorph.addRight a).continuous hx)
      have hphysical := hψ.2 hxψ
      simpa only [Set.mem_setOf_eq, add_sub_cancel_right] using hphysical
  have hcancel : translateSchwartz (-a) φ = ψ := by
    ext x
    simp [φ, translateSchwartz_apply]
  have hinterchange :=
    integral_add_right_eq_self
      (μ := (volume : Measure (Fin m → ℝ)))
      (fun y ↦ F (y - a) * ψ y) a
  calc
    T ψ = (T.comp (translateSchwartzCLM (-a))) φ := by
      rw [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply, hcancel]
    _ = ∫ x, F x * φ x := hrep φ hφ
    _ = ∫ y, F (y - a) * ψ y := by
      rw [← hinterchange]
      apply integral_congr_ae
      filter_upwards with x
      simp [φ, translateSchwartz_apply]

end SCV
