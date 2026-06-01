import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.LocalEOWChartLinear

/-!
# Distributional Representation Gluing

Neutral support for the OS-II Malgrange-Zerner route: if local representatives
agree on overlaps and each represents the same Schwartz distribution on its
carrier, then the glued representative represents that distribution on every
set covered by the carriers.
-/

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

/-- Pull back a represented distribution through a measure-preserving continuous
linear coordinate equivalence.

This is the neutral chart-transport step used after OS-II Lemma 5.1/
Malgrange-Zerner: if the chart distribution is represented by `H`, then the
pulled-back distribution is represented by `H ∘ e`. -/
theorem representsDistributionOn_pullback_measurePreservingCLE
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    (T : SchwartzMap F ℂ →L[ℂ] ℂ)
    (H : F → ℂ)
    (V : Set F)
    (hrep : RepresentsDistributionOn T H V) :
    RepresentsDistributionOn
      (T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm))
      (fun x : E => H (e x))
      (e ⁻¹' V) := by
  intro φ hφ
  let ψ : SchwartzMap F ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) φ
  have hψ_support : SupportsInOpen (ψ : F → ℂ) V := by
    constructor
    · simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hφ.1.comp_homeomorph e.symm.toHomeomorph
    · intro y hy
      have hy_pre :
          e.symm y ∈ tsupport (φ : E → ℂ) := by
        exact
          tsupport_comp_subset_preimage
            (φ : E → ℂ) e.symm.continuous hy
      have hyV : e (e.symm y) ∈ V := hφ.2 hy_pre
      simpa using hyV
  calc
    (T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)) φ
        = T ψ := by
            rfl
    _ = ∫ y : F, H y * ψ y := hrep ψ hψ_support
    _ = ∫ x : E, H (e x) * φ x := by
      symm
      have hchange :=
        hmp.integral_comp
          e.toHomeomorph.measurableEmbedding
          (g := fun y : F => H y * ψ y)
      simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hchange

/-- Chart form of `representsDistributionOn_pullback_measurePreservingCLE`.

If pushing original tests into chart coordinates gives a distribution represented
by `Hchart`, then the original distribution is represented on the preimage
carrier by the pulled-back chart kernel. -/
theorem representsDistributionOn_of_chart_rep_measurePreservingCLE
    (e : E ≃L[ℝ] F)
    (hmp : MeasurePreserving e volume volume)
    (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    (Hchart : F → ℂ)
    (V : Set F)
    (hrep :
      RepresentsDistributionOn
        (T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e))
        Hchart V) :
    RepresentsDistributionOn
      T
      (fun x : E => Hchart (e x))
      (e ⁻¹' V) := by
  intro φ hφ
  let ψ : SchwartzMap F ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) φ
  have hψ_support : SupportsInOpen (ψ : F → ℂ) V := by
    constructor
    · simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hφ.1.comp_homeomorph e.symm.toHomeomorph
    · intro y hy
      have hy_pre :
          e.symm y ∈ tsupport (φ : E → ℂ) := by
        exact
          tsupport_comp_subset_preimage
            (φ : E → ℂ) e.symm.continuous hy
      have hyV : e (e.symm y) ∈ V := hφ.2 hy_pre
      simpa using hyV
  have hψ_pull :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ = φ := by
    ext x
    simp [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  calc
    T φ = T ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) ψ) := by
      rw [hψ_pull]
    _ = ∫ y : F, Hchart y * ψ y := hrep ψ hψ_support
    _ = ∫ x : E, Hchart (e x) * φ x := by
      symm
      have hchange :=
        hmp.integral_comp
          e.toHomeomorph.measurableEmbedding
          (g := fun y : F => Hchart y * ψ y)
      simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hchange

/-- Pull a represented real-edge distribution through an affine local EOW chart.

This is the distributional chart-change step used in the OS-II Lemma 5.1
localization: pushing tests forward by `localEOWRealChart x0 ys` and multiplying
by the inverse absolute determinant in
`localEOWAffineDistributionPullbackCLM` exactly transports the representing
kernel by composition with the affine chart. -/
theorem representsDistributionOn_localEOWAffineDistributionPullbackCLM
    {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (H : (Fin m → ℝ) → ℂ)
    (U : Set (Fin m → ℝ))
    (hrep : RepresentsDistributionOn T H U) :
    RepresentsDistributionOn
      (localEOWAffineDistributionPullbackCLM x0 ys hli T)
      (fun u => H (localEOWRealChart x0 ys u))
      {u | localEOWRealChart x0 ys u ∈ U} := by
  intro φ hφ
  let ψ : SchwartzMap (Fin m → ℝ) ℂ :=
    localEOWAffineTestPushforwardCLM x0 ys hli φ
  have hψ_support : SupportsInOpen (ψ : (Fin m → ℝ) → ℂ) U := by
    constructor
    · dsimp [ψ]
      exact HasCompactSupport.localEOWAffineTestPushforwardCLM x0 ys hli
        hφ.1
    · intro y hy
      have hy_img :=
        tsupport_localEOWAffineTestPushforwardCLM_subset x0 ys hli φ hy
      rcases hy_img with ⟨u, hu, rfl⟩
      exact hφ.2 hu
  calc
    localEOWAffineDistributionPullbackCLM x0 ys hli T φ =
        ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) * T ψ := by
          simpa [ψ] using
            localEOWAffineDistributionPullbackCLM_apply x0 ys hli T φ
    _ =
        ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
          ∫ y : Fin m → ℝ, H y * ψ y := by
          rw [hrep ψ hψ_support]
    _ =
        ∫ u : Fin m → ℝ,
          H (localEOWRealChart x0 ys u) * φ u := by
          exact
            integral_localEOWAffineTestPushforwardCLM_changeOfVariables
              x0 ys hli H φ

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

end SCV
