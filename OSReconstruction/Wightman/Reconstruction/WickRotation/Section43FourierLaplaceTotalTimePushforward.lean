import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Section 4.3 Total-Time Product-Source Pushforward

This file records the first finite-dimensional source-current bridge between
the Section 4.3 product source in time-difference variables and the OS-II
total-time shell.  The two-variable theorem is the checked Lean form of the
change of variables `(s, u) ↦ s + u`: compact strict-positive product sources
push forward to compact strict-positive convolution sources.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators Convolution Pointwise

namespace OSReconstruction

/-- Convolution of two one-dimensional compact strict-positive time sources.

The sum of two strict-positive time variables is strict-positive, and compact
support is preserved by convolution. -/
def section43CompactPositiveTimeSource1D_convolution
    (g h : Section43CompactPositiveTimeSource1D) :
    Section43CompactPositiveTimeSource1D := by
  let fconv : ℝ → ℂ :=
    (g.f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (h.f : ℝ → ℂ)
  have hconv_compact : HasCompactSupport fconv := by
    simpa [fconv] using
      (g.compact.convolution (L := ContinuousLinearMap.mul ℝ ℂ) h.compact)
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) fconv := by
    have hg_loc : LocallyIntegrable (g.f : ℝ → ℂ) volume := by
      exact (g.f.integrable (μ := volume)).locallyIntegrable
    simpa [fconv] using
      h.compact.contDiff_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℂ) hg_loc
        (h.f.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h.f : ℝ → ℂ))
  let convS : SchwartzMap ℝ ℂ := hconv_compact.toSchwartzMap hconv_smooth
  have hconv_eq : (convS : ℝ → ℂ) = fconv := by
    ext x
    simp [convS]
  refine ⟨convS, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ tsupport fconv := by
      simpa [hconv_eq] using hx
    have hsum_closed : IsClosed
        (tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ)) := by
      exact (g.compact.isCompact.add h.compact.isCompact).isClosed
    have htsupp_subset :
        tsupport fconv ⊆
          tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ) := by
      refine closure_minimal ?_ hsum_closed
      exact (support_convolution_subset
        (L := ContinuousLinearMap.mul ℝ ℂ)).trans
          (Set.add_subset_add subset_closure subset_closure)
    have hxsum :
        x ∈ tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ) :=
      htsupp_subset hx'
    rcases hxsum with ⟨u, hu, v, hv, rfl⟩
    exact add_pos (Set.mem_Ioi.mp (g.positive hu)) (Set.mem_Ioi.mp (h.positive hv))
  · simpa [hconv_eq] using hconv_compact

/-- Concrete integral formula for the one-dimensional positive-time source
convolution. -/
theorem section43CompactPositiveTimeSource1D_convolution_apply
    (g h : Section43CompactPositiveTimeSource1D) (t : ℝ) :
    (section43CompactPositiveTimeSource1D_convolution g h).f t =
      ∫ s : ℝ, (g.f s) * h.f (t - s) := by
  simp [section43CompactPositiveTimeSource1D_convolution, convolution_def]

private theorem section43_integral_finSucc_cons_eq
    {m : ℕ} (F : (Fin (m + 1) → ℝ) → ℂ) :
    (∫ z : ℝ × (Fin m → ℝ), F (Fin.cons z.1 z.2)) =
      ∫ x : Fin (m + 1) → ℝ, F x := by
  have h :=
    ((MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0).symm).integral_comp'
      (g := F)
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Fin.cons_zero] using h

/-- Base case of the total-time product-source pushforward.

For one time-difference variable, the Section 4.3 product source is already
the one-dimensional compact positive source, and the total-time map is
`ξ ↦ ξ 0`. -/
theorem section43_totalTimeProductSource_integral_fin_one
    (K : ℝ → ℂ)
    (gs : Fin 1 → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin 1 → ℝ,
        K (∑ p : Fin 1, ξ p) *
          (section43TimeProductSource gs).f ξ) =
      ∫ t : ℝ, K t * (gs 0).f t := by
  have hcomp :=
    MeasureTheory.MeasurePreserving.integral_comp'
      (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ)
      (fun t : ℝ => K t * (gs 0).f t)
  calc
    (∫ ξ : Fin 1 → ℝ,
        K (∑ p : Fin 1, ξ p) *
          (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin 1 → ℝ, K (ξ 0) * (gs 0).f (ξ 0) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        simp [section43TimeProductSource, section43TimeProductTensor,
          SchwartzMap.productTensor_apply]
    _ = ∫ t : ℝ, K t * (gs 0).f t := by
        simpa [ContinuousLinearEquiv.coe_funUnique] using hcomp

/-- Head/tail split for the total-time product-source integral.

The product source splits into its head source and tail product source, while
the OS-II total time splits as `t + sum tail`. -/
theorem section43_totalTimeProductSource_integral_cons
    {n : ℕ}
    (K : ℝ → ℂ)
    (gs : Fin (n + 1) → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin (n + 1) → ℝ,
        K (∑ p : Fin (n + 1), ξ p) *
          (section43TimeProductSource gs).f ξ) =
      ∫ z : ℝ × (Fin n → ℝ),
        K (z.1 + ∑ p : Fin n, z.2 p) *
          ((gs 0).f z.1 *
            (section43TimeProductSource (fun p : Fin n => gs p.succ)).f z.2) := by
  let F : (Fin (n + 1) → ℝ) → ℂ := fun ξ =>
    K (∑ p : Fin (n + 1), ξ p) *
      (section43TimeProductSource gs).f ξ
  calc
    (∫ ξ : Fin (n + 1) → ℝ,
        K (∑ p : Fin (n + 1), ξ p) *
          (section43TimeProductSource gs).f ξ)
        = ∫ x : Fin (n + 1) → ℝ, F x := rfl
    _ = ∫ z : ℝ × (Fin n → ℝ), F (Fin.cons z.1 z.2) := by
        rw [section43_integral_finSucc_cons_eq]
    _ =
      ∫ z : ℝ × (Fin n → ℝ),
        K (z.1 + ∑ p : Fin n, z.2 p) *
          ((gs 0).f z.1 *
            (section43TimeProductSource (fun p : Fin n => gs p.succ)).f z.2) := by
        refine integral_congr_ae ?_
        filter_upwards with z
        simp [F, Fin.sum_univ_succ, section43TimeProductSource_cons]

/-- Two-variable product source written in ordinary product coordinates. -/
theorem section43_totalTimeProductSource_integral_fin_two_pair
    (K : ℝ → ℂ)
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ) =
      ∫ z : ℝ × ℝ,
        K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2) := by
  let G : ℝ × ℝ → ℂ := fun z =>
    K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2)
  have hcomp :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).integral_comp'
      (g := G)
  calc
    (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ)
        = ∫ ξ : Fin 2 → ℝ, G (MeasurableEquiv.finTwoArrow ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        simp [G, section43TimeProductSource, section43TimeProductTensor,
          SchwartzMap.productTensor_apply, Fin.sum_univ_two]
    _ = ∫ z : ℝ × ℝ, G z := by
        simpa using hcomp
    _ = ∫ z : ℝ × ℝ,
        K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2) := rfl

/-- The total-time shear `(s, u) ↦ (s + u, s)` preserves planar Lebesgue
measure. -/
private theorem section43_measurePreserving_totalTimeShear :
    MeasurePreserving
      ((MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm)
      ((volume : MeasureTheory.Measure (ℝ × ℝ))) volume := by
  have hshear : MeasurePreserving (MeasurableEquiv.shearAddRight ℝ)
      ((volume : MeasureTheory.Measure (ℝ × ℝ))) volume := by
    simpa using (measurePreserving_prod_add
      (μ := (volume : MeasureTheory.Measure ℝ))
      (ν := (volume : MeasureTheory.Measure ℝ)) :
        MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
          ((volume : MeasureTheory.Measure ℝ).prod
            (volume : MeasureTheory.Measure ℝ))
          ((volume : MeasureTheory.Measure ℝ).prod
            (volume : MeasureTheory.Measure ℝ)))
  have hswap : MeasurePreserving
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      ((volume : MeasureTheory.Measure (ℝ × ℝ))) volume := by
    simpa using (Measure.measurePreserving_swap
      (μ := (volume : MeasureTheory.Measure ℝ))
      (ν := (volume : MeasureTheory.Measure ℝ)))
  exact hswap.comp hshear

/-- First weighted total-time pushforward identity.

For two positive time-difference sources, integrating a kernel depending only
on the total time against the Section 4.3 product source is the same as
integrating the same kernel against the convolution source in total time. -/
theorem section43_totalTimeProductSource_integral_fin_two_convolution
    (K : ℝ → ℂ)
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D)
    (hF : Integrable (fun z : ℝ × ℝ =>
      K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2)))) :
    (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ) =
      ∫ t : ℝ,
        K t *
          (section43CompactPositiveTimeSource1D_convolution
            (gs 0) (gs 1)).f t := by
  let F : ℝ × ℝ → ℂ := fun z =>
    K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2))
  have hcomp := section43_measurePreserving_totalTimeShear.integral_comp'
    (g := F)
  have hF' : Integrable F := by
    simpa [F] using hF
  calc
    (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ)
        = ∫ z : ℝ × ℝ,
            K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2) := by
        exact section43_totalTimeProductSource_integral_fin_two_pair K gs
    _ = ∫ z : ℝ × ℝ, F z := by
        calc
          (∫ z : ℝ × ℝ,
              K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2))
              =
            ∫ z : ℝ × ℝ,
              F (((MeasurableEquiv.shearAddRight ℝ).trans
                MeasurableEquiv.prodComm) z) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            simp [F, MeasurableEquiv.shearAddRight, MeasurableEquiv.prodComm]
          _ = ∫ z : ℝ × ℝ, F z := by
            simpa using hcomp
    _ = ∫ t : ℝ,
        ∫ s : ℝ, K t * ((gs 0).f s * (gs 1).f (t - s)) := by
        simpa [F] using (integral_prod F hF')
    _ = ∫ t : ℝ,
        K t * ∫ s : ℝ, (gs 0).f s * (gs 1).f (t - s) := by
        refine integral_congr_ae ?_
        filter_upwards with t
        simpa using (integral_const_mul
          (μ := (volume : MeasureTheory.Measure ℝ)) (K t)
          (fun s : ℝ => (gs 0).f s * (gs 1).f (t - s)))
    _ = ∫ t : ℝ,
        K t *
          (section43CompactPositiveTimeSource1D_convolution
            (gs 0) (gs 1)).f t := by
        refine integral_congr_ae ?_
        filter_upwards with t
        rw [section43CompactPositiveTimeSource1D_convolution_apply]

/-- The Fubini integrability premise in the two-source total-time pushforward
is supplied by continuity of the total-time kernel and compactness of the
Section 4.3 product source. -/
theorem section43_totalTimeProductSource_integrable_fin_two_convolution_kernel
    (K : ℝ → ℂ) (hK : Continuous K)
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D) :
    Integrable (fun z : ℝ × ℝ =>
      K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2))) := by
  let H : (Fin 2 → ℝ) → ℂ := fun ξ =>
    K (∑ p : Fin 2, ξ p) * (section43TimeProductSource gs).f ξ
  let G : ℝ × ℝ → ℂ := fun z =>
    K (z.1 + z.2) * ((gs 0).f z.1 * (gs 1).f z.2)
  let F : ℝ × ℝ → ℂ := fun z =>
    K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2))
  have hH_cont : Continuous H := by
    fun_prop
  have hH_compact : HasCompactSupport H := by
    simpa [H] using (HasCompactSupport.mul_left
      (f := fun ξ : Fin 2 → ℝ => K (∑ p : Fin 2, ξ p))
      (f' := fun ξ : Fin 2 → ℝ => (section43TimeProductSource gs).f ξ)
      (section43TimeProductSource gs).compact)
  have hH_int : Integrable H :=
    hH_cont.integrable_of_hasCompactSupport hH_compact
  have hG_cont : Continuous G := by
    fun_prop
  have hG_int : Integrable G := by
    have hfin := (MeasureTheory.volume_preserving_finTwoArrow ℝ)
    have hiff := hfin.integrable_comp hG_cont.aestronglyMeasurable
    exact hiff.mp (by
      simpa [H, G, section43TimeProductSource, section43TimeProductTensor,
        SchwartzMap.productTensor_apply, Fin.sum_univ_two] using hH_int)
  have hF_cont : Continuous F := by
    fun_prop
  have hiff :=
    section43_measurePreserving_totalTimeShear.integrable_comp
      hF_cont.aestronglyMeasurable
  have hFG :
      F ∘ ((MeasurableEquiv.shearAddRight ℝ).trans
        MeasurableEquiv.prodComm) = G := by
    funext z
    simp [F, G, MeasurableEquiv.shearAddRight, MeasurableEquiv.prodComm]
  exact hiff.mp (by
    simpa [hFG] using hG_int)

/-- Local-support version of the Fubini integrability premise in the
two-source total-time pushforward.

Only positive-half-line continuity of the total-time kernel is required.  The
strict-positive compact source support and the shear `(s, u) ↦ (s + u, s)`
force the actual support of the two-variable kernel into `{z | 0 < z.1}`. -/
theorem section43_totalTimeProductSource_integrable_fin_two_convolution_kernel_of_continuousOn_Ioi
    (K : ℝ → ℂ) (hK : ContinuousOn K (Set.Ioi 0))
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D) :
    Integrable (fun z : ℝ × ℝ =>
      K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2))) := by
  let F : ℝ × ℝ → ℂ := fun z =>
    K z.1 * ((gs 0).f z.2 * (gs 1).f (z.1 - z.2))
  let Cprod : Set (ℝ × ℝ) :=
    Set.prod (tsupport ((gs 0).f : ℝ → ℂ))
      (tsupport ((gs 1).f : ℝ → ℂ))
  let shear : ℝ × ℝ → ℝ × ℝ := fun w => (w.1 + w.2, w.1)
  let Eshear : Set (ℝ × ℝ) := shear '' Cprod
  have hCprod_compact : IsCompact Cprod := by
    simpa [Cprod] using
      ((gs 0).compact.isCompact.prod (gs 1).compact.isCompact)
  have hshear_cont : Continuous shear := by
    dsimp [shear]
    fun_prop
  have hEshear_compact : IsCompact Eshear := by
    simpa [Eshear] using hCprod_compact.image hshear_cont
  have hEshear_subset_Ioi : Eshear ⊆ {z : ℝ × ℝ | z.1 ∈ Set.Ioi (0 : ℝ)} := by
    rintro z ⟨w, hw, rfl⟩
    have hw0 : w.1 ∈ tsupport ((gs 0).f : ℝ → ℂ) := by
      simpa [Cprod] using hw.1
    have hw1 : w.2 ∈ tsupport ((gs 1).f : ℝ → ℂ) := by
      simpa [Cprod] using hw.2
    exact add_pos (Set.mem_Ioi.mp ((gs 0).positive hw0))
      (Set.mem_Ioi.mp ((gs 1).positive hw1))
  have hF_cont : ContinuousOn F Eshear := by
    have hKfst : ContinuousOn (fun z : ℝ × ℝ => K z.1) Eshear := by
      exact hK.comp (continuous_fst.continuousOn) hEshear_subset_Ioi
    have hweight :
        Continuous (fun z : ℝ × ℝ =>
          (gs 0).f z.2 * (gs 1).f (z.1 - z.2)) := by
      fun_prop
    exact hKfst.mul hweight.continuousOn
  have hsupp : Function.support F ⊆ Eshear := by
    intro z hz
    have hweight_ne :
        (gs 0).f z.2 * (gs 1).f (z.1 - z.2) ≠ 0 := by
      exact (mul_ne_zero_iff.mp hz).2
    have h0_ne : (gs 0).f z.2 ≠ 0 :=
      (mul_ne_zero_iff.mp hweight_ne).1
    have h1_ne : (gs 1).f (z.1 - z.2) ≠ 0 :=
      (mul_ne_zero_iff.mp hweight_ne).2
    have hmem : (z.2, z.1 - z.2) ∈ Cprod := by
      constructor
      · exact subset_tsupport _ h0_ne
      · exact subset_tsupport _ h1_ne
    refine ⟨(z.2, z.1 - z.2), hmem, ?_⟩
    ext
    · dsimp [shear]
      ring
    · dsimp [shear]
  have hIntOn : IntegrableOn F Eshear :=
    hF_cont.integrableOn_compact hEshear_compact
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/-- Weighted two-source total-time pushforward with the natural continuity
hypothesis on the total-time kernel. -/
theorem section43_totalTimeProductSource_integral_fin_two_convolution_of_continuous
    (K : ℝ → ℂ) (hK : Continuous K)
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ) =
      ∫ t : ℝ,
        K t *
          (section43CompactPositiveTimeSource1D_convolution
            (gs 0) (gs 1)).f t := by
  exact section43_totalTimeProductSource_integral_fin_two_convolution K gs
    (section43_totalTimeProductSource_integrable_fin_two_convolution_kernel
      K hK gs)

end OSReconstruction
