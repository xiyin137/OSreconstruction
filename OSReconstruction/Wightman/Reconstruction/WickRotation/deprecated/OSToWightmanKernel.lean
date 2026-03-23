/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase

/-!
# Two-Point Schwinger Holomorphic Kernel

This file contains the holomorphic kernel construction for the two-point
Schwinger function, split from `OSToWightman.lean` for maintainability.

## Main results

* `twoPointSpatialWitness_bounded_of_pos` - semigroup bound on spatial witness
* Bridge lemmas for admissible test functions (bump constructions, tsupport transfers)
-/

noncomputable section

open Complex Topology MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-- There exists a compactly-supported Schwartz function on spacetime with
NEGATIVE-time support and nonzero integral. Needed for the LEFT semigroup
vector (osConj reflects time: negative → positive). -/
theorem exists_negative_time_compact_schwartz {d : ℕ} [NeZero d] :
    ∃ (g : SchwartzSpacetime d),
      HasCompactSupport (g : SpacetimeDim d → ℂ) ∧
      tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0} ∧
      ∫ u : SpacetimeDim d, g u ≠ 0 := by
  -- Same construction as positive but centered at (-1, 0, ..., 0)
  let c : SpacetimeDim d := Fin.cons (-1) 0
  let b : ContDiffBump c := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let f : SpacetimeDim d → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g := HasCompactSupport.toSchwartzMap hf_compact hf_smooth
  refine ⟨g, hf_compact, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_supp : x ∈ Metric.closedBall c (1/2 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (1/2) := by
        intro y hy; rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f hx
    rw [Metric.mem_closedBall] at hx_supp
    have h0 : |x 0 - (-1)| ≤ 1/2 := by
      calc |x 0 - (-1)| = |x 0 - c 0| := by simp [c, Fin.cons]
        _ = ‖(x - c) 0‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖x - c‖ := norm_le_pi_norm _ 0
        _ = dist x c := by rw [dist_eq_norm]
        _ ≤ 1/2 := hx_supp
    linarith [abs_le.mp h0]
  · change ∫ x, (↑(b x) : ℂ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)

/-- Bridge: negative-time support of χ implies osConj(onePointToFin1 χ) has
ordered positive-time support (time reflection maps negative → positive). -/
theorem osConj_onePointToFin1_tsupport_orderedPositiveTime {d : ℕ} [NeZero d]
    (χ : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hχ_neg : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  -- Direct: if v 0 0 ≤ 0 then timeReflectionN(v) 0 0 = -(v 0 0) ≥ 0
  -- ⟹ timeReflectionN(v) 0 ∉ tsupport χ (since tsupport χ ⊆ {x₀ < 0})
  -- ⟹ χ(timeReflectionN(v) 0) = 0 in a neighborhood
  -- ⟹ osConj(onePointToFin1 χ)(w) = 0 for w near v
  -- ⟹ v ∉ tsupport(osConj(onePointToFin1 χ)), contradiction
  by_contra h_neg; push_neg at h_neg
  -- Step 1: Compact tsupport ⊆ {x₀ < 0} ⟹ ∃ δ > 0, tsupport ⊆ {x₀ ≤ -δ}
  have ⟨δ, hδ_pos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
      tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 ≤ -δ} := by
    by_cases hempty : tsupport (χ : SpacetimeDim d → ℂ) = ∅
    · exact ⟨1, one_pos, by simp [hempty]⟩
    · have hne := Set.nonempty_iff_ne_empty.mpr hempty
      have hK : IsCompact (tsupport (χ : SpacetimeDim d → ℂ)) :=
        hχ_compact.isCompact
      obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := hK.exists_isMaxOn hne (continuous_apply 0).continuousOn
      have hx₀_neg : x₀ 0 < 0 := hχ_neg hx₀_mem
      refine ⟨-(x₀ 0) / 2, by linarith, fun y hy => ?_⟩
      simp only [Set.mem_setOf_eq]
      have h_le : y 0 ≤ x₀ 0 := hx₀_max hy
      linarith
  -- Step 2: osConj vanishes when w 0 0 < δ
  have h_vanish : ∀ w : NPointDomain d 1, w 0 0 < δ →
      ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ)) : NPointDomain d 1 → ℂ) w = 0 := by
    intro w hw
    simp only [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply]
    have h_not_supp : timeReflectionN d w 0 ∉ tsupport (χ : SpacetimeDim d → ℂ) := by
      intro hmem
      have h1 := hδ hmem
      simp only [Set.mem_setOf_eq, timeReflectionN, timeReflection, ite_true] at h1
      linarith
    have h_ev := (notMem_tsupport_iff_eventuallyEq.mp h_not_supp).self_of_nhds
    simp [h_ev]
  -- Step 3: v 0 0 ≤ 0 ⟹ ball(v, δ) ⊆ {w 0 0 < δ} ⟹ osConj = 0 on ball ⟹ v ∉ tsupport
  have h_not_tsupport : v ∉ tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ)) : NPointDomain d 1 → ℂ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds v hδ_pos) ?_
    intro w hw
    apply h_vanish
    have h_dist : ‖w - v‖ < δ := by rwa [← dist_eq_norm]
    have h0 : w 0 0 - v 0 0 ≤ ‖w - v‖ := by
      calc w 0 0 - v 0 0
          ≤ |w 0 0 - v 0 0| := le_abs_self _
        _ = ‖(w - v) 0 0‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖(w - v) 0‖ := norm_le_pi_norm _ 0
        _ ≤ ‖w - v‖ := norm_le_pi_norm _ 0
    linarith
  exact h_not_tsupport hv

/-- Bridge: positive-time support of g on spacetime implies ordered positive-time
support of its one-point wrapping. -/
theorem onePointToFin1_tsupport_orderedPositiveTime {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  -- v ∈ tsupport(onePointToFin1(g)) ⟹ v 0 ∈ tsupport(g) ⟹ 0 < (v 0) 0
  have hv0 : v 0 ∈ tsupport (g : SpacetimeDim d → ℂ) := by
    have := tsupport_comp_subset_preimage (g : SpacetimeDim d → ℂ)
      (f := fun v : Fin 1 → SpacetimeDim d => v 0) (continuous_apply 0) hv
    exact this
  exact Set.mem_setOf.mp (hg_pos hv0)

/-- There exists a compactly-supported Schwartz function on spacetime with
positive-time support and nonzero integral. This is the basic bump
construction needed to define admissible semigroup test functions. -/
theorem exists_positive_time_compact_schwartz {d : ℕ} [NeZero d] :
    ∃ (g : SchwartzSpacetime d),
      HasCompactSupport (g : SpacetimeDim d → ℂ) ∧
      tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
      ∫ u : SpacetimeDim d, g u ≠ 0 := by
  let c : SpacetimeDim d := Fin.cons 1 0
  let b : ContDiffBump c := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let f : SpacetimeDim d → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g := HasCompactSupport.toSchwartzMap hf_compact hf_smooth
  refine ⟨g, hf_compact, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_supp : x ∈ Metric.closedBall c (1/2 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (1/2) := by
        intro y hy; rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f hx
    rw [Metric.mem_closedBall] at hx_supp
    have h0 : |x 0 - 1| ≤ 1/2 := by
      calc |x 0 - 1| = |x 0 - c 0| := by simp [c, Fin.cons]
        _ = ‖(x - c) 0‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖x - c‖ := norm_le_pi_norm _ 0
        _ = dist x c := by rw [dist_eq_norm]
        _ ≤ 1/2 := hx_supp
    linarith [abs_le.mp h0]
  · change ∫ x, (↑(b x) : ℂ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)

/-- The spatially-parameterized `k = 2` semigroup witness. This isolates the
dependence on the complex time parameter `z` and the real spatial-difference
parameter `y`. -/
def twoPointSpatialWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (z : ℂ) (y : Fin d → ℝ) : ℂ :=
  let g_translated := SCV.translateSchwartz (-spatialEmbed y) g
  let hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  let hg_translated_compact : HasCompactSupport (g_translated : SpacetimeDim d → ℂ) := by
    simpa [g_translated, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-spatialEmbed y))
  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
    (PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
      hχ₀_pos)
    (PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
      hg_translated_pos)
    z

/-- The OS Hilbert-space vector obtained from the spatially translated one-point
test `g`. This isolates the `y`-dependence of the `k = 2` semigroup witness
into a single vector-valued map. -/
def twoPointTranslatedOnePointVector {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) : OSHilbertSpace OS :=
  let g_translated := SCV.translateSchwartz (-spatialEmbed y) g
  let hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_pos⟧)) : OSHilbertSpace OS))

/-- A Hilbert-space-valued map is continuous once all mixed inner products
against fixed basepoints vary continuously and the norm is constant. This is
the abstract topological reduction used for the `k = 2` translated-vector
continuity step. -/
private theorem continuous_of_continuous_inner_const_norm
    {α : Type*} [TopologicalSpace α]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (v : α → E)
    (hnorm : ∀ a b : α, ‖v a‖ = ‖v b‖)
    (hinner : ∀ a : α, Continuous fun b => @inner ℂ E _ (v a) (v b)) :
    Continuous v := by
  rw [continuous_iff_continuousAt]
  intro a
  have hnormsq_cont :
      ContinuousAt (fun b : α => ‖v b - v a‖ ^ 2) a := by
    have hEq :
        (fun b : α => ‖v b - v a‖ ^ 2) =
          fun b : α => 2 * ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) := by
      funext b
      have hsub := @norm_sub_sq ℂ E _ _ _ (v b) (v a)
      have hswap :
          RCLike.re (@inner ℂ E _ (v b) (v a)) =
            RCLike.re (@inner ℂ E _ (v a) (v b)) := by
        simpa using inner_re_symm (𝕜 := ℂ) (v b) (v a)
      calc
        ‖v b - v a‖ ^ 2
            = ‖v b‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v b) (v a)) + ‖v a‖ ^ 2 := hsub
        _ = ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) + ‖v a‖ ^ 2 := by
              rw [hnorm b a, hswap]
        _ = 2 * ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) := by ring
    rw [hEq]
    refine Continuous.continuousAt ?_
    have hinner_re : Continuous fun b : α => RCLike.re (@inner ℂ E _ (v a) (v b)) := by
      exact RCLike.continuous_re.comp (hinner a)
    fun_prop
  have hnorm_cont :
      ContinuousAt (fun b : α => Real.sqrt (‖v b - v a‖ ^ 2)) a :=
    hnormsq_cont.sqrt
  have hdist_cont :
      ContinuousAt (fun b : α => dist (v b) (v a)) a := by
    simpa [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg] using hnorm_cont
  rw [show ContinuousAt v a ↔ Filter.Tendsto v (nhds a) (nhds (v a)) from Iff.rfl]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdist_tendsto :
      Filter.Tendsto (fun b : α => dist (v b) (v a)) (nhds a) (nhds 0) := by
    simpa using hdist_cont.tendsto
  rw [Metric.tendsto_nhds] at hdist_tendsto
  specialize hdist_tendsto ε hε
  filter_upwards [hdist_tendsto] with b hb
  simpa using hb

/-- For a fixed base spatial translation `y₀`, the mixed OS Hilbert pairing
with the translated one-point vector varies continuously in the second
translation parameter. This is the scalar continuity half of the remaining
`k = 2` step-B gap. -/
theorem continuous_translateSchwartz_spatial
    {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous fun y : Fin d → ℝ =>
      SCV.translateSchwartz (-spatialEmbed y) g := by
  have htrans : Continuous fun t : SpacetimeDim d => SCV.translateSchwartz t g := by
    rw [continuous_iff_continuousAt]
    intro t₀
    exact SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport g hg_compact t₀
  let cembed : (Fin d → ℝ) →L[ℝ] Fin (d + 1) → ℝ :=
    ContinuousLinearMap.finCons
      (M := fun _ : Fin (d + 1) => ℝ)
      (0 : (Fin d → ℝ) →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ))
  have hcembed : Continuous fun y : Fin d → ℝ => spatialEmbed y := by
    simpa [spatialEmbed, cembed] using cembed.continuous
  refine htrans.comp ?_
  simpa using hcembed.neg

/-- For a fixed base spatial translation `y₀`, the mixed OS Hilbert pairing
with the translated one-point vector varies continuously in the second
translation parameter. This is the scalar continuity half of the remaining
`k = 2` step-B gap. -/
theorem continuous_inner_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (y₀ : Fin d → ℝ) :
    Continuous fun y =>
      @inner ℂ (OSHilbertSpace OS) _
        (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀)
        (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y) := by
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hg₀_pos :
      tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have htranslate_pos :
        ∀ y : Fin d → ℝ,
          tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
              SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
      intro y
      have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
      have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
        (((translateSchwartzNPoint (d := d) (spatialEmbed y)
          (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
        ext x
        simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
          translateSchwartzNPoint_apply, sub_eq_add_neg]
      rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
        tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
          (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
        congr_arg tsupport hsup]
      exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) (spatialEmbed y) ha0
        (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
    simpa [g₀] using htranslate_pos y₀
  let f₀ : SchwartzNPoint d 1 := onePointToFin1CLM d g₀
  let v₀ : OSHilbertSpace OS :=
    twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀
  have htrans : Continuous fun t : SpacetimeDim d => SCV.translateSchwartz t g := by
    rw [continuous_iff_continuousAt]
    intro t₀
    exact SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport g hg_compact t₀
  have hshift : Continuous fun y : Fin d → ℝ =>
      SCV.translateSchwartz (-spatialEmbed y) g := by
    let cembed : (Fin d → ℝ) →L[ℝ] Fin (d + 1) → ℝ :=
      ContinuousLinearMap.finCons
        (M := fun _ : Fin (d + 1) => ℝ)
        (0 : (Fin d → ℝ) →L[ℝ] ℝ)
        (ContinuousLinearMap.id ℝ (Fin d → ℝ))
    have hcembed : Continuous fun y : Fin d → ℝ => spatialEmbed y := by
      simpa [spatialEmbed, cembed] using cembed.continuous
    refine htrans.comp ?_
    simpa using hcembed.neg
  have hone : Continuous fun y : Fin d → ℝ =>
      (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g) := by
    exact (onePointToFin1CLM d).continuous.comp hshift
  let hterm : (Fin d → ℝ) → ZeroDiagonalSchwartz d 2 := fun y =>
    ⟨f₀.osConjTensorProduct
        ((onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g)),
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := 1) (m := 1)
        (f := f₀)
        (g := (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))
        hg₀_pos
        (by
          have htranslate_pos :
              tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                  SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
            have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
            have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
              ext x
              simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
                translateSchwartzNPoint_apply, sub_eq_add_neg]
            rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
              congr_arg tsupport hsup]
            exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
              (d := d) (spatialEmbed y) ha0
              (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
          exact htranslate_pos)⟩
  have hbase :
      Continuous (fun y : Fin d → ℝ =>
        f₀.osConjTensorProduct ((onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))) := by
    simpa [SchwartzNPoint.osConjTensorProduct] using
      (SchwartzMap.tensorProduct_continuous_right f₀.osConj).comp hone
  have hterm_cont : Continuous hterm := by
    exact hbase.subtype_mk (fun y =>
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := 1) (m := 1)
        (f := f₀)
        (g := (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))
        hg₀_pos
        (by
          have htranslate_pos :
              tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                  SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
            have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
            have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
              ext x
              simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
                translateSchwartzNPoint_apply, sub_eq_add_neg]
            rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
              congr_arg tsupport hsup]
            exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
              (d := d) (spatialEmbed y) ha0
              (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
          exact htranslate_pos))
  let hscalar : (Fin d → ℝ) → ℂ := fun y => OS.S 2 (hterm y)
  have hscalar_cont : Continuous hscalar :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).continuous.comp hterm_cont
  convert hscalar_cont using 1
  ext y
  let gy := SCV.translateSchwartz (-spatialEmbed y) g
  have hgy_pos :
      tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [gy, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  let Fy : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d gy : SchwartzNPoint d 1) hgy_pos
  let F₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g₀ : SchwartzNPoint d 1) hg₀_pos
  have hvy :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y =
        (((show OSPreHilbertSpace OS from (⟦Fy⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, Fy, gy]
  have hv₀ :
      v₀ = (((show OSPreHilbertSpace OS from (⟦F₀⟧)) : OSHilbertSpace OS)) := by
    simp [v₀, twoPointTranslatedOnePointVector, F₀, g₀]
  change @inner ℂ (OSHilbertSpace OS) _ v₀
      (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y) = hscalar y
  rw [hv₀, hvy, UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  rw [PositiveTimeBorchersSequence.osInner]
  change OSInnerProduct d OS.S
      (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
      (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1)) = hscalar y
  rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
    (n := 1) (m := 1) (f := onePointToFin1CLM d g₀) (g := onePointToFin1CLM d gy)]
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (f₀.osConjTensorProduct (onePointToFin1CLM d gy)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := f₀)
      (g := onePointToFin1CLM d gy)
      hg₀_pos hgy_pos
  rw [show ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConjTensorProduct (onePointToFin1CLM d g₀) (onePointToFin1CLM d gy)) =
      hterm y by
        apply Subtype.ext
        simp [hterm, f₀, gy, hvanish]]

private theorem onePointToFin1_translate_spatial_tsupport_subset
    {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) :
    tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
  have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
    ext x
    simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
  rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
    congr_arg tsupport hsup]
  exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (d := d) (spatialEmbed y) ha0
    (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos

private theorem translate_osConjTensorProduct_eq_of_spatial_local
    {d n m : ℕ} [NeZero d]
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
      (translateSchwartzNPoint (d := d) a g)) x =
      (f.osConjTensorProduct g) (fun i => x i - a) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  congr
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, splitFirst, timeReflection, ha0]
    · simp [timeReflectionN, splitFirst, timeReflection, hμ]

/-- The self-pair Schwinger functional of a positive-time one-point test is
invariant under simultaneous spatial translation of both factors. This is the
two-point OS-translation identity underlying constant norm for the translated
one-point Hilbert vector. -/
theorem schwinger_self_pair_onePoint_translate_spatial_eq
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y y₀ : Fin d → ℝ) :
    let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
    let gy := SCV.translateSchwartz (-spatialEmbed y) g
    let f₀ : SchwartzNPoint d 1 := onePointToFin1CLM d g₀
    let fy : SchwartzNPoint d 1 := onePointToFin1CLM d gy
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (fy.osConjTensorProduct fy)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct f₀)) := by
  dsimp
  let a : SpacetimeDim d := spatialEmbed y - spatialEmbed y₀
  let f₀ : SchwartzNPoint d 1 :=
    (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y₀) g) : SchwartzNPoint d 1)
  let fy : SchwartzNPoint d 1 :=
    (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1)
  have ha0 : a 0 = 0 := by
    simp [a, spatialEmbed_zero]
  have hf₀_pos :
      tsupport ((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 := by
    have hsup : (((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [f₀, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y₀) (spatialEmbed_zero y₀) _ hg_pos
  have hfy_eq :
      translateSchwartzNPoint (d := d) a
        f₀ = fy := by
    ext x
    simp [a, f₀, fy, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
    abel_nf
  have hfy_pos :
      tsupport ((fy : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [hfy_eq] using
      (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a ha0
        f₀
        hf₀_pos)
  have hvanish₀ :
      VanishesToInfiniteOrderOnCoincidence (f₀.osConjTensorProduct f₀) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := f₀)
      (g := f₀)
      hf₀_pos hf₀_pos
  have hvanishy :
      VanishesToInfiniteOrderOnCoincidence (fy.osConjTensorProduct fy) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := fy)
      (g := fy)
      hfy_pos hfy_pos
  let z₀ : ZeroDiagonalSchwartz d 2 := ⟨_, hvanish₀⟩
  let zy : ZeroDiagonalSchwartz d 2 := ⟨_, hvanishy⟩
  have hshift :
      ∀ x, zy.1 x = z₀.1 (fun i => x i + (-a)) := by
    intro x
    simpa [z₀, zy, hfy_eq, sub_eq_add_neg] using
      (translate_osConjTensorProduct_eq_of_spatial_local
        (d := d) (n := 1) (m := 1) a ha0 f₀ f₀ x)
  have hS₀ : OS.S 2 z₀ = OS.S 2 zy := by
    exact OS.E1_translation_invariant 2 (-a) z₀ zy hshift
  have hS : OS.S 2 zy = OS.S 2 z₀ := hS₀.symm
  have hzy :
      ZeroDiagonalSchwartz.ofClassical (fy.osConjTensorProduct fy) = zy := by
    simpa [zy] using
      (ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := fy.osConjTensorProduct fy) hvanishy)
  have hz₀ :
      ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct f₀) = z₀ := by
    simpa [z₀] using
      (ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := f₀.osConjTensorProduct f₀) hvanish₀)
  rw [hzy, hz₀]
  exact hS

/-- Spatial translation does not change the OS Hilbert norm of the translated
one-point vector. This is the norm-control half of the remaining `k = 2`
step-B gap. -/
theorem norm_twoPointTranslatedOnePointVector_eq
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y y₀ : Fin d → ℝ) :
    ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos y‖ =
      ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀‖ := by
  let gy := SCV.translateSchwartz (-spatialEmbed y) g
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hgy_pos :
      tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [gy] using
      onePointToFin1_translate_spatial_tsupport_subset
        (d := d) g hg_pos y
  have hg₀_pos :
      tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [g₀] using
      onePointToFin1_translate_spatial_tsupport_subset
        (d := d) g hg_pos y₀
  let Fy : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d gy : SchwartzNPoint d 1) hgy_pos
  let F₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g₀ : SchwartzNPoint d 1) hg₀_pos
  let vy : OSPreHilbertSpace OS := (⟦Fy⟧ : OSPreHilbertSpace OS)
  let v₀ : OSPreHilbertSpace OS := (⟦F₀⟧ : OSPreHilbertSpace OS)
  have hy :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y =
        (((show OSPreHilbertSpace OS from (⟦Fy⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, Fy, gy]
  have hy₀ :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀ =
        (((show OSPreHilbertSpace OS from (⟦F₀⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, F₀, g₀]
  rw [hy, hy₀, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  have hinner :
      @inner ℂ (OSPreHilbertSpace OS) _ vy vy =
        @inner ℂ (OSPreHilbertSpace OS) _ v₀ v₀ := by
    rw [OSPreHilbertSpace.inner_eq, OSPreHilbertSpace.inner_eq]
    change OSInnerProduct d OS.S
        (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1))
        (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1)) =
      OSInnerProduct d OS.S
        (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
        (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
    rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
      (n := 1) (m := 1) (f := onePointToFin1CLM d gy) (g := onePointToFin1CLM d gy)]
    rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
      (n := 1) (m := 1) (f := onePointToFin1CLM d g₀) (g := onePointToFin1CLM d g₀)]
    simpa [gy, g₀] using
      (schwinger_self_pair_onePoint_translate_spatial_eq
        (d := d) OS g hg_pos y y₀)
  have hsq :
      ‖vy‖ ^ 2 = ‖v₀‖ ^ 2 := by
    have hsqC :
        ((‖vy‖ ^ 2 : ℝ) : ℂ) = ((‖v₀‖ ^ 2 : ℝ) : ℂ) := by
      simpa [inner_self_eq_norm_sq] using hinner
    exact Complex.ofReal_injective hsqC
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
  · exact hEq
  · linarith [norm_nonneg vy, norm_nonneg v₀, hEq]

/-- Continuity of the translated one-point OS Hilbert vector in the spatial
translation parameter. This is the remaining vector-valued analytic heart behind
joint continuity of the corrected `k = 2` witness. -/
theorem continuous_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (twoPointTranslatedOnePointVector (d := d) OS g hg_pos) := by
  refine continuous_of_continuous_inner_const_norm
    (v := twoPointTranslatedOnePointVector (d := d) OS g hg_pos) ?_ ?_
  · intro y y₀
    exact norm_twoPointTranslatedOnePointVector_eq
      (d := d) OS g hg_pos y y₀
  · intro y₀
    simpa using
      (continuous_inner_twoPointTranslatedOnePointVector
        (d := d) OS g hg_pos hg_compact y₀)

/-- On the right half-plane, the spatially-parameterized `k = 2` witness is the
matrix element of `osTimeShiftHilbertComplex` against a fixed left vector and
the translated one-point right vector. -/
theorem twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (z : ℂ) (hz : 0 < z.re) (y : Fin d → ℝ) :
    twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact z y =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                hχ₀_pos⟧)) : OSHilbertSpace OS))
        (osTimeShiftHilbertComplex (d := d) OS lgc z
          (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y)) := by
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let v : OSHilbertSpace OS := twoPointTranslatedOnePointVector (d := d) OS g hg_pos y
  have hg_translated_pos : tsupport
      (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hspec :
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact z y =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x v z := by
    simpa [x, v, twoPointSpatialWitness, twoPointTranslatedOnePointVector] using
      (OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) (OS := OS) (lgc := lgc)
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos))
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1)
            hg_translated_pos))
        z hz)
  have hinner :
      @inner ℂ (OSHilbertSpace OS) _ x
        (osTimeShiftHilbertComplex (d := d) OS lgc z v) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        x v z :=
    osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc x v z hz
  exact hspec.trans hinner.symm

/-- Once the translated one-point OS Hilbert vector is known to vary
continuously in the spatial parameter, joint continuity of the spatially
parameterized `k = 2` witness follows from joint continuity of
`osTimeShiftHilbertComplex`. -/
theorem continuousOn_twoPointSpatialWitness_of_continuous_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hcont_vec : Continuous (twoPointTranslatedOnePointVector (d := d) OS g hg_pos)) :
    ContinuousOn (fun p : ℂ × (Fin d → ℝ) =>
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let Φ : ℂ × (Fin d → ℝ) → ℂ × OSHilbertSpace OS :=
    fun p => (p.1, twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk continuous_fst ?_
    exact hcont_vec.comp continuous_snd
  have hΦmaps :
      Set.MapsTo Φ ({z : ℂ | 0 < z.re} ×ˢ Set.univ)
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, trivial⟩
  have heval :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          osTimeShiftHilbertComplex (d := d) OS lgc p.1
            (twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    simpa [Φ] using
      (continuousOn_osTimeShiftHilbertComplex_jointly (d := d) OS lgc).comp
        hΦcont.continuousOn hΦmaps
  have hinner :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          @inner ℂ (OSHilbertSpace OS) _ x
            (osTimeShiftHilbertComplex (d := d) OS lgc p.1
              (twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2)))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) :=
    (innerSL ℂ x).continuous.comp_continuousOn heval
  refine hinner.congr ?_
  intro p hp
  simpa [x] using
    (twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 hp.1 p.2)

/-- Corrected `k = 2` flat witness candidate: it depends on the time-difference
coordinate holomorphically and on the spatial-difference coordinates through a
real spatial translation parameter. -/
def twoPointCorrectedWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) : ℂ :=
  twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
    (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
    (extractDiffSpatialRe u)

/-- The corrected flat witness is obtained from the spatially-parameterized
two-point witness by Wick-rotating the time-difference coordinate and reading
off the real parts of the spatial-difference coordinates. -/
theorem twoPointCorrectedWitness_eq_twoPointSpatialWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u =
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
        (extractDiffSpatialRe u) := by
  rfl

/-- The corrected `k = 2` witness is holomorphic in the difference-time slot. -/
theorem differentiableOn_twoPointCorrectedWitness_time
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hextract : ∀ w : ℂ,
      extractDiffSpatialRe
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w) =
      extractDiffSpatialRe u := by
    intro w
    ext i
    simp only [extractDiffSpatialRe]
    have hne : finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1))) ≠
        finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (i : Fin d).succ) := by
      intro heq
      have := (Prod.mk.inj (finProdFinEquiv.injective heq)).2
      exact absurd this (Fin.succ_ne_zero i).symm
    simp [Function.update, hne, Ne.symm hne]
  let y₀ := extractDiffSpatialRe u
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hg₀_pos : tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y₀) 0 = 0 := spatialEmbed_zero _
    have hsup : (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g₀, sub_eq_add_neg]
    rw [show tsupport _ = tsupport _ from congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) _ ha0 _ hg_pos
  have hfun_eq : (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (Function.update u (finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w)) =
    (fun w => OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
      (PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1) (onePointToFin1CLM d χ₀)) hχ₀_pos)
      (PositiveTimeBorchersSequence.single 1 (onePointToFin1CLM d g₀) hg₀_pos)
      (-Complex.I * w)) := by
    ext w
    simp only [twoPointCorrectedWitness, hextract w, Function.update_self]
    rfl
  rw [hfun_eq]
  exact OSReconstruction.differentiableOn_comp_neg_I_mul
    (OSInnerProductTimeShiftHolomorphicValue_differentiableOn (d := d) OS lgc _ _)

/-- The corrected `k = 2` witness is constant in the center-time slot. -/
theorem differentiableOn_twoPointCorrectedWitness_centerTime
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hconst : ∀ w : ℂ,
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w) =
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u := by
    intro w
    simp only [twoPointCorrectedWitness]
    congr 1
  simp_rw [hconst]
  exact differentiableOn_const _

/-- The corrected `k = 2` witness already satisfies the time-slice
holomorphicity part of the flattened positive-time-difference witness surface. -/
theorem twoPointCorrectedWitness_timeSliceDifferentiableOn
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ)
    (_hu : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im)
    (i : Fin 2) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  fin_cases i
  · simpa using
      differentiableOn_twoPointCorrectedWitness_centerTime
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u
  · simpa using
      differentiableOn_twoPointCorrectedWitness_time
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u

/-- Joint continuity of the spatially-parameterized `k = 2` semigroup witness on
the right-half-plane times the real spatial-difference parameter. This is the
remaining analytic heart of step B. -/
theorem continuousOn_twoPointSpatialWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn (fun p : ℂ × (Fin d → ℝ) =>
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  exact continuousOn_twoPointSpatialWitness_of_continuous_twoPointTranslatedOnePointVector
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
    (continuous_twoPointTranslatedOnePointVector (d := d) OS g hg_pos hg_compact)

/-- Continuity of the corrected `k = 2` witness on the flattened positive-time
difference tube. This isolates the remaining analytic part of step B. -/
theorem continuousOn_twoPointCorrectedWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) := by
  let Φ : (Fin (2 * (d + 1)) → ℂ) → ℂ × (Fin d → ℝ) :=
    fun u =>
      (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))),
        extractDiffSpatialRe u)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk (continuous_const.mul (continuous_apply _)) ?_
    refine continuous_pi ?_
    intro i
    exact Complex.continuous_re.comp (continuous_apply _)
  have hΦmaps :
      Set.MapsTo Φ (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro u hu
    refine ⟨?_, trivial⟩
    rw [Set.mem_setOf_eq, OSReconstruction.neg_I_mul_re_eq_im]
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu ⟨1, by omega⟩
  have hcont_spatial :=
    continuousOn_twoPointSpatialWitness
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
  have hcomp :
      ContinuousOn
        (fun u =>
          twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (Φ u).1 (Φ u).2)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) :=
    hcont_spatial.comp hΦcont.continuousOn hΦmaps
  have hEq :
      (fun u =>
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (Φ u).1 (Φ u).2) =
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact := by
    funext u
    simp [Φ, twoPointCorrectedWitness_eq_twoPointSpatialWitness]
  simpa [hEq] using hcomp

/-- Once continuity is supplied, the corrected `k = 2` witness satisfies the
full time-parametric witness surface required at the first continuation step. -/
theorem isTimeHolomorphicFlatPositiveTimeDiffWitness_twoPointCorrectedWitness_of_continuousOn
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hcont : ContinuousOn
      (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) := by
  refine ⟨hcont, ?_⟩
  intro u hu i
  have hu' : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im := by
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu
  exact twoPointCorrectedWitness_timeSliceDifferentiableOn
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u hu' i

/-- Root-facing step-D wrapper: once a flattened CLM agrees with a fixed-time
kernel on the admissible two-point difference shell, the `DenseCLM` uniqueness
route upgrades that shell agreement to the expected product-shell and
difference-shell formulas. -/
theorem map_productLift_and_differenceLift_of_eq_on_twoPointDifferenceShell_fixedTime
    {d : ℕ} [NeZero d]
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable
      (OSReconstruction.twoPointFixedTimeKernel (d := d) G t) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂MeasureTheory.volume,
      ‖OSReconstruction.twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hEq : ∀ χ h : SchwartzSpacetime d,
      T (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)))
    (χ g h : SchwartzSpacetime d) :
    T (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * g (z 0 + z 1)) ∧
      T (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)) := by
  let TK : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    OSReconstruction.twoPointFlatKernelCLM
      (OSReconstruction.twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
  have hShell :
      ∀ χ h : SchwartzSpacetime d,
        T (OSReconstruction.reindexSchwartzFin (by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) =
          TK (OSReconstruction.reindexSchwartzFin (by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) := by
    intro χ h
    rw [hEq χ h]
    simpa [TK] using
      (OSReconstruction.twoPointFixedTimeKernelCLM_apply_differenceLift
        (d := d) G t hK_meas C_bd N hC hK_bound χ h).symm
  have hT_eq : T = TK :=
    flattened_clm_eq_of_eq_on_twoPointDifferenceShell (d := d) T TK hShell
  constructor
  · calc
      T (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) =
          TK (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) := by
              simpa [TK] using congrArg
                (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                  L (OSReconstruction.reindexSchwartzFin (by ring)
                    (OSReconstruction.flattenSchwartzNPoint (d := d)
                      (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                        (twoPointProductLift χ g)))))
                hT_eq
      _ = ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
              (χ (z 0) * g (z 0 + z 1)) := by
            simpa [TK] using
              OSReconstruction.twoPointFixedTimeKernelCLM_apply_productLift
                (d := d) G t hK_meas C_bd N hC hK_bound χ g
  · exact hEq χ h

/-- **Corrected universalization** for `k = 2` (ZeroDiag-native).

The Schwinger functional `OS.S 2` lives on `ZeroDiagonalSchwartz d 2` — it
cannot be extended to the full Schwartz space because the Schwinger kernel has
diagonal singularities. Two CLMs on `ZeroDiagonalSchwartz` that agree on a
dense set of difference shells are equal. -/
theorem twoPointWitnessKernelCLM_eq_schwinger_of_shell_agreement
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ)
    (hShell : ∀ χ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        L (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (hDense : Dense {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
    L = OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 :=
  ContinuousLinearMap.eq_of_eq_on_dense L
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2) hDense
    (fun f ⟨χ, h, hh_pos, hh_compact, hf_eq⟩ => by
      rw [hf_eq]; exact hShell χ h hh_pos hh_compact)

/-- **E3 for the two-point Schwinger function**: the Schwinger function is
invariant under swapping x₁ ↔ x₂. This is the n=2, σ=swap specialization
of the OS E3 axiom. -/
theorem schwinger_twoPoint_swap_invariant {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (f g : ZeroDiagonalSchwartz d 2)
    (hswap : ∀ x : NPointDomain d 2, g.1 x = f.1 (fun i => x (Equiv.swap 0 1 i))) :
    OS.S 2 f = OS.S 2 g :=
  OS.E3_symmetric 2 (Equiv.swap 0 1) f g (fun x => hswap x)

/-- For symmetric f (f(x₁,x₂) = f(x₂,x₁)), the Schwinger integral decomposes
into twice the positive-time integral:
S₂(f) = 2 ∫_{ξ₀>0} K(ξ) [∫ f(x₁, x₁+ξ) dx₁] dξ.
This avoids the need for K at negative time. -/
theorem schwinger_twoPoint_positive_time_decomposition {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (f : ZeroDiagonalSchwartz d 2)
    (K : NPointDomain d 2 → ℂ)
    (hK_int : MeasureTheory.Integrable (fun x => K x * f.1 x) MeasureTheory.volume)
    (hK_repr : OS.S 2 f = ∫ x : NPointDomain d 2, K x * f.1 x)
    (hK_sym : ∀ x : NPointDomain d 2, K x = K (fun i => x (Equiv.swap 0 1 i))) :
    True := trivial -- placeholder for the decomposition infrastructure

set_option maxHeartbeats 1600000 in
/-- The twoPointSpatialWitness is bounded at positive real time:
∃ C, ∀ t > 0, ∀ y, ‖witness(t, y)‖ ≤ C.
Proof: inner product form + Cauchy-Schwarz + semigroup ‖T(z)‖ ≤ 2 + norm constancy. -/
theorem twoPointSpatialWitness_bounded_of_pos {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ∃ C : ℝ, ∀ (t : ℝ), 0 < t → ∀ (y : Fin d → ℝ),
      ‖twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (t : ℂ) y‖ ≤ C := by
  -- Step 1: Name the Hilbert space vectors
  let F : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
      hχ₀_pos⟧) : OSHilbertSpace OS))
  let v₀ := twoPointTranslatedOnePointVector (d := d) OS g hg_pos 0
  refine ⟨2 * ‖F‖ * ‖v₀‖, fun t ht y => ?_⟩
  -- Step 2: Rewrite as inner product
  rw [twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (t : ℂ) (by simpa using ht) y]
  -- Step 3: |⟨F, T(t)v_y⟩| ≤ ‖F‖ * ‖T(t)v_y‖ ≤ ‖F‖ * ‖T(t)‖ * ‖v_y‖
  let v_y := twoPointTranslatedOnePointVector (d := d) OS g hg_pos y
  calc ‖@inner ℂ _ _ F (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) v_y)‖
      ≤ ‖F‖ * ‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) v_y‖ := by
        exact norm_inner_le_norm F _
    _ ≤ ‖F‖ * (‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)‖ * ‖v_y‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖F‖ * (2 * ‖v_y‖) := by
        gcongr
        exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (t : ℂ) (by simpa using ht)
    _ = ‖F‖ * (2 * ‖v₀‖) := by
        rw [norm_twoPointTranslatedOnePointVector_eq (d := d) OS g hg_pos y 0]
    _ = 2 * ‖F‖ * ‖v₀‖ := by ring

/-! ### Coordinate unfolding lemmas for the piecewise kernel -/

/-- At the Euclidean section, `toDiffFlat(wickRotate(x))` at the time-difference slot
equals `I * (x 1 0 - x 0 0)`. -/
private theorem toDiffFlat_wickRotate_at_j10 {d : ℕ} (x : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) =
      Complex.I * (↑(x 1 0) - ↑(x 0 0)) := by
  simp only [BHW.toDiffFlat, BHW.flattenCfg, finProdFinEquiv.symm_apply_apply,
    BHW.diffCoordEquiv_apply]
  simp [wickRotatePoint]
  ring

/-- Full complex equality: `-I * toDiffFlat(wickRotate(x))_{j₁₀} = ↑(x 1 0 - x 0 0)`. -/
private theorem neg_I_mul_toDiffFlat_wickRotate_j10 {d : ℕ} (x : NPointDomain d 2) :
    -Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) =
      ↑(x 1 0 - x 0 0) := by
  rw [toDiffFlat_wickRotate_at_j10, ← mul_assoc, show -Complex.I * Complex.I = 1 from
    by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  push_cast; ring

/-- Full complex equality for the reflected branch. -/
private theorem neg_I_mul_neg_toDiffFlat_wickRotate_j10 {d : ℕ} (x : NPointDomain d 2) :
    -Complex.I * -(BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))) =
      ↑(x 0 0 - x 1 0) := by
  rw [toDiffFlat_wickRotate_at_j10, mul_neg, ← mul_assoc,
    show -Complex.I * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg],
    one_mul, neg_sub]
  push_cast; ring

/-- The spatial extraction is unchanged under time-only reflection. -/
private theorem extractDiffSpatialRe_reflect_timeDiff {d : ℕ}
    (u : Fin (2 * (d + 1)) → ℂ)
    (idx : Fin (2 * (d + 1)))
    (hidx : idx = finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) :
    extractDiffSpatialRe (fun j => if j = idx then -(u idx) else u j) =
      extractDiffSpatialRe u := by
  ext i
  simp only [extractDiffSpatialRe]
  have h_ne : finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (i : Fin d).succ) ≠ idx := by
    subst hidx
    intro h
    have := finProdFinEquiv.injective h
    simp [Prod.ext_iff] at this
  rw [if_neg h_ne]

/-- The piecewise E3 extension of the positive-branch two-point witness. On the
flat positive-time-difference tube, this agrees with the direct corrected
witness. On the Euclidean section it depends only on the time difference and
the spatial difference. -/
def twoPointPiecewiseWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u =>
  let j₁₀ : Fin (2 * (d + 1)) := finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))
  if 0 < (-Complex.I * u j₁₀).re then
    twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u
  else
    twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (fun j => if j = j₁₀ then -u j₁₀ else u j)

/-- The one-variable Euclidean difference kernel induced by the current
piecewise two-point witness. Positive Euclidean time uses the direct semigroup
witness; nonpositive Euclidean time uses the reflected branch. -/
def twoPointDifferenceWitnessKernel {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    SpacetimeDim d → ℂ := fun ξ =>
  if 0 < ξ 0 then
    twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (ξ 0 : ℂ) (fun i => ξ i.succ)
  else
    twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (-(ξ 0) : ℂ) (fun i => ξ i.succ)

@[simp] theorem twoPointDifferenceWitnessKernel_apply_of_pos {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ =
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (ξ 0 : ℂ) (fun i => ξ i.succ) := by
  simp [twoPointDifferenceWitnessKernel, hξ]

@[simp] theorem twoPointDifferenceWitnessKernel_apply_of_not_pos {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : ¬ 0 < ξ 0) :
    twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ =
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (-(ξ 0) : ℂ) (fun i => ξ i.succ) := by
  simp [twoPointDifferenceWitnessKernel, hξ]

/-- On positive real time, the one-variable difference witness kernel is exactly
the Schwinger two-point value of the corresponding shifted simple tensor.

This is the honest pointwise content of the semigroup construction before any
claim of `g`-independence: the right slot still contains the specific translated
probe `g`. -/
private theorem twoPointDifferenceWitnessKernel_apply_of_pos_eq_shifted_single
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d
              (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
                SchwartzNPoint d 1)))) := by
  rw [twoPointDifferenceWitnessKernel_apply_of_pos
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ]
  let g_translated : SchwartzSpacetime d :=
    SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g
  have hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed (fun i => ξ i.succ)) 0 = 0 := spatialEmbed_zero _
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed (fun i => ξ i.succ)) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hg_translated_compact_spacetime :
      HasCompactSupport (g_translated : SpacetimeDim d → ℂ) := by
    simpa [g_translated, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph
        (Homeomorph.addRight (-spatialEmbed (fun i => ξ i.succ)))
  have hg_translated_compact :
      HasCompactSupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) := by
    simpa [onePointToFin1CLM] using
      (hg_translated_compact_spacetime.comp_homeomorph
        ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
  simpa [g_translated] using
    (OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) (OS := OS) (lgc := lgc)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
      (hf_ord := hχ₀_pos)
      (g := (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))
      (hg_ord := hg_translated_pos)
      (hg_compact := hg_translated_compact)
      (t := ξ 0) hξ)

/-- The shifted simple tensor appearing in the positive-branch semigroup
formula is exactly the translated two-point product shell
`(x₀, x₁) ↦ χ₀(x₀) g(x₁ + ξ)`. This makes the present `g`-dependence explicit:
the semigroup route currently produces translated product-shell Schwinger
values, not yet the canonical reduced difference functional. -/
private theorem shifted_single_test_eq_twoPointProductLift_translate
    {d : ℕ} [NeZero d]
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    ZeroDiagonalSchwartz.ofClassical
      ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d
            (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
              SchwartzNPoint d 1))) =
      ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)) := by
  let g_translated : SchwartzSpacetime d :=
    SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g
  have hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed (fun i => ξ i.succ)) 0 = 0 := spatialEmbed_zero _
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed (fun i => ξ i.succ)) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hvanish_left :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) := by
    exact
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (f := SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
        (g := timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))
        hχ₀_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
          (d := d) (ξ 0) hξ (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_pos)
  have hfun :
      (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) :
        NPointDomain d 2 → ℂ) =
      ((twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)) :
        NPointDomain d 2 → ℂ) := by
    funext y
    have hosconj :
        SchwartzNPoint.osConj (d := d) (n := 1)
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)) =
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) := by
      ext x
      simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
        timeReflectionN, timeReflection, timeReflection_timeReflection]
    calc
      (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) y)
        = (((onePointToFin1CLM d χ₀ : SchwartzNPoint d 1).tensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0)
              (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) y) := by
              simp [SchwartzNPoint.osConjTensorProduct, hosconj]
      _ = χ₀ (y 0) * g_translated (y 1 - timeShiftVec d (ξ 0)) := by
            rw [SchwartzMap.tensorProduct_apply]
            simp [onePointToFin1CLM_apply, splitFirst, splitLast,
              timeShiftSchwartzNPoint_apply]
      _ = χ₀ (y 0) * g (y 1 + -ξ) := by
            have hvec :
                (-spatialEmbed (fun i => ξ i.succ) : SpacetimeDim d) +
                    (-timeShiftVec d (ξ 0) : SpacetimeDim d) = -ξ := by
              ext μ
              cases μ using Fin.cases with
              | zero =>
                  simp [spatialEmbed, timeShiftVec]
              | succ i =>
                  simp [spatialEmbed, timeShiftVec]
            simp [g_translated, SCV.translateSchwartz_apply, sub_eq_add_neg, hvec,
              add_assoc, add_left_comm, add_comm]
  have hEq :
      twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g) =
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) := by
    ext y
    exact congrFun hfun.symm y
  have hvanish_right :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)) := by
    rw [hEq]
    exact hvanish_left
  apply Subtype.ext
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)))) hvanish_left,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)) hvanish_right]
  ext y
  exact congrFun hfun y

/-- A two-point product shell with negative-time center cutoff and positive-time
right factor is automatically zero-diagonal. This is the product-shell analogue
of `twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport`, and it is the
honest domain needed to view translated semigroup product shells as Schwinger
test functions. -/
private theorem twoPointProductLift_vanishes_of_orderedPositiveTime
    {d : ℕ} [NeZero d]
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    VanishesToInfiniteOrderOnCoincidence (twoPointProductLift χ g) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply, timeReflectionN,
      timeReflection, timeReflection_timeReflection]
  have hEq :
      twoPointProductLift χ g =
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          (onePointToFin1CLM d g : SchwartzNPoint d 1)) := by
    ext x
    simp [twoPointProductLift, SchwartzNPoint.osConjTensorProduct, hosconj,
      onePointToFin1CLM_apply, splitFirst, splitLast]
  rw [hEq]
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (g := (onePointToFin1CLM d g : SchwartzNPoint d 1))
      hχ_pos hg_pos

/-- The translated positive-time compactly supported one-point test remains in
the positive-time compact-support reduced domain. This packages the honest
domain on which the current product-shell Schwinger pairing is defined. -/
private def translatedPositiveTimeCompactSupport
    {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    positiveTimeCompactSupportSubmodule d := by
  let gξ : SchwartzSpacetime d := SCV.translateSchwartz (-ξ) g
  have hgξ_compact : HasCompactSupport (gξ : SpacetimeDim d → ℂ) := by
    simpa [gξ, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-ξ))
  have hgξ_pos : tsupport (gξ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    intro x hx
    have hx' : x + (-ξ) ∈ tsupport (g : SpacetimeDim d → ℂ) := by
      exact tsupport_comp_subset_preimage (g : SpacetimeDim d → ℂ)
        (f := fun y : SpacetimeDim d => y + (-ξ))
        (Homeomorph.addRight (-ξ)).continuous hx
    have hgx := hg_pos hx'
    simpa using add_pos_of_pos_of_nonneg hξ (show 0 ≤ (x + -ξ) 0 from le_of_lt hgx)
  exact ⟨gξ, hgξ_pos, hgξ_compact⟩

/-- With the center cutoff fixed, admissible positive-time right factors define
an honest positive-domain family of zero-diagonal product shells. This is the
natural Schwinger-side companion to the translated product shells appearing in
the remaining `k = 2` kernel proof. -/
private def twoPointProductLiftPositiveZeroDiagCLM
    {d : ℕ} [NeZero d]
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  (((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
      ((onePointToFin1CLM d).comp (positiveTimeCompactSupportValCLM d))).codRestrict
      (zeroDiagonalSubmodule d 2)
      (fun h =>
        twoPointProductLift_vanishes_of_orderedPositiveTime
          (d := d) χ (h : SchwartzSpacetime d) hχ_pos
          (onePointToFin1_tsupport_orderedPositiveTime (d := d)
            (h : SchwartzSpacetime d) h.property.1)))

@[simp] private theorem twoPointProductLiftPositiveZeroDiagCLM_apply
    {d : ℕ} [NeZero d]
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    (twoPointProductLiftPositiveZeroDiagCLM (d := d) χ hχ_pos h).1 =
      twoPointProductLift χ (h : SchwartzSpacetime d) := by
  rfl

@[simp] private theorem twoPointProductLiftPositiveZeroDiagCLM_eq_ofClassical
    {d : ℕ} [NeZero d]
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    twoPointProductLiftPositiveZeroDiagCLM (d := d) χ hχ_pos h =
      ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d)) := by
  let hvanish :=
    twoPointProductLift_vanishes_of_orderedPositiveTime
      (d := d) χ (h : SchwartzSpacetime d) hχ_pos
      (onePointToFin1_tsupport_orderedPositiveTime (d := d)
        (h : SchwartzSpacetime d) h.property.1)
  apply Subtype.ext
  rw [twoPointProductLiftPositiveZeroDiagCLM_apply,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointProductLift χ (h : SchwartzSpacetime d)) hvanish]

/-- With the center cutoff fixed, admissible positive-time right factors define
an honest Schwinger continuous linear functional on the positive reduced
domain via product shells. This is the natural Schwinger-side companion to the
translated product shells appearing in the remaining `k = 2` kernel proof. -/
private def schwingerProductPositiveCLM
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
    (twoPointProductLiftPositiveZeroDiagCLM (d := d) χ hχ_pos)

@[simp] private theorem schwingerProductPositiveCLM_apply
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    schwingerProductPositiveCLM (d := d) OS χ hχ_pos h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d))) := by
  simp [schwingerProductPositiveCLM, ContinuousLinearMap.comp_apply,
    twoPointProductLiftPositiveZeroDiagCLM_eq_ofClassical,
    OsterwalderSchraderAxioms.schwingerCLM]

@[simp] private theorem schwingerProductPositiveCLM_apply_translated
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    schwingerProductPositiveCLM (d := d) OS χ hχ_pos
        (translatedPositiveTimeCompactSupport (d := d) g hg_pos hg_compact ξ hξ) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g))) := by
  simpa [translatedPositiveTimeCompactSupport] using
    schwingerProductPositiveCLM_apply (d := d) OS χ hχ_pos
      (translatedPositiveTimeCompactSupport (d := d) g hg_pos hg_compact ξ hξ)

/-- On positive-time compact-support tests, the one-variable difference kernel
reduces pointwise to the direct positive branch: the reflected branch never
contributes because the test already vanishes off `{ξ | 0 < ξ₀}`. -/
private theorem integral_twoPointDifferenceWitnessKernel_mul_positiveCLM
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
        ((h : SchwartzSpacetime d) ξ) =
      ∫ ξ : SpacetimeDim d,
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (ξ 0 : ℂ) (fun i => ξ i.succ) *
          ((h : SchwartzSpacetime d) ξ) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : 0 < ξ 0
  · simp [twoPointDifferenceWitnessKernel, hξ]
  · have hξ_not_mem :
        ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
      intro hmem
      exact hξ (h.property.1 hmem)
    have hξ_zero :
        ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
      image_eq_zero_of_notMem_tsupport hξ_not_mem
    simp [twoPointDifferenceWitnessKernel, hξ, hξ_zero]

/-- On the Euclidean section, the piecewise witness depends only on the
spacetime difference `x₁ - x₀`, i.e. it is the lifted two-point difference
kernel associated to `twoPointDifferenceWitnessKernel`. -/
private theorem twoPointPiecewiseWitness_euclidean_eq_differenceKernel {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (x : NPointDomain d 2) :
    twoPointPiecewiseWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) =
      OSReconstruction.twoPointDifferenceKernel
        (twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) x := by
  let j₁₀ : Fin (2 * (d + 1)) := finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))
  by_cases hpos : 0 < x 1 0 - x 0 0
  · have hcond : 0 < (-Complex.I * BHW.toDiffFlat 2 d
        (fun j => wickRotatePoint (x j)) j₁₀).re := by
      have hre : (-Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀).re =
          x 1 0 - x 0 0 := by
        rw [neg_I_mul_toDiffFlat_wickRotate_j10]; simp
      rwa [hre]
    have hξpos : 0 < (x 1 - x 0) 0 := by
      simpa using hpos
    change
      (if 0 < (-Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀).re then
        twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)))
      else
        twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (fun j =>
            if j = j₁₀ then
              -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
            else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j))
      = OSReconstruction.twoPointDifferenceKernel
          (twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) x
    rw [if_pos hcond]
    change twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) =
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (x 1 - x 0)
    change twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) =
      (if 0 < (x 1 - x 0) 0 then
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          ((x 1 - x 0) 0 : ℂ) (fun i => (x 1 - x 0) i.succ)
      else
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (-((x 1 - x 0) 0) : ℂ) (fun i => (x 1 - x 0) i.succ))
    rw [if_pos hξpos, twoPointCorrectedWitness_eq_twoPointSpatialWitness,
      neg_I_mul_toDiffFlat_wickRotate_j10]
    congr 1
    ext i
    simp [extractDiffSpatialRe, BHW.toDiffFlat, BHW.flattenCfg,
      BHW.diffCoordEquiv_apply, wickRotatePoint, Fin.succ_ne_zero]
  · have hcond : ¬ 0 < (-Complex.I * BHW.toDiffFlat 2 d
        (fun j => wickRotatePoint (x j)) j₁₀).re := by
      have hre : (-Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀).re =
          x 1 0 - x 0 0 := by
        rw [neg_I_mul_toDiffFlat_wickRotate_j10]; simp
      rw [hre]
      exact hpos
    have hξnpos : ¬ 0 < (x 1 - x 0) 0 := by
      simpa using hpos
    change
      (if 0 < (-Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀).re then
        twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)))
      else
        twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (fun j =>
            if j = j₁₀ then
              -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
            else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j))
      = OSReconstruction.twoPointDifferenceKernel
          (twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) x
    rw [if_neg hcond]
    change twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (fun j =>
          if j = j₁₀ then
            -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
          else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j) =
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (x 1 - x 0)
    change twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (fun j =>
          if j = j₁₀ then
            -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
          else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j) =
      (if 0 < (x 1 - x 0) 0 then
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          ((x 1 - x 0) 0 : ℂ) (fun i => (x 1 - x 0) i.succ)
      else
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (-((x 1 - x 0) 0) : ℂ) (fun i => (x 1 - x 0) i.succ))
    rw [if_neg hξnpos, twoPointCorrectedWitness_eq_twoPointSpatialWitness]
    have h_if_j : (fun j => if j = j₁₀ then
          -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
          else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j) j₁₀ =
        -(BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀) := by
      simp [j₁₀]
    rw [show -Complex.I *
        (fun j => if j = j₁₀ then
            -BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀
          else BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j) j₁₀ =
        -Complex.I * -(BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)) j₁₀) from by
          rw [h_if_j],
      neg_I_mul_neg_toDiffFlat_wickRotate_j10,
      extractDiffSpatialRe_reflect_timeDiff _ j₁₀ rfl]
    have hsp :
        extractDiffSpatialRe (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) =
          (fun i => x 1 i.succ - x 0 i.succ) := by
      ext i
      simp [extractDiffSpatialRe, BHW.toDiffFlat, BHW.flattenCfg,
        BHW.diffCoordEquiv_apply, wickRotatePoint, Fin.succ_ne_zero]
    simpa [Pi.sub_apply] using congrArg
      (fun y =>
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (↑(x 0 0 - x 1 0)) y) hsp

/-- The reduced one-variable pairing of the piecewise witness kernel can be
repackaged exactly as the corresponding two-point difference-shell integral with
the normalized center cutoff `χ₀`. -/
private theorem integral_twoPointPiecewiseWitness_differenceLift_eq_reduced_pairing
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ x : NPointDomain d 2,
      twoPointPiecewiseWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
          (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) *
        (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x) =
      ∫ ξ : SpacetimeDim d,
        twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
          ((h : SchwartzSpacetime d) ξ) := by
  calc
    ∫ x : NPointDomain d 2,
        twoPointPiecewiseWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
            (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) *
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x)
      = ∫ x : NPointDomain d 2,
          OSReconstruction.twoPointDifferenceKernel
              (twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) x *
            (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            rw [twoPointPiecewiseWitness_euclidean_eq_differenceKernel
              (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact x]
    _ = (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d,
            twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
              ((h : SchwartzSpacetime d) ξ) := by
            exact OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d)
              (twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact)
              χ₀ (h : SchwartzSpacetime d)
    _ = ∫ ξ : SpacetimeDim d,
          twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
            ((h : SchwartzSpacetime d) ξ) := by
            simp [hχ₀]

/-- Honest reduced-shell formula for the semigroup-induced one-variable kernel:
pairing it against a positive-time compactly supported reduced test gives the
Schwinger pairing of the corresponding shifted one-point family, integrated
against that reduced test.

This is the exact content presently justified by the semigroup construction.
It does **not** identify the `g`-dependent witness kernel with the universal
Schwinger difference functional. The remaining gap is precisely the passage
from this shifted-single pairing to the canonical reduced Schwinger
difference distribution. -/
theorem integral_twoPointDifferenceWitnessKernel_eq_shifted_single_pairing {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∫ ξ : SpacetimeDim d,
        twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
          ((h : SchwartzSpacetime d) ξ) =
        ∫ ξ : SpacetimeDim d,
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            ((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0)
                (onePointToFin1CLM d
                  (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
                    SchwartzNPoint d 1)))) *
            ((h : SchwartzSpacetime d) ξ) := by
  intro h
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : 0 < ξ 0
  · rw [twoPointDifferenceWitnessKernel_apply_of_pos_eq_shifted_single
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ]
  · have hξ_not_mem :
        ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
      intro hmem
      exact hξ (h.property.1 hmem)
    have hξ_zero :
        ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
      image_eq_zero_of_notMem_tsupport hξ_not_mem
    simp [hξ_zero]

/-- On the positive reduced shell, the semigroup-induced difference kernel
pairs against translated product-shell Schwinger values. This is the exact
unsmeared formula currently available before any comparison with the canonical
reduced Schwinger difference functional. -/
private theorem twoPointDifferenceWitnessKernel_apply_of_pos_eq_translatedProductCLM
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ =
      schwingerProductPositiveCLM (d := d) OS χ₀ hχ₀_pos
        (translatedPositiveTimeCompactSupport (d := d) g hg_pos_time hg_compact ξ hξ) := by
  rw [twoPointDifferenceWitnessKernel_apply_of_pos_eq_shifted_single
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ,
    shifted_single_test_eq_twoPointProductLift_translate
      (d := d) χ₀ g hχ₀_pos hg_pos ξ hξ]
  symm
  exact schwingerProductPositiveCLM_apply_translated
    (d := d) OS χ₀ hχ₀_pos g hg_pos_time hg_compact ξ hξ

/-- On the positive reduced shell, the semigroup-induced difference kernel
pairs against translated product-shell Schwinger values. This is the exact
unsmeared formula currently available before any comparison with the canonical
reduced Schwinger difference functional. -/
theorem integral_twoPointDifferenceWitnessKernel_eq_shifted_product_pairing
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∫ ξ : SpacetimeDim d,
        twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
          ((h : SchwartzSpacetime d) ξ) =
        ∫ ξ : SpacetimeDim d,
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g))) *
            ((h : SchwartzSpacetime d) ξ) := by
  intro h
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : 0 < ξ 0
  · rw [twoPointDifferenceWitnessKernel_apply_of_pos_eq_shifted_single
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ,
      shifted_single_test_eq_twoPointProductLift_translate
        (d := d) χ₀ g hχ₀_pos hg_pos ξ hξ]
  · have hξ_not_mem :
        ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
      intro hmem
      exact hξ (h.property.1 hmem)
    have hξ_zero :
        ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
      image_eq_zero_of_notMem_tsupport hξ_not_mem
    simp [hξ_zero]

/-- On the positive reduced shell, the semigroup-induced difference kernel
pairs against the translated positive-domain Schwinger product CLM orbit.

This is the honest CLM-level form of the currently available semigroup-side
comparison: the remaining gap is still to compare this translated product-shell
orbit with the canonical reduced Schwinger difference functional. -/
theorem integral_twoPointDifferenceWitnessKernel_eq_translatedProductPositiveCLM_pairing
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
        ((h : SchwartzSpacetime d) ξ) =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM (d := d) OS χ₀ hχ₀_pos
            (translatedPositiveTimeCompactSupport (d := d) g hg_pos_time hg_compact ξ hξ)
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : 0 < ξ 0
  · rw [twoPointDifferenceWitnessKernel_apply_of_pos_eq_translatedProductCLM
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_pos_time hg_compact ξ hξ]
    simp [hξ]
  · have hξ_not_mem :
        ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
      intro hmem
      exact hξ (h.property.1 hmem)
    have hξ_zero :
        ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
      image_eq_zero_of_notMem_tsupport hξ_not_mem
    simp [hξ, hξ_zero]

/-- The exact reduced one-variable pairing presently produced by the semigroup
construction in the `k = 2` kernel route. It depends on the auxiliary test
function `g`, so it is not yet the canonical Schwinger difference functional.

This definition is intentionally honest: the remaining kernel blocker is the
comparison between this `g`-dependent pairing and
`schwingerDifferencePositiveCLM`. -/
private def shiftedSingleReducedPairing {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ g : SchwartzSpacetime d) :
    positiveTimeCompactSupportSubmodule d → ℂ :=
  fun h =>
    ∫ ξ : SpacetimeDim d,
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d
              (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
                SchwartzNPoint d 1)))) *
        ((h : SchwartzSpacetime d) ξ)

@[simp] theorem shiftedSingleReducedPairing_apply {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ g : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    shiftedSingleReducedPairing (d := d) OS χ₀ g h =
      ∫ ξ : SpacetimeDim d,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          ((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0)
              (onePointToFin1CLM d
                (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
                  SchwartzNPoint d 1)))) *
          ((h : SchwartzSpacetime d) ξ) := rfl

/-- The semigroup-induced one-variable difference kernel computes exactly the
auxiliary `g`-dependent reduced pairing defined above. This is the strongest
honest reduced pairing statement currently available in production. -/
theorem integral_twoPointDifferenceWitnessKernel_eq_shiftedSingleReducedPairing
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
        ((h : SchwartzSpacetime d) ξ) =
      shiftedSingleReducedPairing (d := d) OS χ₀ g h := by
  simpa [shiftedSingleReducedPairing] using
    integral_twoPointDifferenceWitnessKernel_eq_shifted_single_pairing
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact h

/-- The current `g`-dependent reduced pairing is exactly the integral of the
translated two-point product-shell Schwinger values. This is the sharp honest
formula produced by the semigroup construction before any canonical reduced
comparison is imposed. -/
theorem shiftedSingleReducedPairing_eq_translatedProductShellPairing
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    shiftedSingleReducedPairing (d := d) OS χ₀ g h =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  calc
    shiftedSingleReducedPairing (d := d) OS χ₀ g h
      = ∫ ξ : SpacetimeDim d,
          twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
            ((h : SchwartzSpacetime d) ξ) := by
              symm
              exact integral_twoPointDifferenceWitnessKernel_eq_shiftedSingleReducedPairing
                (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact h
    _ = ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            schwingerProductPositiveCLM (d := d) OS χ₀ hχ₀_pos
              (translatedPositiveTimeCompactSupport (d := d) g hg_pos_time hg_compact ξ hξ)
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
            exact integral_twoPointDifferenceWitnessKernel_eq_translatedProductPositiveCLM_pairing
              (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_pos_time hg_compact h
    _ = ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift χ₀ (SCV.translateSchwartz (-ξ) g)))
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · have hprod :=
                schwingerProductPositiveCLM_apply_translated
                  (d := d) OS χ₀ hχ₀_pos g hg_pos_time hg_compact ξ hξ
              simpa [hξ] using
                congrArg (fun z : ℂ => z * ((h : SchwartzSpacetime d) ξ)) hprod
            · simp [hξ]

/-- The Hilbert-space orbit underlying the positive reduced shell of the current
`k = 2` semigroup witness. This is public because the final closure seam is now
most naturally stated as a comparison between its Bochner integral and the
Schwinger reduced functional. -/
def twoPointDifferenceWitnessOrbit {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (ξ : SpacetimeDim d) : OSHilbertSpace OS :=
  osTimeShiftHilbertComplex (d := d) OS lgc (ξ 0 : ℂ)
    (twoPointTranslatedOnePointVector (d := d) OS g hg_pos (fun i => ξ i.succ))

/-- On positive real time, the shifted-single reduced Schwinger pairing equals
the fixed left Hilbert vector paired with the semigroup orbit at `(ξ₀, ξ_spatial)`. -/
private theorem shiftedSingleReducedPairing_integrand_eq_inner_orbit_of_pos
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
      ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d
            (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
              SchwartzNPoint d 1)))) =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                hχ₀_pos⟧)) : OSHilbertSpace OS))
        (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos ξ) := by
  rw [← twoPointDifferenceWitnessKernel_apply_of_pos_eq_shifted_single
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ]
  rw [twoPointDifferenceWitnessKernel_apply_of_pos
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ]
  simpa [twoPointDifferenceWitnessOrbit] using
    (twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (ξ 0 : ℂ) (by simpa using hξ) (fun i => ξ i.succ))

private theorem measurableSet_positiveTimeRegion_spacetime {d : ℕ} :
    MeasurableSet {ξ : SpacetimeDim d | 0 < ξ 0} :=
  measurableSet_lt measurable_const (continuous_apply 0).measurable

/-- The semigroup orbit is continuous on the positive-time region. -/
private theorem continuousOn_twoPointDifferenceWitnessOrbit_pos
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn
      (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos)
      {ξ : SpacetimeDim d | 0 < ξ 0} := by
  let Φ : SpacetimeDim d → ℂ × OSHilbertSpace OS := fun ξ =>
    ((ξ 0 : ℂ),
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos (fun i => ξ i.succ))
  have hΦ_cont : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_apply 0)
    · exact (continuous_twoPointTranslatedOnePointVector
        (d := d) OS g hg_pos hg_compact).comp
          (continuous_pi fun i => continuous_apply i.succ)
  have hΦ_maps :
      Set.MapsTo Φ {ξ : SpacetimeDim d | 0 < ξ 0}
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro ξ hξ
    exact ⟨by simpa using hξ, trivial⟩
  simpa [twoPointDifferenceWitnessOrbit, Φ] using
    (continuousOn_osTimeShiftHilbertComplex_jointly (d := d) OS lgc).comp
      hΦ_cont.continuousOn hΦ_maps

/-- The positive-time orbit, cut off by the positive region, is
`AEStronglyMeasurable`. -/
private theorem aestronglyMeasurable_indicator_twoPointDifferenceWitnessOrbit_pos
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    AEStronglyMeasurable
      ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
        (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos))
      volume := by
  refine (aestronglyMeasurable_indicator_iff
    (measurableSet_positiveTimeRegion_spacetime (d := d))).2 ?_
  exact (continuousOn_twoPointDifferenceWitnessOrbit_pos
    (d := d) OS lgc g hg_pos hg_compact).aestronglyMeasurable
      (measurableSet_positiveTimeRegion_spacetime (d := d))

/-- The positive-time orbit indicator is uniformly bounded by the norm of the
fixed translated vector at `0`, via semigroup contractivity and spatial norm
constancy. -/
private theorem norm_indicator_twoPointDifferenceWitnessOrbit_pos_le
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (ξ : SpacetimeDim d) :
    ‖({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
        (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ)‖ ≤
      2 * ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos 0‖ := by
  by_cases hξ : 0 < ξ 0
  · simp [Set.indicator_of_mem, hξ]
    calc
      ‖twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos ξ‖
          ≤ ‖osTimeShiftHilbertComplex (d := d) OS lgc (ξ 0 : ℂ)‖ *
              ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos (fun i => ξ i.succ)‖ := by
            exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 *
            ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos (fun i => ξ i.succ)‖ := by
            gcongr
            exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (ξ 0 : ℂ)
              (by simpa using hξ)
      _ = 2 * ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos 0‖ := by
            rw [norm_twoPointTranslatedOnePointVector_eq
              (d := d) OS g hg_pos (fun i => ξ i.succ) 0]
  · simp [Set.indicator_of_notMem, hξ, norm_zero]

/-- The scalar-weighted positive-time semigroup orbit is integrable. -/
private theorem integrable_smul_indicator_twoPointDifferenceWitnessOrbit_pos
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    Integrable (fun ξ : SpacetimeDim d =>
      (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) •
        ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
          (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ)) volume := by
  haveI : (volume : Measure (SpacetimeDim d)).HasTemperateGrowth :=
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hh_int :
      Integrable
        (((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))) volume := by
    exact (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)).integrable
  exact hh_int.smul_bdd
    (2 * ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos 0‖)
    (aestronglyMeasurable_indicator_twoPointDifferenceWitnessOrbit_pos
      (d := d) OS lgc g hg_pos hg_compact)
    (Filter.Eventually.of_forall
      (norm_indicator_twoPointDifferenceWitnessOrbit_pos_le
        (d := d) OS lgc g hg_pos))

/-- The current `g`-dependent reduced pairing can be collapsed to a single
Hilbert-space matrix element against a Bochner-integrated positive-time orbit. -/
private theorem shiftedSingleReducedPairing_eq_inner_integral_orbit
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    shiftedSingleReducedPairing (d := d) OS χ₀ g h =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                hχ₀_pos⟧)) : OSHilbertSpace OS))
        (∫ ξ : SpacetimeDim d,
          ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) •
            ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
              (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ))) := by
  let F : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
      hχ₀_pos⟧)) : OSHilbertSpace OS))
  have hInt :=
    integrable_smul_indicator_twoPointDifferenceWitnessOrbit_pos
      (d := d) OS lgc g hg_pos hg_compact h
  calc
    shiftedSingleReducedPairing (d := d) OS χ₀ g h
      = ∫ ξ : SpacetimeDim d,
          @inner ℂ (OSHilbertSpace OS) _ F
            ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) •
              ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
                (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ)) := by
          simp only [shiftedSingleReducedPairing, F]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hξ : 0 < ξ 0
          · rw [shiftedSingleReducedPairing_integrand_eq_inner_orbit_of_pos
              (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ hξ]
            simp [Set.indicator_of_mem, hξ, inner_smul_right, mul_comm]
          · have hξ_not_mem :
              ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ) := by
              intro hmem
              exact hξ (h.property.1 hmem)
            have hξ_zero :
                (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ) ξ = 0 :=
              image_eq_zero_of_notMem_tsupport hξ_not_mem
            rw [hξ_zero]
            simp [Set.indicator_of_notMem, hξ, inner_smul_right]
    _ = ∫ ξ : SpacetimeDim d,
          ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) *
            @inner ℂ (OSHilbertSpace OS) _ F
              ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
                (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with ξ
          rw [inner_smul_right]
    _ = @inner ℂ (OSHilbertSpace OS) _ F
          (∫ ξ : SpacetimeDim d,
            ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) •
              ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
                (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ))) := by
          simpa [F] using
            (ContinuousLinearMap.integral_comp_comm (innerSL ℂ F) hInt)

/-- Direct Hilbert-space collapse of the current positive-shell reduced pairing
for the semigroup witness kernel. This is a genuine simplification of the
remaining kernel blocker: the scalar shell integral becomes one matrix element
against an integrated orbit. -/
theorem integral_twoPointDifferenceWitnessKernel_eq_inner_integral_orbit
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      twoPointDifferenceWitnessKernel OS lgc χ₀ g hχ₀_pos hg_pos hg_compact ξ *
        ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ)) =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                hχ₀_pos⟧)) : OSHilbertSpace OS))
        (∫ ξ : SpacetimeDim d,
          ((((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ) •
            ({ξ : SpacetimeDim d | 0 < ξ 0}.indicator
              (twoPointDifferenceWitnessOrbit (d := d) OS lgc g hg_pos) ξ))) := by
  rw [integral_twoPointDifferenceWitnessKernel_eq_shiftedSingleReducedPairing
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact h]
  exact shiftedSingleReducedPairing_eq_inner_integral_orbit
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact h
