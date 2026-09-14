/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWDbar
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth Cutoffs for the Local Distributional EOW Route

This file proves the compact cutoff theorem used by the local holomorphic
`∂bar` bridge.  The result is pure SCV infrastructure: a compactly supported
smooth real cutoff that is equal to one on an open neighborhood of the
topological support of a local Schwartz test.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Manifold

namespace SCV

variable {m : ℕ}

/-- If a Schwartz test is compactly supported inside an open complex chart
set, then there is a smooth real cutoff supported in that open set and equal to
one on a neighborhood of the test's topological support.

The construction uses two metric thickenings of `tsupport φ`, then applies
Mathlib's smooth support theorem to the pair
`closure (thickening r₁ K) ⊆ thickening r₂ K`. -/
theorem exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
    (U : Set (ComplexChartSpace m))
    (hU_open : IsOpen U)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    ∃ χ : ComplexChartSpace m → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 ∧
      ∃ V : Set (ComplexChartSpace m),
        IsOpen V ∧
        tsupport (φ : ComplexChartSpace m → ℂ) ⊆ V ∧
        V ⊆ U ∧
        Set.EqOn χ (fun _ => 1) V := by
  let K : Set (ComplexChartSpace m) := tsupport (φ : ComplexChartSpace m → ℂ)
  have hK_compact : IsCompact K := hφ.1
  have hK_U : K ⊆ U := hφ.2
  obtain ⟨r, hrpos, hrsub⟩ :=
    hK_compact.exists_cthickening_subset_open hU_open hK_U
  let r₂ : ℝ := r / 2
  have hr₂pos : 0 < r₂ := half_pos hrpos
  have hr₂le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let r₁ : ℝ := r₂ / 2
  have hr₁pos : 0 < r₁ := half_pos hr₂pos
  have hr₁lt₂ : r₁ < r₂ := half_lt_self hr₂pos
  have hr₁le₂ : r₁ ≤ r₂ := le_of_lt hr₁lt₂
  let V₁ : Set (ComplexChartSpace m) := Metric.thickening r₁ K
  let V₂ : Set (ComplexChartSpace m) := Metric.thickening r₂ K
  have hV₁_open : IsOpen V₁ := isOpen_thickening
  have hV₂_open : IsOpen V₂ := isOpen_thickening
  have hK_sub_V₁ : K ⊆ V₁ := self_subset_thickening hr₁pos K
  have hclV₁_sub_V₂ : closure V₁ ⊆ V₂ := by
    exact (closure_thickening_subset_cthickening r₁ K).trans
      (cthickening_subset_thickening' hr₂pos hr₁lt₂ K)
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, ComplexChartSpace m)) (n := (⊤ : ℕ∞))
      hV₂_open isClosed_closure hclV₁_sub_V₂
  have hχ_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ := hχsmooth.contDiff
  have hχ_tsupport_cthickening :
      tsupport χ ⊆ Metric.cthickening r₂ K := by
    rw [tsupport, hχsupport]
    exact closure_thickening_subset_cthickening r₂ K
  have hχ_compact : HasCompactSupport χ := by
    exact IsCompact.of_isClosed_subset (hK_compact.cthickening)
      (isClosed_tsupport χ) hχ_tsupport_cthickening
  have hχ_tsupport_U : tsupport χ ⊆ U := by
    exact hχ_tsupport_cthickening.trans
      ((cthickening_mono hr₂le K).trans hrsub)
  have hV₁_sub_U : V₁ ⊆ U := by
    exact (thickening_subset_cthickening_of_le hr₁le₂ K).trans
      ((cthickening_mono hr₂le K).trans hrsub)
  have hχ_eq_one_V₁ : Set.EqOn χ (fun _ => 1) V₁ := by
    intro x hx
    exact (hχone x).1 (subset_closure hx)
  exact ⟨χ, hχ_contDiff, hχ_compact, hχ_tsupport_U, hχrange,
    V₁, hV₁_open, hK_sub_V₁, hV₁_sub_U, hχ_eq_one_V₁⟩

/-- A compact subset of an open finite-dimensional real chart admits a
Schwartz cutoff that is identically one on the compact set and supported in
the open set. -/
theorem exists_schwartz_cutoff_eq_one_on_compact_subset_open
    {K U : Set (Fin m → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ U := by
  obtain ⟨r, hrpos, hrsub⟩ :=
    hK.exists_cthickening_subset_open hU hKU
  let r₂ : ℝ := r / 2
  have hr₂pos : 0 < r₂ := half_pos hrpos
  have hr₂le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let r₁ : ℝ := r₂ / 2
  have hr₁pos : 0 < r₁ := half_pos hr₂pos
  have hr₁lt₂ : r₁ < r₂ := half_lt_self hr₂pos
  have hr₁le₂ : r₁ ≤ r₂ := le_of_lt hr₁lt₂
  let V₁ : Set (Fin m → ℝ) := Metric.thickening r₁ K
  let V₂ : Set (Fin m → ℝ) := Metric.thickening r₂ K
  have hV₂_open : IsOpen V₂ := isOpen_thickening
  have hK_sub_V₁ : K ⊆ V₁ := self_subset_thickening hr₁pos K
  have hclV₁_sub_V₂ : closure V₁ ⊆ V₂ := by
    exact (closure_thickening_subset_cthickening r₁ K).trans
      (cthickening_subset_thickening' hr₂pos hr₁lt₂ K)
  obtain ⟨χ, hχsmooth, _hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, Fin m → ℝ)) (n := (⊤ : ℕ∞))
      hV₂_open isClosed_closure hclV₁_sub_V₂
  have hχ_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ := hχsmooth.contDiff
  have hχ_tsupport_cthickening :
      tsupport χ ⊆ Metric.cthickening r₂ K := by
    rw [tsupport, hχsupport]
    exact closure_thickening_subset_cthickening r₂ K
  have hχ_compact : HasCompactSupport χ := by
    exact IsCompact.of_isClosed_subset (hK.cthickening)
      (isClosed_tsupport χ) hχ_tsupport_cthickening
  have hχ_tsupport_U : tsupport χ ⊆ U := by
    exact hχ_tsupport_cthickening.trans
      ((cthickening_mono hr₂le K).trans hrsub)
  let f : (Fin m → ℝ) → ℂ := fun x => (χ x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp hχ_contDiff
  have hf_compact : HasCompactSupport f :=
    hχ_compact.comp_left Complex.ofReal_zero
  let χS : SchwartzMap (Fin m → ℝ) ℂ :=
    hf_compact.toSchwartzMap hf_smooth
  have hχS_apply : ∀ x, χS x = f x :=
    HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth
  refine ⟨χS, ?_, ?_⟩
  · intro x hx
    rw [hχS_apply]
    have hxV₁ : x ∈ V₁ := hK_sub_V₁ hx
    have hχx : χ x = 1 := (hχone x).1 (subset_closure hxV₁)
    simp [f, hχx]
  · intro x hx
    have hxf : x ∈ tsupport f := by
      simpa [χS, hχS_apply] using hx
    have hxχ : x ∈ tsupport χ := by
      simpa [tsupport, f, Function.support] using hxf
    exact hχ_tsupport_U hxχ

end SCV
