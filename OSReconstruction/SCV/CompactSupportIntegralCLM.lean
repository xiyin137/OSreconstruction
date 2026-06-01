import OSReconstruction.SCV.DistributionalEOWSupport

open Set Filter MeasureTheory
open scoped Topology

namespace SCV

/-- A locally continuous factor becomes globally continuous after multiplication
by a continuous cutoff whose topological support is contained in the open
continuity domain. -/
theorem continuous_mul_of_continuousOn_of_tsupport_subset_open
    {E : Type*} [TopologicalSpace E]
    {U : Set E} {χ H : E → ℂ}
    (hU : IsOpen U)
    (hχ : Continuous χ)
    (hχ_support : tsupport χ ⊆ U)
    (hH : ContinuousOn H U) :
    Continuous (fun x => χ x * H x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · exact hχ.continuousAt.mul (hH.continuousAt (hU.mem_nhds hxU))
  · have hx_not_ts : x ∉ tsupport χ := fun hx => hxU (hχ_support hx)
    let N : Set E := (tsupport χ)ᶜ
    have hN_open : IsOpen N := by
      dsimp [N]
      exact (isClosed_tsupport χ).isOpen_compl
    have hxN : x ∈ N := hx_not_ts
    have h_event : (fun y => χ y * H y) =ᶠ[𝓝 x] (fun _ : E => 0) := by
      filter_upwards [hN_open.mem_nhds hxN] with y hy
      have hy_not_support : y ∉ Function.support χ := by
        intro hy_support
        exact hy (subset_tsupport χ hy_support)
      have hχy : χ y = 0 := by
        by_contra hne
        exact hy_not_support hne
      simp [hχy]
    exact continuousAt_const.congr_of_eventuallyEq h_event

/-- Integration against a continuous compactly supported multiplier is a
continuous linear functional on finite-dimensional Schwartz space. -/
theorem compactSupport_integralMultiplierCLM_fin
    {m : Nat}
    (g : (Fin m → ℝ) → ℂ)
    (hg_cont : Continuous g)
    (hg_compact : HasCompactSupport g) :
    ∃ L : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        L φ = ∫ x, g x * φ x := by
  have hK : IsCompact (tsupport g) := by
    simpa [HasCompactSupport] using hg_compact
  obtain ⟨R0, hR0⟩ :=
    hK.exists_bound_of_continuousOn (continuous_norm.continuousOn)
  let R : ℝ := max R0 0
  have htsupport_ball : tsupport g ⊆ Metric.closedBall (0 : Fin m → ℝ) R := by
    intro x hx
    have hbound0 : ‖‖x‖‖ ≤ R0 := hR0 x hx
    have hbound : ‖x‖ ≤ R0 := by
      simpa using hbound0
    have hR : ‖x‖ ≤ R := le_trans hbound (le_max_left _ _)
    simpa [Metric.mem_closedBall, dist_eq_norm, R] using hR
  obtain ⟨L, hL⟩ :=
    SCV.exists_closedBall_integral_clm_of_continuousOn
      (m := m) (R := R) (g := g) hg_cont.continuousOn
  refine ⟨L, ?_⟩
  intro φ
  let s : Set (Fin m → ℝ) := Metric.closedBall (0 : Fin m → ℝ) R
  have hzero : ∀ x : Fin m → ℝ, x ∉ s → g x * φ x = 0 := by
    intro x hx
    have hx_not_ts : x ∉ tsupport g := by
      intro hxg
      exact hx (htsupport_ball hxg)
    have hx_not_support : x ∉ Function.support g := by
      intro hsupp
      exact hx_not_ts (subset_tsupport g hsupp)
    have hgx : g x = 0 := by
      simpa [Function.mem_support] using hx_not_support
    simp [hgx]
  calc
    L φ = ∫ x in s, g x * φ x := hL φ
    _ = ∫ x, g x * φ x :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero

/-- A locally continuous branch becomes a global Schwartz distribution after
multiplication by a compact cutoff supported in its continuity carrier.  On
tests where the cutoff is one, this distribution is exactly the original branch
pairing. -/
theorem compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
    {m : Nat} {U : Set (Fin m → ℝ)}
    (H : (Fin m → ℝ) → ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hU : IsOpen U)
    (hχ_compact : HasCompactSupport (χ : (Fin m → ℝ) → ℂ))
    (hχ_support : tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ U)
    (hH : ContinuousOn H U) :
    ∃ L : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      (∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        L φ = ∫ x, (χ x * H x) * φ x) ∧
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        (∀ x ∈ tsupport (φ : (Fin m → ℝ) → ℂ), χ x = 1) →
          L φ = ∫ x, H x * φ x := by
  classical
  let g : (Fin m → ℝ) → ℂ := fun x => χ x * H x
  have hg_cont : Continuous g := by
    exact
      continuous_mul_of_continuousOn_of_tsupport_subset_open
        (U := U) hU χ.continuous hχ_support hH
  have hg_compact : HasCompactSupport g := by
    simpa [g, mul_comm] using
      (HasCompactSupport.mul_left (f := H) hχ_compact)
  rcases compactSupport_integralMultiplierCLM_fin g hg_cont hg_compact with
    ⟨L, hL⟩
  refine ⟨L, ?_, ?_⟩
  · intro φ
    exact hL φ
  · intro φ hχ_one
    calc
      L φ = ∫ x, (χ x * H x) * φ x := hL φ
      _ = ∫ x, H x * φ x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport (φ : (Fin m → ℝ) → ℂ)
        · simp [hχ_one x hx]
        · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
          simp [hφx]

end SCV
