import OSReconstruction.SCV.LocalContinuousEOWEnvelope
import OSReconstruction.SCV.LocalEOWChartLinear

/-!
# Fixed-Basis Local EOW Chart Windows

The final local distributional EOW patching argument must use one cone basis
for all edge points.  This file extracts the small finite-dimensional facts
needed before the final patching layer.
-/

noncomputable section

open BigOperators Topology MeasureTheory

namespace SCV

/-- A nonempty cone that does not contain zero forces the ambient finite
dimension to be positive. -/
theorem positive_dimension_of_nonempty_not_zero
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_ne : C.Nonempty)
    (hC_not_zero : (0 : Fin m → ℝ) ∉ C) :
    0 < m := by
  cases m with
  | zero =>
      rcases hC_ne with ⟨y, hy⟩
      exact (hC_not_zero (by
        have hy0 : y = 0 := by
          ext i
          exact Fin.elim0 i
        simpa [hy0] using hy)).elim
  | succ m =>
      exact Nat.succ_pos m

/-- Positive linear combinations of fixed cone directions remain in a convex
cone, after normalizing to a convex combination and scaling back. -/
theorem cone_positive_combination_mem
    {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hC_conv : Convex ℝ C)
    (hC_cone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (a : Fin m → ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (ha_sum_pos : 0 < ∑ j, a j) :
    (∑ j, a j • ys j) ∈ C := by
  let s : ℝ := ∑ j, a j
  have hs_pos : 0 < s := by simpa [s] using ha_sum_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hweights_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 ≤ s⁻¹ * a j := by
    intro j _hj
    exact mul_nonneg (inv_nonneg.mpr hs_pos.le) (ha_nonneg j)
  have hweights_sum : (∑ j, s⁻¹ * a j) = 1 := by
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hs_ne
  have hconv_mem : (∑ j, (s⁻¹ * a j) • ys j) ∈ C :=
    hC_conv.sum_mem
      (t := Finset.univ)
      (w := fun j => s⁻¹ * a j)
      (z := ys)
      hweights_nonneg
      hweights_sum
      (by
        intro j _hj
        exact hys j)
  have hscaled : s • (∑ j, (s⁻¹ * a j) • ys j) ∈ C :=
    hC_cone s hs_pos _ hconv_mem
  convert hscaled using 1
  ext i
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  calc
    a j * ys j i = 1 * (a j * ys j i) := by rw [one_mul]
    _ = (s * s⁻¹) * (a j * ys j i) := by rw [mul_inv_cancel₀ hs_ne]
    _ = s * (s⁻¹ * a j * ys j i) := by ring

/-- Fixed-basis version of `exists_localContinuousEOW_chart_window`.

The cone basis `ys` is supplied by the caller, so the same basis can be reused
at every real edge point before patching local envelopes. -/
theorem exists_localContinuousEOW_fixedBasis_chart_window {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hE_open : IsOpen E)
    (hC_conv : Convex ℝ C)
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (x0 : Fin m → ℝ) (hx0 : x0 ∈ E)
    (ys : Fin m → Fin m → ℝ)
    (hys_mem : ∀ j, ys j ∈ C) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∃ r : ℝ, 0 < r ∧
    ∃ δ : ℝ, 0 < δ ∧
      δ * 10 ≤ ρ ∧
      (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E) ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus) ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) ∧
      (∀ {w : Fin m → ℂ} {l : ℂ},
        w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
        (∀ j, (w j).im = 0) →
        0 < l.im →
        ‖l‖ ≤ 2 →
          localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) ∧
      (∀ {w : Fin m → ℂ} {l : ℂ},
        w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
        (∀ j, (w j).im = 0) →
        l.im < 0 →
        ‖l‖ ≤ 2 →
          localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus) := by
  obtain ⟨ρ, hρ, hρE⟩ := localEOWRealChart_closedBall_subset hE_open x0 hx0 ys
  have hB_compact : IsCompact (Metric.closedBall (0 : Fin m → ℝ) ρ) :=
    isCompact_closedBall (x := (0 : Fin m → ℝ)) (r := ρ)
  have hB_E : localEOWRealChart x0 ys '' Metric.closedBall (0 : Fin m → ℝ) ρ ⊆ E := by
    rintro y ⟨u, hu, rfl⟩
    exact hρE u hu
  obtain ⟨r, hr, hplus, hminus⟩ :=
    localEOWChart_twoSided_polywedge_mem Ωplus Ωminus E C hlocal_wedge hC_conv
      x0 ys hys_mem (Metric.closedBall (0 : Fin m → ℝ) ρ) hB_compact hB_E
  obtain ⟨δ, hδ, hδρ, hδsum⟩ := exists_localEOWSmp_delta hm hρ hr
  have hupper : ∀ {w : Fin m → ℂ} {l : ℂ},
      w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
      (∀ j, (w j).im = 0) →
      0 < l.im →
      ‖l‖ ≤ 2 →
        localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus :=
    fun {_w} {_l} hw hw_real hl_pos hl_norm =>
      localEOWChart_smp_upper_mem_of_delta hm Ωplus x0 ys hδ hδρ hδsum
        hplus hw hw_real hl_pos hl_norm
  have hlower : ∀ {w : Fin m → ℂ} {l : ℂ},
      w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) →
      (∀ j, (w j).im = 0) →
      l.im < 0 →
      ‖l‖ ≤ 2 →
        localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus :=
    fun {_w} {_l} hw hw_real hl_neg hl_norm =>
      localEOWChart_smp_lower_mem_of_delta hm Ωminus x0 ys hδ hδρ hδsum
        hminus hw hw_real hl_neg hl_norm
  exact ⟨ρ, hρ, r, hr, δ, hδ, hδρ, hδsum,
    hρE, hplus, hminus, hupper, hlower⟩

/-- The local EOW chart as an affine homeomorphism of complex coordinate
space, when the fixed real cone directions form a basis. -/
noncomputable def localEOWComplexAffineEquiv {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) :
    (Fin m → ℂ) ≃ₜ (Fin m → ℂ) := by
  classical
  let Φinv := Classical.choose (localEOWChart_equiv x0 ys hli)
  have hΦ := Classical.choose_spec (localEOWChart_equiv x0 ys hli)
  exact
    { toEquiv :=
        { toFun := localEOWChart x0 ys
          invFun := Φinv
          left_inv := hΦ.2.1
          right_inv := hΦ.2.2 }
      continuous_toFun := continuous_localEOWChart x0 ys
      continuous_invFun := hΦ.1.continuous }

@[simp]
theorem localEOWComplexAffineEquiv_apply {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) (w : Fin m → ℂ) :
    localEOWComplexAffineEquiv x0 ys hli w = localEOWChart x0 ys w := by
  simp [localEOWComplexAffineEquiv]

theorem localEOWComplexAffineEquiv_realEmbed {m : ℕ}
    (x0 u : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) :
    localEOWComplexAffineEquiv x0 ys hli (realEmbed u) =
      realEmbed (localEOWRealChart x0 ys u) := by
  rw [localEOWComplexAffineEquiv_apply]
  simpa [realEmbed] using localEOWChart_real x0 ys u

theorem localEOWComplexAffineEquiv_image_open {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    {U : Set (Fin m → ℂ)}
    (hU : IsOpen U) :
    IsOpen (localEOWComplexAffineEquiv x0 ys hli '' U) :=
  (localEOWComplexAffineEquiv x0 ys hli).isOpenMap U hU

theorem differentiableOn_comp_localEOWComplexAffineEquiv_symm {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    {U : Set (Fin m → ℂ)} {H : (Fin m → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H U) :
    DifferentiableOn ℂ
      (fun z => H ((localEOWComplexAffineEquiv x0 ys hli).symm z))
      (localEOWComplexAffineEquiv x0 ys hli '' U) := by
  classical
  let Φinv := Classical.choose (localEOWChart_equiv x0 ys hli)
  have hΦ := Classical.choose_spec (localEOWChart_equiv x0 ys hli)
  have hsymm_diff :
      Differentiable ℂ (localEOWComplexAffineEquiv x0 ys hli).symm := by
    simpa [localEOWComplexAffineEquiv, Φinv] using hΦ.1
  refine hH.comp hsymm_diff.differentiableOn ?_
  rintro z ⟨w, hw, rfl⟩
  have hleft :
      (localEOWComplexAffineEquiv x0 ys hli).symm (localEOWChart x0 ys w) = w := by
    simpa [localEOWComplexAffineEquiv, Φinv] using hΦ.2.1 w
  simpa [hleft] using hw

/-- Adding an original real displacement corresponds, in local EOW chart
coordinates, to adding the inverse real-linear displacement. -/
theorem localEOWComplexAffineEquiv_symm_add_realEmbed {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (z : Fin m → ℂ) (t : Fin m → ℝ) :
    (localEOWComplexAffineEquiv x0 ys hli).symm (z + realEmbed t) =
      (localEOWComplexAffineEquiv x0 ys hli).symm z +
        realEmbed ((localEOWRealLinearCLE ys hli).symm t) := by
  let A := localEOWComplexAffineEquiv x0 ys hli
  apply A.injective
  calc
    A (A.symm (z + realEmbed t)) = z + realEmbed t := by
      exact A.apply_symm_apply (z + realEmbed t)
    _ = A (A.symm z) + realEmbed t := by
      rw [A.apply_symm_apply z]
    _ = A (A.symm z) +
        realEmbed (localEOWRealLinearPart ys
          ((localEOWRealLinearCLE ys hli).symm t)) := by
      have hlin :
          localEOWRealLinearPart ys
              ((localEOWRealLinearCLE ys hli).symm t) = t := by
        rw [← localEOWRealLinearCLE_apply ys hli]
        exact (localEOWRealLinearCLE ys hli).apply_symm_apply t
      rw [hlin]
    _ = A (A.symm z + realEmbed ((localEOWRealLinearCLE ys hli).symm t)) := by
      change
        localEOWChart x0 ys (A.symm z) +
            realEmbed (localEOWRealLinearPart ys
              ((localEOWRealLinearCLE ys hli).symm t)) =
          localEOWChart x0 ys
            (A.symm z + realEmbed ((localEOWRealLinearCLE ys hli).symm t))
      rw [localEOWChart_add_realEmbed]

end SCV
