import OSReconstruction.SCV.LocalContinuousEOWEnvelope

/-!
# Local Continuous Edge-of-the-Wedge Side Agreement

This file contains the one-dimensional line argument which proves that the
local Rudin envelope agrees with the input holomorphic branches on the two
small side wedges.  It is split from `LocalContinuousEOWEnvelope.lean` to keep
the active frontier small.
-/

noncomputable section

open BigOperators Topology MeasureTheory

namespace SCV

/-- The Rudin side-agreement line is affine over real convex combinations. -/
theorem localEOWLine_affine_real_combo {m : ℕ}
    (ζ : Fin m → ℂ) (z1 z2 : ℂ) (a b : ℝ) (hab : a + b = 1) :
    localEOWLine ζ (a • z1 + b • z2) =
      a • localEOWLine ζ z1 + b • localEOWLine ζ z2 := by
  ext j
  simp only [localEOWLine, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  have hab' : ((a : ℂ) + (b : ℂ)) = 1 := by exact_mod_cast hab
  linear_combination -(((ζ j).re : ℂ)) * hab'

/-- On a real parameter, the local side-agreement line lands on the real edge
of the local chart. -/
theorem localEOWLine_chart_real {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (ζ : Fin m → ℂ) (t : ℝ) :
    localEOWChart x0 ys (localEOWLine ζ (t : ℂ)) =
      realEmbed (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (t : ℂ) j).re)) := by
  have hline :
      localEOWLine ζ (t : ℂ) =
        fun j => ((localEOWLine ζ (t : ℂ) j).re : ℂ) := by
    ext j
    apply Complex.ext
    · simp
    · simp [localEOWLine_real_im_zero]
  calc
    localEOWChart x0 ys (localEOWLine ζ (t : ℂ))
        = localEOWChart x0 ys
            (fun j => ((localEOWLine ζ (t : ℂ) j).re : ℂ)) := by
          exact congrArg (localEOWChart x0 ys) hline
    _ = realEmbed (localEOWRealChart x0 ys
          (fun j => (localEOWLine ζ (t : ℂ) j).re)) := by
          simpa using localEOWChart_real x0 ys
            (fun j => (localEOWLine ζ (t : ℂ) j).re)

/-- Boundary convergence of the plus branch along the side-agreement line. -/
theorem tendsto_localEOWLine_upper_to_boundaryValue {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fplus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFplus_bv :
      ∀ y ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_pos : ∀ j, 0 < (ζ j).im)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem :
      localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun z : ℂ => Fplus (localEOWChart x0 ys (localEOWLine ζ z)))
      (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re)))) := by
  let y : Fin m → ℝ :=
    localEOWRealChart x0 ys (fun j => (localEOWLine ζ (x : ℂ) j).re)
  have hx_ball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hchart_cont :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (nhds (realEmbed y)) := by
    have hcont :
        Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
          (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
          (nhds (localEOWChart x0 ys (localEOWLine ζ (x : ℂ)))) :=
      ((continuous_localEOWChart x0 ys).continuousAt.comp
          ((differentiable_localEOWLine ζ).continuous.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hreal :
        localEOWChart x0 ys (localEOWLine ζ (x : ℂ)) = realEmbed y := by
      simpa [y] using localEOWLine_chart_real x0 ys ζ x
    simpa [hreal] using hcont
  have hchart_mem :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (Filter.principal Ωplus) := by
    refine Filter.tendsto_principal.mpr ?_
    have hnorm :
        ∀ᶠ z in nhdsWithin (x : ℂ) EOW.UpperHalfPlane,
          z ∈ Metric.ball (0 : ℂ) 2 :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)
    filter_upwards [hnorm, self_mem_nhdsWithin] with z hz_norm hz_upper
    have hz_norm' : ‖z‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz_norm
    exact localEOWChart_line_upper_mem_of_delta hm Ωplus x0 ys
      hδ hδρ hδsum hplus hζ hζ_pos (le_of_lt hz_norm') hz_upper
  exact (hFplus_bv y (by simpa [y] using hE_mem)).comp
    (Filter.tendsto_inf.mpr ⟨hchart_cont, hchart_mem⟩)

/-- Boundary convergence of the minus branch along the side-agreement line. -/
theorem tendsto_localEOWLine_lower_to_boundaryValue {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fminus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFminus_bv :
      ∀ y ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_pos : ∀ j, 0 < (ζ j).im)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem :
      localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun z : ℂ => Fminus (localEOWChart x0 ys (localEOWLine ζ z)))
      (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re)))) := by
  let y : Fin m → ℝ :=
    localEOWRealChart x0 ys (fun j => (localEOWLine ζ (x : ℂ) j).re)
  have hx_ball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hchart_cont :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (nhds (realEmbed y)) := by
    have hcont :
        Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
          (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
          (nhds (localEOWChart x0 ys (localEOWLine ζ (x : ℂ)))) :=
      ((continuous_localEOWChart x0 ys).continuousAt.comp
          ((differentiable_localEOWLine ζ).continuous.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hreal :
        localEOWChart x0 ys (localEOWLine ζ (x : ℂ)) = realEmbed y := by
      simpa [y] using localEOWLine_chart_real x0 ys ζ x
    simpa [hreal] using hcont
  have hchart_mem :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (Filter.principal Ωminus) := by
    refine Filter.tendsto_principal.mpr ?_
    have hnorm :
        ∀ᶠ z in nhdsWithin (x : ℂ) EOW.LowerHalfPlane,
          z ∈ Metric.ball (0 : ℂ) 2 :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)
    filter_upwards [hnorm, self_mem_nhdsWithin] with z hz_norm hz_lower
    have hz_norm' : ‖z‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz_norm
    exact localEOWChart_line_lower_mem_of_delta hm Ωminus x0 ys
      hδ hδρ hδsum hminus hζ hζ_pos (le_of_lt hz_norm') hz_lower
  exact (hFminus_bv y (by simpa [y] using hE_mem)).comp
    (Filter.tendsto_inf.mpr ⟨hchart_cont, hchart_mem⟩)

/-- Boundary convergence of the minus branch along a side-agreement line whose
target point has negative imaginary coordinates. -/
theorem tendsto_localEOWLine_upper_to_boundaryValue_of_negative {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fminus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFminus_bv :
      ∀ y ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_neg : ∀ j, (ζ j).im < 0)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem :
      localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun z : ℂ => Fminus (localEOWChart x0 ys (localEOWLine ζ z)))
      (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re)))) := by
  let y : Fin m → ℝ :=
    localEOWRealChart x0 ys (fun j => (localEOWLine ζ (x : ℂ) j).re)
  have hx_ball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hchart_cont :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (nhds (realEmbed y)) := by
    have hcont :
        Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
          (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
          (nhds (localEOWChart x0 ys (localEOWLine ζ (x : ℂ)))) :=
      ((continuous_localEOWChart x0 ys).continuousAt.comp
          ((differentiable_localEOWLine ζ).continuous.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hreal :
        localEOWChart x0 ys (localEOWLine ζ (x : ℂ)) = realEmbed y := by
      simpa [y] using localEOWLine_chart_real x0 ys ζ x
    simpa [hreal] using hcont
  have hchart_mem :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (Filter.principal Ωminus) := by
    refine Filter.tendsto_principal.mpr ?_
    have hnorm :
        ∀ᶠ z in nhdsWithin (x : ℂ) EOW.UpperHalfPlane,
          z ∈ Metric.ball (0 : ℂ) 2 :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)
    filter_upwards [hnorm, self_mem_nhdsWithin] with z hz_norm hz_upper
    have hz_norm' : ‖z‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz_norm
    exact localEOWChart_line_upper_mem_of_delta_of_negative hm Ωminus x0 ys
      hδ hδρ hδsum hminus hζ hζ_neg (le_of_lt hz_norm') hz_upper
  exact (hFminus_bv y (by simpa [y] using hE_mem)).comp
    (Filter.tendsto_inf.mpr ⟨hchart_cont, hchart_mem⟩)

/-- Boundary convergence of the plus branch along a side-agreement line whose
target point has negative imaginary coordinates. -/
theorem tendsto_localEOWLine_lower_to_boundaryValue_of_negative {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {E : Set (Fin m → ℝ)}
    (Fplus : (Fin m → ℂ) → ℂ) (bv : (Fin m → ℝ) → ℂ)
    (hFplus_bv :
      ∀ y ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_neg : ∀ j, (ζ j).im < 0)
    {x : ℝ} (hx : |x| < 2)
    (hE_mem :
      localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re) ∈ E) :
    Filter.Tendsto
      (fun z : ℂ => Fplus (localEOWChart x0 ys (localEOWLine ζ z)))
      (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
      (nhds (bv (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (x : ℂ) j).re)))) := by
  let y : Fin m → ℝ :=
    localEOWRealChart x0 ys (fun j => (localEOWLine ζ (x : ℂ) j).re)
  have hx_ball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hchart_cont :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (nhds (realEmbed y)) := by
    have hcont :
        Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
          (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
          (nhds (localEOWChart x0 ys (localEOWLine ζ (x : ℂ)))) :=
      ((continuous_localEOWChart x0 ys).continuousAt.comp
          ((differentiable_localEOWLine ζ).continuous.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hreal :
        localEOWChart x0 ys (localEOWLine ζ (x : ℂ)) = realEmbed y := by
      simpa [y] using localEOWLine_chart_real x0 ys ζ x
    simpa [hreal] using hcont
  have hchart_mem :
      Filter.Tendsto (fun z : ℂ => localEOWChart x0 ys (localEOWLine ζ z))
        (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (Filter.principal Ωplus) := by
    refine Filter.tendsto_principal.mpr ?_
    have hnorm :
        ∀ᶠ z in nhdsWithin (x : ℂ) EOW.LowerHalfPlane,
          z ∈ Metric.ball (0 : ℂ) 2 :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)
    filter_upwards [hnorm, self_mem_nhdsWithin] with z hz_norm hz_lower
    have hz_norm' : ‖z‖ < 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz_norm
    exact localEOWChart_line_lower_mem_of_delta_of_negative hm Ωplus x0 ys
      hδ hδρ hδsum hplus hζ hζ_neg (le_of_lt hz_norm') hz_lower
  exact (hFplus_bv y (by simpa [y] using hE_mem)).comp
    (Filter.tendsto_inf.mpr ⟨hchart_cont, hchart_mem⟩)

/-- The local Rudin envelope equals the boundary value on real points of the
side-agreement line. -/
theorem localRudinEnvelope_line_eq_boundary_of_real {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ y ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    (hFminus_bv :
      ∀ y ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {ζ : Fin m → ℂ} {t : ℝ}
    (hLt : localEOWLine ζ (t : ℂ) ∈
      Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    localRudinEnvelope δ x0 ys Fplus Fminus (localEOWLine ζ (t : ℂ)) =
      bv (localEOWRealChart x0 ys
        (fun j => (localEOWLine ζ (t : ℂ) j).re)) := by
  have hE_smp : ∀ s : ℝ, |s| < 2 →
      localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ (localEOWLine ζ (t : ℂ)) (s : ℂ) j).re) ∈ E := by
    intro s hs
    apply hE_mem
    have hs_norm : ‖(s : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hs
    exact localEOWSmp_re_mem_closedBall hδ hδρ
      (Metric.ball_subset_closedBall hLt) hs_norm
  exact localRudinEnvelope_eq_boundary_of_real hm Ωplus Ωminus
    hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
    hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
    hplus hminus (Metric.ball_subset_closedBall hLt)
    (fun j => localEOWLine_real_im_zero ζ t j) hE_smp

set_option maxHeartbeats 1200000 in
/-- On the small positive-imaginary coordinate ball, the local Rudin envelope
agrees with the plus holomorphic branch. -/
theorem localRudinEnvelope_eq_plus_on_positive_ball {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ y ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    (hFminus_bv :
      ∀ y ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_pos : ∀ j, 0 < (ζ j).im) :
    localRudinEnvelope δ x0 ys Fplus Fminus ζ =
      Fplus (localEOWChart x0 ys ζ) := by
  let L : ℂ → Fin m → ℂ := localEOWLine ζ
  have hL_I : L Complex.I = ζ := by
    simpa [L] using localEOWLine_I ζ
  have hL_diff : Differentiable ℂ L := by
    simpa [L] using differentiable_localEOWLine ζ
  have hL_real : ∀ (t : ℝ) j, (L (t : ℂ) j).im = 0 := by
    intro t j
    simpa [L] using localEOWLine_real_im_zero ζ t j
  let bv_line : ℝ → ℂ := fun t =>
    bv (localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))
  have hbv_line_ca : ∀ (t : ℝ), |t| < 2 → ContinuousAt bv_line t := by
    intro t ht
    have ht_norm : ‖(t : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt ht
    have hmem : localEOWRealChart x0 ys
        (fun j => (L (t : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ ht_norm
    have hcoords :
        ContinuousAt (fun t : ℝ => fun j => (L (t : ℂ) j).re) t :=
      continuousAt_pi.mpr fun j =>
        Complex.continuous_re.continuousAt.comp
          ((continuous_apply j).continuousAt.comp
            (hL_diff.continuous.continuousAt.comp
              Complex.continuous_ofReal.continuousAt))
    have hrealchart_ca :
        ContinuousAt (localEOWRealChart x0 ys)
          (fun j => (L (t : ℂ) j).re) :=
      (continuous_localEOWRealChart x0 ys).continuousAt
    have hrealchart_comp :
        ContinuousAt
          (fun t : ℝ => localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re)) t :=
      hrealchart_ca.comp' hcoords
    change ContinuousAt
      (fun t : ℝ => bv (localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))) t
    exact ContinuousAt.comp'
      (f := fun t : ℝ => localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))
      (g := bv) (x := t)
      (hbv_cont.continuousAt (hE_open.mem_nhds hmem)) hrealchart_comp
  let gp : ℂ → ℂ := fun z =>
    if z.im > 0 then Fplus (localEOWChart x0 ys (L z)) else bv_line z.re
  let gm : ℂ → ℂ := fun z =>
    if z.im < 0 then Fminus (localEOWChart x0 ys (L z)) else bv_line z.re
  have hgp_eq_real : ∀ z : ℂ, z.im = 0 → gp z = bv_line z.re := fun z hz => by
    simp only [gp, show ¬ z.im > 0 from not_lt.mpr (le_of_eq hz), ite_false]
  have hgm_eq_real : ∀ z : ℂ, z.im = 0 → gm z = bv_line z.re := fun z hz => by
    simp only [gm, show ¬ z.im < 0 from not_lt.mpr (le_of_eq hz.symm), ite_false]
  have hchartL_diff : Differentiable ℂ (fun z => localEOWChart x0 ys (L z)) :=
    (differentiable_localEOWChart x0 ys).comp hL_diff
  have hgp_diff : DifferentiableOn ℂ gp
      (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 2 := by
      have hz_lt : ‖z‖ < 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact le_of_lt hz_lt
    have hz_upper : 0 < z.im := hz.2
    have hmem : localEOWChart x0 ys (L z) ∈ Ωplus := by
      simpa [L] using localEOWChart_line_upper_mem_of_delta hm Ωplus x0 ys
        hδ hδρ hδsum hplus hζ hζ_pos hz_norm hz_upper
    have hbranch : DifferentiableWithinAt ℂ
        (fun z => Fplus (localEOWChart x0 ys (L z)))
        (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) z :=
      ((hFplus_diff.differentiableAt (hΩplus_open.mem_nhds hmem)).comp z
        hchartL_diff.differentiableAt).differentiableWithinAt
    exact hbranch.congr
      (fun y hy => by
        have hy_upper : 0 < y.im := hy.2
        simp [gp, hy_upper])
      (by simp [gp, hz_upper])
  have hgm_diff : DifferentiableOn ℂ gm
      (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 2 := by
      have hz_lt : ‖z‖ < 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact le_of_lt hz_lt
    have hz_lower : z.im < 0 := hz.2
    have hmem : localEOWChart x0 ys (L z) ∈ Ωminus := by
      simpa [L] using localEOWChart_line_lower_mem_of_delta hm Ωminus x0 ys
        hδ hδρ hδsum hminus hζ hζ_pos hz_norm hz_lower
    have hbranch : DifferentiableWithinAt ℂ
        (fun z => Fminus (localEOWChart x0 ys (L z)))
        (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) z :=
      ((hFminus_diff.differentiableAt (hΩminus_open.mem_nhds hmem)).comp z
        hchartL_diff.differentiableAt).differentiableWithinAt
    exact hbranch.congr
      (fun y hy => by
        have hy_lower : y.im < 0 := hy.2
        simp [gm, hy_lower])
      (by simp [gm, hz_lower])
  have hgp_diff_disk : DifferentiableOn ℂ gp
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.UpperHalfPlane) := by
    simpa using hgp_diff
  have hgm_diff_disk : DifferentiableOn ℂ gm
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.LowerHalfPlane) := by
    simpa using hgm_diff
  have hmatch_line : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp (x : ℂ) = gm (x : ℂ) := by
    intro x _ _
    rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x),
      hgm_eq_real (x : ℂ) (Complex.ofReal_im x)]
  have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (nhds (gp (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_norm : ‖(x : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hx_abs
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (L (x : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hx_norm
    have hgp_at : gp (x : ℂ) = bv_line x := by
      rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x), Complex.ofReal_re]
    rw [hgp_at]
    have hbranch := tendsto_localEOWLine_upper_to_boundaryValue hm Ωplus x0 ys
      Fplus bv hFplus_bv hδ hδρ hδsum hplus hζ hζ_pos hx_abs
      (by simpa [L] using hx_mem)
    have heq : (fun z : ℂ => Fplus (localEOWChart x0 ys (L z)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.UpperHalfPlane] gp := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.im := hz
      show Fplus (localEOWChart x0 ys (L z)) = gp z
      simp [gp, hz']
    simpa [L, bv_line] using Filter.Tendsto.congr' heq hbranch
  have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gm (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (nhds (gm (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_norm : ‖(x : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hx_abs
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (L (x : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hx_norm
    have hgm_at : gm (x : ℂ) = bv_line x := by
      rw [hgm_eq_real (x : ℂ) (Complex.ofReal_im x), Complex.ofReal_re]
    rw [hgm_at]
    have hbranch := tendsto_localEOWLine_lower_to_boundaryValue hm Ωminus x0 ys
      Fminus bv hFminus_bv hδ hδρ hδsum hminus hζ hζ_pos hx_abs
      (by simpa [L] using hx_mem)
    have heq : (fun z : ℂ => Fminus (localEOWChart x0 ys (L z)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.LowerHalfPlane] gm := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z.im < 0 := hz
      show Fminus (localEOWChart x0 ys (L z)) = gm z
      simp [gm, hz']
    simpa [L, bv_line] using Filter.Tendsto.congr' heq hbranch
  have hbv_real : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) {c : ℂ | c.im = 0})
        (nhds (gp (x : ℂ))) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hgp_at : gp (t : ℂ) = bv_line t := by
      rw [hgp_eq_real (t : ℂ) (Complex.ofReal_im t), Complex.ofReal_re]
    rw [hgp_at]
    exact ((hbv_line_ca t ht_abs).tendsto.comp
      (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hgp_eq_real z hz).symm)
  obtain ⟨U_L, F_1d, hUL_open, hUL_conv, _, hUL_int, hF1d_holo,
      hF1d_gp, _, hball_L⟩ :=
    local_edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
      hgp_diff_disk hgm_diff_disk hgp_bv hgm_bv hmatch_line hbv_real
  have hball_sub : Metric.ball (0 : ℂ) 2 ⊆ U_L := by
    calc
      Metric.ball (0 : ℂ) 2
          = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ)
              ((2 - (-2 : ℝ)) / 2) := by
            congr 1 <;> simp
      _ ⊆ U_L := hball_L
  have hF1d_I : F_1d Complex.I = Fplus (localEOWChart x0 ys ζ) := by
    have hI_U : Complex.I ∈ U_L := hball_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
      norm_num)
    rw [hF1d_gp Complex.I ⟨hI_U, show 0 < Complex.I.im by simp [Complex.I_im]⟩]
    simp [gp, hL_I]
  have hF1d_real : ∀ (t : ℝ), (-2 : ℝ) < t → t < 2 →
      F_1d (t : ℂ) = bv_line t := by
    intro t ht_lo ht_hi
    have h_mem := hUL_int t ht_lo ht_hi
    have h_nebot : Filter.NeBot (nhdsWithin (t : ℂ) EOW.UpperHalfPlane) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro ε' hε'
      exact ⟨(t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I,
        show 0 < ((t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I).im by
          simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]
          linarith,
        by
          rw [dist_comm, dist_eq_norm,
            show (t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I - (t : ℂ) =
                ((ε' / 2 : ℝ) : ℂ) * Complex.I by
              push_cast
              ring,
            norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_pos (by linarith : ε' / 2 > 0)]
          linarith⟩
    have h_agree : ∀ᶠ z in nhdsWithin (t : ℂ) EOW.UpperHalfPlane,
        F_1d z = gp z := by
      filter_upwards [nhdsWithin_le_nhds (hUL_open.mem_nhds h_mem),
        self_mem_nhdsWithin] with z hz_U hz_UHP
      exact hF1d_gp z ⟨hz_U, hz_UHP⟩
    exact tendsto_nhds_unique
      ((hF1d_holo.continuousOn.continuousAt (hUL_open.mem_nhds h_mem)).tendsto.mono_left
        nhdsWithin_le_nhds)
      ((hgp_bv t ht_lo ht_hi).congr' (h_agree.mono fun _ h => h.symm))
      |>.trans (by rw [hgp_eq_real (t : ℂ) (Complex.ofReal_im t), Complex.ofReal_re])
  have hL0_ball : L 0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
    simpa [L] using localEOWLine_zero_mem_ball (ζ := ζ) hζ
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp
    (hL_diff.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hL0_ball))
  have hF0L_real : ∀ (t : ℝ), |t| < ε₀ →
      localRudinEnvelope δ x0 ys Fplus Fminus (L (t : ℂ)) = bv_line t := by
    intro t ht
    have hLt_ball : L (t : ℂ) ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) :=
      hε₀_sub (show (t : ℂ) ∈ Metric.ball 0 ε₀ by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        exact ht)
    simpa [L, bv_line] using
      localRudinEnvelope_line_eq_boundary_of_real hm Ωplus Ωminus E
        hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
        hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
        hE_mem hplus hminus (ζ := ζ) (t := t) (by simpa [L] using hLt_ball)
  set V := L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ U_L with hV_def
  have hpre_conv : Convex ℝ (L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    simp only [Set.mem_preimage] at hz₁ hz₂ ⊢
    have hline :
        L (a • z₁ + b • z₂) = a • L z₁ + b • L z₂ := by
      simpa [L] using localEOWLine_affine_real_combo ζ z₁ z₂ a b hab
    rw [hline]
    exact (convex_ball (0 : Fin m → ℂ) (δ / 2)) hz₁ hz₂ ha hb hab
  have hV_open : IsOpen V := (Metric.isOpen_ball.preimage hL_diff.continuous).inter hUL_open
  have hV_conv : Convex ℝ V := hpre_conv.inter hUL_conv
  have hV_preconn : IsPreconnected V := hV_conv.isPreconnected
  have h0_V : (0 : ℂ) ∈ V := ⟨hL0_ball, hball_sub (by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num)⟩
  have hI_V : Complex.I ∈ V := by
    constructor
    · simpa [hL_I] using hζ
    · exact hball_sub (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
        norm_num)
  let h : ℂ → ℂ := fun z =>
    localRudinEnvelope δ x0 ys Fplus Fminus (L z) - F_1d z
  have hEnv_diff : DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys Fplus Fminus)
      (Metric.ball (0 : Fin m → ℂ) (δ / 2)) :=
    differentiableOn_localRudinEnvelope hm Ωplus Ωminus E
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
      hE_mem hplus hminus
  have hh_anal : AnalyticOnNhd ℂ h V := by
    intro z hz
    have h1 : AnalyticAt ℂ
        (fun z => localRudinEnvelope δ x0 ys Fplus Fminus (L z)) z :=
      ((hEnv_diff.comp hL_diff.differentiableOn fun z hz => hz).mono
        Set.inter_subset_left).analyticAt (hV_open.mem_nhds hz)
    have h2 : AnalyticAt ℂ F_1d z :=
      (hF1d_holo.mono Set.inter_subset_right).analyticAt (hV_open.mem_nhds hz)
    exact h1.sub h2
  set c := min (ε₀ / 2) 1 with hc_def
  have hc_pos : 0 < c := by positivity
  have hh_zero : ∀ (t : ℝ), 0 < |t| → |t| < c → h (t : ℂ) = 0 := by
    intro t _ ht_c
    have ht_ε₀ : |t| < ε₀ := lt_of_lt_of_le ht_c ((min_le_left _ _).trans (by linarith))
    have ht_2 : (-2 : ℝ) < t ∧ t < 2 := by
      obtain ⟨h1, h2⟩ := abs_le.mp ht_c.le
      exact ⟨by linarith [min_le_right (ε₀ / 2) (1 : ℝ)],
        by linarith [min_le_right (ε₀ / 2) (1 : ℝ)]⟩
    show localRudinEnvelope δ x0 ys Fplus Fminus (L (t : ℂ)) - F_1d (t : ℂ) = 0
    rw [hF0L_real t ht_ε₀, hF1d_real t ht_2.1 ht_2.2, sub_self]
  have hh_freq : Filter.Frequently (fun z => h z = 0)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨rad, hrad_pos, hrad_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    set s := min (c / 2) (rad / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in : (s : ℂ) ∈ U' ∩ {(0 : ℂ)}ᶜ := by
      constructor
      · exact hrad_sub (by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs_pos]
          linarith [min_le_right (c / 2) (rad / 2)])
      · exact hs_ne
    exact hU'_sub hs_in (hh_zero s (by rw [abs_of_pos hs_pos]; positivity)
      (by rw [abs_of_pos hs_pos]; linarith [min_le_left (c / 2) (rad / 2)]))
  have hh_eqOn : Set.EqOn h 0 V :=
    hh_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hV_preconn h0_V hh_freq
  have hh_I := hh_eqOn hI_V
  simp only [h, Pi.zero_apply, sub_eq_zero] at hh_I
  rw [hL_I] at hh_I
  exact hh_I.trans hF1d_I

set_option maxHeartbeats 1200000 in
/-- On the small negative-imaginary coordinate ball, the local Rudin envelope
agrees with the minus holomorphic branch. -/
theorem localRudinEnvelope_eq_minus_on_negative_ball {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ y ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    (hFminus_bv :
      ∀ y ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hζ_neg : ∀ j, (ζ j).im < 0) :
    localRudinEnvelope δ x0 ys Fplus Fminus ζ =
      Fminus (localEOWChart x0 ys ζ) := by
  let L : ℂ → Fin m → ℂ := localEOWLine ζ
  have hL_I : L Complex.I = ζ := by
    simpa [L] using localEOWLine_I ζ
  have hL_diff : Differentiable ℂ L := by
    simpa [L] using differentiable_localEOWLine ζ
  let bv_line : ℝ → ℂ := fun t =>
    bv (localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))
  have hbv_line_ca : ∀ (t : ℝ), |t| < 2 → ContinuousAt bv_line t := by
    intro t ht
    have ht_norm : ‖(t : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt ht
    have hmem : localEOWRealChart x0 ys
        (fun j => (L (t : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ ht_norm
    have hcoords :
        ContinuousAt (fun t : ℝ => fun j => (L (t : ℂ) j).re) t :=
      continuousAt_pi.mpr fun j =>
        Complex.continuous_re.continuousAt.comp
          ((continuous_apply j).continuousAt.comp
            (hL_diff.continuous.continuousAt.comp
              Complex.continuous_ofReal.continuousAt))
    have hrealchart_ca :
        ContinuousAt (localEOWRealChart x0 ys)
          (fun j => (L (t : ℂ) j).re) :=
      (continuous_localEOWRealChart x0 ys).continuousAt
    have hrealchart_comp :
        ContinuousAt
          (fun t : ℝ => localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re)) t :=
      hrealchart_ca.comp' hcoords
    change ContinuousAt
      (fun t : ℝ => bv (localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))) t
    exact ContinuousAt.comp'
      (f := fun t : ℝ => localEOWRealChart x0 ys (fun j => (L (t : ℂ) j).re))
      (g := bv) (x := t)
      (hbv_cont.continuousAt (hE_open.mem_nhds hmem)) hrealchart_comp
  let gp : ℂ → ℂ := fun z =>
    if z.im > 0 then Fminus (localEOWChart x0 ys (L z)) else bv_line z.re
  let gm : ℂ → ℂ := fun z =>
    if z.im < 0 then Fplus (localEOWChart x0 ys (L z)) else bv_line z.re
  have hgp_eq_real : ∀ z : ℂ, z.im = 0 → gp z = bv_line z.re := fun z hz => by
    simp only [gp, show ¬ z.im > 0 from not_lt.mpr (le_of_eq hz), ite_false]
  have hgm_eq_real : ∀ z : ℂ, z.im = 0 → gm z = bv_line z.re := fun z hz => by
    simp only [gm, show ¬ z.im < 0 from not_lt.mpr (le_of_eq hz.symm), ite_false]
  have hchartL_diff : Differentiable ℂ (fun z => localEOWChart x0 ys (L z)) :=
    (differentiable_localEOWChart x0 ys).comp hL_diff
  have hgp_diff : DifferentiableOn ℂ gp
      (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 2 := by
      have hz_lt : ‖z‖ < 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact le_of_lt hz_lt
    have hz_upper : 0 < z.im := hz.2
    have hmem : localEOWChart x0 ys (L z) ∈ Ωminus := by
      simpa [L] using localEOWChart_line_upper_mem_of_delta_of_negative hm Ωminus x0 ys
        hδ hδρ hδsum hminus hζ hζ_neg hz_norm hz_upper
    have hbranch : DifferentiableWithinAt ℂ
        (fun z => Fminus (localEOWChart x0 ys (L z)))
        (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane) z :=
      ((hFminus_diff.differentiableAt (hΩminus_open.mem_nhds hmem)).comp z
        hchartL_diff.differentiableAt).differentiableWithinAt
    exact hbranch.congr
      (fun y hy => by
        have hy_upper : 0 < y.im := hy.2
        simp [gp, hy_upper])
      (by simp [gp, hz_upper])
  have hgm_diff : DifferentiableOn ℂ gm
      (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 2 := by
      have hz_lt : ‖z‖ < 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact le_of_lt hz_lt
    have hz_lower : z.im < 0 := hz.2
    have hmem : localEOWChart x0 ys (L z) ∈ Ωplus := by
      simpa [L] using localEOWChart_line_lower_mem_of_delta_of_negative hm Ωplus x0 ys
        hδ hδρ hδsum hplus hζ hζ_neg hz_norm hz_lower
    have hbranch : DifferentiableWithinAt ℂ
        (fun z => Fplus (localEOWChart x0 ys (L z)))
        (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane) z :=
      ((hFplus_diff.differentiableAt (hΩplus_open.mem_nhds hmem)).comp z
        hchartL_diff.differentiableAt).differentiableWithinAt
    exact hbranch.congr
      (fun y hy => by
        have hy_lower : y.im < 0 := hy.2
        simp [gm, hy_lower])
      (by simp [gm, hz_lower])
  have hgp_diff_disk : DifferentiableOn ℂ gp
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.UpperHalfPlane) := by
    simpa using hgp_diff
  have hgm_diff_disk : DifferentiableOn ℂ gm
      (Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ) ((2 - (-2 : ℝ)) / 2) ∩
        EOW.LowerHalfPlane) := by
    simpa using hgm_diff
  have hmatch_line : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 → gp (x : ℂ) = gm (x : ℂ) := by
    intro x _ _
    rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x),
      hgm_eq_real (x : ℂ) (Complex.ofReal_im x)]
  have hgp_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
        (nhds (gp (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_norm : ‖(x : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hx_abs
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (L (x : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hx_norm
    have hgp_at : gp (x : ℂ) = bv_line x := by
      rw [hgp_eq_real (x : ℂ) (Complex.ofReal_im x), Complex.ofReal_re]
    rw [hgp_at]
    have hbranch := tendsto_localEOWLine_upper_to_boundaryValue_of_negative hm Ωminus x0 ys
      Fminus bv hFminus_bv hδ hδρ hδsum hminus hζ hζ_neg hx_abs
      (by simpa [L] using hx_mem)
    have heq : (fun z : ℂ => Fminus (localEOWChart x0 ys (L z)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.UpperHalfPlane] gp := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.im := hz
      show Fminus (localEOWChart x0 ys (L z)) = gp z
      simp [gp, hz']
    simpa [L, bv_line] using Filter.Tendsto.congr' heq hbranch
  have hgm_bv : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gm (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
        (nhds (gm (x : ℂ))) := by
    intro x hx_lo hx_hi
    have hx_abs : |x| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hx_norm : ‖(x : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_of_lt hx_abs
    have hx_mem : localEOWRealChart x0 ys
        (fun j => (L (x : ℂ) j).re) ∈ E := by
      apply hE_mem
      simpa [L] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hx_norm
    have hgm_at : gm (x : ℂ) = bv_line x := by
      rw [hgm_eq_real (x : ℂ) (Complex.ofReal_im x), Complex.ofReal_re]
    rw [hgm_at]
    have hbranch := tendsto_localEOWLine_lower_to_boundaryValue_of_negative hm Ωplus x0 ys
      Fplus bv hFplus_bv hδ hδρ hδsum hplus hζ hζ_neg hx_abs
      (by simpa [L] using hx_mem)
    have heq : (fun z : ℂ => Fplus (localEOWChart x0 ys (L z)))
        =ᶠ[nhdsWithin (x : ℂ) EOW.LowerHalfPlane] gm := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z.im < 0 := hz
      show Fplus (localEOWChart x0 ys (L z)) = gm z
      simp [gm, hz']
    simpa [L, bv_line] using Filter.Tendsto.congr' heq hbranch
  have hbv_real : ∀ x : ℝ, (-2 : ℝ) < x → x < 2 →
      Filter.Tendsto gp (nhdsWithin (x : ℂ) {c : ℂ | c.im = 0})
        (nhds (gp (x : ℂ))) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hgp_at : gp (t : ℂ) = bv_line t := by
      rw [hgp_eq_real (t : ℂ) (Complex.ofReal_im t), Complex.ofReal_re]
    rw [hgp_at]
    exact ((hbv_line_ca t ht_abs).tendsto.comp
      (Complex.continuous_re.continuousAt.mono_left nhdsWithin_le_nhds)).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hgp_eq_real z hz).symm)
  obtain ⟨U_L, F_1d, hUL_open, hUL_conv, _, hUL_int, hF1d_holo,
      hF1d_gp, _, hball_L⟩ :=
    local_edge_of_the_wedge_1d (-2) 2 (by norm_num) gp gm
      hgp_diff_disk hgm_diff_disk hgp_bv hgm_bv hmatch_line hbv_real
  have hball_sub : Metric.ball (0 : ℂ) 2 ⊆ U_L := by
    calc
      Metric.ball (0 : ℂ) 2
          = Metric.ball ((((-2 : ℝ) + 2) / 2 : ℝ) : ℂ)
              ((2 - (-2 : ℝ)) / 2) := by
            congr 1 <;> simp
      _ ⊆ U_L := hball_L
  have hF1d_I : F_1d Complex.I = Fminus (localEOWChart x0 ys ζ) := by
    have hI_U : Complex.I ∈ U_L := hball_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
      norm_num)
    rw [hF1d_gp Complex.I ⟨hI_U, show 0 < Complex.I.im by simp [Complex.I_im]⟩]
    simp [gp, hL_I]
  have hF1d_real : ∀ (t : ℝ), (-2 : ℝ) < t → t < 2 →
      F_1d (t : ℂ) = bv_line t := by
    intro t ht_lo ht_hi
    have h_mem := hUL_int t ht_lo ht_hi
    have h_nebot : Filter.NeBot (nhdsWithin (t : ℂ) EOW.UpperHalfPlane) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
      intro ε' hε'
      exact ⟨(t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I,
        show 0 < ((t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I).im by
          simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]
          linarith,
        by
          rw [dist_comm, dist_eq_norm,
            show (t : ℂ) + ((ε' / 2 : ℝ) : ℂ) * Complex.I - (t : ℂ) =
                ((ε' / 2 : ℝ) : ℂ) * Complex.I by
              push_cast
              ring,
            norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_pos (by linarith : ε' / 2 > 0)]
          linarith⟩
    have h_agree : ∀ᶠ z in nhdsWithin (t : ℂ) EOW.UpperHalfPlane,
        F_1d z = gp z := by
      filter_upwards [nhdsWithin_le_nhds (hUL_open.mem_nhds h_mem),
        self_mem_nhdsWithin] with z hz_U hz_UHP
      exact hF1d_gp z ⟨hz_U, hz_UHP⟩
    exact tendsto_nhds_unique
      ((hF1d_holo.continuousOn.continuousAt (hUL_open.mem_nhds h_mem)).tendsto.mono_left
        nhdsWithin_le_nhds)
      ((hgp_bv t ht_lo ht_hi).congr' (h_agree.mono fun _ h => h.symm))
      |>.trans (by rw [hgp_eq_real (t : ℂ) (Complex.ofReal_im t), Complex.ofReal_re])
  have hL0_ball : L 0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
    simpa [L] using localEOWLine_zero_mem_ball (ζ := ζ) hζ
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp
    (hL_diff.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hL0_ball))
  have hF0L_real : ∀ (t : ℝ), |t| < ε₀ →
      localRudinEnvelope δ x0 ys Fplus Fminus (L (t : ℂ)) = bv_line t := by
    intro t ht
    have hLt_ball : L (t : ℂ) ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) :=
      hε₀_sub (show (t : ℂ) ∈ Metric.ball 0 ε₀ by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        exact ht)
    simpa [L, bv_line] using
      localRudinEnvelope_line_eq_boundary_of_real hm Ωplus Ωminus E
        hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
        hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
        hE_mem hplus hminus (ζ := ζ) (t := t) (by simpa [L] using hLt_ball)
  set V := L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩ U_L with hV_def
  have hpre_conv : Convex ℝ (L ⁻¹' Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    simp only [Set.mem_preimage] at hz₁ hz₂ ⊢
    have hline :
        L (a • z₁ + b • z₂) = a • L z₁ + b • L z₂ := by
      simpa [L] using localEOWLine_affine_real_combo ζ z₁ z₂ a b hab
    rw [hline]
    exact (convex_ball (0 : Fin m → ℂ) (δ / 2)) hz₁ hz₂ ha hb hab
  have hV_open : IsOpen V := (Metric.isOpen_ball.preimage hL_diff.continuous).inter hUL_open
  have hV_conv : Convex ℝ V := hpre_conv.inter hUL_conv
  have hV_preconn : IsPreconnected V := hV_conv.isPreconnected
  have h0_V : (0 : ℂ) ∈ V := ⟨hL0_ball, hball_sub (by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num)⟩
  have hI_V : Complex.I ∈ V := by
    constructor
    · simpa [hL_I] using hζ
    · exact hball_sub (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
        norm_num)
  let h : ℂ → ℂ := fun z =>
    localRudinEnvelope δ x0 ys Fplus Fminus (L z) - F_1d z
  have hEnv_diff : DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys Fplus Fminus)
      (Metric.ball (0 : Fin m → ℂ) (δ / 2)) :=
    differentiableOn_localRudinEnvelope hm Ωplus Ωminus E
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
      hE_mem hplus hminus
  have hh_anal : AnalyticOnNhd ℂ h V := by
    intro z hz
    have h1 : AnalyticAt ℂ
        (fun z => localRudinEnvelope δ x0 ys Fplus Fminus (L z)) z :=
      ((hEnv_diff.comp hL_diff.differentiableOn fun z hz => hz).mono
        Set.inter_subset_left).analyticAt (hV_open.mem_nhds hz)
    have h2 : AnalyticAt ℂ F_1d z :=
      (hF1d_holo.mono Set.inter_subset_right).analyticAt (hV_open.mem_nhds hz)
    exact h1.sub h2
  set c := min (ε₀ / 2) 1 with hc_def
  have hc_pos : 0 < c := by positivity
  have hh_zero : ∀ (t : ℝ), 0 < |t| → |t| < c → h (t : ℂ) = 0 := by
    intro t _ ht_c
    have ht_ε₀ : |t| < ε₀ := lt_of_lt_of_le ht_c ((min_le_left _ _).trans (by linarith))
    have ht_2 : (-2 : ℝ) < t ∧ t < 2 := by
      obtain ⟨h1, h2⟩ := abs_le.mp ht_c.le
      exact ⟨by linarith [min_le_right (ε₀ / 2) (1 : ℝ)],
        by linarith [min_le_right (ε₀ / 2) (1 : ℝ)]⟩
    show localRudinEnvelope δ x0 ys Fplus Fminus (L (t : ℂ)) - F_1d (t : ℂ) = 0
    rw [hF0L_real t ht_ε₀, hF1d_real t ht_2.1 ht_2.2, sub_self]
  have hh_freq : Filter.Frequently (fun z => h z = 0)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨rad, hrad_pos, hrad_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    set s := min (c / 2) (rad / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in : (s : ℂ) ∈ U' ∩ {(0 : ℂ)}ᶜ := by
      constructor
      · exact hrad_sub (by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs_pos]
          linarith [min_le_right (c / 2) (rad / 2)])
      · exact hs_ne
    exact hU'_sub hs_in (hh_zero s (by rw [abs_of_pos hs_pos]; positivity)
      (by rw [abs_of_pos hs_pos]; linarith [min_le_left (c / 2) (rad / 2)]))
  have hh_eqOn : Set.EqOn h 0 V :=
    hh_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hV_preconn h0_V hh_freq
  have hh_I := hh_eqOn hI_V
  simp only [h, Pi.zero_apply, sub_eq_zero] at hh_I
  rw [hL_I] at hh_I
  exact hh_I.trans hF1d_I

/-- Local continuous edge-of-the-wedge envelope in the checked coordinate
chart.  The agreement statements are deliberately restricted to the explicit
positive and negative coordinate side balls. -/
theorem local_continuous_edge_of_the_wedge_envelope {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E) (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv :
      ∀ x ∈ E, Filter.Tendsto Fplus
        (nhdsWithin (realEmbed x) Ωplus) (nhds (bv x)))
    (hFminus_bv :
      ∀ x ∈ E, Filter.Tendsto Fminus
        (nhdsWithin (realEmbed x) Ωminus) (nhds (bv x)))
    (x0 : Fin m → ℝ) (hx0 : x0 ∈ E) :
    ∃ ys : Fin m → Fin m → ℝ,
      (∀ j, ys j ∈ C) ∧ LinearIndependent ℝ ys ∧
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
        ∃ F0 : (Fin m → ℂ) → ℂ,
          DifferentiableOn ℂ F0 (Metric.ball (0 : Fin m → ℂ) (δ / 2)) ∧
          (∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
            (∀ j, 0 < (w j).im) →
              localEOWChart x0 ys w ∈ Ωplus ∧
              F0 w = Fplus (localEOWChart x0 ys w)) ∧
          (∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
            (∀ j, (w j).im < 0) →
              localEOWChart x0 ys w ∈ Ωminus ∧
              F0 w = Fminus (localEOWChart x0 ys w)) ∧
          (∀ u : Fin m → ℝ,
            (fun j => (u j : ℂ)) ∈
              Metric.ball (0 : Fin m → ℂ) (δ / 2) →
              F0 (fun j => (u j : ℂ)) =
                bv (localEOWRealChart x0 ys u)) ∧
          (∀ G : (Fin m → ℂ) → ℂ,
            DifferentiableOn ℂ G (Metric.ball (0 : Fin m → ℂ) (δ / 2)) →
            (∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
              (∀ j, 0 < (w j).im) →
                G w = Fplus (localEOWChart x0 ys w)) →
            ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), G w = F0 w) := by
  obtain ⟨ys, hys_mem, hys_li, ρ, hρ, r, hr, δ, hδ, hδρ, hδsum,
      hE_mem, hplus, hminus, _hupper_smp, _hlower_smp⟩ :=
    exists_localContinuousEOW_chart_window hm Ωplus Ωminus E C
      hE_open hC_open hC_conv hC_ne hlocal_wedge x0 hx0
  let F0 : (Fin m → ℂ) → ℂ := localRudinEnvelope δ x0 ys Fplus Fminus
  have hF0_diff : DifferentiableOn ℂ F0 (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
    exact differentiableOn_localRudinEnvelope hm Ωplus Ωminus E
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
      hE_mem hplus hminus
  refine ⟨ys, hys_mem, hys_li, ρ, hρ, r, hr, δ, hδ, hδρ, hδsum,
    hE_mem, hplus, hminus, F0, hF0_diff, ?_, ?_, ?_, ?_⟩
  · intro w hw hw_pos
    constructor
    · exact localEOWChart_ball_positive_mem_of_delta hm Ωplus x0 ys
        hδ hδρ hδsum hplus hw hw_pos
    · simpa [F0] using
        localRudinEnvelope_eq_plus_on_positive_ball hm Ωplus Ωminus E
          hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
          hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_pos
  · intro w hw hw_neg
    constructor
    · exact localEOWChart_ball_negative_mem_of_delta hm Ωminus x0 ys
        hδ hδρ hδsum hminus hw hw_neg
    · simpa [F0] using
        localRudinEnvelope_eq_minus_on_negative_ball hm Ωplus Ωminus E
          hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
          hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_neg
  · intro u hu
    have hu_closed :
        (fun j => (u j : ℂ)) ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) :=
      Metric.ball_subset_closedBall hu
    have hu_real : ∀ j, ((fun j => (u j : ℂ)) j).im = 0 := by
      intro j
      simp
    have hE_smp : ∀ s : ℝ, |s| < 2 →
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ (fun j => (u j : ℂ)) (s : ℂ) j).re) ∈ E := by
      intro s hs
      apply hE_mem
      have hs_norm : ‖(s : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_of_lt hs
      exact localEOWSmp_re_mem_closedBall hδ hδρ hu_closed hs_norm
    simpa [F0] using
      localRudinEnvelope_eq_boundary_of_real hm Ωplus Ωminus
        hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
        hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum
        hplus hminus hu_closed hu_real hE_smp
  · intro G hG_diff hG_plus w hw
    let z0 : Fin m → ℂ := fun _ => ((δ / 4 : ℝ) : ℂ) * Complex.I
    have hz0_im : ∀ j, (z0 j).im = δ / 4 := by
      intro j
      simp [z0, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have hz0_pos : ∀ j, 0 < (z0 j).im := by
      intro j
      rw [hz0_im j]
      linarith
    have hz0_ball : z0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖z0‖ = ‖((δ / 4 : ℝ) : ℂ) * Complex.I‖ := by
          apply le_antisymm
          · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
            intro j
            rfl
          · exact norm_le_pi_norm z0 ⟨0, hm⟩
        _ = δ / 4 := by
          rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_pos (by linarith : 0 < δ / 4)]
        _ < δ / 2 := by linarith
    have hPos_open : IsOpen {w : Fin m → ℂ | ∀ j, 0 < (w j).im} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply j))
    have hball_open : IsOpen (Metric.ball (0 : Fin m → ℂ) (δ / 2)) :=
      Metric.isOpen_ball
    have hF0_anal :
        AnalyticOnNhd ℂ F0 (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := fun z hz =>
      SCV.differentiableOn_analyticAt hball_open hF0_diff hz
    have hG_anal :
        AnalyticOnNhd ℂ G (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := fun z hz =>
      SCV.differentiableOn_analyticAt hball_open hG_diff hz
    have hpreconn : IsPreconnected (Metric.ball (0 : Fin m → ℂ) (δ / 2)) :=
      (convex_ball (0 : Fin m → ℂ) (δ / 2)).isPreconnected
    have hF0_plus : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        (∀ j, 0 < (w j).im) →
          F0 w = Fplus (localEOWChart x0 ys w) := by
      intro w hw hw_pos
      simpa [F0] using
        localRudinEnvelope_eq_plus_on_positive_ball hm Ωplus Ωminus E
          hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
          hE_open bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_pos
    have h_eq_near : G =ᶠ[nhds z0] F0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Metric.ball (0 : Fin m → ℂ) (δ / 2) ∩
          {w : Fin m → ℂ | ∀ j, 0 < (w j).im}, ?_, ?_⟩
      · exact Filter.inter_mem (Metric.isOpen_ball.mem_nhds hz0_ball)
          (hPos_open.mem_nhds hz0_pos)
      · intro z hz
        exact (hG_plus z hz.1 hz.2).trans (hF0_plus z hz.1 hz.2).symm
    have hEqOn : Set.EqOn G F0 (Metric.ball (0 : Fin m → ℂ) (δ / 2)) :=
      hG_anal.eqOn_of_preconnected_of_eventuallyEq hF0_anal hpreconn hz0_ball h_eq_near
    exact hEqOn hw

end SCV
