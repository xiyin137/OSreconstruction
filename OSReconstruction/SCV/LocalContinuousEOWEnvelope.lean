import OSReconstruction.SCV.LocalContinuousEOW

/-!
# Local Continuous Edge-of-the-Wedge Envelope Helpers

This file contains the analytic helper lemmas needed to turn the checked local
Rudin mean-value identity into a local continuous edge-of-the-wedge envelope.
It deliberately lives outside `LocalContinuousEOW.lean`, which is the stable
local Rudin substrate.
-/

noncomputable section

open BigOperators Topology MeasureTheory

namespace SCV

/-- The Rudin circle integrand used for the local coordinate envelope.  The
upper and lower branches are selected by the sign of `sin θ`; the two boundary
angles contribute zero. -/
def localRudinIntegrand {m : ℕ} (δ : ℝ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (w : Fin m → ℂ) (θ : ℝ) : ℂ :=
  if 0 < Real.sin θ then
    Fplus (localEOWChart x0 ys
      (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
  else if Real.sin θ < 0 then
    Fminus (localEOWChart x0 ys
      (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
  else 0

/-- The unnormalized Rudin circle integral for the local coordinate envelope. -/
def localRudinIntegral {m : ℕ} (δ : ℝ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (w : Fin m → ℂ) : ℂ :=
  ∫ θ in (-Real.pi)..Real.pi,
    localRudinIntegrand δ x0 ys Fplus Fminus w θ

/-- The normalized local Rudin envelope candidate. -/
def localRudinEnvelope {m : ℕ} (δ : ℝ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (w : Fin m → ℂ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • localRudinIntegral δ x0 ys Fplus Fminus w

/-- The complex line through a coordinate point used in Rudin side agreement:
`L(z)_j = Re ζ_j + z Im ζ_j`. -/
def localEOWLine {m : ℕ} (ζ : Fin m → ℂ) (z : ℂ) : Fin m → ℂ :=
  fun j => ((ζ j).re : ℂ) + z * ((ζ j).im : ℂ)

theorem localEOWLine_I {m : ℕ} (ζ : Fin m → ℂ) :
    localEOWLine ζ Complex.I = ζ := by
  ext j
  apply Complex.ext
  · simp [localEOWLine, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  · simp [localEOWLine, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]

theorem localEOWLine_im {m : ℕ} (ζ : Fin m → ℂ) (z : ℂ) (j : Fin m) :
    (localEOWLine ζ z j).im = z.im * (ζ j).im := by
  simp [localEOWLine, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re]

theorem localEOWLine_real_im_zero {m : ℕ} (ζ : Fin m → ℂ) (t : ℝ) (j : Fin m) :
    (localEOWLine ζ (t : ℂ) j).im = 0 := by
  simp [localEOWLine_im]

theorem differentiable_localEOWLine {m : ℕ} (ζ : Fin m → ℂ) :
    Differentiable ℂ (localEOWLine ζ) := by
  rw [differentiable_pi]
  intro j
  exact (differentiable_const _).add (differentiable_id.mul (differentiable_const _))

theorem localEOWLine_zero_mem_ball {m : ℕ} {δ : ℝ}
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    localEOWLine ζ 0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
  have hζ_norm : ‖ζ‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hζ
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖localEOWLine ζ 0‖ ≤ ‖ζ‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg ζ)).2 ?_
      intro j
      simp only [localEOWLine, zero_mul, add_zero, Complex.norm_real]
      exact (Complex.abs_re_le_norm (ζ j)).trans (norm_le_pi_norm ζ j)
    _ < δ / 2 := hζ_norm

theorem localRudinIntegrand_zero_of_sin_eq_zero {m : ℕ} (δ : ℝ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (w : Fin m → ℂ) {θ : ℝ} (hsin : Real.sin θ = 0) :
    localRudinIntegrand δ x0 ys Fplus Fminus w θ = 0 := by
  simp [localRudinIntegrand, hsin]

/-- Continuity in the Rudin parameter of the scaled local Möbius product.  This
is the public local analogue of the private `scaledMoebiusProd_continuousAt`
helper in `TubeDomainExtension.lean`. -/
theorem continuousAt_localEOWSmp_param {m : ℕ} (δ : ℝ)
    (l : ℂ) (hl : ‖l‖ ≤ 1) (w0 : Fin m → ℂ)
    (hw0 : ∀ j, ‖w0 j / (δ : ℂ)‖ < 1) :
    ContinuousAt (fun w : Fin m → ℂ => localEOWSmp δ w l) w0 := by
  have h_div : ContinuousAt (fun w : Fin m → ℂ => fun k => w k / (δ : ℂ)) w0 :=
    continuousAt_pi.mpr fun k => (continuous_apply k).continuousAt.div_const _
  have h_mem : (fun k => w0 k / (δ : ℂ)) ∈ Metric.ball (0 : Fin m → ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    exact hw0
  have h_set_eq : {w : Fin m → ℂ | ∀ j, ‖w j‖ < 1} = Metric.ball 0 1 := by
    ext w
    simp [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  have h_mp : ContinuousAt (fun w => moebiusProd w l) (fun k => w0 k / (δ : ℂ)) :=
    (h_set_eq ▸ (moebiusProd_differentiable_w l hl)).continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds h_mem)
  have h_comp : ContinuousAt (fun w => moebiusProd (fun k => w k / (δ : ℂ)) l) w0 :=
    ContinuousAt.comp (g := fun w => moebiusProd w l) h_mp h_div
  apply continuousAt_pi.mpr
  intro j
  exact continuousAt_const.mul ((continuous_apply j).continuousAt.comp h_comp)

/-- Coordinate-update margin inside the local Rudin ball.  This is the metric
input needed to apply Cauchy estimates coordinatewise to the Rudin integral. -/
theorem exists_localRudin_coordinate_update_margin
    {m : ℕ} {δ : ℝ} {z : Fin m → ℂ}
    (hz : z ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (j : Fin m) :
    ∃ ε' : ℝ, 0 < ε' ∧
      (∀ ζ, dist ζ (z j) ≤ 2 * ε' →
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) ∧
      (∀ t ∈ Metric.ball (z j) ε', ∀ ζ ∈ Metric.closedBall t ε',
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
  have hz_norm : ‖z‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hR_pos : 0 < δ / 2 := lt_of_le_of_lt (norm_nonneg z) hz_norm
  let ε' : ℝ := (δ / 2 - ‖z‖) / 4
  have hε_pos : 0 < ε' := by
    dsimp [ε']
    linarith
  have h_update : ∀ ζ, dist ζ (z j) ≤ 2 * ε' →
      Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hR_pos]
    intro k
    by_cases hk : k = j
    · subst k
      simp only [Function.update]
      have htri : ‖ζ‖ ≤ ‖z j‖ + ‖ζ - z j‖ := by
        calc
          ‖ζ‖ = ‖z j + (ζ - z j)‖ := by ring_nf
          _ ≤ ‖z j‖ + ‖ζ - z j‖ := norm_add_le _ _
      calc
        ‖ζ‖ ≤ ‖z j‖ + ‖ζ - z j‖ := htri
        _ = ‖z j‖ + dist ζ (z j) := by rw [dist_eq_norm]
        _ ≤ ‖z‖ + 2 * ε' := add_le_add (norm_le_pi_norm z j) hζ
        _ < δ / 2 := by
          dsimp [ε']
          linarith
    · simp only [Function.update, hk]
      exact lt_of_le_of_lt (norm_le_pi_norm z k) hz_norm
  refine ⟨ε', hε_pos, h_update, ?_⟩
  intro t ht ζ hζ
  apply h_update
  calc
    dist ζ (z j) ≤ dist ζ t + dist t (z j) := dist_triangle ζ t (z j)
    _ ≤ ε' + ε' := by
      have hζ_le : dist ζ t ≤ ε' := by
        simpa [Metric.mem_closedBall] using hζ
      have ht_lt : dist t (z j) < ε' := by
        simpa [Metric.mem_ball] using ht
      exact add_le_add hζ_le (le_of_lt ht_lt)
    _ = 2 * ε' := by ring

set_option maxHeartbeats 800000 in
/-- A Cauchy-estimate/Leibniz rule for one coordinate of the local Rudin
integral.  This is the public local analogue of the private
`differentiableAt_parametric_integral` helper in `TubeDomainExtension.lean`. -/
theorem differentiableAt_localRudin_parametric_integral
    {m : ℕ} (G : (Fin m → ℂ) → ℝ → ℂ)
    {z : Fin m → ℂ} {j : Fin m} {δ : ℝ}
    (hz : z ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    {ε' : ℝ} (hε'_pos : 0 < ε')
    (h_upd : ∀ ζ, dist ζ (z j) ≤ 2 * ε' →
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (h_upd_t : ∀ t ∈ Metric.ball (z j) ε', ∀ ζ ∈ Metric.closedBall t ε',
        Function.update z j ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (h_G_meas : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2),
        AEStronglyMeasurable (G w)
          (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)))
    (M : ℝ) (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ, ‖G w θ‖ ≤ M)
    (h_G_diffAt : ∀ θ, Real.sin θ ≠ 0 → ∀ t,
        Function.update z j t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2) →
        DifferentiableAt ℂ (fun ζ => G (Function.update z j ζ) θ) t)
    (hG_zero : ∀ w θ, Real.sin θ = 0 → G w θ = 0) :
    DifferentiableAt ℂ
        (fun ζ => ∫ θ in (-Real.pi)..Real.pi, G (Function.update z j ζ) θ) (z j) := by
  have h_cauchy : ∀ θ : ℝ, Real.sin θ ≠ 0 → ∀ t ∈ Metric.ball (z j) ε',
      ‖deriv (fun ζ => G (Function.update z j ζ) θ) t‖ ≤ M / ε' := by
    intro θ hsin t ht
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε'_pos
    · constructor
      · exact fun ζ hζ => (h_G_diffAt θ hsin ζ (h_upd_t t ht ζ
          (Metric.ball_subset_closedBall hζ))).differentiableWithinAt
      · rw [closure_ball t hε'_pos.ne']
        exact fun ζ hζ => (h_G_diffAt θ hsin ζ
          (h_upd_t t ht ζ hζ)).continuousAt.continuousWithinAt
    · exact fun ζ hζ => hM _ (h_upd_t t ht ζ (Metric.sphere_subset_closedBall hζ)) θ
  set F' : ℂ → ℝ → ℂ := fun ζ θ =>
    if Real.sin θ = 0 then 0
    else deriv (fun ζ' => G (Function.update z j ζ') θ) ζ with hF'_def
  have h_hasderiv : ∀ θ : ℝ, ∀ t ∈ Metric.ball (z j) ε',
      HasDerivAt (fun ζ => G (Function.update z j ζ) θ) (F' t θ) t := by
    intro θ t ht
    by_cases hsin : Real.sin θ = 0
    · simp only [F', if_pos hsin]
      have hG_eq : (fun ζ => G (Function.update z j ζ) θ) = fun _ => 0 := by
        ext ζ
        exact hG_zero _ θ hsin
      rw [hG_eq]
      exact hasDerivAt_const _ _
    · simp only [F', if_neg hsin]
      exact (h_G_diffAt θ hsin t
        (h_upd_t t ht t (Metric.mem_closedBall_self hε'_pos.le))).hasDerivAt
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM z hz 0)
  have h_F'_bound : ∀ θ : ℝ, ∀ t ∈ Metric.ball (z j) ε',
      ‖F' t θ‖ ≤ M / ε' := by
    intro θ t ht
    by_cases hsin : Real.sin θ = 0
    · simp only [F', if_pos hsin, norm_zero]
      exact div_nonneg hM_nn hε'_pos.le
    · simp only [F', if_neg hsin]
      exact h_cauchy θ hsin t ht
  have hF'_meas : AEStronglyMeasurable (F' (z j))
      (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    set y : ℕ → ℂ := fun n => z j + (↑(ε' / ((n : ℝ) + 2)) : ℂ)
    have hy_rpos : ∀ n : ℕ, (0 : ℝ) < ε' / ((n : ℝ) + 2) := fun n =>
      div_pos hε'_pos (by positivity)
    have hy_ball : ∀ n, y n ∈ Metric.ball (z j) ε' := fun n => by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hy_rpos n)]
      exact div_lt_self hε'_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hy_mem : ∀ n, Function.update z j (y n) ∈
        Metric.ball (0 : Fin m → ℂ) (δ / 2) := fun n =>
      h_upd_t (z j) (Metric.mem_ball_self hε'_pos) (y n)
        (Metric.ball_subset_closedBall (hy_ball n))
    have hy_ne : ∀ n, y n ≠ z j := fun n => by
      intro h
      have := congr_arg (· - z j) h
      simp only [y, add_sub_cancel_left, sub_self] at this
      exact absurd (Complex.ofReal_eq_zero.mp this) (ne_of_gt (hy_rpos n))
    have hy_tend : Filter.Tendsto y Filter.atTop (nhdsWithin (z j) {z j}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · suffices h : Filter.Tendsto (fun n : ℕ => (↑(ε' / ((n : ℝ) + 2)) : ℂ))
            Filter.atTop (nhds 0) by
          have := h.const_add (z j)
          simp only [add_zero] at this
          exact this
        rw [show (0 : ℂ) = (↑(0 : ℝ) : ℂ) from by simp]
        apply Filter.Tendsto.comp (Complex.continuous_ofReal.tendsto 0)
        apply squeeze_zero (fun n => le_of_lt (hy_rpos n))
        · intro n
          apply div_le_div_of_nonneg_left hε'_pos.le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
          linarith [Nat.cast_nonneg (α := ℝ) n]
        · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          rw [show (0 : ℝ) = ε' * 0 from (mul_zero ε').symm]
          exact (tendsto_const_nhds.mul h1).congr fun n => by ring
      · exact Filter.Eventually.of_forall fun n =>
          Set.mem_compl_singleton_iff.mpr (hy_ne n)
    set dq : ℕ → ℝ → ℂ := fun n θ =>
      (y n - z j)⁻¹ • (G (Function.update z j (y n)) θ - G z θ)
    have hdq_meas : ∀ n, AEStronglyMeasurable (dq n)
        (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := fun n => by
      refine ((h_G_meas _ (hy_mem n)).sub (h_G_meas z hz)).const_smul
        ((y n - z j)⁻¹) |>.congr ?_
      exact Filter.Eventually.of_forall fun θ => rfl
    have hdq_tend : ∀ θ, Filter.Tendsto (fun n => dq n θ) Filter.atTop
        (nhds (F' (z j) θ)) := by
      intro θ
      have h_slope := (h_hasderiv θ (z j) (Metric.mem_ball_self hε'_pos)).tendsto_slope
      have h_eq : ∀ n, dq n θ =
          slope (fun ζ => G (Function.update z j ζ) θ) (z j) (y n) := by
        intro n
        simp only [dq, slope, vsub_eq_sub]
        congr 1
        congr 1
        exact congr_arg (fun w => G w θ) (Function.update_eq_self j z).symm
      simp_rw [h_eq]
      exact h_slope.comp hy_tend
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hdq_meas
      (Filter.Eventually.of_forall hdq_tend)
  have hG_int : IntervalIntegrable (fun θ => G (Function.update z j (z j)) θ)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    have : (fun θ => G (Function.update z j (z j)) θ) = G z := by
      ext θ
      rw [Function.update_eq_self]
    rw [this, intervalIntegrable_iff]
    exact MeasureTheory.IntegrableOn.of_bound
      (lt_of_le_of_lt (MeasureTheory.measure_mono Set.uIoc_subset_uIcc) measure_Icc_lt_top)
      (h_G_meas z hz)
      M (Filter.Eventually.of_forall fun θ => hM z hz θ)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun ζ θ => G (Function.update z j ζ) θ) (F' := F')
    (Metric.ball_mem_nhds (z j) hε'_pos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds (z j) hε'_pos)
      fun ζ hζ => h_G_meas _
        (h_upd _ ((Metric.mem_ball.mp hζ).le.trans (by linarith))))
    hG_int
    hF'_meas
    (MeasureTheory.ae_of_all _ fun θ _ t ht => h_F'_bound θ t ht)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ t ht => h_hasderiv θ t ht)).2.differentiableAt

/-- Choose the local chart window used by the continuous local EOW construction.
This packages the genuine geometric shrink step: a cone basis, a closed real
chart ball inside the edge, one two-sided local wedge radius, and one Rudin
`δ` whose circle arcs remain in the corresponding local wedge neighborhoods. -/
theorem exists_localContinuousEOW_chart_window {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hE_open : IsOpen E) (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
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
  obtain ⟨ys, hys_mem, hys_li⟩ := open_set_contains_basis hm C hC_open hC_ne
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
  exact ⟨ys, hys_mem, hys_li, ρ, hρ, r, hr, δ, hδ, hδρ, hδsum,
    hρE, hplus, hminus, hupper, hlower⟩

/-- Unit-circle Rudin arcs with complex centers map into the local plus wedge.
This is the local replacement for the global `Phi_pos_in_tube` step in the
holomorphy proof of the Rudin integral. -/
theorem localEOWChart_smp_upper_mem_of_delta_on_sphere {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : Fin m → ℂ} {l : ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hl_norm : ‖l‖ = 1) (hl_pos : 0 < l.im) :
    localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (localEOWSmp δ w l j).re
  let v : Fin m → ℝ := fun j => (localEOWSmp δ w l j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWSmp_re_mem_closedBall hδ hδρ hw (by linarith)
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    show 0 < (localEOWSmp δ w l j).im
    show 0 < ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hδ (moebiusProd_im_pos hw_norm hl_norm hl_pos j)
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => (hv_pos j).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : v j0 ≤ ∑ j, v j :=
      Finset.single_le_sum (fun j _ => hv_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (hv_pos j0) hle
  have hv_bound : ∀ j, v j ≤ δ * 10 := by
    intro j
    calc
      v j ≤ |v j| := le_abs_self _
      _ ≤ ‖localEOWSmp δ w l j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWSmp δ w l j)
      _ ≤ δ * 10 :=
        localEOWSmp_norm_le_extended_of_closedBall hδ hw (by linarith) j
  have hv_sum_lt : (∑ j, v j) < r := by
    calc
      ∑ j, v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) =
        localEOWSmp δ w l := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- Unit-circle Rudin arcs with complex centers map into the local minus wedge.
This is the reflected companion to
`localEOWChart_smp_upper_mem_of_delta_on_sphere`. -/
theorem localEOWChart_smp_lower_mem_of_delta_on_sphere {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ} {l : ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hl_norm : ‖l‖ = 1) (hl_neg : l.im < 0) :
    localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (localEOWSmp δ w l j).re
  let v : Fin m → ℝ := fun j => (localEOWSmp δ w l j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWSmp_re_mem_closedBall hδ hδρ hw (by linarith)
  have hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ hw
  have hv_neg : ∀ j, v j < 0 := by
    intro j
    show (localEOWSmp δ w l j).im < 0
    show ((δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j).im < 0
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hδ (moebiusProd_im_neg hw_norm hl_norm hl_neg j)
  have hv_nonpos : ∀ j, v j ≤ 0 := fun j => (hv_neg j).le
  have hneg_nonneg : ∀ j, 0 ≤ -v j := fun j => neg_nonneg.mpr (hv_nonpos j)
  have hv_sum_pos : 0 < ∑ j, -v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : -v j0 ≤ ∑ j, -v j :=
      Finset.single_le_sum (fun j _ => hneg_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (neg_pos.mpr (hv_neg j0)) hle
  have hv_bound : ∀ j, -v j ≤ δ * 10 := by
    intro j
    calc
      -v j ≤ |-v j| := le_abs_self _
      _ = |v j| := abs_neg _
      _ ≤ ‖localEOWSmp δ w l j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWSmp δ w l j)
      _ ≤ δ * 10 :=
        localEOWSmp_norm_le_extended_of_closedBall hδ hw (by linarith) j
  have hv_sum_lt : (∑ j, -v j) < r := by
    calc
      ∑ j, -v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) =
        localEOWSmp δ w l := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- Measurability of the local Rudin circle integrand on the integration
interval.  This is one of the analytic inputs to the coordinatewise
Leibniz/Cauchy theorem for the Rudin integral. -/
theorem aestronglyMeasurable_localRudinIntegrand {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    AEStronglyMeasurable (localRudinIntegrand δ x0 ys Fplus Fminus w)
      (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
  apply AEStronglyMeasurable.restrict
  have hs_pos : MeasurableSet {θ : ℝ | 0 < Real.sin θ} :=
    (isOpen_lt continuous_const Real.continuous_sin).measurableSet
  have hs_neg : MeasurableSet {θ : ℝ | Real.sin θ < 0} :=
    (isOpen_lt Real.continuous_sin continuous_const).measurableSet
  have h_inner : Continuous (fun θ : ℝ =>
      localEOWChart x0 ys
        (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    (continuous_localEOWChart x0 ys).comp (continuous_localEOWSmp_theta hδ hw)
  have hmem_pos : ∀ θ ∈ {θ : ℝ | 0 < Real.sin θ},
      localEOWChart x0 ys
        (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))) ∈ Ωplus := by
    intro θ hθ
    exact localEOWChart_smp_upper_mem_of_delta_on_sphere hm Ωplus x0 ys
      hδ hδρ hδsum hplus (Metric.ball_subset_closedBall hw)
      (Complex.norm_exp_ofReal_mul_I θ) (by simpa [Complex.exp_ofReal_mul_I_im] using hθ)
  have hmem_neg : ∀ θ ∈ {θ : ℝ | Real.sin θ < 0},
      localEOWChart x0 ys
        (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))) ∈ Ωminus := by
    intro θ hθ
    exact localEOWChart_smp_lower_mem_of_delta_on_sphere hm Ωminus x0 ys
      hδ hδρ hδsum hminus (Metric.ball_subset_closedBall hw)
      (Complex.norm_exp_ofReal_mul_I θ) (by simpa [Complex.exp_ofReal_mul_I_im] using hθ)
  have hg_pos : AEStronglyMeasurable
      (fun θ : ℝ => Fplus (localEOWChart x0 ys
        (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I)))))
      (MeasureTheory.volume.restrict {θ | 0 < Real.sin θ}) :=
    (hFplus_diff.continuousOn.comp h_inner.continuousOn hmem_pos).aestronglyMeasurable
      hs_pos
  have hg_neg : AEStronglyMeasurable
      (fun θ : ℝ => Fminus (localEOWChart x0 ys
        (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I)))))
      (MeasureTheory.volume.restrict {θ | Real.sin θ < 0}) :=
    (hFminus_diff.continuousOn.comp h_inner.continuousOn hmem_neg).aestronglyMeasurable
      hs_neg
  letI : DecidablePred (· ∈ {θ : ℝ | 0 < Real.sin θ}) := fun _ => Classical.dec _
  letI : DecidablePred (· ∈ {θ : ℝ | Real.sin θ < 0}) := fun _ => Classical.dec _
  exact (hg_pos.piecewise hs_pos
    ((hg_neg.piecewise hs_neg
      (aestronglyMeasurable_const (b := (0 : ℂ)))).mono_measure
      MeasureTheory.Measure.restrict_le_self)).congr
    (Filter.Eventually.of_forall fun θ => by
      simp only [Set.piecewise, Set.mem_setOf_eq, localRudinIntegrand])

/-- Pointwise continuity of the local Rudin integrand as a function of the
complex Rudin center.  This is the dominated-convergence input for continuity
of the circle integral. -/
theorem continuousAt_localRudinIntegrand_param {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    {w0 : Fin m → ℂ}
    (hw0 : w0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (θ : ℝ) :
    ContinuousAt
      (fun w => localRudinIntegrand δ x0 ys Fplus Fminus w θ) w0 := by
  set l : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hl_norm : ‖l‖ = 1 := by
    dsimp [l]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hl_le : ‖l‖ ≤ 1 := by rw [hl_norm]
  have hw0_div : ∀ j, ‖w0 j / (δ : ℂ)‖ < 1 :=
    localEOWSmp_div_norm_lt_one_of_closedBall hδ (Metric.ball_subset_closedBall hw0)
  have h_smp : ContinuousAt (fun w : Fin m → ℂ => localEOWSmp δ w l) w0 :=
    continuousAt_localEOWSmp_param δ l hl_le w0 hw0_div
  have h_chart : ContinuousAt
      (fun w : Fin m → ℂ => localEOWChart x0 ys (localEOWSmp δ w l)) w0 :=
    (continuous_localEOWChart x0 ys).continuousAt.comp h_smp
  by_cases hpos : 0 < Real.sin θ
  · have h_eq :
        (fun w => localRudinIntegrand δ x0 ys Fplus Fminus w θ) =
        fun w => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)) := by
      ext w
      simp [localRudinIntegrand, l, hpos]
    rw [h_eq]
    have hbase : localEOWChart x0 ys (localEOWSmp δ w0 l) ∈ Ωplus :=
      localEOWChart_smp_upper_mem_of_delta_on_sphere hm Ωplus x0 ys
        hδ hδρ hδsum hplus (Metric.ball_subset_closedBall hw0) hl_norm
        (by simpa [l, Complex.exp_ofReal_mul_I_im] using hpos)
    exact ContinuousAt.comp
      (f := fun w : Fin m → ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
      (g := Fplus)
      (hFplus_diff.continuousOn.continuousAt (hΩplus_open.mem_nhds hbase))
      h_chart
  · by_cases hneg : Real.sin θ < 0
    · have h_eq :
          (fun w => localRudinIntegrand δ x0 ys Fplus Fminus w θ) =
          fun w => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)) := by
        ext w
        simp [localRudinIntegrand, l, hpos, hneg]
      rw [h_eq]
      have hbase : localEOWChart x0 ys (localEOWSmp δ w0 l) ∈ Ωminus :=
        localEOWChart_smp_lower_mem_of_delta_on_sphere hm Ωminus x0 ys
          hδ hδρ hδsum hminus (Metric.ball_subset_closedBall hw0) hl_norm
          (by simpa [l, Complex.exp_ofReal_mul_I_im] using hneg)
      exact ContinuousAt.comp
        (f := fun w : Fin m → ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
        (g := Fminus)
        (hFminus_diff.continuousOn.continuousAt (hΩminus_open.mem_nhds hbase))
        h_chart
    · have h_eq :
          (fun w => localRudinIntegrand δ x0 ys Fplus Fminus w θ) =
          fun _ => 0 := by
        ext w
        simp [localRudinIntegrand, hpos, hneg]
      rw [h_eq]
      exact continuousAt_const

/-- Continuity of the unnormalized local Rudin integral under a uniform
integrand bound. -/
theorem continuousAt_localRudinIntegral_of_bound {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    (M : ℝ)
    (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ,
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M)
    {w0 : Fin m → ℂ}
    (hw0 : w0 ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    ContinuousAt (localRudinIntegral δ x0 ys Fplus Fminus) w0 := by
  show ContinuousAt
    (fun w => ∫ θ in (-Real.pi)..Real.pi,
      localRudinIntegrand δ x0 ys Fplus Fminus w θ) w0
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [Metric.isOpen_ball.mem_nhds hw0] with w hw
    exact aestronglyMeasurable_localRudinIntegrand hm Ωplus Ωminus
      Fplus Fminus hFplus_diff hFminus_diff x0 ys
      hδ hδρ hδsum hplus hminus hw
  · filter_upwards [Metric.isOpen_ball.mem_nhds hw0] with w hw
    filter_upwards with θ _hθ
    exact hM w hw θ
  · exact intervalIntegrable_const
  · filter_upwards with θ _hθ
    exact continuousAt_localRudinIntegrand_param hm Ωplus Ωminus
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      x0 ys hδ hδρ hδsum hplus hminus hw0 θ

/-- Coordinatewise holomorphy of the local Rudin integrand away from the two
circle-boundary angles.  This supplies the pointwise differentiability input
for `differentiableAt_localRudin_parametric_integral`. -/
theorem differentiableAt_localRudinIntegrand_update {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    {z : Fin m → ℂ} {j : Fin m} {t : ℂ} {θ : ℝ}
    (hsin : Real.sin θ ≠ 0)
    (ht : Function.update z j t ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2)) :
    DifferentiableAt ℂ
      (fun ζ =>
        localRudinIntegrand δ x0 ys Fplus Fminus (Function.update z j ζ) θ) t := by
  set l : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hl_norm : ‖l‖ = 1 := by
    dsimp [l]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hl_le : ‖l‖ ≤ 1 := by rw [hl_norm]
  have h_update_div_diff :
      DifferentiableAt ℂ
        (fun ζ : ℂ => fun k => Function.update z j ζ k / (δ : ℂ)) t := by
    rw [differentiableAt_pi]
    intro k
    by_cases hk : k = j
    · subst k
      simp only [Function.update]
      exact differentiableAt_id.div_const _
    · simp only [Function.update, hk]
      exact differentiableAt_const (z k / (δ : ℂ))
  have h_unit_mem :
      (fun k => Function.update z j t k / (δ : ℂ)) ∈
        Metric.ball (0 : Fin m → ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    exact localEOWSmp_div_norm_lt_one_of_closedBall hδ
      (Metric.ball_subset_closedBall ht)
  have h_set_eq : {w : Fin m → ℂ | ∀ j, ‖w j‖ < 1} =
      Metric.ball (0 : Fin m → ℂ) 1 := by
    ext w
    simp [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  have h_mp : DifferentiableAt ℂ (fun w : Fin m → ℂ => moebiusProd w l)
      (fun k => Function.update z j t k / (δ : ℂ)) :=
    (h_set_eq ▸ (moebiusProd_differentiable_w l hl_le)).differentiableAt
      (Metric.isOpen_ball.mem_nhds h_unit_mem)
  have h_mp_update : DifferentiableAt ℂ
      (fun ζ : ℂ => moebiusProd (fun k => Function.update z j ζ k / (δ : ℂ)) l) t :=
    by
      simpa [Function.comp_def] using h_mp.comp t h_update_div_diff
  have h_smp_diff : DifferentiableAt ℂ
      (fun ζ : ℂ => localEOWSmp δ (Function.update z j ζ) l) t := by
    rw [differentiableAt_pi]
    intro k
    show DifferentiableAt ℂ
      (fun ζ : ℂ => (δ : ℂ) *
        moebiusProd (fun k => Function.update z j ζ k / (δ : ℂ)) l k) t
    have h_apply : DifferentiableAt ℂ
        (fun q : Fin m → ℂ => q k)
        (moebiusProd (fun k => Function.update z j t k / (δ : ℂ)) l) :=
      differentiableAt_apply (𝕜 := ℂ) k _
    exact (differentiableAt_const _).mul
      (by simpa [Function.comp_def] using h_apply.comp t h_mp_update)
  have h_chart_diff : DifferentiableAt ℂ
      (fun ζ : ℂ => localEOWChart x0 ys (localEOWSmp δ (Function.update z j ζ) l)) t :=
    (differentiable_localEOWChart x0 ys).differentiableAt.comp t h_smp_diff
  by_cases hpos : 0 < Real.sin θ
  · have h_eq :
        (fun ζ =>
          localRudinIntegrand δ x0 ys Fplus Fminus (Function.update z j ζ) θ) =
        fun ζ => Fplus
          (localEOWChart x0 ys (localEOWSmp δ (Function.update z j ζ) l)) := by
      ext ζ
      simp [localRudinIntegrand, l, hpos]
    rw [h_eq]
    have hbase : localEOWChart x0 ys (localEOWSmp δ (Function.update z j t) l) ∈ Ωplus :=
      localEOWChart_smp_upper_mem_of_delta_on_sphere hm Ωplus x0 ys
        hδ hδρ hδsum hplus (Metric.ball_subset_closedBall ht) hl_norm
        (by simpa [l, Complex.exp_ofReal_mul_I_im] using hpos)
    exact (hFplus_diff.differentiableAt (hΩplus_open.mem_nhds hbase)).comp t h_chart_diff
  · have hneg : Real.sin θ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hsin
    have h_eq :
        (fun ζ =>
          localRudinIntegrand δ x0 ys Fplus Fminus (Function.update z j ζ) θ) =
        fun ζ => Fminus
          (localEOWChart x0 ys (localEOWSmp δ (Function.update z j ζ) l)) := by
      ext ζ
      simp [localRudinIntegrand, l, hpos, hneg]
    rw [h_eq]
    have hbase : localEOWChart x0 ys (localEOWSmp δ (Function.update z j t) l) ∈ Ωminus :=
      localEOWChart_smp_lower_mem_of_delta_on_sphere hm Ωminus x0 ys
        hδ hδρ hδsum hminus (Metric.ball_subset_closedBall ht) hl_norm
        (by simpa [l, Complex.exp_ofReal_mul_I_im] using hneg)
    exact (hFminus_diff.differentiableAt (hΩminus_open.mem_nhds hbase)).comp t h_chart_diff

/-- Coordinatewise holomorphy of the actual local Rudin integral, assuming the
single compact uniform bound on the circle integrand.  This theorem consumes
the checked side-domain, measurability, and pointwise holomorphy inputs; after
it, the remaining analytic blocker for the local envelope is precisely the
compact-bound theorem for `localRudinIntegrand`. -/
theorem differentiableAt_localRudinIntegral_of_bound {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    {z : Fin m → ℂ} (hz : z ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (j : Fin m)
    (M : ℝ)
    (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ,
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M) :
    DifferentiableAt ℂ
      (fun ζ => ∫ θ in (-Real.pi)..Real.pi,
        localRudinIntegrand δ x0 ys Fplus Fminus
          (Function.update z j ζ) θ) (z j) := by
  obtain ⟨ε', hε', h_upd, h_upd_t⟩ :=
    exists_localRudin_coordinate_update_margin hz j
  exact differentiableAt_localRudin_parametric_integral
    (G := localRudinIntegrand δ x0 ys Fplus Fminus)
    (z := z) (j := j) (δ := δ) hz hε' h_upd h_upd_t
    (fun w hw =>
      aestronglyMeasurable_localRudinIntegrand hm Ωplus Ωminus
        Fplus Fminus hFplus_diff hFminus_diff x0 ys
        hδ hδρ hδsum hplus hminus hw)
    M hM
    (fun θ hsin t ht =>
      differentiableAt_localRudinIntegrand_update hm Ωplus Ωminus
        hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
        x0 ys hδ hδρ hδsum hplus hminus hsin ht)
    (fun w θ hsin =>
      localRudinIntegrand_zero_of_sin_eq_zero δ x0 ys Fplus Fminus w hsin)

/-- Joint holomorphy of the unnormalized local Rudin integral on the coordinate
ball, assuming the compact uniform integrand bound.  This is exactly the
Osgood step of the Rudin construction. -/
theorem differentiableOn_localRudinIntegral_of_bound {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    (M : ℝ)
    (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ,
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M) :
    DifferentiableOn ℂ
      (localRudinIntegral δ x0 ys Fplus Fminus)
      (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
  refine osgood_lemma Metric.isOpen_ball _ ?_ ?_
  · intro w hw
    exact (continuousAt_localRudinIntegral_of_bound hm Ωplus Ωminus
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      x0 ys hδ hδρ hδsum hplus hminus M hM hw).continuousWithinAt
  · intro z hz j
    exact differentiableAt_localRudinIntegral_of_bound hm Ωplus Ωminus
      hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
      x0 ys hδ hδρ hδsum hplus hminus hz j M hM

/-- Joint holomorphy of the normalized local Rudin envelope candidate under
the same compact uniform bound. -/
theorem differentiableOn_localRudinEnvelope_of_bound {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    (M : ℝ)
    (hM : ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ,
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M) :
    DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys Fplus Fminus)
      (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
  change DifferentiableOn ℂ
    (fun w => ((2 * Real.pi)⁻¹ : ℝ) •
      localRudinIntegral δ x0 ys Fplus Fminus w)
    (Metric.ball (0 : Fin m → ℂ) (δ / 2))
  exact (differentiableOn_localRudinIntegral_of_bound hm Ωplus Ωminus
    hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
    x0 ys hδ hδρ hδsum hplus hminus M hM).const_smul ((2 * Real.pi)⁻¹ : ℝ)

set_option maxHeartbeats 1000000 in
/-- Uniform compact bound for the local Rudin circle integrand.  The proof
constructs the continuous boundary extension on
`closedBall 0 (δ / 2) × sphere 0 1`, exactly as in the global
`TubeDomainExtension.lean` Rudin proof, but using the local chart and the
explicit local side domains. -/
theorem exists_bound_localRudinIntegrand {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin m → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
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
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
    ∃ M : ℝ, ∀ w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2), ∀ θ,
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M := by
  have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
    simp [Complex.norm_real, abs_of_pos hδ]
  have cball_comp_le_half :
      ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2 := by
    intro w hw j
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [norm_div, hδ_cnorm]
    calc
      ‖w j‖ / δ ≤ ‖w‖ / δ := by
        gcongr
        exact norm_le_pi_norm w j
      _ ≤ (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
  have cball_comp_lt :
      ∀ w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ < 1 := by
    intro w hw j
    linarith [cball_comp_le_half w hw j]
  have sphere_norm : ∀ l ∈ Metric.sphere (0 : ℂ) 1, ‖l‖ = 1 := by
    intro l hl
    rwa [← dist_zero_right]
  have sphere_normSq : ∀ l ∈ Metric.sphere (0 : ℂ) 1, Complex.normSq l = 1 := by
    intro l hl
    have h := sphere_norm l hl
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  have smp_cont : ContinuousOn
      (fun p : (Fin m → ℂ) × ℂ => localEOWSmp δ p.1 p.2)
      (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    apply continuousOn_pi.mpr
    intro j
    show ContinuousOn
      (fun p : (Fin m → ℂ) × ℂ =>
        (δ : ℂ) * moebiusProd (fun k => p.1 k / (δ : ℂ)) p.2 j)
      (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1)
    have h_proj : ContinuousOn
        (fun p : (Fin m → ℂ) × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1) :=
      (((continuous_apply j).comp continuous_fst).div_const _ |>.prodMk
        continuous_snd).continuousOn
    have h_maps : Set.MapsTo
        (fun p : (Fin m → ℂ) × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1)
        (Metric.ball (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) := by
      intro ⟨w, l⟩ ⟨hw, hl⟩
      exact ⟨by
          rw [Metric.mem_ball, dist_zero_right]
          exact cball_comp_lt w hw j,
        by rwa [Metric.mem_closedBall, dist_zero_right] at hl ⊢⟩
    exact continuousOn_const.mul (moebiusRudin_continuousOn.comp h_proj h_maps)
  have chart_smp_cont : ContinuousOn
      (fun p : (Fin m → ℂ) × ℂ =>
        localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
      (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (continuous_localEOWChart x0 ys).comp_continuousOn smp_cont
  have real_chart_smp_cont : ContinuousOn
      (fun p : (Fin m → ℂ) × ℂ =>
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ p.1 p.2 j).re))
      (Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    apply (continuous_localEOWRealChart x0 ys).comp_continuousOn
    exact continuousOn_pi.mpr fun j =>
      Complex.continuous_re.comp_continuousOn
        ((continuous_apply j).comp_continuousOn smp_cont)
  have smp_pos_mem : ∀ p : (Fin m → ℂ) × ℂ,
      p ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1 →
      0 < p.2.im →
      localEOWChart x0 ys (localEOWSmp δ p.1 p.2) ∈ Ωplus := by
    intro ⟨w, l⟩ ⟨hw, hl⟩ him
    exact localEOWChart_smp_upper_mem_of_delta_on_sphere hm Ωplus x0 ys
      hδ hδρ hδsum hplus hw (sphere_norm l hl) him
  have smp_neg_mem : ∀ p : (Fin m → ℂ) × ℂ,
      p ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1 →
      p.2.im < 0 →
      localEOWChart x0 ys (localEOWSmp δ p.1 p.2) ∈ Ωminus := by
    intro ⟨w, l⟩ ⟨hw, hl⟩ him
    exact localEOWChart_smp_lower_mem_of_delta_on_sphere hm Ωminus x0 ys
      hδ hδρ hδsum hminus hw (sphere_norm l hl) him
  let h : (Fin m → ℂ) × ℂ → ℂ := fun p =>
    if 0 < p.2.im then
      Fplus (localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
    else if p.2.im < 0 then
      Fminus (localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
    else
      bv (localEOWRealChart x0 ys (fun j => (localEOWSmp δ p.1 p.2 j).re))
  set S := Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ Metric.sphere (0 : ℂ) 1
  have hS_cpt : IsCompact S :=
    (isCompact_closedBall (x := (0 : Fin m → ℂ)) (r := δ / 2)).prod
      (isCompact_sphere (0 : ℂ) 1)
  have hS_ne : S.Nonempty := by
    refine ⟨(0, 1), ?_⟩
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
      exact div_nonneg hδ.le (by norm_num)
    · rw [Metric.mem_sphere, dist_zero_right]
      norm_num
  have h_cont : ContinuousOn h S := by
    intro ⟨w0, l0⟩ hwl0
    rcases hwl0 with ⟨hw0, hl0⟩
    have hS_sub :
        S ⊆ Metric.closedBall (0 : Fin m → ℂ) (δ / 2) ×ˢ
          Metric.closedBall (0 : ℂ) 1 :=
      Set.prod_mono le_rfl Metric.sphere_subset_closedBall
    have h_chart_cwa : ContinuousWithinAt
        (fun p : (Fin m → ℂ) × ℂ =>
          localEOWChart x0 ys (localEOWSmp δ p.1 p.2)) S (w0, l0) :=
      (chart_smp_cont.mono hS_sub).continuousWithinAt ⟨hw0, hl0⟩
    have h_real_cwa : ContinuousWithinAt
        (fun p : (Fin m → ℂ) × ℂ =>
          localEOWRealChart x0 ys
            (fun j => (localEOWSmp δ p.1 p.2 j).re)) S (w0, l0) :=
      (real_chart_smp_cont.mono hS_sub).continuousWithinAt ⟨hw0, hl0⟩
    have him_pos_open : IsOpen {p : (Fin m → ℂ) × ℂ | (0 : ℝ) < p.2.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
    have him_neg_open : IsOpen {p : (Fin m → ℂ) × ℂ | p.2.im < (0 : ℝ)} :=
      isOpen_lt (Complex.continuous_im.comp continuous_snd) continuous_const
    by_cases h_pos : 0 < l0.im
    · have h_ev : h =ᶠ[nhdsWithin (w0, l0) S]
          fun p => Fplus (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)) := by
        filter_upwards [nhdsWithin_le_nhds (him_pos_open.mem_nhds h_pos)]
          with ⟨w, l⟩ him
        exact if_pos him
      exact (((hFplus_diff.differentiableAt (hΩplus_open.mem_nhds
        (smp_pos_mem (w0, l0) ⟨hw0, hl0⟩ h_pos))).continuousAt
        ).comp_continuousWithinAt
          (f := fun p : (Fin m → ℂ) × ℂ =>
            localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
          h_chart_cwa).congr_of_eventuallyEq h_ev
          (show h (w0, l0) = _ from if_pos h_pos)
    · by_cases h_neg : l0.im < 0
      · have h_ev : h =ᶠ[nhdsWithin (w0, l0) S]
            fun p => Fminus (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)) := by
          filter_upwards [nhdsWithin_le_nhds (him_neg_open.mem_nhds h_neg)]
            with ⟨w, l⟩ him
          simp only [h, if_neg (not_lt.mpr him.le), if_pos him]
        exact (((hFminus_diff.differentiableAt (hΩminus_open.mem_nhds
          (smp_neg_mem (w0, l0) ⟨hw0, hl0⟩ h_neg))).continuousAt
          ).comp_continuousWithinAt
            (f := fun p : (Fin m → ℂ) × ℂ =>
              localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
            h_chart_cwa).congr_of_eventuallyEq h_ev
            (show h (w0, l0) = _ from by
              simp only [h, if_neg (not_lt.mpr h_neg.le), if_pos h_neg]
              rfl)
      · have him : l0.im = 0 :=
          le_antisymm (not_lt.mp h_pos) (not_lt.mp h_neg)
        set x' : Fin m → ℝ :=
          localEOWRealChart x0 ys (fun j => (localEOWSmp δ w0 l0 j).re)
        have hx'E : x' ∈ E := by
          have hreal_mem : (fun j => (localEOWSmp δ w0 l0 j).re) ∈
              Metric.closedBall (0 : Fin m → ℝ) ρ :=
            localEOWSmp_re_mem_closedBall hδ hδρ hw0
              ((sphere_norm l0 hl0).le.trans (by norm_num))
          simpa [x'] using hE_mem _ hreal_mem
        have h_val : h (w0, l0) = bv x' := by
          show (if 0 < l0.im then _ else if l0.im < 0 then _ else _) = _
          rw [if_neg h_pos, if_neg h_neg]
        have h_chart_real :
            localEOWChart x0 ys (localEOWSmp δ w0 l0) = realEmbed x' := by
          simpa [x'] using
            localEOWChart_smp_realEdge_eq_of_unit_real x0 ys
              (sphere_normSq l0 hl0) him
        have cwa_pos : ContinuousWithinAt h
            (S ∩ {p | 0 < p.2.im}) (w0, l0) := by
          show Filter.Tendsto h _ (nhds (h (w0, l0)))
          rw [h_val]
          have h_maps : Set.MapsTo
              (fun p : (Fin m → ℂ) × ℂ =>
                localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
              (S ∩ {p | 0 < p.2.im}) Ωplus :=
            fun p hp => smp_pos_mem p hp.1 hp.2
          have h_tendsto := (h_chart_cwa.mono
            Set.inter_subset_left).tendsto_nhdsWithin h_maps
          rw [h_chart_real] at h_tendsto
          exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
            fun p hp => show h p = _ from by
              cases p with | mk w l => exact if_pos hp.2)).mpr
            ((hFplus_bv x' hx'E).comp h_tendsto)
        have cwa_neg : ContinuousWithinAt h
            (S ∩ {p | p.2.im < 0}) (w0, l0) := by
          show Filter.Tendsto h _ (nhds (h (w0, l0)))
          rw [h_val]
          have h_maps : Set.MapsTo
              (fun p : (Fin m → ℂ) × ℂ =>
                localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
              (S ∩ {p | p.2.im < 0}) Ωminus :=
            fun p hp => smp_neg_mem p hp.1 hp.2
          have h_tendsto := (h_chart_cwa.mono
            Set.inter_subset_left).tendsto_nhdsWithin h_maps
          rw [h_chart_real] at h_tendsto
          exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
            fun p hp => show h p = _ from by
              cases p with | mk w l =>
                have him_neg : l.im < 0 := hp.2
                simp only [h, if_neg (not_lt.mpr him_neg.le), if_pos him_neg]
                rfl)).mpr
            ((hFminus_bv x' hx'E).comp h_tendsto)
        have cwa_zero : ContinuousWithinAt h
            (S ∩ {p | p.2.im = 0}) (w0, l0) := by
          show Filter.Tendsto h _ (nhds (h (w0, l0)))
          rw [h_val]
          have h_re_cwa : ContinuousWithinAt
              (fun p : (Fin m → ℂ) × ℂ =>
                localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ p.1 p.2 j).re))
              (S ∩ {p | p.2.im = 0}) (w0, l0) :=
            h_real_cwa.mono Set.inter_subset_left
          have h_re_maps : Set.MapsTo
              (fun p : (Fin m → ℂ) × ℂ =>
                localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ p.1 p.2 j).re))
              (S ∩ {p | p.2.im = 0}) E := by
            intro ⟨w, l⟩ hp
            rcases hp with ⟨⟨hw, hl⟩, _him⟩
            exact hE_mem _
              (localEOWSmp_re_mem_closedBall hδ hδρ hw
                ((sphere_norm l hl).le.trans (by norm_num)))
          have h_composed : Filter.Tendsto
              (fun p : (Fin m → ℂ) × ℂ =>
                bv (localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ p.1 p.2 j).re)))
              (nhdsWithin (w0, l0) (S ∩ {p | p.2.im = 0}))
              (nhds (bv x')) :=
            Filter.Tendsto.comp
              (hbv_cont.continuousWithinAt hx'E)
              (h_re_cwa.tendsto_nhdsWithin h_re_maps)
          exact (Filter.tendsto_congr' (eventually_nhdsWithin_of_forall
            fun ⟨w, l⟩ ⟨_, him_mem⟩ =>
              show h (w, l) =
                bv (localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ w l j).re)) from by
              have him0 : l.im = 0 := him_mem
              simp only [h, if_neg (not_lt.mpr (le_of_eq him0)),
                if_neg (not_lt.mpr (le_of_eq him0.symm))])).mpr h_composed
        exact (cwa_pos.union (cwa_neg.union cwa_zero)).mono
          (fun ⟨w, l⟩ hS => (lt_trichotomy l.im 0).elim
            (fun hlt => Or.inr (Or.inl ⟨hS, hlt⟩))
            (fun h => h.elim
              (fun heq => Or.inr (Or.inr ⟨hS, heq⟩))
              (fun hgt => Or.inl ⟨hS, hgt⟩)))
  obtain ⟨M, hM⟩ := hS_cpt.exists_bound_of_continuousOn h_cont
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM _ hS_ne.some_mem)
  refine ⟨M, fun w hw θ => ?_⟩
  set l : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hl_def
  have hl_sphere : l ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hwl : (w, l) ∈ S :=
    ⟨Metric.ball_subset_closedBall hw, hl_sphere⟩
  by_cases hsin_pos : 0 < Real.sin θ
  · have hl_im : 0 < l.im := by
      show 0 < (Complex.exp ((θ : ℂ) * Complex.I)).im
      rw [Complex.exp_ofReal_mul_I_im]
      exact hsin_pos
    calc
      ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ = ‖h (w, l)‖ := by
        simp only [localRudinIntegrand, h, if_pos hsin_pos, if_pos hl_im, ← hl_def]
      _ ≤ M := hM _ hwl
  · by_cases hsin_neg : Real.sin θ < 0
    · have hl_im : l.im < 0 := by
        show (Complex.exp ((θ : ℂ) * Complex.I)).im < 0
        rw [Complex.exp_ofReal_mul_I_im]
        exact hsin_neg
      calc
        ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ = ‖h (w, l)‖ := by
          simp only [localRudinIntegrand, h, if_neg hsin_pos, if_pos hsin_neg,
            if_neg (not_lt.mpr hl_im.le), if_pos hl_im, ← hl_def]
        _ ≤ M := hM _ hwl
    · simp only [localRudinIntegrand, if_neg hsin_pos, if_neg hsin_neg, norm_zero]
      exact hM_nn

/-- Bound-free holomorphy of the normalized local Rudin envelope on the
coordinate ball.  This combines the compact-bound theorem with the Osgood
holomorphy theorem for the integral. -/
theorem differentiableOn_localRudinEnvelope {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin m → ℝ) → ℂ)
    (hbv_cont : ContinuousOn bv E)
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
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
    DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys Fplus Fminus)
      (Metric.ball (0 : Fin m → ℂ) (δ / 2)) := by
  obtain ⟨M, hM⟩ := exists_bound_localRudinIntegrand hm Ωplus Ωminus E
    hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
    bv hbv_cont hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum hE_mem hplus hminus
  exact differentiableOn_localRudinEnvelope_of_bound hm Ωplus Ωminus
    hΩplus_open hΩminus_open Fplus Fminus hFplus_diff hFminus_diff
    x0 ys hδ hδρ hδsum hplus hminus M hM

/-- The local Rudin envelope has boundary value `bv` at real coordinate
centers.  This is `local_rudin_mean_value_real` expressed with the envelope
definition used by the side-agreement proof. -/
theorem localRudinEnvelope_eq_boundary_of_real {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (Fplus Fminus : (Fin m → ℂ) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    {E : Set (Fin m → ℝ)} (hE_open : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hFplus_bv : ∀ y ∈ E,
      Filter.Tendsto Fplus (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
    (hFminus_bv : ∀ y ∈ E,
      Filter.Tendsto Fminus (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
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
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.closedBall (0 : Fin m → ℂ) (δ / 2))
    (hw_real : ∀ j, (w j).im = 0)
    (hE_mem : ∀ s : ℝ, |s| < 2 →
      localEOWRealChart x0 ys (fun j => (localEOWSmp δ w (s : ℂ) j).re) ∈ E) :
    localRudinEnvelope δ x0 ys Fplus Fminus w =
      bv (localEOWRealChart x0 ys (fun j => (w j).re)) := by
  simpa [localRudinEnvelope, localRudinIntegral, localRudinIntegrand] using
    local_rudin_mean_value_real hm Ωplus Ωminus hΩplus_open hΩminus_open
      Fplus Fminus hFplus_diff hFminus_diff hE_open bv hbv_cont
      hFplus_bv hFminus_bv x0 ys hδ hδρ hδsum hplus hminus hw hw_real hE_mem

/-- Norm bound for the one-dimensional Rudin side-agreement line. -/
theorem localEOWLine_norm_le_delta_ten_of_norm_le_two {m : ℕ}
    {δ : ℝ} (hδ : 0 < δ)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ∀ j, ‖localEOWLine ζ z j‖ ≤ δ * 10 := by
  have hζ_norm : ‖ζ‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hζ
  intro j
  calc
    ‖localEOWLine ζ z j‖
        ≤ ‖((ζ j).re : ℂ)‖ + ‖z * ((ζ j).im : ℂ)‖ := by
          simpa [localEOWLine] using
            norm_add_le ((ζ j).re : ℂ) (z * ((ζ j).im : ℂ))
    _ = |(ζ j).re| + ‖z‖ * |(ζ j).im| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
    _ ≤ ‖ζ j‖ + ‖z‖ * ‖ζ j‖ := by
          have hre : |(ζ j).re| ≤ ‖ζ j‖ := Complex.abs_re_le_norm _
          have him : |(ζ j).im| ≤ ‖ζ j‖ := Complex.abs_im_le_norm _
          have hprod : ‖z‖ * |(ζ j).im| ≤ ‖z‖ * ‖ζ j‖ :=
            mul_le_mul_of_nonneg_left him (norm_nonneg z)
          linarith
    _ ≤ ‖ζ‖ + ‖z‖ * ‖ζ‖ := by
          have hj : ‖ζ j‖ ≤ ‖ζ‖ := norm_le_pi_norm ζ j
          have hprod : ‖z‖ * ‖ζ j‖ ≤ ‖z‖ * ‖ζ‖ :=
            mul_le_mul_of_nonneg_left hj (norm_nonneg z)
          linarith
    _ = (1 + ‖z‖) * ‖ζ‖ := by ring
    _ ≤ 3 * (δ / 2) := by
          have hz3 : 1 + ‖z‖ ≤ 3 := by linarith
          exact mul_le_mul hz3 hζ_norm.le (norm_nonneg ζ) (by norm_num)
    _ ≤ δ * 10 := by nlinarith

/-- The real part of the one-dimensional side-agreement line remains in the
local real chart ball for `‖z‖ ≤ 2`. -/
theorem localEOWLine_re_closedBall_of_norm_le_two {m : ℕ}
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    {ζ : Fin m → ℂ}
    (hζ : ζ ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    {z : ℂ} (hz : ‖z‖ ≤ 2) :
    (fun j => (localEOWLine ζ z j).re) ∈
      Metric.closedBall (0 : Fin m → ℝ) ρ := by
  have hρ_nonneg : 0 ≤ ρ := by
    nlinarith
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg hρ_nonneg).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  calc
    |(localEOWLine ζ z j).re| ≤ ‖localEOWLine ζ z j‖ :=
      Complex.abs_re_le_norm _
    _ ≤ δ * 10 :=
      localEOWLine_norm_le_delta_ten_of_norm_le_two hδ hζ hz j
    _ ≤ ρ := hδρ

/-- The side-agreement line maps the upper half-plane into the explicit local
plus polywedge when the target point has positive imaginary coordinates. -/
theorem localEOWChart_line_upper_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
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
    {z : ℂ} (hz_norm : ‖z‖ ≤ 2) (hz_pos : 0 < z.im) :
    localEOWChart x0 ys (localEOWLine ζ z) ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (localEOWLine ζ z j).re
  let v : Fin m → ℝ := fun j => (localEOWLine ζ z j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hz_norm
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    simp [v, localEOWLine_im, mul_pos hz_pos (hζ_pos j)]
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => (hv_pos j).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : v j0 ≤ ∑ j, v j :=
      Finset.single_le_sum (fun j _ => hv_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (hv_pos j0) hle
  have hv_bound : ∀ j, v j ≤ δ * 10 := by
    intro j
    calc
      v j ≤ |v j| := le_abs_self _
      _ ≤ ‖localEOWLine ζ z j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWLine ζ z j)
      _ ≤ δ * 10 :=
        localEOWLine_norm_le_delta_ten_of_norm_le_two hδ hζ hz_norm j
  have hv_sum_lt : (∑ j, v j) < r := by
    calc
      ∑ j, v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = localEOWLine ζ z := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- The side-agreement line maps the lower half-plane into the explicit local
minus polywedge when the target point has positive imaginary coordinates. -/
theorem localEOWChart_line_lower_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
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
    {z : ℂ} (hz_norm : ‖z‖ ≤ 2) (hz_neg : z.im < 0) :
    localEOWChart x0 ys (localEOWLine ζ z) ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (localEOWLine ζ z j).re
  let v : Fin m → ℝ := fun j => (localEOWLine ζ z j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hz_norm
  have hv_neg : ∀ j, v j < 0 := by
    intro j
    simp [v, localEOWLine_im, mul_neg_of_neg_of_pos hz_neg (hζ_pos j)]
  have hv_nonpos : ∀ j, v j ≤ 0 := fun j => (hv_neg j).le
  have hneg_nonneg : ∀ j, 0 ≤ -v j := fun j => neg_nonneg.mpr (hv_nonpos j)
  have hv_sum_pos : 0 < ∑ j, -v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : -v j0 ≤ ∑ j, -v j :=
      Finset.single_le_sum (fun j _ => hneg_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (neg_pos.mpr (hv_neg j0)) hle
  have hv_bound : ∀ j, -v j ≤ δ * 10 := by
    intro j
    calc
      -v j ≤ |-v j| := le_abs_self _
      _ = |v j| := abs_neg _
      _ ≤ ‖localEOWLine ζ z j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWLine ζ z j)
      _ ≤ δ * 10 :=
        localEOWLine_norm_le_delta_ten_of_norm_le_two hδ hζ hz_norm j
  have hv_sum_lt : (∑ j, -v j) < r := by
    calc
      ∑ j, -v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = localEOWLine ζ z := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- For a target point with negative imaginary coordinates, the side-agreement
line maps the upper half-plane into the explicit local minus polywedge. -/
theorem localEOWChart_line_upper_mem_of_delta_of_negative {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
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
    {z : ℂ} (hz_norm : ‖z‖ ≤ 2) (hz_pos : 0 < z.im) :
    localEOWChart x0 ys (localEOWLine ζ z) ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (localEOWLine ζ z j).re
  let v : Fin m → ℝ := fun j => (localEOWLine ζ z j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hz_norm
  have hv_neg : ∀ j, v j < 0 := by
    intro j
    simp [v, localEOWLine_im, mul_neg_of_pos_of_neg hz_pos (hζ_neg j)]
  have hv_nonpos : ∀ j, v j ≤ 0 := fun j => (hv_neg j).le
  have hneg_nonneg : ∀ j, 0 ≤ -v j := fun j => neg_nonneg.mpr (hv_nonpos j)
  have hv_sum_pos : 0 < ∑ j, -v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : -v j0 ≤ ∑ j, -v j :=
      Finset.single_le_sum (fun j _ => hneg_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (neg_pos.mpr (hv_neg j0)) hle
  have hv_bound : ∀ j, -v j ≤ δ * 10 := by
    intro j
    calc
      -v j ≤ |-v j| := le_abs_self _
      _ = |v j| := abs_neg _
      _ ≤ ‖localEOWLine ζ z j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWLine ζ z j)
      _ ≤ δ * 10 :=
        localEOWLine_norm_le_delta_ten_of_norm_le_two hδ hζ hz_norm j
  have hv_sum_lt : (∑ j, -v j) < r := by
    calc
      ∑ j, -v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = localEOWLine ζ z := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- For a target point with negative imaginary coordinates, the side-agreement
line maps the lower half-plane into the explicit local plus polywedge. -/
theorem localEOWChart_line_lower_mem_of_delta_of_negative {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
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
    {z : ℂ} (hz_norm : ‖z‖ ≤ 2) (hz_neg : z.im < 0) :
    localEOWChart x0 ys (localEOWLine ζ z) ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (localEOWLine ζ z j).re
  let v : Fin m → ℝ := fun j => (localEOWLine ζ z j).im
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    simpa [u] using localEOWLine_re_closedBall_of_norm_le_two hδ hδρ hζ hz_norm
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    simp [v, localEOWLine_im, mul_pos_of_neg_of_neg hz_neg (hζ_neg j)]
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => (hv_pos j).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : v j0 ≤ ∑ j, v j :=
      Finset.single_le_sum (fun j _ => hv_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (hv_pos j0) hle
  have hv_bound : ∀ j, v j ≤ δ * 10 := by
    intro j
    calc
      v j ≤ |v j| := le_abs_self _
      _ ≤ ‖localEOWLine ζ z j‖ := by
        simpa [v] using Complex.abs_im_le_norm (localEOWLine ζ z j)
      _ ≤ δ * 10 :=
        localEOWLine_norm_le_delta_ten_of_norm_le_two hδ hζ hz_norm j
  have hv_sum_lt : (∑ j, v j) < r := by
    calc
      ∑ j, v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = localEOWLine ζ z := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- The small positive-imaginary coordinate ball maps into the local plus wedge.
This is the honest side domain used for local agreement before any optional
side-connectedness enlargement. -/
theorem localEOWChart_ball_positive_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωplus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hw_pos : ∀ j, 0 < (w j).im) :
    localEOWChart x0 ys w ∈ Ωplus := by
  let u : Fin m → ℝ := fun j => (w j).re
  let v : Fin m → ℝ := fun j => (w j).im
  have hw_norm : ‖w‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hρ_nonneg).2 ?_
    intro j
    rw [Real.norm_eq_abs]
    calc
      |(w j).re| ≤ ‖w j‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ ≤ ρ := by nlinarith
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    exact hw_pos j
  have hv_nonneg : ∀ j, 0 ≤ v j := fun j => (hv_pos j).le
  have hv_sum_pos : 0 < ∑ j, v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : v j0 ≤ ∑ j, v j :=
      Finset.single_le_sum (fun j _ => hv_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (hv_pos j0) hle
  have hv_bound : ∀ j, v j ≤ δ * 10 := by
    intro j
    calc
      v j ≤ |v j| := le_abs_self _
      _ ≤ ‖w j‖ := by
        simpa [v] using Complex.abs_im_le_norm (w j)
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ ≤ δ * 10 := by nlinarith
  have hv_sum_lt : (∑ j, v j) < r := by
    calc
      ∑ j, v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hplus u hu v hv_nonneg hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = w := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

/-- The small negative-imaginary coordinate ball maps into the local minus
wedge.  This is the reflected side-domain companion to
`localEOWChart_ball_positive_mem_of_delta`. -/
theorem localEOWChart_ball_negative_mem_of_delta {m : ℕ} (hm : 0 < m)
    (Ωminus : Set (Fin m → ℂ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
    {w : Fin m → ℂ}
    (hw : w ∈ Metric.ball (0 : Fin m → ℂ) (δ / 2))
    (hw_neg : ∀ j, (w j).im < 0) :
    localEOWChart x0 ys w ∈ Ωminus := by
  let u : Fin m → ℝ := fun j => (w j).re
  let v : Fin m → ℝ := fun j => (w j).im
  have hw_norm : ‖w‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hρ_nonneg : 0 ≤ ρ := by nlinarith
  have hu : u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hρ_nonneg).2 ?_
    intro j
    rw [Real.norm_eq_abs]
    calc
      |(w j).re| ≤ ‖w j‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ ≤ ρ := by nlinarith
  have hv_neg : ∀ j, v j < 0 := by
    intro j
    exact hw_neg j
  have hv_nonpos : ∀ j, v j ≤ 0 := fun j => (hv_neg j).le
  have hneg_nonneg : ∀ j, 0 ≤ -v j := fun j => neg_nonneg.mpr (hv_nonpos j)
  have hv_sum_pos : 0 < ∑ j, -v j := by
    let j0 : Fin m := ⟨0, hm⟩
    have hle : -v j0 ≤ ∑ j, -v j :=
      Finset.single_le_sum (fun j _ => hneg_nonneg j) (Finset.mem_univ j0)
    exact lt_of_lt_of_le (neg_pos.mpr (hv_neg j0)) hle
  have hv_bound : ∀ j, -v j ≤ δ * 10 := by
    intro j
    calc
      -v j ≤ |-v j| := le_abs_self _
      _ = |v j| := abs_neg _
      _ ≤ ‖w j‖ := by
        simpa [v] using Complex.abs_im_le_norm (w j)
      _ ≤ ‖w‖ := norm_le_pi_norm w j
      _ ≤ δ * 10 := by nlinarith
  have hv_sum_lt : (∑ j, -v j) < r := by
    calc
      ∑ j, -v j ≤ ∑ _j : Fin m, δ * 10 :=
        Finset.sum_le_sum (fun j _ => hv_bound j)
      _ = (Fintype.card (Fin m) : ℝ) * (δ * 10) := by simp
      _ < r := hδsum
  have hmem := hminus u hu v hv_nonpos hv_sum_pos hv_sum_lt
  have hdecomp :
      (fun j => ((u j : ℂ) + (v j : ℂ) * Complex.I)) = w := by
    ext j
    simp [u, v, Complex.re_add_im]
  rwa [hdecomp] at hmem

end SCV
