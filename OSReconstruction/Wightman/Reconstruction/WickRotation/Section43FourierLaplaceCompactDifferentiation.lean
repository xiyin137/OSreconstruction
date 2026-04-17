import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceHigherDerivatives

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

attribute [local instance 101] secondCountableTopologyEither_of_left

namespace OSReconstruction

/-- If a function is zero in a neighborhood of a point, then every ambient
iterated Fréchet derivative at that point is zero. -/
theorem iteratedFDeriv_eq_zero_of_eventuallyEq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E}
    (hf : f =ᶠ[𝓝 x] 0) (r : ℕ) :
    iteratedFDeriv ℝ r f x = 0 := by
  rw [(hf.iteratedFDeriv ℝ r).eq_of_nhds]
  simp

/-- Multiplying a smooth rapidly decaying function on the support of the
multiplier derivatives by a temperate multiplier gives a Schwartz function. -/
noncomputable def schwartzMap_of_temperate_mul_rapid_on_derivSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ F : E → ℂ)
    (S : Set E)
    (hχ_temperate : Function.HasTemperateGrowth χ)
    (hχ_deriv_support :
      ∀ r : ℕ, ∀ x : E,
        iteratedFDeriv ℝ r χ x ≠ 0 → x ∈ S)
    (hF_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hF_rapid_on_S :
      ∀ r s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ S, (1 + ‖x‖) ^ s * ‖iteratedFDeriv ℝ r F x‖ ≤ C) :
    SchwartzMap E ℂ where
  toFun := fun x => χ x * F x
  smooth' := hχ_temperate.1.mul hF_smooth
  decay' := by
    intro k n
    rcases hχ_temperate.norm_iteratedFDeriv_le_uniform n with
      ⟨kχ, Cχ, hCχ_nonneg, hCχ_bound⟩
    choose CF hCF_nonneg hCF_bound using fun i : ℕ =>
      hF_rapid_on_S (n - i) (k + kχ)
    let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cχ * CF i
    refine ⟨C, ?_⟩
    intro x
    have hn_top : (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (le_top (a := (n : ℕ∞)))
    have hLeib := norm_iteratedFDeriv_mul_le (n := n) hχ_temperate.1 hF_smooth x
      hn_top
    have hone_pos : 0 ≤ 1 + ‖x‖ := by positivity
    have hxpow_le : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
      exact pow_le_pow_left₀ (norm_nonneg x) (by linarith [norm_nonneg x]) k
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (n - i) F x‖) ≤
          (n.choose i : ℝ) * Cχ * CF i := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (by simpa using hi)
      have hchoose_nonneg : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
      have hF_norm_nonneg : 0 ≤ ‖iteratedFDeriv ℝ (n - i) F x‖ := norm_nonneg _
      have hχ_bound := hCχ_bound i hi_le x
      by_cases hχ_zero : iteratedFDeriv ℝ i χ x = 0
      · have hleft_zero :
            ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
              ‖iteratedFDeriv ℝ (n - i) F x‖) = 0 := by
          simp [hχ_zero]
        rw [hleft_zero]
        exact mul_nonneg (mul_nonneg hchoose_nonneg hCχ_nonneg) (hCF_nonneg i)
      · have hxS : x ∈ S := hχ_deriv_support i x hχ_zero
        have hF_bound := hCF_bound i x hxS
        have hpoly_mul :
            ‖x‖ ^ k * (1 + ‖x‖) ^ kχ ≤ (1 + ‖x‖) ^ (k + kχ) := by
          calc
            ‖x‖ ^ k * (1 + ‖x‖) ^ kχ ≤
                (1 + ‖x‖) ^ k * (1 + ‖x‖) ^ kχ := by
                  exact mul_le_mul_of_nonneg_right hxpow_le (pow_nonneg hone_pos kχ)
            _ = (1 + ‖x‖) ^ (k + kχ) := by
                  rw [← pow_add]
        have hcore :
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i χ x‖ *
              ‖iteratedFDeriv ℝ (n - i) F x‖ ≤ Cχ * CF i := by
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i χ x‖ *
                ‖iteratedFDeriv ℝ (n - i) F x‖
                ≤ ‖x‖ ^ k * (Cχ * (1 + ‖x‖) ^ kχ) *
                    ‖iteratedFDeriv ℝ (n - i) F x‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hχ_bound (pow_nonneg (norm_nonneg x) k))
                    hF_norm_nonneg
            _ = Cχ * (‖x‖ ^ k * (1 + ‖x‖) ^ kχ *
                    ‖iteratedFDeriv ℝ (n - i) F x‖) := by ring
            _ ≤ Cχ * ((1 + ‖x‖) ^ (k + kχ) *
                    ‖iteratedFDeriv ℝ (n - i) F x‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hpoly_mul hF_norm_nonneg)
                    hCχ_nonneg
            _ ≤ Cχ * CF i := by
                  exact mul_le_mul_of_nonneg_left hF_bound hCχ_nonneg
        calc
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (n - i) F x‖)
              = (n.choose i : ℝ) *
                  (‖x‖ ^ k * ‖iteratedFDeriv ℝ i χ x‖ *
                    ‖iteratedFDeriv ℝ (n - i) F x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (Cχ * CF i) := by
                exact mul_le_mul_of_nonneg_left hcore hchoose_nonneg
          _ = (n.choose i : ℝ) * Cχ * CF i := by ring
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => χ y * F y) x‖
          ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
                ‖iteratedFDeriv ℝ (n - i) F x‖ := by
            exact mul_le_mul_of_nonneg_left hLeib (pow_nonneg (norm_nonneg x) k)
      _ = ∑ i ∈ Finset.range (n + 1),
              ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
                ‖iteratedFDeriv ℝ (n - i) F x‖) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cχ * CF i := by
            exact Finset.sum_le_sum hterm
      _ = C := by rfl

/-- Membership in the closed ball centered at `0` gives the expected norm
bound for the Section 4.3 time variable. -/
theorem norm_le_of_mem_time_closedBall_zero
    (n : ℕ) (τ : Fin n → ℝ) {R : ℝ}
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R) :
    ‖τ‖ ≤ R := by
  simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hτ

/-- A point in the unit closed ball around `q` has norm at most `‖q‖ + 1`. -/
theorem norm_nPoint_le_norm_add_one_of_mem_closedBall
    (d n : ℕ) [NeZero d]
    (q q' : NPointDomain d n)
    (hq' : q' ∈ Metric.closedBall q (1 : ℝ)) :
    ‖q'‖ ≤ ‖q‖ + 1 := by
  have hdist : dist q' q ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall] using hq'
  have hsub : ‖q' - q‖ ≤ (1 : ℝ) := by
    simpa [dist_eq_norm] using hdist
  have htri : ‖q'‖ ≤ ‖q' - q‖ + ‖q‖ := by
    calc
      ‖q'‖ = ‖(q' - q) + q‖ := by
        simp
      _ ≤ ‖q' - q‖ + ‖q‖ := norm_add_le _ _
  linarith

/-- On a compact product of a time ball and a unit `q`-ball, the absolute
Laplace exponential is uniformly bounded by a scalar depending only on the
center `q` and the time radius. -/
theorem norm_exp_neg_section43_timePair_le_local_closedBall
    (d n : ℕ) [NeZero d]
    (q q' : NPointDomain d n)
    (τ : Fin n → ℝ)
    {R : ℝ} (hR_nonneg : 0 ≤ R)
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R)
    (hq' : q' ∈ Metric.closedBall q (1 : ℝ)) :
    ‖Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) *
          (section43QTime (d := d) (n := n) q' k : ℂ)))‖ ≤
      Real.exp
        (R * ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (‖q‖ + 1))) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hτ_norm : ‖τ‖ ≤ R :=
    norm_le_of_mem_time_closedBall_zero n τ hτ
  have hq_norm : ‖q'‖ ≤ ‖q‖ + 1 :=
    norm_nPoint_le_norm_add_one_of_mem_closedBall d n q q' hq'
  have hterm :
      ∀ k : Fin n,
        |τ k * section43QTime (d := d) (n := n) q' k| ≤
          R * (section43QTimeCoordOpNorm d n k * (‖q‖ + 1)) := by
    intro k
    have hτk : |τ k| ≤ R := by
      have hcoord : ‖τ k‖ ≤ ‖τ‖ := norm_le_pi_norm τ k
      have hcoord_abs : |τ k| ≤ ‖τ‖ := by
        simpa [Real.norm_eq_abs] using hcoord
      exact hcoord_abs.trans hτ_norm
    have hcoef_nonneg : 0 ≤ section43QTimeCoordOpNorm d n k := by
      dsimp [section43QTimeCoordOpNorm]
      exact norm_nonneg _
    have hqk :
        |section43QTime (d := d) (n := n) q' k| ≤
          section43QTimeCoordOpNorm d n k * (‖q‖ + 1) := by
      have hbase := abs_section43QTime_coord_le_opNorm d n q' k
      have hbase' :
          |section43QTime (d := d) (n := n) q' k| ≤
            section43QTimeCoordOpNorm d n k * ‖q'‖ := by
        simpa [section43QTimeCoordOpNorm] using hbase
      exact hbase'.trans
        (mul_le_mul_of_nonneg_left hq_norm hcoef_nonneg)
    calc
      |τ k * section43QTime (d := d) (n := n) q' k| =
          |τ k| * |section43QTime (d := d) (n := n) q' k| := by
            rw [abs_mul]
      _ ≤ R * (section43QTimeCoordOpNorm d n k * (‖q‖ + 1)) := by
            exact mul_le_mul hτk hqk (abs_nonneg _) hR_nonneg
  have hsum_abs :
      -(∑ k : Fin n,
          τ k * section43QTime (d := d) (n := n) q' k) ≤
        ∑ k : Fin n,
          |τ k * section43QTime (d := d) (n := n) q' k| := by
    calc
      -(∑ k : Fin n,
          τ k * section43QTime (d := d) (n := n) q' k)
          ≤ |∑ k : Fin n,
              τ k * section43QTime (d := d) (n := n) q' k| := by
              exact neg_le_abs _
      _ ≤ ∑ k : Fin n,
          |τ k * section43QTime (d := d) (n := n) q' k| := by
              exact Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      ∑ k : Fin n,
          |τ k * section43QTime (d := d) (n := n) q' k| ≤
        ∑ k : Fin n,
          R * (section43QTimeCoordOpNorm d n k * (‖q‖ + 1)) := by
    exact Finset.sum_le_sum fun k _hk => hterm k
  have hsum_eval :
      (∑ k : Fin n,
          R * (section43QTimeCoordOpNorm d n k * (‖q‖ + 1))) =
        R * ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (‖q‖ + 1)) := by
    rw [← Finset.mul_sum, Finset.sum_mul]
  have hre :
      (-(∑ k : Fin n,
        (τ k : ℂ) *
          (section43QTime (d := d) (n := n) q' k : ℂ))).re =
        -(∑ k : Fin n,
          τ k * section43QTime (d := d) (n := n) q' k) := by
    simp
  rw [hre]
  exact hsum_abs.trans (hsum_bound.trans hsum_eval.le)

/-- On a one-sided collar, the Laplace exponential is controlled by shifting to
nonnegative times and paying the compact time-slab radius `R`. -/
theorem norm_exp_neg_timePair_le_exp_thickened_margin_sum
    (n : ℕ)
    {δ ε R : ℝ} (_hδ_pos : 0 < δ) (hε_nonneg : 0 ≤ ε)
    (_hR_nonneg : 0 ≤ R)
    (t τ : Fin n → ℝ)
    (ht : ∀ i : Fin n, -ε ≤ t i)
    (hτ_low : ∀ i : Fin n, δ ≤ τ i)
    (hτ_norm : ‖τ‖ ≤ R) :
    ‖Complex.exp (-(∑ k : Fin n, (τ k : ℂ) * (t k : ℂ)))‖ ≤
      Real.exp (∑ _ : Fin n, R * ε) *
        Real.exp (-(δ * ∑ k : Fin n, (t k + ε))) := by
  rw [Complex.norm_exp]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hterm : ∀ k : Fin n,
      δ * (t k + ε) - R * ε ≤ τ k * t k := by
    intro k
    have hu_nonneg : 0 ≤ t k + ε := by linarith [ht k]
    have hτ_abs : |τ k| ≤ R := by
      have hcoord : ‖τ k‖ ≤ ‖τ‖ := norm_le_pi_norm τ k
      have hcoord_abs : |τ k| ≤ ‖τ‖ := by
        simpa [Real.norm_eq_abs] using hcoord
      exact hcoord_abs.trans hτ_norm
    have hτ_le_R : τ k ≤ R := (le_abs_self (τ k)).trans hτ_abs
    have hδ_le : δ * (t k + ε) ≤ τ k * (t k + ε) := by
      exact mul_le_mul_of_nonneg_right (hτ_low k) hu_nonneg
    have hR_le : τ k * ε ≤ R * ε := by
      exact mul_le_mul_of_nonneg_right hτ_le_R hε_nonneg
    calc
      δ * (t k + ε) - R * ε ≤ τ k * (t k + ε) - τ k * ε := by
        linarith
      _ = τ k * t k := by ring
  have hsum :=
    Finset.sum_le_sum (s := Finset.univ) fun k _hk => hterm k
  have hsum_left :
      (∑ k : Fin n, (δ * (t k + ε) - R * ε)) =
        δ * (∑ k : Fin n, (t k + ε)) - ∑ _ : Fin n, R * ε := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum' : δ * (∑ k : Fin n, (t k + ε)) - ∑ _ : Fin n, R * ε ≤
      ∑ k : Fin n, τ k * t k := by
    simpa [hsum_left] using hsum
  have hmain :
      -(∑ k : Fin n, τ k * t k) ≤
        (∑ _ : Fin n, R * ε) + -(δ * ∑ k : Fin n, (t k + ε)) := by
    linarith
  have hre :
      (-(∑ k : Fin n, (τ k : ℂ) * (t k : ℂ))).re =
        -(∑ k : Fin n, τ k * t k) := by
    simp
  rw [hre]
  exact hmain

/-- Exponential damping in shifted nonnegative collar times dominates every
polynomial weight in the original collar time norm. -/
theorem exp_margin_sum_controls_thickened_time_polynomial
    (n : ℕ)
    {δ ε R : ℝ} (hδ_pos : 0 < δ) (_hε_nonneg : 0 ≤ ε)
    (_hR_nonneg : 0 ≤ R) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : Fin n → ℝ,
        (∀ i : Fin n, -ε ≤ t i) →
          (1 + ‖t‖) ^ s *
            (Real.exp (∑ _ : Fin n, R * ε) *
              Real.exp (-(δ * ∑ k : Fin n, (t k + ε)))) ≤ C := by
  rcases SCV.pow_mul_exp_neg_le_const hδ_pos s with ⟨C0, hC0_pos, hC0_bound⟩
  let e : Fin n → ℝ := fun _ => ε
  let B : ℝ := 1 + ‖e‖
  let K : ℝ := Real.exp (∑ _ : Fin n, R * ε)
  let C : ℝ := K * B ^ s * Real.exp δ * C0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht
  let u : Fin n → ℝ := fun i => t i + ε
  have hu_nonneg : ∀ i : Fin n, 0 ≤ u i := by
    intro i
    dsimp [u]
    linarith [ht i]
  have ht_eq : t = u - e := by
    funext i
    dsimp [u, e]
    ring
  have ht_norm_le : ‖t‖ ≤ ‖u‖ + ‖e‖ := by
    rw [ht_eq]
    exact norm_sub_le u e
  have hone_norm_t : 1 + ‖t‖ ≤ B * (1 + ‖u‖) := by
    calc
      1 + ‖t‖ ≤ 1 + (‖u‖ + ‖e‖) := by linarith
      _ ≤ B * (1 + ‖u‖) := by
          dsimp [B]
          nlinarith [norm_nonneg u, norm_nonneg e]
  have hpow_t : (1 + ‖t‖) ^ s ≤ (B * (1 + ‖u‖)) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hone_norm_t s
  have hsum_nonneg : 0 ≤ ∑ k : Fin n, u k :=
    Finset.sum_nonneg fun k _hk => hu_nonneg k
  have hnorm_u_le_sum : ‖u‖ ≤ ∑ k : Fin n, u k := by
    simpa using pi_norm_le_sum_of_nonneg (x := u) hu_nonneg
  have hone_norm_u_le : 1 + ‖u‖ ≤ 1 + ∑ k : Fin n, u k := by
    linarith
  have hpow_u : (1 + ‖u‖) ^ s ≤ (1 + ∑ k : Fin n, u k) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hone_norm_u_le s
  have htail := hC0_bound (1 + ∑ k : Fin n, u k) (by linarith)
  have hexp_eq :
      Real.exp (-(δ * ∑ k : Fin n, u k)) =
        Real.exp δ * Real.exp (-(δ * (1 + ∑ k : Fin n, u k))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htime_u :
      (1 + ‖u‖) ^ s * Real.exp (-(δ * ∑ k : Fin n, u k)) ≤
        Real.exp δ * C0 := by
    calc
      (1 + ‖u‖) ^ s * Real.exp (-(δ * ∑ k : Fin n, u k))
          ≤ (1 + ∑ k : Fin n, u k) ^ s *
              Real.exp (-(δ * ∑ k : Fin n, u k)) := by
            exact mul_le_mul_of_nonneg_right hpow_u (Real.exp_pos _).le
      _ = Real.exp δ *
            ((1 + ∑ k : Fin n, u k) ^ s *
              Real.exp (-(δ * (1 + ∑ k : Fin n, u k)))) := by
            rw [hexp_eq]
            ring
      _ ≤ Real.exp δ * C0 := by
            exact mul_le_mul_of_nonneg_left htail (Real.exp_pos δ).le
  have hright_nonneg : 0 ≤ K * Real.exp (-(δ * ∑ k : Fin n, u k)) := by
    positivity
  calc
    (1 + ‖t‖) ^ s *
        (Real.exp (∑ _ : Fin n, R * ε) *
          Real.exp (-(δ * ∑ k : Fin n, (t k + ε))))
        = (1 + ‖t‖) ^ s * (K * Real.exp (-(δ * ∑ k : Fin n, u k))) := by
          simp [K, u]
    _ ≤ (B * (1 + ‖u‖)) ^ s * (K * Real.exp (-(δ * ∑ k : Fin n, u k))) := by
          exact mul_le_mul_of_nonneg_right hpow_t hright_nonneg
    _ = K * B ^ s * ((1 + ‖u‖) ^ s * Real.exp (-(δ * ∑ k : Fin n, u k))) := by
          rw [mul_pow]
          ring
    _ ≤ K * B ^ s * (Real.exp δ * C0) := by
          exact mul_le_mul_of_nonneg_left htime_u
            (mul_nonneg hK_nonneg (pow_nonneg hB_nonneg s))
    _ = C := by
          simp [C, mul_assoc]

/-- In finite-dimensional domain, continuity of a family of continuous
multilinear maps is equivalent to continuity of all applied scalar families.

This is the multilinear analogue of Mathlib's `continuous_clm_apply`, proved
by repeatedly currying the leftmost variable. -/
theorem continuous_cmlm_apply_nPoint
    (d n r : ℕ) [NeZero d]
    {X : Type*} [TopologicalSpace X]
    {L : X →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ} :
    Continuous L ↔
      ∀ m : Fin r → NPointDomain d n, Continuous fun x => L x m := by
  induction r generalizing X with
  | zero =>
      constructor
      · intro hL m
        exact
          (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin 0 => NPointDomain d n) ℂ m).continuous.comp hL
      · intro h
        let e :=
          continuousMultilinearCurryFin0 ℝ (NPointDomain d n) ℂ
        have he : Continuous fun x => e (L x) := by
          simpa [e] using h (0 : Fin 0 → NPointDomain d n)
        have hback : Continuous fun x => e.symm (e (L x)) :=
          e.symm.continuous.comp he
        simpa [e] using hback
  | succ r ih =>
      constructor
      · intro hL m
        exact
          (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin (r + 1) => NPointDomain d n) ℂ m).continuous.comp hL
      · intro h
        let e :=
          continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (r + 1) => NPointDomain d n) ℂ
        have hcurry : Continuous fun x => e (L x) := by
          refine (continuous_clm_apply
            (𝕜 := ℝ) (E := NPointDomain d n)).2 ?_
          intro head
          refine (ih (L := fun x => e (L x) head)).2 ?_
          intro tail
          simpa [e, ContinuousMultilinearMap.curryLeft_apply] using
            h (Fin.cons head tail)
        have hback : Continuous fun x => e.symm (e (L x)) :=
          e.symm.continuous.comp hcurry
        simpa [e] using hback

/-- A fixed derivative word contributes a scalar factor depending continuously
on the real time variable. -/
theorem continuous_section43DerivativeWordScalar
    (d n r : ℕ) [NeZero d]
    (a : Section43DerivativeWord d n r)
    (m : Fin r → NPointDomain d n) :
    Continuous fun τ : Fin n → ℝ =>
      section43DerivativeWordScalar d n r a τ m := by
  induction r with
  | zero =>
      exact continuous_const
  | succ r ih =>
      cases h : a 0 with
      | time k =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          have hold : Continuous fun τ : Fin n → ℝ =>
              section43DerivativeWordScalar d n r oldWord τ oldDirections :=
            ih oldWord oldDirections
          have hτk : Continuous fun τ : Fin n → ℝ => (τ k : ℂ) :=
            Complex.continuous_ofReal.comp (continuous_apply k)
          have hqk : Continuous fun _τ : Fin n → ℝ =>
              (section43QTime (d := d) (n := n) (m 0) k : ℂ) :=
            continuous_const
          simpa [section43DerivativeWordScalar, h, oldWord, oldDirections, mul_assoc]
            using (hτk.mul (hqk.mul hold)).neg
      | spatial i =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          have hold : Continuous fun τ : Fin n → ℝ =>
              section43DerivativeWordScalar d n r oldWord τ oldDirections :=
            ih oldWord oldDirections
          have hhead : Continuous fun _τ : Fin n → ℝ =>
              ((section43QSpatial (d := d) (n := n) (m 0) i : ℝ) : ℂ) :=
            continuous_const
          simpa [section43DerivativeWordScalar, h, oldWord, oldDirections]
            using hhead.mul hold

set_option backward.isDefEq.respectTransparency false in
/-- Applied all-order pointwise derivatives are continuous in the real time
variable.  The proof uses the finite derivative-word expansion. -/
theorem continuous_section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (m : Fin r → NPointDomain d n) :
    Continuous fun τ : Fin n → ℝ =>
      iteratedFDeriv ℝ r
        (fun q' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
        q m := by
  classical
  let Efun : (Fin n → ℝ) → ℂ := fun τ =>
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  have hE : Continuous Efun := by
    dsimp [Efun]
    fun_prop
  have hsum : Continuous fun τ : Fin n → ℝ =>
      ∑ a : Section43DerivativeWord d n r,
        section43DerivativeWordScalar d n r a τ m *
          Efun τ *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43DerivativeWordInput d n r F a)
            (τ, section43QSpatial (d := d) (n := n) q) := by
    refine continuous_finset_sum Finset.univ fun a _ha => ?_
    have hscalar :=
      continuous_section43DerivativeWordScalar d n r a m
    have hP : Continuous fun τ : Fin n → ℝ =>
        partialFourierSpatial_fun (d := d) (n := n)
          (section43DerivativeWordInput d n r F a)
          (τ, section43QSpatial (d := d) (n := n) q) := by
      let hbase : Continuous
          (partialFourierSpatial_fun
            (d := d) (n := n) (section43DerivativeWordInput d n r F a)) :=
        continuous_partialFourierSpatial_fun
          (d := d) (n := n) (section43DerivativeWordInput d n r F a)
      let hpath : Continuous fun τ : Fin n → ℝ =>
          (τ, section43QSpatial (d := d) (n := n) q) :=
        continuous_id.prodMk continuous_const
      simpa using hbase.comp hpath
    exact (hscalar.mul hE).mul hP
  convert hsum using 1
  ext τ
  rw [section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply_eq_sum_words]

set_option backward.isDefEq.respectTransparency false in
/-- The CLM-valued all-order pointwise derivative is continuous in the real
time variable for fixed ambient momentum `q`. -/
theorem continuous_section43FourierLaplace_timeIntegrand_iteratedFDeriv
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n) :
    Continuous fun τ : Fin n → ℝ =>
      iteratedFDeriv ℝ r
        (fun q' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
        q := by
  refine (continuous_cmlm_apply_nPoint d n r).2 ?_
  intro m
  exact continuous_section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply
    d n r F q m

set_option backward.isDefEq.respectTransparency false in
/-- Compact local domination for the derivative of the pointwise all-order
Fourier-Laplace integrand.  This is the all-order analogue of the compiled
first-derivative local bound, but it uses the finite derivative-word majorant
instead of a separate joint-continuity compactness argument. -/
theorem section43FourierLaplace_timeIntegrand_iteratedFDeriv_curryLeft_local_bound_of_compact
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    ∃ bound : (Fin n → ℝ) → ℝ,
      Integrable bound ∧
      ∀ᵐ τ, ∀ q' ∈ Metric.closedBall q (1 : ℝ),
        ‖(iteratedFDeriv ℝ (r + 1)
          (fun q'' : NPointDomain d n =>
            Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) *
                  (section43QTime (d := d) (n := n) q'' k : ℂ))) *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
              (τ, section43QSpatial (d := d) (n := n) q''))
          q').curryLeft‖ ≤ bound τ := by
  classical
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    d n f hf_ord hf_compact with ⟨R, hR_nonneg, hR_supp⟩
  let Kτ : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  choose Cword hCword_nonneg hCword_bound using
    fun a : Section43DerivativeWord d n (r + 1) =>
      exists_norm_bound_partialFourierSpatial_fun
        (d := d) (n := n) (section43DerivativeWordInput d n (r + 1) F a)
  let Cexp : ℝ :=
    Real.exp
      (R * ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
        (‖q‖ + 1)))
  let Csum : ℝ :=
    ∑ a : Section43DerivativeWord d n (r + 1),
      section43DerivativeWordCoeff d n (r + 1) a *
        R ^ section43DerivativeWordTimeCount d n (r + 1) a *
        Cword a
  let C : ℝ := Cexp * Csum
  refine ⟨Set.indicator Kτ (fun _ => C), ?_, ?_⟩
  · simpa [Kτ, C] using integrable_indicator_time_closedBall_const n R C
  · filter_upwards with τ q' hq'
    by_cases hτ_mem : τ ∈ Kτ
    · rw [Set.indicator_of_mem hτ_mem]
      have hτ_norm : ‖τ‖ ≤ R := by
        simpa [Kτ] using norm_le_of_mem_time_closedBall_zero n τ hτ_mem
      have hExp :
          ‖Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ)))‖ ≤ Cexp := by
        simpa [Cexp, Kτ] using
          norm_exp_neg_section43_timePair_le_local_closedBall
            d n q q' τ hR_nonneg hτ_mem hq'
      have hsum :
          (∑ a : Section43DerivativeWord d n (r + 1),
            section43DerivativeWordCoeff d n (r + 1) a *
              ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43DerivativeWordInput d n (r + 1) F a)
                (τ, section43QSpatial (d := d) (n := n) q')‖) ≤ Csum := by
        dsimp [Csum]
        refine Finset.sum_le_sum ?_
        intro a _ha
        let K : ℕ := section43DerivativeWordTimeCount d n (r + 1) a
        have hcoeff_nonneg :
            0 ≤ section43DerivativeWordCoeff d n (r + 1) a :=
          section43DerivativeWordCoeff_nonneg d n (r + 1) a
        have hpow : ‖τ‖ ^ K ≤ R ^ K := by
          exact pow_le_pow_left₀ (norm_nonneg τ) hτ_norm K
        have hP :
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43DerivativeWordInput d n (r + 1) F a)
              (τ, section43QSpatial (d := d) (n := n) q')‖ ≤ Cword a :=
          hCword_bound a (τ, section43QSpatial (d := d) (n := n) q')
        have hpowP :
            ‖τ‖ ^ K *
                ‖partialFourierSpatial_fun (d := d) (n := n)
                  (section43DerivativeWordInput d n (r + 1) F a)
                  (τ, section43QSpatial (d := d) (n := n) q')‖ ≤
              R ^ K * Cword a := by
          exact mul_le_mul hpow hP (norm_nonneg _) (pow_nonneg hR_nonneg K)
        have hmul := mul_le_mul_of_nonneg_left hpowP hcoeff_nonneg
        simpa [K, mul_assoc] using hmul
      have hsum_nonneg : 0 ≤
          ∑ a : Section43DerivativeWord d n (r + 1),
            section43DerivativeWordCoeff d n (r + 1) a *
              ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43DerivativeWordInput d n (r + 1) F a)
                (τ, section43QSpatial (d := d) (n := n) q')‖ := by
        refine Finset.sum_nonneg ?_
        intro a _ha
        exact mul_nonneg
          (mul_nonneg (section43DerivativeWordCoeff_nonneg d n (r + 1) a)
            (pow_nonneg (norm_nonneg τ) _))
          (norm_nonneg _)
      have hmain :=
        norm_section43FourierLaplace_timeIntegrand_iteratedFDeriv_le_sum_words_absExp
          d n (r + 1) F q' τ
      have hnorm :
          ‖(iteratedFDeriv ℝ (r + 1)
            (fun q'' : NPointDomain d n =>
              Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q'' k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n) F
                (τ, section43QSpatial (d := d) (n := n) q''))
            q').curryLeft‖ ≤
            Cexp * Csum := by
        calc
          ‖(iteratedFDeriv ℝ (r + 1)
            (fun q'' : NPointDomain d n =>
              Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q'' k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n) F
                (τ, section43QSpatial (d := d) (n := n) q''))
            q').curryLeft‖ =
              ‖iteratedFDeriv ℝ (r + 1)
                (fun q'' : NPointDomain d n =>
                  Complex.exp
                    (-(∑ k : Fin n,
                      (τ k : ℂ) *
                        (section43QTime (d := d) (n := n) q'' k : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n) F
                    (τ, section43QSpatial (d := d) (n := n) q''))
                q'‖ := by
                rw [ContinuousMultilinearMap.curryLeft_norm]
          _ ≤
              ‖Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q' k : ℂ)))‖ *
                ∑ a : Section43DerivativeWord d n (r + 1),
                  section43DerivativeWordCoeff d n (r + 1) a *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
                    ‖partialFourierSpatial_fun (d := d) (n := n)
                      (section43DerivativeWordInput d n (r + 1) F a)
                      (τ, section43QSpatial (d := d) (n := n) q')‖ := hmain
          _ ≤ Cexp * Csum := by
                exact mul_le_mul hExp hsum hsum_nonneg (Real.exp_pos _).le
      simpa [C, F] using hnorm
    · rw [Set.indicator_of_notMem hτ_mem]
      have hdist_not : ¬ dist τ (0 : Fin n → ℝ) ≤ R := by
        simpa [Kτ, Metric.mem_closedBall] using hτ_mem
      have hlt_dist : R < dist τ (0 : Fin n → ℝ) := lt_of_not_ge hdist_not
      have hlt : R < ‖τ‖ := by
        simpa [dist_eq_norm, sub_zero] using hlt_dist
      have hzero_fun :=
        section43FourierLaplace_timeIntegrand_iteratedFDeriv_eq_zero_of_timeNorm_gt_bound
          d n (r + 1) f hf_ord hR_supp τ hlt
      have hzero_at :
          iteratedFDeriv ℝ (r + 1)
            (fun q'' : NPointDomain d n =>
              Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q'' k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n)
                (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
                (τ, section43QSpatial (d := d) (n := n) q''))
            q' = 0 := by
        simpa using congrFun hzero_fun q'
      simp [hzero_at]

set_option backward.isDefEq.respectTransparency false in
/-- Under compact ordered support, the fixed-`q` all-order pointwise derivative
is Bochner-integrable in the real time variable. -/
theorem integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    Integrable
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun q' : NPointDomain d n =>
            Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) *
                  (section43QTime (d := d) (n := n) q' k : ℂ))) *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
              (τ, section43QSpatial (d := d) (n := n) q'))
          q) := by
  classical
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  have hmeas : AEStronglyMeasurable
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun q' : NPointDomain d n =>
            Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) *
                  (section43QTime (d := d) (n := n) q' k : ℂ))) *
            partialFourierSpatial_fun (d := d) (n := n) F
              (τ, section43QSpatial (d := d) (n := n) q'))
          q) :=
    (continuous_section43FourierLaplace_timeIntegrand_iteratedFDeriv
      d n r F q).aestronglyMeasurable
  cases r with
  | zero =>
      let e :=
        continuousMultilinearCurryFin0 ℝ (NPointDomain d n) ℂ
      have hbase :
          Integrable
            (fun τ : Fin n → ℝ =>
              Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n)
                (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
                (τ, section43QSpatial (d := d) (n := n) q)) :=
        integrable_section43FourierLaplace_timeIntegrand_of_compact
          d n f hf_ord hf_compact q
      have hcomp :
          Integrable
            (fun τ : Fin n → ℝ =>
              e.symm
                (Complex.exp
                  (-(∑ k : Fin n,
                    (τ k : ℂ) *
                      (section43QTime (d := d) (n := n) q k : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
                  (τ, section43QSpatial (d := d) (n := n) q))) :=
        (e.symm : ℂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin 0 => NPointDomain d n) ℂ).integrable_comp hbase
      convert hcomp using 1
  | succ r =>
      rcases
        section43FourierLaplace_timeIntegrand_iteratedFDeriv_curryLeft_local_bound_of_compact
          d n r f hf_ord hf_compact q with
        ⟨bound, hbound_int, hbound⟩
      have hq_self : q ∈ Metric.closedBall q (1 : ℝ) := by
        simp [Metric.mem_closedBall]
      refine Integrable.mono' hbound_int ?_ ?_
      · simpa [F] using hmeas
      · exact hbound.mono fun τ hτ => by
          have hτq := hτ q hq_self
          simpa [F, ContinuousMultilinearMap.curryLeft_norm] using hτq

set_option backward.isDefEq.respectTransparency false in
/-- The curry-left pointwise derivative appearing in the dominated derivative
theorem is aestrongly measurable in the real time variable. -/
theorem aestronglyMeasurable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_curryLeft
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    AEStronglyMeasurable
      (fun τ : Fin n → ℝ =>
        (iteratedFDeriv ℝ (r + 1)
          (fun q' : NPointDomain d n =>
            Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) *
                  (section43QTime (d := d) (n := n) q' k : ℂ))) *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
              (τ, section43QSpatial (d := d) (n := n) q'))
          q).curryLeft) := by
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  let e :=
    continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (r + 1) => NPointDomain d n) ℂ
  have hint :
      Integrable
        (fun τ : Fin n → ℝ =>
          iteratedFDeriv ℝ (r + 1)
            (fun q' : NPointDomain d n =>
              Complex.exp
                (-(∑ k : Fin n,
                  (τ k : ℂ) *
                    (section43QTime (d := d) (n := n) q' k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n) F
                (τ, section43QSpatial (d := d) (n := n) q'))
            q) := by
    simpa [F] using
      integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
        d n (r + 1) f hf_ord hf_compact q
  have hmeas : AEStronglyMeasurable fun τ : Fin n → ℝ =>
      e (iteratedFDeriv ℝ (r + 1)
        (fun q' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
        q) :=
    e.continuous.comp_aestronglyMeasurable hint.aestronglyMeasurable
  simpa [F, e] using hmeas

set_option maxHeartbeats 220000 in
set_option backward.isDefEq.respectTransparency false in
/-- Under compact ordered support, the integrated all-order derivative
candidate has derivative given by the curry-left of the next integrated
candidate. -/
theorem section43FourierLaplaceIntegral_iteratedFDerivCandidate_hasFDerivAt_of_compact_orderedSupport
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    HasFDerivAt
      (fun q' : NPointDomain d n =>
        section43FourierLaplaceIntegral_iteratedFDerivCandidate
          d n r f hf_ord q')
      ((section43FourierLaplaceIntegral_iteratedFDerivCandidate
        d n (r + 1) f hf_ord q).curryLeft)
      q := by
  classical
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  let Fint : NPointDomain d n → (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ :=
    fun q' τ =>
      iteratedFDeriv ℝ r
        (fun q'' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q'' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q''))
        q'
  let Fderiv : NPointDomain d n → (Fin n → ℝ) →
      NPointDomain d n →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ :=
    fun q' τ =>
      (iteratedFDeriv ℝ (r + 1)
        (fun q'' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q'' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q''))
        q').curryLeft
  rcases
    section43FourierLaplace_timeIntegrand_iteratedFDeriv_curryLeft_local_bound_of_compact
      d n r f hf_ord hf_compact q with
    ⟨bound, hbound_int, hbound⟩
  have hs : Metric.closedBall q (1 : ℝ) ∈ 𝓝 q :=
    Metric.closedBall_mem_nhds q zero_lt_one
  have hF_meas : ∀ᶠ q' in 𝓝 q, AEStronglyMeasurable (Fint q') := by
    exact Filter.Eventually.of_forall fun q' =>
      (integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
        d n r f hf_ord hf_compact q').aestronglyMeasurable
  have hF_int : Integrable (Fint q) := by
    simpa [Fint, F] using
      integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
        d n r f hf_ord hf_compact q
  have hbound' : ∀ᵐ τ : Fin n → ℝ, ∀ q' ∈ Metric.closedBall q (1 : ℝ),
      ‖Fderiv q' τ‖ ≤ bound τ := by
    simpa [Fderiv, F] using hbound
  have hq_self : q ∈ Metric.closedBall q (1 : ℝ) := by
    simp [Metric.mem_closedBall]
  let Phi : (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin (r + 1) => NPointDomain d n) ℂ :=
    fun τ =>
      iteratedFDeriv ℝ (r + 1)
        (fun q'' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q'' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q''))
        q
  have hnext_int :
      @Integrable
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => NPointDomain d n) ℂ)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        SeminormedAddGroup.toContinuousENorm
        (Fin n → ℝ) _ Phi volume := by
    simpa [F] using
      integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
        d n (r + 1) f hf_ord hf_compact q
  have hcurry_lipschitz :
      LipschitzWith 1
        (fun L : ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => NPointDomain d n) ℂ =>
          L.curryLeft) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro L M
    simp only [NNReal.coe_one, one_mul]
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : L.curryLeft - M.curryLeft = (L - M).curryLeft := by
      ext v mtail
      simp [ContinuousMultilinearMap.curryLeft_apply]
    rw [hsub, ContinuousMultilinearMap.curryLeft_norm]
  have hFderiv_int :
      @Integrable
        (NPointDomain d n →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        SeminormedAddGroup.toContinuousENorm
        (Fin n → ℝ) _ (Fderiv q) volume := by
    refine Integrable.mono
      (f := Fderiv q)
      (g := Phi)
      hnext_int ?_ ?_
    · have hmeas :
          AEStronglyMeasurable
            (fun τ : Fin n → ℝ => (Phi τ).curryLeft) :=
          hcurry_lipschitz.continuous.comp_aestronglyMeasurable
            hnext_int.aestronglyMeasurable
      simpa [Fderiv, Phi] using hmeas
    · filter_upwards with τ
      simp [Fderiv, Phi, ContinuousMultilinearMap.curryLeft_norm]
  have hFderiv_meas := hFderiv_int.aestronglyMeasurable
  have hdiff : ∀ᵐ τ : Fin n → ℝ, ∀ q' ∈ Metric.closedBall q (1 : ℝ),
      HasFDerivAt (Fint · τ) (Fderiv q' τ) q' := by
    filter_upwards with τ q' _hq'
    simpa [Fint, Fderiv, F] using
      hasFDerivAt_section43FourierLaplace_timeIntegrand_iteratedFDeriv_curryLeft
        d n r F q' τ
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume)
      (F := Fint) (F' := Fderiv) (x₀ := q)
      (s := Metric.closedBall q (1 : ℝ)) (bound := bound)
      hs hF_meas hF_int hFderiv_meas hbound' hbound_int hdiff
  have hderivIntegral :
      (∫ τ : Fin n → ℝ, Fderiv q τ) =
        ((∫ τ : Fin n → ℝ, Phi τ).curryLeft) := by
    letI : SeminormedAddCommGroup
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => NPointDomain d n) ℂ) :=
      NormedAddCommGroup.toSeminormedAddCommGroup
    letI : SeminormedAddCommGroup
        (NPointDomain d n →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ) :=
      NormedAddCommGroup.toSeminormedAddCommGroup
    let curryLI :
        ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => NPointDomain d n) ℂ →ₗᵢ[ℝ]
          (NPointDomain d n →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ) :=
      { toLinearMap :=
          { toFun := fun L => L.curryLeft
            map_add' := by
              intro L M
              rfl
            map_smul' := by
              intro c L
              rfl }
        norm_map' := by
          intro L
          exact ContinuousMultilinearMap.curryLeft_norm L }
    haveI : CompleteSpace
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => NPointDomain d n) ℂ) := inferInstance
    change (∫ τ : Fin n → ℝ, curryLI (Phi τ)) =
      curryLI (∫ τ : Fin n → ℝ, Phi τ)
    exact
      (ContinuousLinearMap.integral_comp_comm
          (𝕜 := ℝ)
          (E := ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => NPointDomain d n) ℂ)
          (Fₗ := NPointDomain d n →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ)
          (X := Fin n → ℝ)
          (μ := volume)
          curryLI.toContinuousLinearMap hnext_int)
  rw [hderivIntegral] at hmain
  simpa [section43FourierLaplaceIntegral_iteratedFDerivCandidate,
    Fint, Fderiv, F] using hmain

set_option backward.isDefEq.respectTransparency false in
/-- Under compact ordered support, the iterated derivatives of the
Fourier-Laplace integral are the integrated pointwise derivative candidates. -/
theorem section43FourierLaplaceIntegral_iteratedFDeriv_eq_candidate_of_compact_orderedSupport
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q')
      q =
      section43FourierLaplaceIntegral_iteratedFDerivCandidate
        d n r f hf_ord q := by
  classical
  let G : NPointDomain d n → ℂ := fun q' =>
    section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q'
  induction r generalizing q with
  | zero =>
      ext m
      have hint :
          Integrable
            (fun τ : Fin n → ℝ =>
              iteratedFDeriv ℝ 0
                (fun q' : NPointDomain d n =>
                  Complex.exp
                    (-(∑ k : Fin n,
                      (τ k : ℂ) *
                        (section43QTime (d := d) (n := n) q' k : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
                    (τ, section43QSpatial (d := d) (n := n) q'))
                q) := by
        simpa using
          integrable_section43FourierLaplace_timeIntegrand_iteratedFDeriv_of_compact
            d n 0 f hf_ord hf_compact q
      change
        section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q =
          (∫ τ : Fin n → ℝ,
            iteratedFDeriv ℝ 0
              (fun q' : NPointDomain d n =>
                Complex.exp
                  (-(∑ k : Fin n,
                    (τ k : ℂ) *
                      (section43QTime (d := d) (n := n) q' k : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
                  (τ, section43QSpatial (d := d) (n := n) q'))
              q) m
      rw [ContinuousMultilinearMap.integral_apply hint m]
      simp [section43FourierLaplaceIntegral, iteratedFDeriv_zero_apply]
  | succ r ih =>
      have hfun :
          iteratedFDeriv ℝ r G =
          fun q' : NPointDomain d n =>
            section43FourierLaplaceIntegral_iteratedFDerivCandidate
              d n r f hf_ord q' := by
        funext q'
        simpa [G] using ih q'
      have hfd :
          fderiv ℝ (iteratedFDeriv ℝ r G) q =
            (section43FourierLaplaceIntegral_iteratedFDerivCandidate
              d n (r + 1) f hf_ord q).curryLeft := by
        have hderiv :=
          section43FourierLaplaceIntegral_iteratedFDerivCandidate_hasFDerivAt_of_compact_orderedSupport
            d n r f hf_ord hf_compact q
        rw [hfun]
        exact hderiv.fderiv
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfd]
      exact ContinuousMultilinearMap.uncurry_curryLeft _

set_option backward.isDefEq.respectTransparency false in
/-- Under compact ordered support, the Section 4.3 Fourier-Laplace integral is
ambient smooth in the positive-energy variable. -/
theorem section43FourierLaplaceIntegral_contDiff_of_compact_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : NPointDomain d n =>
        section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q) := by
  classical
  let G : NPointDomain d n → ℂ := fun q =>
    section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q
  change ContDiff ℝ (↑(⊤ : ℕ∞)) G
  refine contDiff_of_differentiable_iteratedFDeriv
    (𝕜 := ℝ) (E := NPointDomain d n) (F := ℂ) (f := G) (n := (⊤ : ℕ∞)) ?_
  intro r _hr
  have hfun :
      iteratedFDeriv ℝ r G =
      fun q : NPointDomain d n =>
        section43FourierLaplaceIntegral_iteratedFDerivCandidate
          d n r f hf_ord q := by
    funext q
    simpa [G] using
      section43FourierLaplaceIntegral_iteratedFDeriv_eq_candidate_of_compact_orderedSupport
        d n r f hf_ord hf_compact q
  rw [hfun]
  intro q
  exact
    (section43FourierLaplaceIntegral_iteratedFDerivCandidate_hasFDerivAt_of_compact_orderedSupport
      d n r f hf_ord hf_compact q).differentiableAt

set_option backward.isDefEq.respectTransparency false in
/-- Rapid decay of the actual all-order derivatives of the Section 4.3
Fourier-Laplace integral on the positive-energy half-space. -/
theorem section43FourierLaplaceIntegral_iteratedFDeriv_rapid_on_positiveEnergy
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖q‖) ^ s *
          ‖iteratedFDeriv ℝ r
            (fun q' : NPointDomain d n =>
              section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q')
            q‖ ≤ C := by
  intro s
  rcases
    section43FourierLaplaceIntegral_iteratedFDerivCandidate_rapid_on_positiveEnergy
      d n r f hf_ord hδ_pos hδ_supp s with
    ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro q hq
  rw [section43FourierLaplaceIntegral_iteratedFDeriv_eq_candidate_of_compact_orderedSupport
    d n r f hf_ord hf_compact q]
  exact hC_bound q hq

/-- A positive-energy Schwartz witness is an ambient smooth function whose
all ambient derivatives have rapid bounds when restricted to the
positive-energy half-space.

The ambient derivative formulation is deliberately stronger than an intrinsic
`iteratedFDerivWithin` formulation on the closed half-space.  It matches the
compiled Fourier-Laplace estimates and is the surface needed for the later
closed-half-space Schwartz extension theorem. -/
structure Section43PositiveEnergySchwartzWitness
    (d n : ℕ) [NeZero d] (F : NPointDomain d n → ℂ) : Prop where
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) F
  rapid :
    ∀ r s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖q‖) ^ s * ‖iteratedFDeriv ℝ r F q‖ ≤ C

/-- The compact ordered-support Fourier-Laplace integral supplies the
positive-energy Schwartz witness needed for the Section 4.3 representative
extension step. -/
theorem section43FourierLaplaceIntegral_positiveEnergySchwartzWitness_of_compact_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    Section43PositiveEnergySchwartzWitness d n
      (fun q : NPointDomain d n =>
        section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q) := by
  refine ⟨?_, ?_⟩
  · exact section43FourierLaplaceIntegral_contDiff_of_compact_orderedSupport
      d n f hf_ord hf_compact
  · intro r s
    exact section43FourierLaplaceIntegral_iteratedFDeriv_rapid_on_positiveEnergy
      d n r f hf_ord hf_compact hδ_pos hδ_supp s

/-- One-sided collar of the Section 4.3 positive-energy half-space. -/
def section43PositiveEnergyThickening (d n : ℕ) [NeZero d] (ε : ℝ) :
    Set (NPointDomain d n) :=
  {q | ∀ i : Fin n, -ε ≤ section43QTime (d := d) (n := n) q i}

/-- Positive energy is contained in every nonnegative one-sided collar. -/
theorem section43PositiveEnergyRegion_subset_thickening
    (d n : ℕ) [NeZero d] {ε : ℝ} (hε : 0 ≤ ε) :
    section43PositiveEnergyRegion d n ⊆ section43PositiveEnergyThickening d n ε := by
  intro q hq i
  have hqi : 0 ≤ section43QTime (d := d) (n := n) q i := by
    simpa [section43PositiveEnergyRegion, section43QTime, nPointTimeSpatialCLE] using hq i
  linarith

/-- Product cutoff in the Section 4.3 time variables.  It is identically `1`
on the positive-energy half-space and vanishes once any time coordinate is
at most `-1`. -/
noncomputable def section43PositiveEnergyCutoff (d n : ℕ) [NeZero d] :
    NPointDomain d n → ℂ :=
  fun q => ∏ i : Fin n, (SCV.smoothCutoff (section43QTime (d := d) (n := n) q i) : ℂ)

/-- The positive-energy cutoff is exactly `1` on the positive-energy region. -/
theorem section43PositiveEnergyCutoff_eq_one_of_mem
    (d n : ℕ) [NeZero d]
    {q : NPointDomain d n}
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    section43PositiveEnergyCutoff d n q = 1 := by
  rw [section43PositiveEnergyCutoff]
  apply Finset.prod_eq_one
  intro i _hi
  have hi : 0 ≤ section43QTime (d := d) (n := n) q i := by
    simpa [section43PositiveEnergyRegion, section43QTime, nPointTimeSpatialCLE] using hq i
  rw [SCV.smoothCutoff_one_of_nonneg hi]
  simp

/-- The positive-energy cutoff vanishes when one time coordinate lies at or
below `-1`. -/
theorem section43PositiveEnergyCutoff_eq_zero_of_time_le_neg_one
    (d n : ℕ) [NeZero d]
    {q : NPointDomain d n} {i : Fin n}
    (hi : section43QTime (d := d) (n := n) q i ≤ -1) :
    section43PositiveEnergyCutoff d n q = 0 := by
  rw [section43PositiveEnergyCutoff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    rw [SCV.smoothCutoff_zero_of_le_neg_one hi]
    simp)

/-- The positive-energy cutoff vanishes outside the unit one-sided collar. -/
theorem section43PositiveEnergyCutoff_eq_zero_of_not_mem_thickening_one
    (d n : ℕ) [NeZero d]
    {q : NPointDomain d n}
    (hq : q ∉ section43PositiveEnergyThickening d n 1) :
    section43PositiveEnergyCutoff d n q = 0 := by
  rw [section43PositiveEnergyThickening] at hq
  rcases not_forall.mp hq with ⟨i, hi_not⟩
  have hi : section43QTime (d := d) (n := n) q i < -1 := not_le.mp hi_not
  exact section43PositiveEnergyCutoff_eq_zero_of_time_le_neg_one
    d n (le_of_lt hi)

/-- The product cutoff is ambient smooth. -/
theorem section43PositiveEnergyCutoff_contDiff
    (d n : ℕ) [NeZero d] :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43PositiveEnergyCutoff d n) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun q : NPointDomain d n =>
      ∏ i : Fin n, (SCV.smoothCutoff (section43QTime (d := d) (n := n) q i) : ℂ))
  apply contDiff_prod
  intro i _hi
  have hcoord :
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun q : NPointDomain d n => section43QTime (d := d) (n := n) q i) := by
    simpa [section43QTimeCLM_apply] using
      (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i).comp
        (section43QTimeCLM d n)).contDiff :
        ContDiff ℝ (↑(⊤ : ℕ∞))
          (fun q : NPointDomain d n =>
            ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i).comp
              (section43QTimeCLM d n)) q))
  exact Complex.ofRealCLM.contDiff.comp (SCV.smoothCutoff_contDiff.comp hcoord)

/-- The positive-energy cutoff has temperate growth. -/
theorem section43PositiveEnergyCutoff_hasTemperateGrowth
    (d n : ℕ) [NeZero d] :
    Function.HasTemperateGrowth (section43PositiveEnergyCutoff d n) := by
  classical
  change Function.HasTemperateGrowth
    (fun q : NPointDomain d n =>
      ∏ i : Fin n, (SCV.smoothCutoff (section43QTime (d := d) (n := n) q i) : ℂ))
  let factor : Fin n → NPointDomain d n → ℂ := fun i q =>
    (SCV.smoothCutoff (section43QTime (d := d) (n := n) q i) : ℂ)
  have hfactor : ∀ i : Fin n, Function.HasTemperateGrowth (factor i) := by
    intro i
    have hcoord : Function.HasTemperateGrowth
        (fun q : NPointDomain d n => section43QTime (d := d) (n := n) q i) := by
      simpa [section43QTimeCLM_apply] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i).comp
          (section43QTimeCLM d n)).hasTemperateGrowth)
    simpa [factor, Function.comp_def] using
      SCV.smoothCutoff_complex_hasTemperateGrowth.comp hcoord
  have hprod : Function.HasTemperateGrowth
      (fun q : NPointDomain d n => ∏ i : Fin n, factor i q) := by
    let P : Finset (Fin n) → Prop := fun s =>
      Function.HasTemperateGrowth (fun q : NPointDomain d n => ∏ i ∈ s, factor i q)
    change P Finset.univ
    refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?empty ?insert
    · simp [P, Function.HasTemperateGrowth.const]
    · intro a s has ih
      have ha : Function.HasTemperateGrowth (factor a) := hfactor a
      have hs : Function.HasTemperateGrowth
          (fun q : NPointDomain d n => ∏ i ∈ s, factor i q) := ih
      simpa [P, Finset.prod_insert has] using ha.mul hs
  simpa [factor] using hprod

/-- Every derivative of the positive-energy cutoff vanishes outside the unit
one-sided collar. -/
theorem section43PositiveEnergyCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
    (d n r : ℕ) [NeZero d]
    {q : NPointDomain d n}
    (hq : q ∉ section43PositiveEnergyThickening d n 1) :
    iteratedFDeriv ℝ r (section43PositiveEnergyCutoff d n) q = 0 := by
  rw [section43PositiveEnergyThickening] at hq
  rcases not_forall.mp hq with ⟨i, hi_not⟩
  have hi : section43QTime (d := d) (n := n) q i < -1 := not_le.mp hi_not
  have hcoord_cont : Continuous fun q' : NPointDomain d n =>
      section43QTime (d := d) (n := n) q' i := by
    simpa [section43QTimeCLM_apply] using
      (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i).comp
        (section43QTimeCLM d n)).continuous)
  have hlt_event : ∀ᶠ q' in 𝓝 q,
      section43QTime (d := d) (n := n) q' i < -1 := by
    exact (isOpen_lt hcoord_cont continuous_const).mem_nhds hi
  have hzero_event : section43PositiveEnergyCutoff d n =ᶠ[𝓝 q] 0 := by
    filter_upwards [hlt_event] with q' hq'
    exact section43PositiveEnergyCutoff_eq_zero_of_time_le_neg_one d n
      (i := i) (le_of_lt hq')
  exact iteratedFDeriv_eq_zero_of_eventuallyEq_zero hzero_event r

/-- The support of every derivative of the positive-energy cutoff is contained
in the unit one-sided collar. -/
theorem section43PositiveEnergyCutoff_iteratedFDeriv_support_subset_thickening_one
    (d n r : ℕ) [NeZero d] :
    ∀ q : NPointDomain d n,
      iteratedFDeriv ℝ r (section43PositiveEnergyCutoff d n) q ≠ 0 →
        q ∈ section43PositiveEnergyThickening d n 1 := by
  intro q hq_nonzero
  by_contra hq
  exact hq_nonzero
    (section43PositiveEnergyCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
      d n r hq)

set_option backward.isDefEq.respectTransparency false in
/-- On a one-sided positive-energy collar, the all-order derivative candidate
is bounded by the compact-slab exponential majorant times the usual integrated
finite-word majorant. -/
theorem section43FourierLaplaceIntegral_iteratedFDerivCandidate_norm_le_thickened_exp_word_integrals_of_timeNorm_bound
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ ε R : ℝ}
    (hδ_pos : 0 < δ) (hε_nonneg : 0 ≤ ε) (hR_nonneg : 0 ≤ R)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (hR_supp :
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyThickening d n ε) :
    let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
    let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
    let E : ℝ :=
      Real.exp (∑ _ : Fin n, R * ε) *
        Real.exp (-(δ * ∑ k : Fin n, (t k + ε)))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
      d n r f hf_ord q‖ ≤
      E *
        section43FourierLaplace_iteratedFDerivWordMajorantIntegral
          d n r F ξ := by
  intro F t E ξ
  let G : (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => NPointDomain d n) ℂ :=
    fun τ =>
      iteratedFDeriv ℝ r
        (fun q' : NPointDomain d n =>
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
        q
  let Jfun : (Fin n → ℝ) → ℝ :=
    section43FourierLaplace_iteratedFDerivWordMajorant d n r F ξ
  have hJ_int : Integrable Jfun (volume : Measure (Fin n → ℝ)) := by
    simpa [Jfun, F, ξ] using
      integrable_section43FourierLaplace_iteratedFDerivWordMajorant
        d n r F ξ
  have hEJ_int :
      Integrable (fun τ : Fin n → ℝ => E * Jfun τ)
        (volume : Measure (Fin n → ℝ)) :=
    hJ_int.const_mul E
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hJfun_nonneg : ∀ τ : Fin n → ℝ, 0 ≤ Jfun τ := by
    intro τ
    dsimp [Jfun, section43FourierLaplace_iteratedFDerivWordMajorant]
    refine Finset.sum_nonneg ?_
    intro a _ha
    exact mul_nonneg
      (mul_nonneg (section43DerivativeWordCoeff_nonneg d n r a)
        (pow_nonneg (norm_nonneg τ) _))
      (norm_nonneg _)
  have hpoint : ∀ τ : Fin n → ℝ, ‖G τ‖ ≤ E * Jfun τ := by
    intro τ
    by_cases hlow : ∃ i : Fin n, τ i < δ
    · have hzero_fun :=
        section43FourierLaplace_timeIntegrand_iteratedFDeriv_eq_zero_of_exists_time_lt_margin
          d n r f hf_ord hδ_supp τ hlow
      have hzero : G τ = 0 := by
        simpa [G, F] using congrFun hzero_fun q
      calc
        ‖G τ‖ = 0 := by simp [hzero]
        _ ≤ E * Jfun τ := mul_nonneg hE_nonneg (hJfun_nonneg τ)
    · by_cases hhigh : R < ‖τ‖
      · have hzero_fun :=
          section43FourierLaplace_timeIntegrand_iteratedFDeriv_eq_zero_of_timeNorm_gt_bound
            d n r f hf_ord hR_supp τ hhigh
        have hzero : G τ = 0 := by
          simpa [G, F] using congrFun hzero_fun q
        calc
          ‖G τ‖ = 0 := by simp [hzero]
          _ ≤ E * Jfun τ := mul_nonneg hE_nonneg (hJfun_nonneg τ)
      · have hτ_low_all : ∀ i : Fin n, δ ≤ τ i := by
          intro i
          exact le_of_not_gt fun hi => hlow ⟨i, hi⟩
        have hτ_norm : ‖τ‖ ≤ R := le_of_not_gt hhigh
        have ht_collar : ∀ i : Fin n, -ε ≤ t i := by
          intro i
          simpa [section43PositiveEnergyThickening, t] using hq i
        have hExp :
            ‖Complex.exp (-(∑ k : Fin n, (τ k : ℂ) * (t k : ℂ)))‖ ≤ E := by
          simpa [E, t] using
            norm_exp_neg_timePair_le_exp_thickened_margin_sum
              n hδ_pos hε_nonneg hR_nonneg t τ ht_collar hτ_low_all hτ_norm
        have hmain :=
          norm_section43FourierLaplace_timeIntegrand_iteratedFDeriv_le_sum_words_absExp
            d n r F q τ
        calc
          ‖G τ‖ ≤
              ‖Complex.exp (-(∑ k : Fin n, (τ k : ℂ) * (t k : ℂ)))‖ * Jfun τ := by
                simpa [G, Jfun, F, ξ, t] using hmain
          _ ≤ E * Jfun τ := by
                exact mul_le_mul_of_nonneg_right hExp (hJfun_nonneg τ)
  calc
    ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
        d n r f hf_ord q‖ =
        ‖∫ τ : Fin n → ℝ, G τ‖ := by
          simp [section43FourierLaplaceIntegral_iteratedFDerivCandidate, G, F]
    _ ≤ ∫ τ : Fin n → ℝ, ‖G τ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ τ : Fin n → ℝ, E * Jfun τ := by
        exact MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun τ => norm_nonneg (G τ))
          hEJ_int
          (Filter.Eventually.of_forall hpoint)
    _ = E * ∫ τ : Fin n → ℝ, Jfun τ := by
        rw [MeasureTheory.integral_const_mul]
    _ = E *
        section43FourierLaplace_iteratedFDerivWordMajorantIntegral d n r F ξ := by
        rw [integral_section43FourierLaplace_iteratedFDerivWordMajorant]

set_option backward.isDefEq.respectTransparency false in
/-- Rapid decay of the all-order derivative candidate on every one-sided
positive-energy collar. -/
theorem section43FourierLaplaceIntegral_iteratedFDerivCandidate_rapid_on_positiveEnergyThickening
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    {δ ε : ℝ} (hδ_pos : 0 < δ) (hε_nonneg : 0 ≤ ε)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyThickening d n ε,
        (1 + ‖q‖) ^ s *
          ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
            d n r f hf_ord q‖ ≤ C := by
  intro s
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
      d n f hf_ord hf_compact with
    ⟨R, hR_nonneg, hR_supp⟩
  rcases section43FourierLaplace_iteratedFDerivWordMajorantIntegral_spatialRapid
      (d := d) (n := n) r F s with
    ⟨Csp, hCsp_nonneg, hCsp_bound⟩
  rcases exp_margin_sum_controls_thickened_time_polynomial
      (n := n) (δ := δ) (ε := ε) (R := R) hδ_pos hε_nonneg hR_nonneg s with
    ⟨Ct, hCt_nonneg, hCt_bound⟩
  let A : ℝ :=
    1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖
  let C : ℝ := A ^ s * Ct * Csp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨C, mul_nonneg (mul_nonneg (pow_nonneg hA_nonneg s) hCt_nonneg)
    hCsp_nonneg, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let E : ℝ :=
    Real.exp (∑ _ : Fin n, R * ε) *
      Real.exp (-(δ * ∑ k : Fin n, (t k + ε)))
  let J : ℝ :=
    section43FourierLaplace_iteratedFDerivWordMajorantIntegral d n r F ξ
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J, section43FourierLaplace_iteratedFDerivWordMajorantIntegral]
    refine Finset.sum_nonneg ?_
    intro a _ha
    exact mul_nonneg (section43DerivativeWordCoeff_nonneg d n r a)
      (integral_nonneg fun τ =>
        mul_nonneg (pow_nonneg (norm_nonneg τ) _)
          (norm_nonneg _))
  have hspatial :
      (1 + ‖ξ‖) ^ s * J ≤ Csp := by
    simpa [J, F, ξ] using hCsp_bound ξ
  have ht_collar : ∀ i : Fin n, -ε ≤ t i := by
    intro i
    simpa [section43PositiveEnergyThickening, t] using hq i
  have htime :
      (1 + ‖t‖) ^ s * E ≤ Ct := by
    simpa [t, E] using hCt_bound t ht_collar
  have hscalar :
      ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
        d n r f hf_ord q‖ ≤ E * J := by
    simpa [E, J, F, t, ξ] using
      section43FourierLaplaceIntegral_iteratedFDerivCandidate_norm_le_thickened_exp_word_integrals_of_timeNorm_bound
        d n r f hf_ord hδ_pos hε_nonneg hR_nonneg hδ_supp hR_supp q hq
  have hnorm :
      1 + ‖q‖ ≤ A * (1 + ‖t‖) * (1 + ‖ξ‖) := by
    simpa [A, t, ξ] using
      one_add_norm_le_section43_time_spatial_product d n q
  have hpow_norm :
      (1 + ‖q‖) ^ s ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hnorm s
  have htime_nonneg : 0 ≤ (1 + ‖t‖) ^ s * E := by
    exact mul_nonneg (pow_nonneg (by positivity) s) (by dsimp [E]; positivity)
  have hspatial_nonneg : 0 ≤ (1 + ‖ξ‖) ^ s * J := by
    exact mul_nonneg (pow_nonneg (by positivity) s) hJ_nonneg
  have hterm_prod :
      ((1 + ‖t‖) ^ s * E) * ((1 + ‖ξ‖) ^ s * J) ≤ Ct * Csp := by
    calc
      ((1 + ‖t‖) ^ s * E) * ((1 + ‖ξ‖) ^ s * J)
          ≤ Ct * ((1 + ‖ξ‖) ^ s * J) := by
            exact mul_le_mul_of_nonneg_right htime hspatial_nonneg
      _ ≤ Ct * Csp := by
            exact mul_le_mul_of_nonneg_left hspatial hCt_nonneg
  calc
    (1 + ‖q‖) ^ s *
        ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
          d n r f hf_ord q‖
        ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ s *
            ‖section43FourierLaplaceIntegral_iteratedFDerivCandidate
              d n r f hf_ord q‖ := by
          exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
    _ ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ s * (E * J) := by
          exact mul_le_mul_of_nonneg_left hscalar (pow_nonneg (by positivity) s)
    _ = A ^ s * (((1 + ‖t‖) ^ s * E) * ((1 + ‖ξ‖) ^ s * J)) := by
          rw [mul_pow, mul_pow]
          ring
    _ ≤ A ^ s * (Ct * Csp) := by
          exact mul_le_mul_of_nonneg_left hterm_prod (pow_nonneg hA_nonneg s)
    _ = C := by
          simp [C, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Rapid decay of the actual all-order derivatives of the Section 4.3
Fourier-Laplace integral on every one-sided positive-energy collar. -/
theorem section43FourierLaplaceIntegral_iteratedFDeriv_rapid_on_positiveEnergyThickening
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    {δ ε : ℝ} (hδ_pos : 0 < δ) (hε_nonneg : 0 ≤ ε)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyThickening d n ε,
        (1 + ‖q‖) ^ s *
          ‖iteratedFDeriv ℝ r
            (fun q' : NPointDomain d n =>
              section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q')
            q‖ ≤ C := by
  intro s
  rcases
    section43FourierLaplaceIntegral_iteratedFDerivCandidate_rapid_on_positiveEnergyThickening
      d n r f hf_ord hf_compact hδ_pos hε_nonneg hδ_supp s with
    ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro q hq
  rw [section43FourierLaplaceIntegral_iteratedFDeriv_eq_candidate_of_compact_orderedSupport
    d n r f hf_ord hf_compact q]
  exact hC_bound q hq

/-- With an explicit strict support margin, a compact ordered-support
Section 4.3 Fourier-Laplace integral has an ambient Schwartz representative
agreeing with it on the positive-energy half-space. -/
theorem exists_section43FourierLaplaceRepresentative_eq_integral_of_compact_orderedSupport_of_margin
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∃ Φ : SchwartzNPoint d n,
      ∀ q ∈ section43PositiveEnergyRegion d n,
        Φ q = section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q := by
  let Ffun : NPointDomain d n → ℂ := fun q =>
    section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q
  let Φ : SchwartzNPoint d n :=
    schwartzMap_of_temperate_mul_rapid_on_derivSupport
      (χ := section43PositiveEnergyCutoff d n)
      (F := Ffun)
      (S := section43PositiveEnergyThickening d n 1)
      (section43PositiveEnergyCutoff_hasTemperateGrowth d n)
      (fun r q hne =>
        section43PositiveEnergyCutoff_iteratedFDeriv_support_subset_thickening_one
          d n r q hne)
      (by
        simpa [Ffun] using
          section43FourierLaplaceIntegral_contDiff_of_compact_orderedSupport
            d n f hf_ord hf_compact)
      (by
        intro r s
        simpa [Ffun] using
          section43FourierLaplaceIntegral_iteratedFDeriv_rapid_on_positiveEnergyThickening
            d n r f hf_ord hf_compact hδ_pos (by norm_num : (0 : ℝ) ≤ 1)
            hδ_supp s)
  refine ⟨Φ, ?_⟩
  intro q hq
  have hχ := section43PositiveEnergyCutoff_eq_one_of_mem d n hq
  change section43PositiveEnergyCutoff d n q * Ffun q = Ffun q
  rw [hχ]
  simp [Ffun]

/-- A compact ordered-support Section 4.3 Fourier-Laplace integral has an
ambient Schwartz representative in the positive-energy quotient sense. -/
theorem exists_section43FourierLaplaceRepresentative_of_compact_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ Φ : SchwartzNPoint d n,
      section43FourierLaplaceRepresentative d n ⟨f, hf_ord⟩ Φ := by
  rcases exists_orderedPositiveTimeRegion_margin_of_compact_tsupport_subset
      d n f hf_ord hf_compact with
    ⟨δ, hδ_pos, hδ_supp⟩
  rcases
    exists_section43FourierLaplaceRepresentative_eq_integral_of_compact_orderedSupport_of_margin
      d n f hf_ord hf_compact hδ_pos hδ_supp with
    ⟨Φ, hΦ⟩
  exact ⟨Φ, hΦ⟩

/-- The genuine Section 4.3 Fourier-Laplace transform component: the
positive-energy quotient class of any compact ordered-support representative. -/
noncomputable def section43FourierLaplaceTransformComponent
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    Section43PositiveEnergyComponent (d := d) n :=
  section43PositiveEnergyQuotientMap (d := d) n
    (Classical.choose
      (exists_section43FourierLaplaceRepresentative_of_compact_orderedSupport
        d n f hf_ord hf_compact))

/-- The chosen transform component admits a concrete Fourier-Laplace
representative, and later proofs should use only this existence/equality
surface rather than depending on the particular `Classical.choose` witness. -/
theorem section43FourierLaplaceTransformComponent_has_representative
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ Φ : SchwartzNPoint d n,
      section43FourierLaplaceRepresentative d n ⟨f, hf_ord⟩ Φ ∧
      section43PositiveEnergyQuotientMap (d := d) n Φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact := by
  let hExist :=
    exists_section43FourierLaplaceRepresentative_of_compact_orderedSupport
      d n f hf_ord hf_compact
  refine ⟨Classical.choose hExist, Classical.choose_spec hExist, ?_⟩
  change
    section43PositiveEnergyQuotientMap (d := d) n (Classical.choose hExist) =
      section43FourierLaplaceTransformComponent d n f hf_ord hf_compact
  rfl

end OSReconstruction
