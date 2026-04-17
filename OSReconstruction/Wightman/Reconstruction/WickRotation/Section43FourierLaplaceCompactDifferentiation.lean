import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceHigherDerivatives

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

attribute [local instance 101] secondCountableTopologyEither_of_left

namespace OSReconstruction

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

end OSReconstruction
