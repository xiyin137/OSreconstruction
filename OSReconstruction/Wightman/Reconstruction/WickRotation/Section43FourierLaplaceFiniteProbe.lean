import Mathlib.LinearAlgebra.Complex.Module
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceDensity

/-!
# Section 4.3 finite-probe Fubini support

This companion file continues the pure-analysis density packet from
`Section43FourierLaplaceDensity.lean`.  The goal is to keep the already-large
density file stable while proving the Banach finite-probe bridge needed for the
weak scalar Fubini theorem.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

namespace Section43CompactPositiveTimeSource1D

private theorem ext_f {g h : Section43CompactPositiveTimeSource1D}
    (hf : g.f = h.f) : g = h := by
  cases g
  cases h
  simp at hf
  subst hf
  rfl

private theorem f_injective :
    Function.Injective (fun g : Section43CompactPositiveTimeSource1D => g.f) := by
  intro g h hf
  exact ext_f hf

instance : Zero Section43CompactPositiveTimeSource1D where
  zero :=
    { f := 0
      positive := by
        intro t ht
        simp at ht
      compact := by
        simpa using
          (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ)) }

instance : Add Section43CompactPositiveTimeSource1D where
  add g h :=
    { f := g.f + h.f
      positive := by
        intro t ht
        have ht' := tsupport_add (g.f : ℝ → ℂ) (h.f : ℝ → ℂ) ht
        exact ht'.elim (fun hg => g.positive hg) (fun hh => h.positive hh)
      compact := by
        simpa using HasCompactSupport.add g.compact h.compact }

instance : SMul ℕ Section43CompactPositiveTimeSource1D where
  smul n g :=
    { f := (n : ℂ) • g.f
      positive := by
        exact
          (tsupport_smul_subset_right
            (fun _ : ℝ => (n : ℂ)) (g.f : ℝ → ℂ)).trans g.positive
      compact := by
        simpa using
          (HasCompactSupport.smul_left
            (f := fun _ : ℝ => (n : ℂ)) (f' := (g.f : ℝ → ℂ)) g.compact) }

instance : AddCommMonoid Section43CompactPositiveTimeSource1D :=
  Function.Injective.addCommMonoid
    (fun g : Section43CompactPositiveTimeSource1D => g.f)
    f_injective rfl
    (by intro g h; rfl)
    (by
      intro g n
      change (n : ℂ) • g.f = n • g.f
      rw [Nat.cast_smul_eq_nsmul ℂ])

instance : SMul ℂ Section43CompactPositiveTimeSource1D where
  smul c g :=
    { f := c • g.f
      positive := by
        exact
          (tsupport_smul_subset_right
            (fun _ : ℝ => c) (g.f : ℝ → ℂ)).trans g.positive
      compact := by
        simpa using
          (HasCompactSupport.smul_left
            (f := fun _ : ℝ => c) (f' := (g.f : ℝ → ℂ)) g.compact) }

private def fAddMonoidHom :
    Section43CompactPositiveTimeSource1D →+ SchwartzMap ℝ ℂ where
  toFun := fun g => g.f
  map_zero' := rfl
  map_add' := by intro g h; rfl

instance : Module ℂ Section43CompactPositiveTimeSource1D :=
  Function.Injective.module ℂ fAddMonoidHom
    (by
      intro g h hf
      exact f_injective hf)
    (by intro c g; rfl)

end Section43CompactPositiveTimeSource1D

set_option backward.isDefEq.respectTransparency false in
/-- The weighted derivative BCF probe is controlled by two Schwartz seminorms.
This is the public Section 4.3 copy of the private Paley-Wiener estimate used to
turn Schwartz-topology convergence of `ψ_z` into BCF-norm convergence. -/
theorem section43WeightedDerivToBCFCLM_norm_le
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖section43WeightedDerivToBCFCLM k n f‖ ≤
      (2 : ℝ) ^ k *
        (SchwartzMap.seminorm ℝ 0 n f +
          SchwartzMap.seminorm ℝ (2 * k) n f) := by
  rw [show ‖section43WeightedDerivToBCFCLM k n f‖ =
      dist (section43WeightedDerivToBCFCLM k n f) 0 by rfl]
  refine (BoundedContinuousFunction.dist_le ?_).2 ?_
  · positivity
  · intro σ
    have hsemi0 := SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 0) (n := n) f σ
    have hsemi2 := SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 2 * k) (n := n) f σ
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, dist_eq_norm, sub_zero,
      section43WeightedDerivToBCFCLM_apply]
    by_cases hσ : |σ| ≤ 1
    · have hpoly : ‖section43PolyWeight k σ‖ ≤ (2 : ℝ) ^ k := by
        rw [section43PolyWeight, Complex.norm_real, Real.norm_of_nonneg]
        · have hσsq : σ ^ 2 ≤ 1 := by
            have hsqabs : |σ| ^ 2 ≤ (1 : ℝ) ^ 2 := by
              gcongr
            simpa [sq_abs] using hsqabs
          calc
            (1 + σ ^ 2) ^ k ≤ (1 + 1) ^ k := by
              gcongr
            _ = (2 : ℝ) ^ k := by ring
        · positivity
      calc
        ‖section43PolyWeight k σ * iteratedDeriv n f σ‖
            ≤ (2 : ℝ) ^ k * ‖iteratedDeriv n f σ‖ := by
              rw [norm_mul]
              gcongr
        _ ≤ (2 : ℝ) ^ k * SchwartzMap.seminorm ℝ 0 n f := by
              exact mul_le_mul_of_nonneg_left
                (by simpa using hsemi0) (pow_nonneg (by positivity) _)
        _ ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n f +
                SchwartzMap.seminorm ℝ (2 * k) n f) := by
              gcongr
              exact le_add_of_nonneg_right (apply_nonneg _ _)
    · have hσgt : 1 < |σ| := lt_of_not_ge hσ
      have hone : 1 ≤ |σ| ^ 2 := by
        have : 1 ≤ |σ| := le_of_lt hσgt
        nlinarith
      have hpoly :
          ‖section43PolyWeight k σ‖ ≤ (2 : ℝ) ^ k * |σ| ^ (2 * k) := by
        rw [section43PolyWeight, Complex.norm_real, Real.norm_of_nonneg]
        · have hσsq : σ ^ 2 = |σ| ^ 2 := by rw [sq_abs]
          calc
            (1 + σ ^ 2) ^ k = (1 + |σ| ^ 2) ^ k := by rw [hσsq]
            _ ≤ (2 * |σ| ^ 2) ^ k := by
                  gcongr
                  linarith
            _ = (2 : ℝ) ^ k * |σ| ^ (2 * k) := by
                  rw [mul_pow]
                  ring_nf
        · positivity
      calc
        ‖section43PolyWeight k σ * iteratedDeriv n f σ‖
            ≤ ((2 : ℝ) ^ k * |σ| ^ (2 * k)) *
                ‖iteratedDeriv n f σ‖ := by
              rw [norm_mul]
              gcongr
        _ = (2 : ℝ) ^ k *
              (|σ| ^ (2 * k) * ‖iteratedDeriv n f σ‖) := by ring
        _ ≤ (2 : ℝ) ^ k * SchwartzMap.seminorm ℝ (2 * k) n f := by
              exact mul_le_mul_of_nonneg_left
                (by simpa using hsemi2) (pow_nonneg (by positivity) _)
        _ ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n f +
                SchwartzMap.seminorm ℝ (2 * k) n f) := by
              gcongr
              exact le_add_of_nonneg_left (apply_nonneg _ _)

private theorem section43_schwartzPsiZ_imagAxis_diff_eq
    (t h : ℝ) (ht : 0 < t) (hth : 0 < t + h)
    (hh_im : ‖((h : ℂ) * Complex.I)‖ ≤ (((t : ℂ) * Complex.I).im) / 2)
    (hh1 : ‖((h : ℂ) * Complex.I)‖ ≤ 1) :
    SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
        (by simpa [Complex.mul_im] using hth) -
      SCV.schwartzPsiZ ((t : ℂ) * Complex.I)
        (by simpa [Complex.mul_im] using ht) -
      ((h : ℂ) * Complex.I) •
        (SchwartzMap.smulLeftCLM ℂ (fun σ : ℝ => Complex.I * (σ : ℂ)))
          (SCV.schwartzPsiZ ((t : ℂ) * Complex.I)
            (by simpa [Complex.mul_im] using ht)) =
    ((h : ℂ) * Complex.I) •
      SCV.schwartzPsiZExpTaylorLinearRemainderQuot
        ((t : ℂ) * Complex.I)
        (by simpa [Complex.mul_im] using ht)
        ((h : ℂ) * Complex.I) hh_im hh1 := by
  have hzadd :
      ((t : ℂ) * Complex.I) + ((h : ℂ) * Complex.I) =
        (((t + h : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  have htemp : (fun σ : ℝ => Complex.I * (σ : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext σ
  simpa [hzadd, SCV.schwartzPsiZ_apply,
    SCV.schwartzPsiZExpTaylorLinearRemainderQuot_apply,
    SchwartzMap.smulLeftCLM_apply_apply htemp, smul_eq_mul] using
    (SCV.psiZ_sub_sub_deriv_eq_smul_remainder
      ((t : ℂ) * Complex.I) ((h : ℂ) * Complex.I) σ)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem continuousAt_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_of_pos
    {t : ℝ} (ht : 0 < t) (k n : ℕ) :
    ContinuousAt
      (fun y : ℝ =>
        section43WeightedDerivToBCFCLM k n
          (section43ImagAxisPsiKernel y))
      t := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let z : ℂ := (t : ℂ) * Complex.I
  have hz : 0 < z.im := by simpa [z, Complex.mul_im] using ht
  let D : ℝ := ‖section43WeightedDerivToBCFCLM k n
    ((SchwartzMap.smulLeftCLM ℂ (fun σ : ℝ => Complex.I * (σ : ℂ)))
      (SCV.schwartzPsiZ z hz))‖
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    SCV.schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz 0 n
  obtain ⟨C2, hC2_nonneg, hC2⟩ :=
    SCV.schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz (2 * k) n
  let C : ℝ := (2 : ℝ) ^ k * (C0 + C2)
  have hD_nonneg : 0 ≤ D := norm_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  let δ : ℝ := min (t / 2) (min 1 (ε / (2 * (D + C + 1))))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · positivity
    · refine lt_min (by norm_num) ?_
      have hden_pos : 0 < 2 * (D + C + 1) := by nlinarith
      exact div_pos hε hden_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  let h : ℝ := y - t
  have hyδ_real : |h| < δ := by
    simpa [h, Real.dist_eq] using hy
  have hhδ : ‖((h : ℂ) * Complex.I)‖ < δ := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using hyδ_real
  have hδ_t : δ ≤ t / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have h_abs_lt_t2 : |y - t| < t / 2 := by
    exact lt_of_lt_of_le (by simpa [h] using hyδ_real) hδ_t
  have hypos : 0 < y := by
    have hleft := (abs_lt.mp h_abs_lt_t2).1
    nlinarith
  have ht_add_h : t + h = y := by
    dsimp [h]
    ring
  have hth : 0 < t + h := by
    rw [ht_add_h]
    exact hypos
  have hh1 : ‖((h : ℂ) * Complex.I)‖ ≤ 1 := by
    exact le_trans (le_of_lt hhδ)
      (by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hh_im : ‖((h : ℂ) * Complex.I)‖ ≤ z.im / 2 := by
    have hle_t : ‖((h : ℂ) * Complex.I)‖ ≤ t / 2 :=
      le_trans (le_of_lt hhδ) hδ_t
    simpa [z, Complex.mul_im] using hle_t
  have hdecomp :=
    section43_schwartzPsiZ_imagAxis_diff_eq t h ht hth hh_im hh1
  have hsplit :
      section43WeightedDerivToBCFCLM k n
        (SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
            (by simpa [Complex.mul_im] using hth) -
          SCV.schwartzPsiZ z hz) =
        ((h : ℂ) * Complex.I) •
            section43WeightedDerivToBCFCLM k n
              (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                z hz ((h : ℂ) * Complex.I) hh_im hh1) +
          ((h : ℂ) * Complex.I) •
            section43WeightedDerivToBCFCLM k n
              ((SchwartzMap.smulLeftCLM ℂ
                  (fun σ : ℝ => Complex.I * (σ : ℂ)))
                (SCV.schwartzPsiZ z hz)) := by
    have htmp :
        section43WeightedDerivToBCFCLM k n
            (SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
                (by simpa [Complex.mul_im] using hth) -
              SCV.schwartzPsiZ z hz) -
          ((h : ℂ) * Complex.I) •
            section43WeightedDerivToBCFCLM k n
              ((SchwartzMap.smulLeftCLM ℂ
                  (fun σ : ℝ => Complex.I * (σ : ℂ)))
                (SCV.schwartzPsiZ z hz)) =
          ((h : ℂ) * Complex.I) •
            section43WeightedDerivToBCFCLM k n
              (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                z hz ((h : ℂ) * Complex.I) hh_im hh1) := by
      simpa [z, hdecomp, map_sub, map_smul] using
        congrArg (section43WeightedDerivToBCFCLM k n) hdecomp
    have htmp2 := eq_add_of_sub_eq htmp
    simpa [add_comm, add_left_comm, add_assoc] using htmp2
  have hrem :
      ‖section43WeightedDerivToBCFCLM k n
          (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
            z hz ((h : ℂ) * Complex.I) hh_im hh1)‖ ≤
        C * ‖((h : ℂ) * Complex.I)‖ := by
    calc
      ‖section43WeightedDerivToBCFCLM k n
          (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
            z hz ((h : ℂ) * Complex.I) hh_im hh1)‖
          ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n
                  (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                    z hz ((h : ℂ) * Complex.I) hh_im hh1) +
                SchwartzMap.seminorm ℝ (2 * k) n
                  (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                    z hz ((h : ℂ) * Complex.I) hh_im hh1)) := by
              exact section43WeightedDerivToBCFCLM_norm_le k n _
      _ ≤ (2 : ℝ) ^ k *
            (C0 * ‖((h : ℂ) * Complex.I)‖ +
              C2 * ‖((h : ℂ) * Complex.I)‖) := by
            gcongr
            · exact hC0 ((h : ℂ) * Complex.I) hh_im hh1
            · exact hC2 ((h : ℂ) * Complex.I) hh_im hh1
      _ = C * ‖((h : ℂ) * Complex.I)‖ := by
            dsimp [C]
            ring
  have hmain :
      ‖section43WeightedDerivToBCFCLM k n
          (SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
              (by simpa [Complex.mul_im] using hth) -
            SCV.schwartzPsiZ z hz)‖
        ≤ ‖((h : ℂ) * Complex.I)‖ *
            (C * ‖((h : ℂ) * Complex.I)‖) +
          ‖((h : ℂ) * Complex.I)‖ * D := by
    calc
      ‖section43WeightedDerivToBCFCLM k n
          (SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
              (by simpa [Complex.mul_im] using hth) -
            SCV.schwartzPsiZ z hz)‖
          = ‖((h : ℂ) * Complex.I) •
                section43WeightedDerivToBCFCLM k n
                  (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                    z hz ((h : ℂ) * Complex.I) hh_im hh1) +
              ((h : ℂ) * Complex.I) •
                section43WeightedDerivToBCFCLM k n
                  ((SchwartzMap.smulLeftCLM ℂ
                      (fun σ : ℝ => Complex.I * (σ : ℂ)))
                    (SCV.schwartzPsiZ z hz))‖ := by
              rw [hsplit]
      _ ≤ ‖((h : ℂ) * Complex.I) •
                section43WeightedDerivToBCFCLM k n
                  (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                    z hz ((h : ℂ) * Complex.I) hh_im hh1)‖ +
            ‖((h : ℂ) * Complex.I) •
                section43WeightedDerivToBCFCLM k n
                  ((SchwartzMap.smulLeftCLM ℂ
                      (fun σ : ℝ => Complex.I * (σ : ℂ)))
                    (SCV.schwartzPsiZ z hz))‖ := norm_add_le _ _
      _ = ‖((h : ℂ) * Complex.I)‖ *
              ‖section43WeightedDerivToBCFCLM k n
                (SCV.schwartzPsiZExpTaylorLinearRemainderQuot
                  z hz ((h : ℂ) * Complex.I) hh_im hh1)‖ +
            ‖((h : ℂ) * Complex.I)‖ * D := by
            simp only [D, norm_smul]
      _ ≤ ‖((h : ℂ) * Complex.I)‖ *
              (C * ‖((h : ℂ) * Complex.I)‖) +
            ‖((h : ℂ) * Complex.I)‖ * D := by
            gcongr
  have hδ_small : δ ≤ ε / (2 * (D + C + 1)) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall :
      ‖((h : ℂ) * Complex.I)‖ *
            (C * ‖((h : ℂ) * Complex.I)‖) +
          ‖((h : ℂ) * Complex.I)‖ * D < ε := by
    have hδfrac : δ * (D + C + 1) < ε := by
      have hden_pos : 0 < 2 * (D + C + 1) := by nlinarith
      have htmp : δ * (2 * (D + C + 1)) ≤ ε := by
        exact (le_div_iff₀ hden_pos).mp hδ_small
      have hlt : δ * (D + C + 1) ≤ ε / 2 := by
        nlinarith
      linarith
    have hnorm_le :
        ‖((h : ℂ) * Complex.I)‖ *
              (C * ‖((h : ℂ) * Complex.I)‖) +
            ‖((h : ℂ) * Complex.I)‖ * D ≤
          δ * (D + C + 1) := by
      have hh_norm_le : ‖((h : ℂ) * Complex.I)‖ ≤ δ := le_of_lt hhδ
      have hsq :
          ‖((h : ℂ) * Complex.I)‖ *
              ‖((h : ℂ) * Complex.I)‖ ≤ δ := by
        have :
            ‖((h : ℂ) * Complex.I)‖ *
                ‖((h : ℂ) * Complex.I)‖ ≤ δ * 1 := by
          refine mul_le_mul hh_norm_le hh1 ?_ ?_
          · exact norm_nonneg _
          · positivity
        simpa using this
      calc
        ‖((h : ℂ) * Complex.I)‖ *
              (C * ‖((h : ℂ) * Complex.I)‖) +
            ‖((h : ℂ) * Complex.I)‖ * D
            = C *
                (‖((h : ℂ) * Complex.I)‖ *
                  ‖((h : ℂ) * Complex.I)‖) +
              D * ‖((h : ℂ) * Complex.I)‖ := by ring
        _ ≤ C * δ + D * δ := by
              gcongr
        _ ≤ δ * (D + C + 1) := by
              ring_nf
              nlinarith [hδ_pos, hC_nonneg, hD_nonneg]
    exact lt_of_le_of_lt hnorm_le hδfrac
  have hdist_eq :
      dist
        (section43WeightedDerivToBCFCLM k n (section43ImagAxisPsiKernel y))
        (section43WeightedDerivToBCFCLM k n (section43ImagAxisPsiKernel t)) =
      ‖section43WeightedDerivToBCFCLM k n
          (SCV.schwartzPsiZ (((t + h : ℝ) : ℂ) * Complex.I)
              (by simpa [Complex.mul_im] using hth) -
            SCV.schwartzPsiZ z hz)‖ := by
    rw [dist_eq_norm, ← map_sub]
    rw [section43ImagAxisPsiKernel_of_pos hypos,
      section43ImagAxisPsiKernel_of_pos ht]
    simp [z, ht_add_h]
  rw [hdist_eq]
  exact lt_of_le_of_lt hmain hsmall

theorem continuousOn_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_Ioi
    (k n : ℕ) :
    ContinuousOn
      (fun t : ℝ =>
        section43WeightedDerivToBCFCLM k n
          (section43ImagAxisPsiKernel t))
      (Set.Ioi (0 : ℝ)) := by
  intro t ht
  exact
    (continuousAt_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_of_pos
      (Set.mem_Ioi.mp ht) k n).continuousWithinAt

private theorem section43_identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have hU_open : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected {z : ℂ | 0 < z.re} := by
    apply Convex.isPreconnected
    intro z hz w hw a b ha hb hab
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    calc
      (a • z + b • w).re = a * z.re + b * w.re := by
        simp [Complex.add_re]
      _ > 0 := by
        rcases ha.lt_or_eq with ha' | ha'
        · have : 0 ≤ b * w.re := mul_nonneg hb hw.le
          have : 0 < a * z.re := mul_pos ha' hz
          linarith
        · have hab' : b = 1 := by linarith
          simp [← ha', hab', hw]
  have hf_an : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} :=
    hf.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} :=
    hg.analyticOnNhd hU_open
  have h1_mem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hfg_an : AnalyticAt ℂ (f - g) 1 :=
    (hf_an 1 h1_mem).sub (hg_an 1 h1_mem)
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, (f - g) z = 0 := by
    rw [Filter.Frequently]
    intro hev
    rw [Filter.Eventually] at hev
    rw [(nhdsWithin_basis_open 1 {(1 : ℂ)}ᶜ).mem_iff] at hev
    obtain ⟨u, ⟨h1u, hu_open⟩, hus⟩ := hev
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu_open 1 h1u
    have hmem : ((1 + ε / 2 : ℝ) : ℂ) ∈ u := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : ((1 + ε / 2 : ℝ) : ℂ) - 1 =
          ((ε / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hsub]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hne : ((1 + ε / 2 : ℝ) : ℂ) ≠ (1 : ℂ) := by
      intro heq
      have := congr_arg Complex.re heq
      simp at this
      linarith [half_pos hε]
    have hzero : (f - g) ((1 + ε / 2 : ℝ) : ℂ) = 0 := by
      simp only [Pi.sub_apply, sub_eq_zero]
      exact hagree (1 + ε / 2) (by linarith)
    exact hus ⟨hmem, hne⟩ hzero
  have hev : ∀ᶠ z in nhds (1 : ℂ), (f - g) z = 0 :=
    hfg_an.frequently_zero_iff_eventually_zero.mp hfreq
  have hfg_an_on : AnalyticOnNhd ℂ (f - g) {z : ℂ | 0 < z.re} :=
    hf_an.sub hg_an
  have heqOn : Set.EqOn (f - g) 0 {z : ℂ | 0 < z.re} :=
    hfg_an_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_preconn h1_mem hev
  intro z hz
  have := heqOn hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

private theorem section43_identity_theorem_upperHalfPlane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f SCV.upperHalfPlane)
    (hg : DifferentiableOn ℂ g SCV.upperHalfPlane)
    (hagree : ∀ η : ℝ, 0 < η → f ((η : ℂ) * Complex.I) = g ((η : ℂ) * Complex.I)) :
    ∀ z : ℂ, 0 < z.im → f z = g z := by
  let fR : ℂ → ℂ := fun w => f (Complex.I * w)
  let gR : ℂ → ℂ := fun w => g (Complex.I * w)
  have hmap : Set.MapsTo (fun w : ℂ => Complex.I * w)
      {z : ℂ | 0 < z.re} SCV.upperHalfPlane := by
    intro z hz
    simpa [SCV.upperHalfPlane, Complex.mul_im] using hz
  have hmul :
      DifferentiableOn ℂ (fun w : ℂ => Complex.I * w)
        {z : ℂ | 0 < z.re} := by
    intro z hz
    simpa using
      (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
        Complex.I).differentiableWithinAt)
  have hfR : DifferentiableOn ℂ fR {z : ℂ | 0 < z.re} := hf.comp hmul hmap
  have hgR : DifferentiableOn ℂ gR {z : ℂ | 0 < z.re} := hg.comp hmul hmap
  have hagreeR : ∀ t : ℝ, 0 < t → fR (t : ℂ) = gR (t : ℂ) := by
    intro t ht
    simpa [fR, gR, mul_comm] using hagree t ht
  intro z hz
  have hzR : 0 < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have hmain :=
    section43_identity_theorem_right_halfplane fR gR hfR hgR hagreeR
      (-Complex.I * z) hzR
  dsimp [fR, gR] at hmain
  convert hmain using 1 <;> ring_nf <;> simp

theorem integrable_section43WeightedProbe_imagAxisPsiKernel_source
    (g : Section43CompactPositiveTimeSource1D)
    (k n : ℕ) :
    Integrable
      (fun t : ℝ =>
        g.f t •
          section43WeightedDerivToBCFCLM k n
            (section43ImagAxisPsiKernel t)) := by
  obtain ⟨δ, R, hδ_pos, _hδR, hsupport⟩ :=
    exists_positive_Icc_bounds_of_compactPositiveTimeSource g
  let F : ℝ → (ℝ →ᵇ ℂ) := fun t =>
    g.f t • section43WeightedDerivToBCFCLM k n
      (section43ImagAxisPsiKernel t)
  have hsupp : Function.support F ⊆ Set.Icc δ R := by
    intro t htF
    have hgf : g.f t ≠ 0 := by
      intro hzero
      apply htF
      simp [F, hzero]
    exact hsupport (subset_tsupport _ hgf)
  have hIcc_subset_Ioi : Set.Icc δ R ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le hδ_pos ht.1
  have hcont_probe :
      ContinuousOn
        (fun t : ℝ =>
          section43WeightedDerivToBCFCLM k n
            (section43ImagAxisPsiKernel t))
        (Set.Icc δ R) :=
    (continuousOn_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_Ioi k n).mono
      hIcc_subset_Ioi
  have hcont_F : ContinuousOn F (Set.Icc δ R) := by
    exact g.f.continuous.continuousOn.smul hcont_probe
  have hIntOn : IntegrableOn F (Set.Icc δ R) :=
    hcont_F.integrableOn_compact isCompact_Icc
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/-- The finite-probe imaginary-axis family.  This is Banach-valued, unlike the
unavailable `SchwartzMap`-valued Bochner integral. -/
noncomputable def section43ProbeImagAxisFamily
    (s : Finset (ℕ × ℕ)) (g : Section43CompactPositiveTimeSource1D) :
    ℝ → ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) :=
  fun t => g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)

theorem section43ProbeImagAxisFamily_apply
    (s : Finset (ℕ × ℕ)) (g : Section43CompactPositiveTimeSource1D)
    (t : ℝ) (p : ↑s.attach) (σ : ℝ) :
    section43ProbeImagAxisFamily s g t p σ =
      g.f t *
        section43WeightedDerivToBCFCLM p.1.1.1 p.1.1.2
          (section43ImagAxisPsiKernel t) σ := by
  simp [section43ProbeImagAxisFamily, section43ProbeCLM, smul_eq_mul]

theorem integrable_section43Probe_imagAxisPsiKernel_source
    (s : Finset (ℕ × ℕ))
    (g : Section43CompactPositiveTimeSource1D) :
    Integrable (section43ProbeImagAxisFamily s g) := by
  refine Integrable.of_eval ?_
  intro p
  simpa [section43ProbeImagAxisFamily, section43ProbeCLM] using
    integrable_section43WeightedProbe_imagAxisPsiKernel_source
      g p.1.1.1 p.1.1.2

theorem section43Probe_representative_component_apply_eq_integral_probeImagAxisFamily
    (s : Finset (ℕ × ℕ)) (g : Section43CompactPositiveTimeSource1D)
    (p : ↑s.attach) (σ : ℝ) :
    section43ProbeCLM s
        (section43OneSidedLaplaceSchwartzRepresentative1D g) p σ =
      ∫ t : ℝ, section43ProbeImagAxisFamily s g t p σ := by
  simpa [section43ProbeImagAxisFamily_apply] using
    section43WeightedDerivToBCFCLM_representative_eq_integral_kernel_apply
      g p.1.1.1 p.1.1.2 σ

/-- Once the finite-probe imaginary-axis family is known to be Bochner
integrable, the scalar component identities assemble into the Banach finite
product identity. -/
theorem section43Probe_integral_imagAxisPsiKernel_of_integrable
    (s : Finset (ℕ × ℕ)) (g : Section43CompactPositiveTimeSource1D)
    (hInt : Integrable (section43ProbeImagAxisFamily s g)) :
    section43ProbeCLM s (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ, section43ProbeImagAxisFamily s g t := by
  ext p σ
  have h_eval_p :
      (∫ t : ℝ, section43ProbeImagAxisFamily s g t) p =
        ∫ t : ℝ, section43ProbeImagAxisFamily s g t p := by
    simpa using
      ((ContinuousLinearMap.proj
          (R := ℂ) (φ := fun _ : ↑s.attach => ℝ →ᵇ ℂ) p).integral_comp_comm
        hInt).symm
  have hInt_p :
      Integrable (fun t : ℝ => section43ProbeImagAxisFamily s g t p) :=
    (ContinuousLinearMap.proj
      (R := ℂ) (φ := fun _ : ↑s.attach => ℝ →ᵇ ℂ) p).integrable_comp hInt
  have h_eval_σ :
      (∫ t : ℝ, section43ProbeImagAxisFamily s g t p) σ =
        ∫ t : ℝ, section43ProbeImagAxisFamily s g t p σ := by
    simpa using
      ((BoundedContinuousFunction.evalCLM ℂ σ).integral_comp_comm
        hInt_p).symm
  rw [h_eval_p, h_eval_σ]
  exact
    section43Probe_representative_component_apply_eq_integral_probeImagAxisFamily
      s g p σ

theorem section43Probe_integral_imagAxisPsiKernel
    (s : Finset (ℕ × ℕ)) (g : Section43CompactPositiveTimeSource1D) :
    section43ProbeCLM s (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ, section43ProbeImagAxisFamily s g t :=
  section43Probe_integral_imagAxisPsiKernel_of_integrable s g
    (integrable_section43Probe_imagAxisPsiKernel_source s g)

/-- Weak scalar Fubini through a fixed finite-probe factorization.  The only
remaining analytic hypothesis is the honest Bochner integrability of the
finite-probe imaginary-axis family. -/
theorem section43OneSidedLaplace_scalar_fubini_apply_of_probe_factorization
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (g : Section43CompactPositiveTimeSource1D)
    (s : Finset (ℕ × ℕ))
    (G : ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) →L[ℂ] ℂ)
    (hTG : T = G.comp (section43ProbeCLM s))
    (hInt : Integrable (section43ProbeImagAxisFamily s g)) :
    T (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ, T (section43ImagAxisPsiKernel t) * g.f t := by
  have hT_apply :
      ∀ f : SchwartzMap ℝ ℂ, T f = G (section43ProbeCLM s f) := by
    intro f
    exact congrArg (fun H => H f) hTG
  calc
    T (section43OneSidedLaplaceSchwartzRepresentative1D g)
        = G (section43ProbeCLM s
            (section43OneSidedLaplaceSchwartzRepresentative1D g)) := by
            exact hT_apply _
    _ = G (∫ t : ℝ, section43ProbeImagAxisFamily s g t) := by
          rw [section43Probe_integral_imagAxisPsiKernel_of_integrable s g hInt]
    _ = ∫ t : ℝ, G (section43ProbeImagAxisFamily s g t) := by
          simpa using (G.integral_comp_comm hInt).symm
    _ = ∫ t : ℝ, T (section43ImagAxisPsiKernel t) * g.f t := by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [hT_apply (section43ImagAxisPsiKernel t)]
          simp [section43ProbeImagAxisFamily, map_smul, smul_eq_mul, mul_comm]

theorem section43OneSidedLaplace_scalar_fubini_apply
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (g : Section43CompactPositiveTimeSource1D) :
    T (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ, T (section43ImagAxisPsiKernel t) * g.f t := by
  obtain ⟨s, G, hTG⟩ := section43_exists_probe_factorization T
  exact section43OneSidedLaplace_scalar_fubini_apply_of_probe_factorization
    T g s G hTG (integrable_section43Probe_imagAxisPsiKernel_source s g)

theorem section43OneSidedAnnihilatorFL_integral_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0)
    (g : Section43CompactPositiveTimeSource1D) :
    ∫ t : ℝ,
      section43OneSidedAnnihilatorFLOnImag A t * g.f t = 0 := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    A.comp section43PositiveEnergyQuotientMap1D
  have hF := section43OneSidedLaplace_scalar_fubini_apply T g
  calc
    ∫ t : ℝ, section43OneSidedAnnihilatorFLOnImag A t * g.f t
        = ∫ t : ℝ, T (section43ImagAxisPsiKernel t) * g.f t := by
            refine integral_congr_ae ?_
            filter_upwards with t
            rw [section43OneSidedAnnihilatorFLOnImag_eq_apply_kernel]
            rfl
    _ = T (section43OneSidedLaplaceSchwartzRepresentative1D g) := hF.symm
    _ = A (section43PositiveEnergyQuotientMap1D
          (section43OneSidedLaplaceSchwartzRepresentative1D g)) := rfl
    _ = A (section43OneSidedLaplaceCompactTransform1D g) := by
          rw [section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient]
    _ = 0 := hA g

theorem section43OneSidedAnnihilatorFLOnImag_eq_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    ∀ t : ℝ, 0 < t →
      section43OneSidedAnnihilatorFLOnImag A t = 0 := by
  have hEqOn :
      Set.EqOn (section43OneSidedAnnihilatorFLOnImag A)
        (fun _ : ℝ => 0) (Set.Ioi (0 : ℝ)) := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      (E := ℝ) isOpen_Ioi
      (continuousOn_section43OneSidedAnnihilatorFLOnImag_Ioi A)
      continuousOn_const ?_
    intro f hf_compact hf_support
    let g : Section43CompactPositiveTimeSource1D :=
      ⟨f, hf_support, hf_compact⟩
    have hzero :=
      section43OneSidedAnnihilatorFL_integral_zero_of_annihilates_laplace
        A hA g
    simpa [g] using hzero
  intro t ht
  exact hEqOn (Set.mem_Ioi.mpr ht)

theorem section43OneSidedAnnihilatorFL_eq_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    ∀ (z : ℂ) (hz : 0 < z.im),
      section43OneSidedAnnihilatorFL A z hz = 0 := by
  let T := section43PositiveEnergy1D_to_oneSidedFourierFunctional A
  let F : ℂ → ℂ := fun z =>
    if hz : 0 < z.im then
      SCV.fourierLaplaceExt T z hz
    else
      0
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    simpa [F, T] using (SCV.fourierLaplaceExt_differentiableOn T)
  have haxis : ∀ η : ℝ, 0 < η → F ((η : ℂ) * Complex.I) = 0 := by
    intro η hη
    have hOn :=
      section43OneSidedAnnihilatorFLOnImag_eq_zero_of_annihilates_laplace
        A hA η hη
    rw [section43OneSidedAnnihilatorFLOnImag_of_pos A hη] at hOn
    have him : 0 < (((η : ℂ) * Complex.I).im) := by
      simpa [Complex.mul_im] using hη
    have hEq :=
      section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
        A (((η : ℂ) * Complex.I)) him
    have hExtZero :
        SCV.fourierLaplaceExt T (((η : ℂ) * Complex.I)) him = 0 := by
      simpa [T] using hEq.symm.trans hOn
    simpa [F, Complex.mul_im, hη] using hExtZero
  intro z hz
  have hFz := section43_identity_theorem_upperHalfPlane F 0
    hF_diff (differentiableOn_const 0) haxis z hz
  have hEq :=
    section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided A z hz
  dsimp [F] at hFz
  rw [dif_pos hz] at hFz
  exact hEq.trans (by simpa [T] using hFz)

theorem section43OneSidedLaplaceCompactTransform1D_dual_annihilator
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    A = 0 :=
  section43PositiveEnergy1D_ext_of_FL_zero A
    (section43OneSidedAnnihilatorFL_eq_zero_of_annihilates_laplace A hA)

theorem section43OneSidedLaplaceCompactTransform1D_map_add
    (g h : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceCompactTransform1D (g + h) =
      section43OneSidedLaplaceCompactTransform1D g +
        section43OneSidedLaplaceCompactTransform1D h := by
  rw [section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient,
    section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient,
    section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient]
  rw [← map_add]
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  intro σ hσ
  have hσ0 : 0 ≤ σ := Set.mem_Ici.mp hσ
  change
    section43OneSidedLaplaceSchwartzRepresentative1D (g + h) σ =
      section43OneSidedLaplaceSchwartzRepresentative1D g σ +
        section43OneSidedLaplaceSchwartzRepresentative1D h σ
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg (g + h) hσ0,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg g hσ0,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg h hσ0]
  unfold section43OneSidedLaplaceRaw
  rw [← integral_add (section43OneSidedLaplaceRaw_integrable_of_nonneg g hσ0)
    (section43OneSidedLaplaceRaw_integrable_of_nonneg h hσ0)]
  refine integral_congr_ae ?_
  filter_upwards with t
  change
    Complex.exp (-(t : ℂ) * (σ : ℂ)) * (g.f t + h.f t) =
      Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t +
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * h.f t
  ring

theorem section43OneSidedLaplaceCompactTransform1D_map_smul
    (c : ℂ) (g : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceCompactTransform1D (c • g) =
      c • section43OneSidedLaplaceCompactTransform1D g := by
  rw [section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient,
    section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient]
  rw [← map_smul]
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  intro σ hσ
  have hσ0 : 0 ≤ σ := Set.mem_Ici.mp hσ
  change
    section43OneSidedLaplaceSchwartzRepresentative1D (c • g) σ =
      c • section43OneSidedLaplaceSchwartzRepresentative1D g σ
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg (c • g) hσ0,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg g hσ0]
  unfold section43OneSidedLaplaceRaw
  change
    ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * (c * g.f t) =
      c * ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
  calc
    ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * (c * g.f t)
        = ∫ t : ℝ, c * (Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
            refine integral_congr_ae ?_
            filter_upwards with t
            ring
    _ = c * ∫ t : ℝ,
          Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t := by
          simpa using
            (integral_const_mul c
              (fun t : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t))

/-- The compact strict-positive one-sided Laplace transform as a linear map.
This exposes its range as a genuine submodule for the Hahn-Banach density step. -/
noncomputable def section43OneSidedLaplaceCompactTransform1DLinearMap :
    Section43CompactPositiveTimeSource1D →ₗ[ℂ] Section43PositiveEnergy1D where
  toFun := section43OneSidedLaplaceCompactTransform1D
  map_add' := section43OneSidedLaplaceCompactTransform1D_map_add
  map_smul' := section43OneSidedLaplaceCompactTransform1D_map_smul

theorem dense_section43OneSidedLaplaceCompactTransform1D_preimage :
    Dense
      (section43PositiveEnergyQuotientMap1D ⁻¹'
        Set.range section43OneSidedLaplaceCompactTransform1D) := by
  let L := section43OneSidedLaplaceCompactTransform1DLinearMap
  let Mq : Submodule ℂ Section43PositiveEnergy1D := LinearMap.range L
  let q := section43PositiveEnergyQuotientMap1D
  let S : Submodule ℂ (SchwartzMap ℝ ℂ) := Mq.comap q.toLinearMap
  have htarget :
      section43PositiveEnergyQuotientMap1D ⁻¹'
          Set.range section43OneSidedLaplaceCompactTransform1D =
        (S : Set (SchwartzMap ℝ ℂ)) := by
    ext φ
    simp [S, Mq, L, q, section43OneSidedLaplaceCompactTransform1DLinearMap]
  rw [htarget]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hS
  have hx : ∃ x : SchwartzMap ℝ ℂ, x ∉ S.topologicalClosure := by
    by_contra hx
    apply hS
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx'
    exact hx ⟨x, hx'⟩
  letI : Module ℝ (SchwartzMap ℝ ℂ) :=
    Module.complexToReal (SchwartzMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ (SchwartzMap ℝ ℂ) :=
    IsScalarTower.complexToReal (M := ℂ) (E := SchwartzMap ℝ ℂ)
  have hconv : Convex ℝ (S.topologicalClosure : Set (SchwartzMap ℝ ℂ)) := by
    intro x hx y hy a b _ha _hb _hab
    exact S.topologicalClosure.add_mem
      (S.topologicalClosure.smul_mem (a : ℂ) hx)
      (S.topologicalClosure.smul_mem (b : ℂ) hy)
  rcases hx with ⟨x, hx⟩
  obtain ⟨f, u, hleft, hright⟩ :=
    geometric_hahn_banach_closed_point
      hconv S.isClosed_topologicalClosure hx
  have hu_pos : 0 < u := by
    have hzero := hleft 0 S.topologicalClosure.zero_mem
    simpa using hzero
  have hf_zero :
      ∀ y ∈ S.topologicalClosure, f y = 0 := by
    intro y hy
    by_contra hre
    let r : ℝ := (u + 1) / f y
    have hlt := hleft ((r : ℂ) • y)
      (S.topologicalClosure.smul_mem (r : ℂ) hy)
    have hreval : f ((r : ℂ) • y) = u + 1 := by
      calc
        f ((r : ℂ) • y) = r * f y := by
          rw [Complex.coe_smul]
          simp [smul_eq_mul]
        _ = u + 1 := by
          dsimp [r]
          field_simp [hre]
    have : ¬ u + 1 < u := by linarith
    exact this (hreval ▸ hlt)
  let F : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    StrongDual.extendRCLike (𝕜 := ℂ) f
  have hF_zero :
      ∀ y ∈ S.topologicalClosure, F y = 0 := by
    intro y hy
    have hyI : (Complex.I : ℂ) • y ∈ S.topologicalClosure :=
      S.topologicalClosure.smul_mem Complex.I hy
    rw [StrongDual.extendRCLike_apply]
    simp [hf_zero y hy, hf_zero ((Complex.I : ℂ) • y) hyI]
  have hker :
      section43PositiveEnergyVanishingSubmodule1D ≤
        LinearMap.ker F.toLinearMap := by
    intro φ hφ
    rw [LinearMap.mem_ker]
    have hφS : φ ∈ S := by
      change q φ ∈ Mq
      have hqzero : q φ = 0 := by
        change (Submodule.Quotient.mk φ : Section43PositiveEnergy1D) = 0
        exact (Submodule.Quotient.mk_eq_zero _).mpr hφ
      rw [hqzero]
      exact Mq.zero_mem
    exact hF_zero φ (S.le_topologicalClosure hφS)
  let A_lin : Section43PositiveEnergy1D →ₗ[ℂ] ℂ :=
    section43PositiveEnergyVanishingSubmodule1D.liftQ F.toLinearMap hker
  let A : Section43PositiveEnergy1D →L[ℂ] ℂ :=
    ContinuousLinearMap.mk A_lin (by
      refine
        section43PositiveEnergyVanishingSubmodule1D.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.2
          ?_
      simpa [A_lin, F, Function.comp] using F.continuous)
  have hAq :
      ∀ φ : SchwartzMap ℝ ℂ, A (q φ) = F φ := by
    intro φ
    change A_lin (Submodule.Quotient.mk φ) = F φ
    simp [A_lin]
  have hA_on_range :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0 := by
    intro g
    let φ := section43OneSidedLaplaceSchwartzRepresentative1D g
    have hφS : φ ∈ S := by
      change q φ ∈ Mq
      rw [← section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient g]
      change L g ∈ LinearMap.range L
      exact LinearMap.mem_range_self L g
    calc
      A (section43OneSidedLaplaceCompactTransform1D g)
          = A (q φ) := by
              rw [section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient]
      _ = F φ := hAq φ
      _ = 0 := hF_zero φ (S.le_topologicalClosure hφS)
  have hA_zero : A = 0 :=
    section43OneSidedLaplaceCompactTransform1D_dual_annihilator A hA_on_range
  have hF_zero_all : F = 0 := by
    ext φ
    have h := hAq φ
    rw [hA_zero] at h
    simpa using h.symm
  have hfx_zero : f x = 0 := by
    have hre := StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f x
    simpa [F, hF_zero_all] using hre.symm
  have : ¬ u < (0 : ℝ) := not_lt_of_ge hu_pos.le
  apply this
  simpa [hfx_zero] using hright

theorem denseRange_section43OneSidedLaplaceCompactTransform1DLinearMap :
    DenseRange section43OneSidedLaplaceCompactTransform1DLinearMap := by
  have hq :
      IsOpenQuotientMap
        (section43PositiveEnergyQuotientMap1D :
          SchwartzMap ℝ ℂ → Section43PositiveEnergy1D) := by
    simpa [section43PositiveEnergyQuotientMap1D] using
      section43PositiveEnergyVanishingSubmodule1D.isOpenQuotientMap_mkQ
  have hdense_set : Dense (Set.range section43OneSidedLaplaceCompactTransform1D) :=
    hq.dense_preimage_iff.mp
      dense_section43OneSidedLaplaceCompactTransform1D_preimage
  simpa [DenseRange, section43OneSidedLaplaceCompactTransform1DLinearMap] using
    hdense_set

end OSReconstruction
