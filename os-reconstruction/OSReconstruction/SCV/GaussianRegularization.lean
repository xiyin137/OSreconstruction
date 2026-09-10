/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import OSReconstruction.SCV.HorizontalConvexity











noncomputable section

open Complex Filter MeasureTheory Set
open scoped RealInnerProductSpace

namespace OSReconstruction.SCV

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise embedding of a real Euclidean vector into a complex
coordinate space. -/
def gaussianRealEmbed (x : EuclideanSpace ℝ ι) : ι → ℂ :=
  fun i => x i

/-- The holomorphic quadratic form used by finite-dimensional Gaussian
regularization. On the real locus it is the squared Euclidean distance. -/
def gaussianComplexSqDist (z : ι → ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∑ i, (z i - (x i : ℂ)) ^ 2

/-- Gaussian kernel with both arguments complex. Keeping this auxiliary kernel
separate makes continuity of its parameter-dependent derivative available from
the standard `ContDiff` calculus. -/
def gaussianComplexKernel
    (c : ℝ) (z y : ι → ℂ) : ℂ :=
  ((Real.pi * c : ℂ) ^
      (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ) *
    Complex.exp
      (-Real.pi ^ 2 * c * ∑ i, (z i - y i) ^ 2))

/-- Gaussian kernel with a real integration variable. -/
def gaussianKernel
    (c : ℝ) (z : ι → ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  gaussianComplexKernel c z (gaussianRealEmbed x)

/-- Normalized finite-dimensional Gaussian regularization. The formula is
defined for every real scale; convergence statements use `c → +∞`. -/
def gaussianRegularization
    (c : ℝ) (f : EuclideanSpace ℝ ι → ℂ) (z : ι → ℂ) : ℂ :=
  ∫ x : EuclideanSpace ℝ ι,
    gaussianKernel c z x * f x

/-- Restrict a complex-coordinate function to the complete real slice used
as the input of Gaussian regularization. -/
def gaussianRealSliceInput
    (F : (ι → ℂ) → ℂ)
    (x : EuclideanSpace ℝ ι) : ℂ :=
  F (gaussianRealEmbed x)

/-- Move one coordinate of a real Gaussian input to a fixed horizontal
line. -/
def gaussianCoordinateShiftedInput
    [DecidableEq ι]
    (F : (ι → ℂ) → ℂ)
    (a : ι)
    (y : ℝ)
    (x : EuclideanSpace ℝ ι) : ℂ :=
  F (Function.update (gaussianRealEmbed x) a ((x a : ℂ) + y * I))

/-- The one-variable coordinate line through a real base point. -/
def gaussianCoordinateLine
    [DecidableEq ι]
    (F : (ι → ℂ) → ℂ)
    (x : ι → ℝ)
    (a : ι)
    (w : ℂ) : ℂ :=
  F (Function.update (fun b => (x b : ℂ)) a w)

/-- Reindex a nonempty finite coordinate type as `Fin (card - 1 + 1)`.
The distinguished coordinate is retained explicitly by the subsequent
`piFinSuccAbove` split. -/
noncomputable def gaussianCoordinateIndexEquiv (a : ι) :
    ι ≃ Fin (Fintype.card ι - 1 + 1) :=
  Fintype.equivFinOfCardEq
    (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨a⟩)).symm

/-- Split a selected coordinate from a finite Euclidean space, preserving the
remaining coordinates in a canonical finite block. -/
noncomputable def gaussianCoordinateSplit (a : ι) :
    EuclideanSpace ℝ ι ≃ᵐ
      ℝ × (Fin (Fintype.card ι - 1) → ℝ) :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).symm |>.trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
      (gaussianCoordinateIndexEquiv a)).trans
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
        (gaussianCoordinateIndexEquiv a a)))

/-- The selected-coordinate Euclidean split preserves Lebesgue volume. -/
theorem gaussianCoordinateSplit_measurePreserving (a : ι) :
    MeasurePreserving (gaussianCoordinateSplit a) := by
  unfold gaussianCoordinateSplit
  apply MeasurePreserving.trans
  · exact PiLp.volume_preserving_ofLp ι
  apply MeasurePreserving.trans
  · exact
      MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
        (gaussianCoordinateIndexEquiv a)
  · exact
      MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
        (gaussianCoordinateIndexEquiv a a)

/-- Fubini after splitting one selected coordinate from a finite Euclidean
space. -/
theorem integral_gaussianCoordinateSplit
    (a : ι)
    (F : EuclideanSpace ℝ ι → ℂ)
    (hF : Integrable F) :
    ∫ u : EuclideanSpace ℝ ι, F u =
      ∫ uRest : Fin (Fintype.card ι - 1) → ℝ,
        ∫ t : ℝ, F ((gaussianCoordinateSplit a).symm (t, uRest)) := by
  let e := gaussianCoordinateSplit a
  have hmp : MeasurePreserving e :=
    gaussianCoordinateSplit_measurePreserving a
  have hpair_int :
      Integrable (fun p : ℝ × (Fin (Fintype.card ι - 1) → ℝ) =>
        F (e.symm p)) := by
    simpa [e] using hmp.symm.integrable_comp_of_integrable hF
  calc
    ∫ u : EuclideanSpace ℝ ι, F u =
        ∫ p : ℝ × (Fin (Fintype.card ι - 1) → ℝ),
          F (e.symm p) := by
      simpa [e] using (hmp.symm.integral_comp' (g := F)).symm
    _ = ∫ uRest : Fin (Fintype.card ι - 1) → ℝ,
          ∫ t : ℝ, F (e.symm (t, uRest)) :=
      integral_prod_symm _ hpair_int

@[simp]
theorem gaussianCoordinateSplit_apply_fst
    (a : ι) (u : EuclideanSpace ℝ ι) :
    (gaussianCoordinateSplit a u).1 = u a := by
  simp only [gaussianCoordinateSplit, MeasurableEquiv.trans_apply]
  change
    (Equiv.piCongrLeft
      (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
      (gaussianCoordinateIndexEquiv a)
      (WithLp.ofLp u))
        (gaussianCoordinateIndexEquiv a a) = WithLp.ofLp u a
  exact
    Equiv.piCongrLeft_apply_apply
      (P := fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
      (e := gaussianCoordinateIndexEquiv a)
      (WithLp.ofLp u) a

@[simp]
theorem gaussianCoordinateSplit_apply_snd_apply
    (a : ι) (u : EuclideanSpace ℝ ι)
    (j : Fin (Fintype.card ι - 1)) :
    (gaussianCoordinateSplit a u).2 j =
      u ((gaussianCoordinateIndexEquiv a).symm
        ((gaussianCoordinateIndexEquiv a a).succAbove j)) := by
  simp only [gaussianCoordinateSplit, MeasurableEquiv.trans_apply]
  change
    (Equiv.piCongrLeft
      (fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
      (gaussianCoordinateIndexEquiv a)
      (WithLp.ofLp u))
        ((gaussianCoordinateIndexEquiv a a).succAbove j) =
      WithLp.ofLp u
        ((gaussianCoordinateIndexEquiv a).symm
          ((gaussianCoordinateIndexEquiv a a).succAbove j))
  simpa using
    Equiv.piCongrLeft_apply_apply
      (P := fun _ : Fin (Fintype.card ι - 1 + 1) => ℝ)
      (e := gaussianCoordinateIndexEquiv a)
      (WithLp.ofLp u)
      ((gaussianCoordinateIndexEquiv a).symm
        ((gaussianCoordinateIndexEquiv a a).succAbove j))

@[simp]
theorem gaussianCoordinateSplit_symm_apply_selected
    (a : ι) (t : ℝ) (uRest : Fin (Fintype.card ι - 1) → ℝ) :
    ((gaussianCoordinateSplit a).symm (t, uRest)) a = t := by
  have h := congrArg Prod.fst
    ((gaussianCoordinateSplit a).apply_symm_apply (t, uRest))
  rw [gaussianCoordinateSplit_apply_fst] at h
  exact h

/-- Changing the selected coordinate in split coordinates leaves every
inactive coordinate unchanged. -/
theorem gaussianCoordinateSplit_symm_apply_ne
    (a b : ι) (hb : b ≠ a)
    (t s : ℝ) (uRest : Fin (Fintype.card ι - 1) → ℝ) :
    ((gaussianCoordinateSplit a).symm (t, uRest)) b =
      ((gaussianCoordinateSplit a).symm (s, uRest)) b := by
  let e := gaussianCoordinateIndexEquiv a
  have heb : e b ≠ e a := by
    intro h
    exact hb (e.injective h)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq heb
  have ht := congrArg (fun p => p.2 j)
    ((gaussianCoordinateSplit a).apply_symm_apply (t, uRest))
  have hs := congrArg (fun p => p.2 j)
    ((gaussianCoordinateSplit a).apply_symm_apply (s, uRest))
  change
    (gaussianCoordinateSplit a
      ((gaussianCoordinateSplit a).symm (t, uRest))).2 j =
      uRest j at ht
  change
    (gaussianCoordinateSplit a
      ((gaussianCoordinateSplit a).symm (s, uRest))).2 j =
      uRest j at hs
  rw [gaussianCoordinateSplit_apply_snd_apply] at ht hs
  have heq :
      e.symm ((e a).succAbove j) = b := by
    rw [hj, e.symm_apply_apply]
  simpa [e, heq] using ht.trans hs.symm

@[simp]
theorem gaussianComplexSqDist_real
    (x y : EuclideanSpace ℝ ι) :
    gaussianComplexSqDist (gaussianRealEmbed x) y =
      (‖x - y‖ ^ 2 : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [gaussianComplexSqDist, gaussianRealEmbed, PiLp.sub_apply,
    Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_sub]

/-- The Gaussian kernel is entire in its complex coordinate. -/
theorem differentiable_gaussianKernel
    (c : ℝ) (x : EuclideanSpace ℝ ι) :
    Differentiable ℂ (fun z : ι → ℂ => gaussianKernel c z x) := by
  simp only [gaussianKernel, gaussianComplexKernel, gaussianRealEmbed]
  fun_prop

/-- The norm of the complex Gaussian kernel separates into real decay and
imaginary growth. -/
theorem norm_gaussianKernel
    (c : ℝ) (z : ι → ℂ) (x : EuclideanSpace ℝ ι) :
    ‖gaussianKernel c z x‖ =
      ‖((Real.pi * c : ℂ) ^
          (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
        Real.exp
          (-Real.pi ^ 2 * c *
            (∑ i, (((z i).re - x i) ^ 2 - (z i).im ^ 2))) := by
  rw [gaussianKernel, gaussianComplexKernel, norm_mul, Complex.norm_exp]
  congr 1
  simp only [neg_mul, mul_re, ofReal_re, ofReal_im, neg_re, Complex.re_sum,
    gaussianRealEmbed, sq, mul_im, sub_re, sub_im, zero_mul, mul_zero,
    sub_zero]
  ring_nf

/-- A translated real Gaussian is integrable at every positive scale. -/
private theorem integrable_rexp_neg_sq_translate
    (c : ℝ) (hc : 0 < c) (u : EuclideanSpace ℝ ι) :
    Integrable (fun x : EuclideanSpace ℝ ι =>
      Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2)) := by
  let a : ℝ := Real.pi ^ 2 * c
  have ha : 0 < a := mul_pos (sq_pos_of_pos Real.pi_pos) hc
  have hcomplex :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ ι)
      (b := (a : ℂ))
      (by simpa using ha)
      0 0
  have hbase :
      Integrable (fun x : EuclideanSpace ℝ ι =>
        Real.exp (-Real.pi ^ 2 * c * ‖x‖ ^ 2)) := by
    have heq :
        (fun x : EuclideanSpace ℝ ι =>
          Real.exp (-Real.pi ^ 2 * c * ‖x‖ ^ 2)) =
        (fun x => ‖Complex.exp (-((a : ℂ)) * ‖x‖ ^ 2 +
          0 * inner ℝ (0 : EuclideanSpace ℝ ι) x)‖) := by
      funext x
      rw [Complex.norm_exp]
      congr 1
      simp only [zero_mul, add_zero]
      norm_cast
      simp [a]
    rw [heq]
    exact hcomplex.norm
  simpa using hbase.comp_sub_left u

/-- Multiplying a positive-scale complex Gaussian kernel by a measurable
bounded function gives an integrable function, without requiring the bounded
function itself to be integrable. -/
theorem integrable_gaussianKernel_mul_of_bounded
    (c : ℝ) (hc : 0 < c)
    (z : ι → ℂ)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun x => gaussianKernel c z x * f x) := by
  let u : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => (z i).re)
  let A : ℝ :=
    ‖((Real.pi * c : ℂ) ^
        (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
      Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) * B
  let K : ℝ :=
    ‖((Real.pi * c : ℂ) ^
        (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
      Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2)
  have hgauss :
      Integrable (fun x : EuclideanSpace ℝ ι =>
        Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2)) :=
    integrable_rexp_neg_sq_translate c hc u
  have hdom :
      Integrable (fun x : EuclideanSpace ℝ ι =>
        A * Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2)) :=
    hgauss.const_mul A
  refine Integrable.mono' hdom ?_ ?_
  · exact
      ((show Continuous fun x : EuclideanSpace ℝ ι =>
          gaussianKernel c z x from by
            simp only [gaussianKernel, gaussianComplexKernel,
              gaussianRealEmbed]
            fun_prop).aestronglyMeasurable.mul hf_meas)
  · filter_upwards with x
    rw [norm_mul]
    have hsq :
        (∑ i, ((z i).re - x i) ^ 2) = ‖u - x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    have hkernel :
        ‖gaussianKernel c z x‖ =
          K * Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2) := by
      rw [norm_gaussianKernel, Finset.sum_sub_distrib, hsq]
      rw [show
        -Real.pi ^ 2 * c *
            (‖u - x‖ ^ 2 - ∑ i, (z i).im ^ 2) =
          Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2 +
            (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2) by ring,
        Real.exp_add]
      simp [K, mul_assoc]
    rw [hkernel]
    have hfactor_nonneg :
        0 ≤ K * Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2) := by
      positivity
    calc
      _ ≤
          (K * Real.exp (-Real.pi ^ 2 * c * ‖u - x‖ ^ 2)) * B :=
        mul_le_mul_of_nonneg_left (hB x) hfactor_nonneg
      _ = _ := by
        dsimp [A, K]
        ring

/-- On a unit complex ball, the positive-scale Gaussian kernels admit one
integrable real-variable norm bound. -/
theorem exists_integrable_norm_gaussianKernel_bound_ball
    (c : ℝ) (hc : 0 < c) (z : ι → ℂ) :
    ∃ bound : EuclideanSpace ℝ ι → ℝ,
      Integrable bound ∧
      ∀ w ∈ Metric.ball z 1, ∀ x, ‖gaussianKernel c w x‖ ≤ bound x := by
  let u : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => (z i).re)
  let a : ℝ := Real.pi ^ 2 * c
  let Y : ℝ := ∑ i, (|(z i).im| + 1) ^ 2
  let A : ℝ :=
    ‖((Real.pi * c : ℂ) ^
        (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
      Real.exp (a * (Y + Fintype.card ι))
  let bound : EuclideanSpace ℝ ι → ℝ :=
    fun x => A * Real.exp (-(a / 2) * ‖u - x‖ ^ 2)
  have ha : 0 < a := mul_pos (sq_pos_of_pos Real.pi_pos) hc
  have hgauss :
      Integrable (fun x : EuclideanSpace ℝ ι =>
        Real.exp (-(a / 2) * ‖u - x‖ ^ 2)) := by
    simpa [show -(a / 2) = -Real.pi ^ 2 * (c / 2) by simp [a]; ring] using
      integrable_rexp_neg_sq_translate (ι := ι) (c / 2) (by positivity) u
  refine ⟨bound, hgauss.const_mul A, ?_⟩
  intro w hw x
  have hw_norm : ‖w - z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hcoord (i : ι) : ‖w i - z i‖ < 1 :=
    (norm_le_pi_norm (w - z) i).trans_lt hw_norm
  have him (i : ι) : |(w i).im| ≤ |(z i).im| + 1 := by
    calc
      |(w i).im| ≤ |(z i).im| + |(w i).im - (z i).im| := by
        linarith [abs_sub_abs_le_abs_sub (w i).im (z i).im]
      _ ≤ |(z i).im| + ‖w i - z i‖ := by
        gcongr
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w i - z i)
      _ ≤ |(z i).im| + 1 := by
        gcongr
        exact le_of_lt (hcoord i)
  have him_sum :
      (∑ i, (w i).im ^ 2) ≤ Y := by
    apply Finset.sum_le_sum
    intro i _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (him i) 2
  have hre_delta (i : ι) :
      ((w i).re - (z i).re) ^ 2 ≤ 1 := by
    have habs : |(w i).re - (z i).re| < 1 := by
      calc
        |(w i).re - (z i).re| =
            |(w i - z i).re| := by rw [Complex.sub_re]
        _ ≤ ‖w i - z i‖ := Complex.abs_re_le_norm _
        _ < 1 := hcoord i
    simpa [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg ((w i).re - (z i).re))
        (le_of_lt habs) 2)
  have hre_delta_sum :
      (∑ i, ((w i).re - (z i).re) ^ 2) ≤ Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hre_delta i
      _ = Fintype.card ι := by simp
  have hreal :
      ‖u - x‖ ^ 2 / 2 - Fintype.card ι ≤
        ∑ i, ((w i).re - x i) ^ 2 := by
    have hpoint (i : ι) :
        ((z i).re - x i) ^ 2 ≤
          2 * (((w i).re - (z i).re) ^ 2 +
            ((w i).re - x i) ^ 2) := by
      nlinarith [sq_nonneg ((w i).re - (z i).re +
        ((w i).re - x i))]
    have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
    simp_rw [mul_add] at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hu :
        (∑ i, ((z i).re - x i) ^ 2) = ‖u - x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [hu] at hsum
    nlinarith
  rw [norm_gaussianKernel, Finset.sum_sub_distrib]
  have hexponent :
      -Real.pi ^ 2 * c *
          ((∑ i, ((w i).re - x i) ^ 2) - ∑ i, (w i).im ^ 2) ≤
        a * (Y + Fintype.card ι) - (a / 2) * ‖u - x‖ ^ 2 := by
    dsimp [a]
    nlinarith
  calc
    _ ≤
        ‖((Real.pi * c : ℂ) ^
            (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
          Real.exp
            (a * (Y + Fintype.card ι) - (a / 2) * ‖u - x‖ ^ 2) := by
      gcongr
    _ = bound x := by
      rw [show
        a * (Y + Fintype.card ι) - (a / 2) * ‖u - x‖ ^ 2 =
          a * (Y + Fintype.card ι) + (-(a / 2) * ‖u - x‖ ^ 2) by ring,
        Real.exp_add]
      simp [bound, A, mul_assoc]

/-- At a positive scale, Gaussian regularization of any measurable bounded
function is entire. -/
theorem differentiable_gaussianRegularization_of_bounded
    (c : ℝ) (hc : 0 < c)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Differentiable ℂ (gaussianRegularization c f) := by
  intro z
  obtain ⟨kernelBound, hkernelBound_int, hkernelBound⟩ :=
    exists_integrable_norm_gaussianKernel_bound_ball c hc z
  let s : Set (ι → ℂ) := Metric.ball z (1 / 2 : ℝ)
  let F : (ι → ℂ) → EuclideanSpace ℝ ι → ℂ :=
    fun w x => gaussianKernel c w x * f x
  let F' :
      (ι → ℂ) → EuclideanSpace ℝ ι → ((ι → ℂ) →L[ℂ] ℂ) :=
    fun w x => (f x) • fderiv ℂ (fun u : ι → ℂ => gaussianKernel c u x) w
  let bound : EuclideanSpace ℝ ι → ℝ :=
    fun x => (4 * B) * kernelBound x
  have hB_nonneg : 0 ≤ B := by
    exact (norm_nonneg (f 0)).trans (hB 0)
  have hrealEmbed_cont :
      Continuous (gaussianRealEmbed : EuclideanSpace ℝ ι → ι → ℂ) := by
    refine continuous_pi ?_
    intro i
    exact Complex.continuous_ofReal.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous
  have hkernel_contDiff :
      ContDiff ℂ 1
        (Function.uncurry
          (fun p : (ι → ℂ) × (ι → ℂ) =>
            fun w : ι → ℂ => gaussianComplexKernel c w p.1)) := by
    simp only [gaussianComplexKernel]
    fun_prop
  have hkernel_fderiv_cont :
      Continuous
        (fun p : (ι → ℂ) × (ι → ℂ) =>
          fderiv ℂ
            (fun w : ι → ℂ => gaussianComplexKernel c w p.1)
            p.2) := by
    exact Continuous.fderiv_one hkernel_contDiff continuous_snd
  have hreal_kernel_fderiv_cont :
      Continuous
        (fun p : (ι → ℂ) × EuclideanSpace ℝ ι =>
          fderiv ℂ
            (fun w : ι → ℂ => gaussianKernel c w p.2)
            p.1) := by
    simpa [gaussianKernel] using
      hkernel_fderiv_cont.comp
        ((hrealEmbed_cont.comp continuous_snd).prodMk continuous_fst)
  have hF_meas :
      ∀ᶠ w in nhds z, AEStronglyMeasurable (F w) volume := by
    refine Filter.Eventually.of_forall ?_
    intro w
    exact
      ((show Continuous fun x : EuclideanSpace ℝ ι =>
          gaussianKernel c w x from by
            simp only [gaussianKernel, gaussianComplexKernel,
              gaussianRealEmbed]
            fun_prop).aestronglyMeasurable.mul hf_meas)
  have hF_int : Integrable (F z) volume := by
    exact integrable_gaussianKernel_mul_of_bounded c hc z hf_meas B hB
  have hF'_meas : AEStronglyMeasurable (F' z) volume := by
    exact hf_meas.smul
      (hreal_kernel_fderiv_cont.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hkernelBound_nonneg :
      ∀ x, 0 ≤ kernelBound x := by
    intro x
    exact (norm_nonneg (gaussianKernel c z x)).trans
      (hkernelBound z (Metric.mem_ball_self zero_lt_one) x)
  have h_bound :
      ∀ᵐ x ∂volume, ∀ w ∈ s, ‖F' w x‖ ≤ bound x := by
    refine Filter.Eventually.of_forall ?_
    intro x w hw
    have hwz : dist w z < 1 / 2 := by
      simpa [s, Metric.mem_ball] using hw
    have hball_sub :
        Metric.ball w (1 / 2 : ℝ) ⊆ Metric.ball z 1 := by
      intro q hq
      rw [Metric.mem_ball] at hq ⊢
      exact (dist_triangle q w z).trans_lt (by linarith)
    have hkernel_deriv :
        ‖fderiv ℂ (fun u : ι → ℂ => gaussianKernel c u x) w‖ ≤
          4 * kernelBound x := by
      have hmaps :
          Set.MapsTo
            (fun u : ι → ℂ => gaussianKernel c u x)
            (Metric.ball w (1 / 2 : ℝ))
            (Metric.closedBall (gaussianKernel c w x)
              (2 * kernelBound x)) := by
        intro q hq
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖gaussianKernel c q x - gaussianKernel c w x‖ ≤
              ‖gaussianKernel c q x‖ + ‖gaussianKernel c w x‖ :=
            norm_sub_le _ _
          _ ≤ kernelBound x + kernelBound x := by
            gcongr
            · exact hkernelBound q (hball_sub hq) x
            · exact hkernelBound w (hball_sub
                (Metric.mem_ball_self (by positivity))) x
          _ = 2 * kernelBound x := by ring
      have hschwarz :=
        norm_fderiv_le_div_of_mapsTo_ball
          (f := fun u : ι → ℂ => gaussianKernel c u x)
          (c := w) (R₁ := (1 / 2 : ℝ))
          (R₂ := 2 * kernelBound x)
          (differentiable_gaussianKernel c x).differentiableOn
          hmaps (by positivity)
      convert hschwarz using 1 <;> ring
    calc
      ‖F' w x‖ =
          ‖f x‖ *
            ‖fderiv ℂ (fun u : ι → ℂ => gaussianKernel c u x) w‖ := by
        simpa [F'] using
          norm_smul (f x)
            (fderiv ℂ (fun u : ι → ℂ => gaussianKernel c u x) w)
      _ ≤ B * (4 * kernelBound x) :=
        mul_le_mul (hB x) hkernel_deriv
          (norm_nonneg _) hB_nonneg
      _ = bound x := by simp [bound]; ring
  have hbound_int : Integrable bound volume :=
    hkernelBound_int.const_mul (4 * B)
  have h_diff :
      ∀ᵐ x ∂volume, ∀ w ∈ s, HasFDerivAt (F · x) (F' w x) w := by
    refine Filter.Eventually.of_forall ?_
    intro x w _hw
    simpa [F, F'] using
      ((differentiable_gaussianKernel c x w).hasFDerivAt.mul_const (f x))
  have hderiv :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds z (by positivity : (0 : ℝ) < 1 / 2))
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [gaussianRegularization, F] using hderiv.differentiableAt

/-- One-variable Gaussian weight used in finite contour shifts. -/
def gaussianContourWeight (b z u : ℂ) : ℂ :=
  Complex.exp (-b * (z - u) ^ 2)

/-- A holomorphic function multiplied by a Gaussian weight. -/
def gaussianContourIntegrand
    (b z : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ :=
  g u * gaussianContourWeight b z u

/-- Exact norm of a real Gaussian weight on a vertical line. -/
theorem norm_gaussianContourWeight_ofReal
    (c x T v : ℝ) :
    ‖gaussianContourWeight c x (T + v * I)‖ =
      Real.exp (-c * ((x - T) ^ 2 - v ^ 2)) := by
  rw [gaussianContourWeight, Complex.norm_exp]
  simp only [neg_mul, mul_re, ofReal_re, ofReal_im, neg_re, sub_re,
    add_re, mul_im, sub_im, add_im, I_re, I_im, zero_mul, mul_zero,
    zero_add, sq]
  congr 1
  ring

/-- A bounded holomorphic factor on a finite vertical edge is controlled by
the explicit Gaussian edge norm. -/
theorem norm_integral_gaussianContourIntegrand_vertical_le
    (g : ℂ → ℂ) (c x T y C : ℝ)
    (hc : 0 ≤ c)
    (hC : 0 ≤ C)
    (hg :
      ∀ v ∈ Set.uIcc 0 y,
        ‖g (T + v * I)‖ ≤ C) :
    ‖∫ v : ℝ in 0..y,
        gaussianContourIntegrand c x g (T + v * I)‖ ≤
      C * Real.exp (-c * ((x - T) ^ 2 - y ^ 2)) * |y| := by
  have hbound :
      ‖∫ v : ℝ in 0..y,
          gaussianContourIntegrand c x g (T + v * I)‖ ≤
        (C * Real.exp (-c * ((x - T) ^ 2 - y ^ 2))) *
          |y - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro v hv
    have hv' : v ∈ Set.uIcc 0 y :=
      Set.uIoc_subset_uIcc hv
    have hv_abs : |v| ≤ |y| := by
      simpa using Set.abs_sub_left_of_mem_uIcc hv'
    have hv_sq : v ^ 2 ≤ y ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq.mpr hv_abs)
    have hexp :
        Real.exp (-c * ((x - T) ^ 2 - v ^ 2)) ≤
          Real.exp (-c * ((x - T) ^ 2 - y ^ 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (by nlinarith [hv_sq]) (by linarith)
    calc
      ‖gaussianContourIntegrand c x g (T + v * I)‖ =
          ‖g (T + v * I)‖ *
            Real.exp (-c * ((x - T) ^ 2 - v ^ 2)) := by
        rw [gaussianContourIntegrand, norm_mul,
          norm_gaussianContourWeight_ofReal]
      _ ≤ C * Real.exp (-c * ((x - T) ^ 2 - v ^ 2)) :=
        mul_le_mul_of_nonneg_right (hg v hv') (Real.exp_nonneg _)
      _ ≤ C * Real.exp (-c * ((x - T) ^ 2 - y ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hC
  simpa using hbound

/-- Exact finite-rectangle contour identity for a Gaussian-weighted
holomorphic function. No decay or global growth hypothesis is needed; the two
vertical-edge terms remain explicit. -/
theorem gaussianContour_horizontal_shift
    (b z : ℂ) (g : ℂ → ℂ) (T y : ℝ)
    (hg :
      DifferentiableOn ℂ g
        (Set.uIcc (-T) T ×ℂ Set.uIcc 0 y)) :
    (∫ x : ℝ in -T..T,
        gaussianContourIntegrand b z g x) -
      (∫ x : ℝ in -T..T,
        gaussianContourIntegrand b z g (x + y * I)) =
      I * (∫ v : ℝ in 0..y,
        gaussianContourIntegrand b z g (-T + v * I)) -
      I * (∫ v : ℝ in 0..y,
        gaussianContourIntegrand b z g (T + v * I)) := by
  have hkernel :
      Differentiable ℂ (fun u : ℂ => gaussianContourWeight b z u) := by
    simp only [gaussianContourWeight]
    fun_prop
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (gaussianContourIntegrand b z g)
      (-T : ℂ) (T + y * I : ℂ)
      (by
        simpa using hg.mul hkernel.differentiableOn)
  have hboundary' :
      (∫ x : ℝ in -T..T,
          gaussianContourIntegrand b z g x) -
        (∫ x : ℝ in -T..T,
          gaussianContourIntegrand b z g (x + y * I)) +
        I * (∫ v : ℝ in 0..y,
          gaussianContourIntegrand b z g (T + v * I)) -
        I * (∫ v : ℝ in 0..y,
          gaussianContourIntegrand b z g (-T + v * I)) = 0 := by
    simpa [gaussianContourIntegrand] using hboundary
  linear_combination hboundary'

/-- A uniformly bounded horizontal slice multiplied by a positive Gaussian
weight is integrable. -/
theorem integrable_gaussianContourIntegrand_horizontal_of_bounded
    (g : ℂ → ℂ) (c x y B : ℝ)
    (hc : 0 < c)
    (hg_meas :
      AEStronglyMeasurable
        (fun t : ℝ => g (t + y * I)))
    (hB : ∀ t : ℝ, ‖g (t + y * I)‖ ≤ B) :
    Integrable
      (fun t : ℝ =>
        gaussianContourIntegrand c x g (t + y * I)) := by
  have hgauss :
      Integrable (fun t : ℝ => Real.exp (-c * (x - t) ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq hc).comp_sub_left x
  let C : ℝ := B * Real.exp (c * y ^ 2)
  have hdom :
      Integrable
        (fun t : ℝ => C * Real.exp (-c * (x - t) ^ 2)) :=
    hgauss.const_mul C
  refine Integrable.mono' hdom ?_ ?_
  · exact hg_meas.mul
      ((show Continuous
          (fun t : ℝ => gaussianContourWeight c x (t + y * I)) by
        simp only [gaussianContourWeight]
        fun_prop).aestronglyMeasurable)
  · filter_upwards with t
    rw [gaussianContourIntegrand, norm_mul,
      norm_gaussianContourWeight_ofReal]
    have hexp :
        Real.exp (-c * ((x - t) ^ 2 - y ^ 2)) =
          Real.exp (c * y ^ 2) *
            Real.exp (-c * (x - t) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    calc
      ‖g (↑t + ↑y * I)‖ *
          (Real.exp (c * y ^ 2) *
            Real.exp (-c * (x - t) ^ 2)) ≤
        B * (Real.exp (c * y ^ 2) *
          Real.exp (-c * (x - t) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hB t) (by positivity)
      _ = C * Real.exp (-c * (x - t) ^ 2) := by
        simp [C]
        ring

/-- A uniformly bounded finite vertical Gaussian edge vanishes when its real
coordinate escapes quadratically from the Gaussian center. -/
theorem tendsto_integral_gaussianContourIntegrand_vertical_edge_atTop
    (g : ℂ → ℂ) (c x y B : ℝ) (edge : ℝ → ℝ)
    (hc : 0 < c)
    (hB : 0 ≤ B)
    (hg :
      ∀ T : ℝ, ∀ v ∈ Set.uIcc 0 y,
        ‖g (edge T + v * I)‖ ≤ B)
    (hedge :
      Tendsto
        (fun T : ℝ => (x - edge T) ^ 2 - y ^ 2)
        atTop atTop) :
    Tendsto
      (fun T : ℝ =>
        ∫ v : ℝ in 0..y,
          gaussianContourIntegrand c x g (edge T + v * I))
      atTop (nhds 0) := by
  have hscale :
      Tendsto
        (fun T : ℝ => c * ((x - edge T) ^ 2 - y ^ 2))
        atTop atTop :=
    hedge.const_mul_atTop hc
  have hexp :
      Tendsto
        (fun T : ℝ =>
          Real.exp (-c * ((x - edge T) ^ 2 - y ^ 2)))
        atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_apply, neg_mul] using
      (tendsto_neg_atTop_atBot.comp hscale)
  have hupper :
      Tendsto
        (fun T : ℝ =>
          B * Real.exp (-c * ((x - edge T) ^ 2 - y ^ 2)) * |y|)
        atTop (nhds 0) := by
    convert (hexp.const_mul B).mul_const |y| using 1 <;> simp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun T =>
        norm_integral_gaussianContourIntegrand_vertical_le
          g c x (edge T) y B hc.le hB (hg T))

/-- Exact full-line contour shift for a uniformly bounded strip-holomorphic
function and a positive Gaussian weight. -/
theorem integral_gaussianContour_horizontal_shift
    (g : ℂ → ℂ) (c x y B : ℝ)
    (hc : 0 < c)
    (hB : 0 ≤ B)
    (hg_diff :
      DifferentiableOn ℂ g
        (Set.univ ×ℂ Set.uIcc 0 y))
    (hg_bound :
      ∀ t : ℝ, ∀ v ∈ Set.uIcc 0 y,
        ‖g (t + v * I)‖ ≤ B) :
    (∫ t : ℝ, gaussianContourIntegrand c x g t) =
      ∫ t : ℝ,
        gaussianContourIntegrand c x g (t + y * I) := by
  have hline_cont (v : ℝ) (hv : v ∈ Set.uIcc 0 y) :
      Continuous (fun t : ℝ => g (t + v * I)) := by
    exact hg_diff.continuousOn.comp_continuous
      (by fun_prop)
      (fun t => by
        rw [Complex.mem_reProdIm]
        exact ⟨Set.mem_univ _, by simpa using hv⟩)
  have hreal_int :
      Integrable
        (fun t : ℝ => gaussianContourIntegrand c x g t) := by
    simpa using
      integrable_gaussianContourIntegrand_horizontal_of_bounded
        g c x 0 B hc
        (by simpa using (hline_cont 0 Set.left_mem_uIcc).aestronglyMeasurable)
        (by
          intro t
          simpa using hg_bound t 0 Set.left_mem_uIcc)
  have hshift_int :
      Integrable
        (fun t : ℝ =>
          gaussianContourIntegrand c x g (t + y * I)) :=
    integrable_gaussianContourIntegrand_horizontal_of_bounded
      g c x y B hc
      (hline_cont y Set.right_mem_uIcc).aestronglyMeasurable
      (fun t => hg_bound t y Set.right_mem_uIcc)
  have hfinite (T : ℝ) :
      (∫ t : ℝ in -T..T,
          gaussianContourIntegrand c x g t) -
        (∫ t : ℝ in -T..T,
          gaussianContourIntegrand c x g (t + y * I)) =
        I * (∫ v : ℝ in 0..y,
          gaussianContourIntegrand c x g (-T + v * I)) -
        I * (∫ v : ℝ in 0..y,
          gaussianContourIntegrand c x g (T + v * I)) := by
    apply gaussianContour_horizontal_shift
    exact hg_diff.mono (by
      intro z hz
      rw [Complex.mem_reProdIm] at hz ⊢
      exact ⟨Set.mem_univ _, hz.2⟩)
  have hreal_lim :
      Tendsto
        (fun T : ℝ =>
          ∫ t : ℝ in -T..T,
            gaussianContourIntegrand c x g t)
        atTop
        (nhds (∫ t : ℝ, gaussianContourIntegrand c x g t)) :=
    intervalIntegral_tendsto_integral hreal_int
      tendsto_neg_atTop_atBot tendsto_id
  have hshift_lim :
      Tendsto
        (fun T : ℝ =>
          ∫ t : ℝ in -T..T,
            gaussianContourIntegrand c x g (t + y * I))
        atTop
        (nhds (∫ t : ℝ,
          gaussianContourIntegrand c x g (t + y * I))) :=
    intervalIntegral_tendsto_integral hshift_int
      tendsto_neg_atTop_atBot tendsto_id
  have hright_lim :
      Tendsto
        (fun T : ℝ =>
          I * (∫ v : ℝ in 0..y,
            gaussianContourIntegrand c x g (-T + v * I)) -
          I * (∫ v : ℝ in 0..y,
            gaussianContourIntegrand c x g (T + v * I)))
        atTop (nhds 0) := by
    have hleft :
        Tendsto
          (fun T : ℝ =>
            ∫ v : ℝ in 0..y,
              gaussianContourIntegrand c x g (-T + v * I))
          atTop (nhds 0) := by
      have hplus :
          Tendsto (fun T : ℝ => T + x) atTop atTop :=
        tendsto_atTop_add_const_right atTop x tendsto_id
      have hsq :
          Tendsto (fun T : ℝ => (T + x) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hplus
      have hsep :
          Tendsto (fun T : ℝ => (T + x) ^ 2 - y ^ 2)
            atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-y ^ 2) hsq)
      have hsep' :
          Tendsto (fun T : ℝ => (x - (-T)) ^ 2 - y ^ 2)
            atTop atTop := by
        convert hsep using 1
        ext T
        ring
      have hleft' :=
        tendsto_integral_gaussianContourIntegrand_vertical_edge_atTop
          g c x y B (fun T => -T) hc hB
          (fun T v hv => by simpa using hg_bound (-T) v hv) hsep'
      convert hleft' using 1 <;> simp
    have hright :
        Tendsto
          (fun T : ℝ =>
            ∫ v : ℝ in 0..y,
              gaussianContourIntegrand c x g (T + v * I))
          atTop (nhds 0) := by
      apply
        tendsto_integral_gaussianContourIntegrand_vertical_edge_atTop
          g c x y B id hc hB
      · simpa using hg_bound
      · have hminus :
            Tendsto (fun T : ℝ => T - x) atTop atTop := by
          simpa [sub_eq_add_neg] using
            (tendsto_atTop_add_const_right atTop (-x) tendsto_id)
        have hsq :
            Tendsto (fun T : ℝ => (T - x) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (α := ℝ)
            (by norm_num : (2 : ℕ) ≠ 0)).comp hminus
        have hsep :
            Tendsto (fun T : ℝ => (T - x) ^ 2 - y ^ 2)
              atTop atTop := by
          simpa [sub_eq_add_neg] using
            (tendsto_atTop_add_const_right atTop (-y ^ 2) hsq)
        convert hsep using 1
        ext T
        simp only [id_eq]
        ring
    simpa using (hleft.const_mul I).sub (hright.const_mul I)
  have hdiff_lim := hreal_lim.sub hshift_lim
  have hzero :
      (∫ t : ℝ, gaussianContourIntegrand c x g t) -
        (∫ t : ℝ,
          gaussianContourIntegrand c x g (t + y * I)) = 0 := by
    apply tendsto_nhds_unique hdiff_lim
    exact hright_lim.congr'
      (Filter.Eventually.of_forall fun T => (hfinite T).symm)
  exact sub_eq_zero.mp hzero

/-- Shift a complex Gaussian center back to the real axis while moving the
bounded holomorphic factor to the corresponding horizontal line. -/
theorem integral_gaussianContour_center_shift
    (g : ℂ → ℂ) (c x y B : ℝ)
    (hc : 0 < c)
    (hB : 0 ≤ B)
    (hg_diff :
      DifferentiableOn ℂ g
        (Set.univ ×ℂ Set.uIcc 0 y))
    (hg_bound :
      ∀ t : ℝ, ∀ v ∈ Set.uIcc 0 y,
        ‖g (t + v * I)‖ ≤ B) :
    (∫ t : ℝ,
        gaussianContourIntegrand c (x + y * I) g t) =
      ∫ t : ℝ,
        g (t + y * I) * gaussianContourWeight c x t := by
  let h : ℂ → ℂ := fun w => g (w + y * I)
  have hmaps :
      Set.MapsTo (fun w : ℂ => w + y * I)
        (Set.univ ×ℂ Set.uIcc 0 (-y))
        (Set.univ ×ℂ Set.uIcc 0 y) := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw ⊢
    constructor
    · exact Set.mem_univ _
    · rcases Set.mem_uIcc.mp hw.2 with hv | hv
      · have him :
            ((fun w : ℂ => w + y * I) w).im = w.im + y := by simp
        rw [him]
        exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
      · have him :
            ((fun w : ℂ => w + y * I) w).im = w.im + y := by simp
        rw [him]
        exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
  have hh_diff :
      DifferentiableOn ℂ h
        (Set.univ ×ℂ Set.uIcc 0 (-y)) :=
    hg_diff.comp
      (by
        change DifferentiableOn ℂ (fun w : ℂ => w + y * I) _
        fun_prop)
      hmaps
  have hh_bound :
      ∀ t : ℝ, ∀ v ∈ Set.uIcc 0 (-y),
        ‖h (t + v * I)‖ ≤ B := by
    intro t v hv
    have hyv : y + v ∈ Set.uIcc 0 y := by
      rcases Set.mem_uIcc.mp hv with h | h
      · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
      · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
    have hb := hg_bound t (y + v) hyv
    convert hb using 1 <;> simp [h] <;> ring_nf
  have hshift :=
    integral_gaussianContour_horizontal_shift
      h c x (-y) B hc hB hh_diff hh_bound
  calc
    (∫ t : ℝ,
        gaussianContourIntegrand c (x + y * I) g t) =
      ∫ t : ℝ,
        gaussianContourIntegrand c x h (t + (-y) * I) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [h, gaussianContourIntegrand, gaussianContourWeight]
      congr 2 <;> ring
    _ = ∫ t : ℝ, gaussianContourIntegrand c x h t := by
      simpa using hshift.symm
    _ = ∫ t : ℝ,
        g (t + y * I) * gaussianContourWeight c x t := by
      apply integral_congr_ae
      filter_upwards with t
      rfl

set_option maxHeartbeats 1200000 in
/-- Shift one coordinate of a multivariable Gaussian center back to the real
axis while moving the input function to the corresponding horizontal slice.

The inactive coordinates of `z` may already be complex. This form is
designed to be iterated coordinate by coordinate. -/
theorem gaussianRegularization_update_eq_shifted
    [DecidableEq ι]
    (F : (ι → ℂ) → ℂ)
    (a : ι)
    (c : ℝ) (hc : 0 < c)
    (z : ι → ℂ)
    (x y B C : ℝ)
    (hreal_cont : Continuous (gaussianRealSliceInput F))
    (hshift_cont :
      Continuous (gaussianCoordinateShiftedInput F a y))
    (hreal_bound :
      ∀ u : EuclideanSpace ℝ ι,
        ‖gaussianRealSliceInput F u‖ ≤ B)
    (hshift_bound :
      ∀ u : EuclideanSpace ℝ ι,
        ‖gaussianCoordinateShiftedInput F a y u‖ ≤ C)
    (hC : 0 ≤ C)
    (hline_diff :
      ∀ xBase : ι → ℝ,
        DifferentiableOn ℂ (gaussianCoordinateLine F xBase a)
          (Set.univ ×ℂ Set.uIcc 0 y))
    (hline_bound :
      ∀ (xBase : ι → ℝ) (t v : ℝ),
        v ∈ Set.uIcc 0 y →
          ‖gaussianCoordinateLine F xBase a (t + v * I)‖ ≤ C) :
    gaussianRegularization c (gaussianRealSliceInput F)
        (Function.update z a ((x : ℂ) + y * I)) =
      gaussianRegularization c
        (gaussianCoordinateShiftedInput F a y)
        (Function.update z a x) := by
  let zLeft : ι → ℂ :=
    Function.update z a ((x : ℂ) + y * I)
  let zRight : ι → ℂ :=
    Function.update z a x
  have hleft_int :
      Integrable (fun u =>
        gaussianKernel c zLeft u * gaussianRealSliceInput F u) :=
    integrable_gaussianKernel_mul_of_bounded
      c hc zLeft hreal_cont.aestronglyMeasurable B hreal_bound
  have hright_int :
      Integrable (fun u =>
        gaussianKernel c zRight u *
          gaussianCoordinateShiftedInput F a y u) :=
    integrable_gaussianKernel_mul_of_bounded
      c hc zRight hshift_cont.aestronglyMeasurable C hshift_bound
  rw [gaussianRegularization, gaussianRegularization]
  change
    (∫ u : EuclideanSpace ℝ ι,
      gaussianKernel c zLeft u * gaussianRealSliceInput F u) =
      ∫ u : EuclideanSpace ℝ ι,
        gaussianKernel c zRight u *
          gaussianCoordinateShiftedInput F a y u
  rw [integral_gaussianCoordinateSplit a _ hleft_int]
  rw [integral_gaussianCoordinateSplit a _ hright_int]
  apply integral_congr_ae
  filter_upwards with uRest
  let uAt : ℝ → EuclideanSpace ℝ ι :=
    fun t => (gaussianCoordinateSplit a).symm (t, uRest)
  let xBase : ι → ℝ := fun b => uAt 0 b
  let g : ℂ → ℂ := gaussianCoordinateLine F xBase a
  let A : ℂ :=
    ((Real.pi * c : ℂ) ^
        (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ)) *
      Complex.exp
        (-Real.pi ^ 2 * c *
          ∑ b ∈ Finset.univ.erase a,
            (z b - (uAt 0 b : ℂ)) ^ 2)
  have hu_selected (t : ℝ) : uAt t a = t := by
    simp [uAt]
  have hu_ne (t : ℝ) (b : ι) (hb : b ≠ a) :
      uAt t b = uAt 0 b := by
    exact gaussianCoordinateSplit_symm_apply_ne a b hb t 0 uRest
  have hrealPoint (t : ℝ) :
      gaussianRealEmbed (uAt t) =
        Function.update (fun b => (xBase b : ℂ)) a t := by
    ext b
    by_cases hb : b = a
    · subst b
      simp [xBase, hu_selected, gaussianRealEmbed]
    · simp [Function.update, hb, xBase, hu_ne t b hb,
        gaussianRealEmbed]
  have hrealInput (t : ℝ) :
      gaussianRealSliceInput F (uAt t) = g t := by
    simp only [gaussianRealSliceInput, g, gaussianCoordinateLine]
    rw [hrealPoint]
  have hshiftInput (t : ℝ) :
      gaussianCoordinateShiftedInput F a y (uAt t) =
        g (t + y * I) := by
    simp only [gaussianCoordinateShiftedInput, g, gaussianCoordinateLine]
    congr 1
    ext b
    by_cases hb : b = a
    · subst b
      simp [hu_selected]
    · simp [Function.update, hb, xBase, hu_ne t b hb,
        gaussianRealEmbed]
  have hsum_left (t : ℝ) :
      (∑ b : ι, (zLeft b - (uAt t b : ℂ)) ^ 2) =
        (((x : ℂ) + y * I) - t) ^ 2 +
          ∑ b ∈ Finset.univ.erase a,
            (z b - (uAt 0 b : ℂ)) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    · simp [zLeft, hu_selected]
    · apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      simp [zLeft, hba, hu_ne t b hba]
  have hsum_right (t : ℝ) :
      (∑ b : ι, (zRight b - (uAt t b : ℂ)) ^ 2) =
        ((x : ℂ) - t) ^ 2 +
          ∑ b ∈ Finset.univ.erase a,
            (z b - (uAt 0 b : ℂ)) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    · simp [zRight, hu_selected]
    · apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      simp [zRight, hba, hu_ne t b hba]
  have hleft_factor (t : ℝ) :
      gaussianKernel c zLeft (uAt t) *
          gaussianRealSliceInput F (uAt t) =
        A * gaussianContourIntegrand
          (Real.pi ^ 2 * c) ((x : ℂ) + y * I) g t := by
    rw [hrealInput]
    simp only [gaussianKernel, gaussianComplexKernel,
      gaussianComplexSqDist, gaussianRealEmbed,
      gaussianContourIntegrand, gaussianContourWeight, A]
    rw [hsum_left]
    have hexpArg :
        -((Real.pi : ℂ) ^ 2) * c *
            ((((x : ℂ) + y * I) - t) ^ 2 +
              ∑ b ∈ Finset.univ.erase a,
                (z b - (uAt 0 b : ℂ)) ^ 2) =
          (-((Real.pi : ℂ) ^ 2) * c *
            (((x : ℂ) + y * I) - t) ^ 2) +
          (-((Real.pi : ℂ) ^ 2) * c *
            ∑ b ∈ Finset.univ.erase a,
              (z b - (uAt 0 b : ℂ)) ^ 2) := by
      ring
    rw [hexpArg, Complex.exp_add]
    ring
  have hright_factor (t : ℝ) :
      gaussianKernel c zRight (uAt t) *
          gaussianCoordinateShiftedInput F a y (uAt t) =
        A * (g (t + y * I) *
          gaussianContourWeight (Real.pi ^ 2 * c) x t) := by
    rw [hshiftInput]
    simp only [gaussianKernel, gaussianComplexKernel,
      gaussianComplexSqDist, gaussianRealEmbed,
      gaussianContourWeight, A]
    rw [hsum_right]
    have hexpArg :
        -((Real.pi : ℂ) ^ 2) * c *
            (((x : ℂ) - t) ^ 2 +
              ∑ b ∈ Finset.univ.erase a,
                (z b - (uAt 0 b : ℂ)) ^ 2) =
          (-((Real.pi : ℂ) ^ 2) * c * ((x : ℂ) - t) ^ 2) +
          (-((Real.pi : ℂ) ^ 2) * c *
            ∑ b ∈ Finset.univ.erase a,
              (z b - (uAt 0 b : ℂ)) ^ 2) := by
      ring
    rw [hexpArg, Complex.exp_add]
    ring
  change
    (∫ t : ℝ,
      gaussianKernel c zLeft (uAt t) *
        gaussianRealSliceInput F (uAt t)) =
      ∫ t : ℝ,
        gaussianKernel c zRight (uAt t) *
          gaussianCoordinateShiftedInput F a y (uAt t)
  rw [show (fun t : ℝ =>
      gaussianKernel c zLeft (uAt t) *
        gaussianRealSliceInput F (uAt t)) =
      fun t : ℝ => A * gaussianContourIntegrand
        (Real.pi ^ 2 * c) ((x : ℂ) + y * I) g (t : ℂ) by
      funext t
      exact hleft_factor t]
  rw [show (fun t : ℝ =>
      gaussianKernel c zRight (uAt t) *
        gaussianCoordinateShiftedInput F a y (uAt t)) =
      fun t : ℝ => A * (g ((t : ℂ) + y * I) *
        gaussianContourWeight (Real.pi ^ 2 * c) x (t : ℂ)) by
      funext t
      exact hright_factor t]
  have hcenter :=
    integral_gaussianContour_center_shift
      g (Real.pi ^ 2 * c) x y C
      (by positivity) hC (hline_diff xBase)
      (fun t v hv => hline_bound xBase t v hv)
  have hcenter' :
      (∫ t : ℝ,
          gaussianContourIntegrand
            (Real.pi ^ 2 * c) ((x : ℂ) + y * I) g t) =
        ∫ t : ℝ,
          g (t + y * I) *
            gaussianContourWeight (Real.pi ^ 2 * c) x t := by
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hcenter
  calc
    (∫ t : ℝ,
        A * gaussianContourIntegrand
          (Real.pi ^ 2 * c) ((x : ℂ) + y * I) g t) =
      A * ∫ t : ℝ,
        gaussianContourIntegrand
          (Real.pi ^ 2 * c) ((x : ℂ) + y * I) g t :=
      MeasureTheory.integral_const_mul A _
    _ = A * ∫ t : ℝ,
        g (t + y * I) *
          gaussianContourWeight (Real.pi ^ 2 * c) x t :=
      congrArg (fun q : ℂ => A * q) hcenter'
    _ = ∫ t : ℝ,
        A * (g (t + y * I) *
          gaussianContourWeight (Real.pi ^ 2 * c) x t) :=
      (MeasureTheory.integral_const_mul A _).symm

@[simp]
theorem gaussianKernel_real
    (c : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianKernel c (gaussianRealEmbed x) y =
      ((Real.pi * c : ℂ) ^
          (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ) *
        Complex.exp (-Real.pi ^ 2 * c * (‖x - y‖ ^ 2 : ℝ))) := by
  change
    ((Real.pi * c : ℂ) ^
        (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ) *
      Complex.exp
        (-Real.pi ^ 2 * c *
          gaussianComplexSqDist (gaussianRealEmbed x) y)) =
      _
  rw [gaussianComplexSqDist_real]

/-- The normalized positive-scale Gaussian kernel has total real mass one. -/
theorem integral_norm_gaussianKernel_real
    (c : ℝ) (hc : 0 < c)
    (x : EuclideanSpace ℝ ι) :
    (∫ y : EuclideanSpace ℝ ι,
      ‖gaussianKernel c (gaussianRealEmbed x) y‖) = 1 := by
  let p : ℝ := Module.finrank ℝ (EuclideanSpace ℝ ι) / 2
  have hpoint :
      ∀ y : EuclideanSpace ℝ ι,
        ‖gaussianKernel c (gaussianRealEmbed x) y‖ =
          (Real.pi * c) ^ p *
            Real.exp (-Real.pi ^ 2 * c * ‖x - y‖ ^ 2) := by
    intro y
    rw [norm_gaussianKernel]
    simp only [gaussianRealEmbed, ofReal_re, ofReal_im]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    have hP :
        ‖((Real.pi * c : ℂ) ^
            (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ =
          (Real.pi * c) ^ p := by
      rw [← Complex.ofReal_mul]
      have hexponent :
          ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℂ) / 2) =
            (((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / 2 : ℝ) : ℂ) := by
        norm_num
      rw [hexponent, Complex.norm_cpow_real]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos Real.pi_pos hc)]
    rw [hP]
    have hsum :
        (∑ i : ι, (x i - y i) ^ 2) = ‖x - y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [hsum]
  rw [show
      (fun y : EuclideanSpace ℝ ι =>
        ‖gaussianKernel c (gaussianRealEmbed x) y‖) =
        fun y =>
          (Real.pi * c) ^ p *
            Real.exp (-Real.pi ^ 2 * c * ‖x - y‖ ^ 2) by
      funext y
      exact hpoint y]
  rw [integral_const_mul]
  have htranslate :
      (∫ y : EuclideanSpace ℝ ι,
          Real.exp (-Real.pi ^ 2 * c * ‖x - y‖ ^ 2)) =
        ∫ v : EuclideanSpace ℝ ι,
          Real.exp (-Real.pi ^ 2 * c * ‖v‖ ^ 2) := by
    exact integral_sub_left_eq_self
      (fun v : EuclideanSpace ℝ ι =>
        Real.exp (-Real.pi ^ 2 * c * ‖v‖ ^ 2))
      volume x
  rw [htranslate]
  have hgauss :
      (∫ v : EuclideanSpace ℝ ι,
          Real.exp (-Real.pi ^ 2 * c * ‖v‖ ^ 2)) =
        (Real.pi / (Real.pi ^ 2 * c)) ^ p := by
    simpa [p, show -Real.pi ^ 2 * c = -(Real.pi ^ 2 * c) by ring] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ ι)
        (show 0 < Real.pi ^ 2 * c by positivity))
  rw [hgauss]
  have hinside :
      (Real.pi * c) * (Real.pi / (Real.pi ^ 2 * c)) = 1 := by
    field_simp [Real.pi_ne_zero, ne_of_gt hc]
  calc
    (Real.pi * c) ^ p *
        (Real.pi / (Real.pi ^ 2 * c)) ^ p =
      ((Real.pi * c) *
        (Real.pi / (Real.pi ^ 2 * c))) ^ p := by
          exact (Real.mul_rpow (by positivity) (by positivity)).symm
    _ = 1 := by rw [hinside]; simp

/-- The total norm of a complex-centered Gaussian is its pure imaginary
growth factor. -/
theorem integral_norm_gaussianKernel
    (c : ℝ) (hc : 0 < c)
    (z : ι → ℂ) :
    (∫ y : EuclideanSpace ℝ ι, ‖gaussianKernel c z y‖) =
      Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) := by
  let u : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => (z i).re)
  have hpoint :
      ∀ y : EuclideanSpace ℝ ι,
        ‖gaussianKernel c z y‖ =
          Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) *
            ‖gaussianKernel c (gaussianRealEmbed u) y‖ := by
    intro y
    rw [norm_gaussianKernel, norm_gaussianKernel]
    simp only [gaussianRealEmbed, ofReal_re, ofReal_im]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    have hre :
        (∑ i : ι, ((u i : ℝ) - y i) ^ 2) =
          ∑ i : ι, ((z i).re - y i) ^ 2 := by
      rfl
    rw [hre, Finset.sum_sub_distrib]
    rw [show
      -Real.pi ^ 2 * c *
          ((∑ i : ι, ((z i).re - y i) ^ 2) -
            ∑ i : ι, (z i).im ^ 2) =
        Real.pi ^ 2 * c * ∑ i : ι, (z i).im ^ 2 +
          (-Real.pi ^ 2 * c *
            ∑ i : ι, ((z i).re - y i) ^ 2) by ring,
      Real.exp_add]
    ring
  rw [show
      (fun y : EuclideanSpace ℝ ι => ‖gaussianKernel c z y‖) =
        fun y =>
          Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) *
            ‖gaussianKernel c (gaussianRealEmbed u) y‖ by
      funext y
      exact hpoint y]
  rw [integral_const_mul, integral_norm_gaussianKernel_real c hc u]
  ring

/-- Gaussian regularization of a measurable bounded input preserves its
bound on the real locus. -/
theorem norm_gaussianRegularization_real_le_of_bounded
    (c : ℝ) (hc : 0 < c)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    (x : EuclideanSpace ℝ ι) :
    ‖gaussianRegularization c f (gaussianRealEmbed x)‖ ≤ B := by
  have hkernel_int :
      Integrable
        (fun y : EuclideanSpace ℝ ι =>
          gaussianKernel c (gaussianRealEmbed x) y) := by
    simpa using
      integrable_gaussianKernel_mul_of_bounded
        c hc (gaussianRealEmbed x)
        (f := fun _ : EuclideanSpace ℝ ι => (1 : ℂ))
        continuous_const.aestronglyMeasurable 1 (by simp)
  have hproduct_int :
      Integrable
        (fun y : EuclideanSpace ℝ ι =>
          gaussianKernel c (gaussianRealEmbed x) y * f y) :=
    integrable_gaussianKernel_mul_of_bounded
      c hc (gaussianRealEmbed x) hf_meas B hB
  rw [gaussianRegularization]
  calc
    ‖∫ y : EuclideanSpace ℝ ι,
        gaussianKernel c (gaussianRealEmbed x) y * f y‖ ≤
      ∫ y : EuclideanSpace ℝ ι,
        ‖gaussianKernel c (gaussianRealEmbed x) y * f y‖ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ ι,
        B * ‖gaussianKernel c (gaussianRealEmbed x) y‖ := by
          apply integral_mono hproduct_int.norm
            (hkernel_int.norm.const_mul B)
          intro y
          dsimp only
          rw [norm_mul]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left (hB y)
              (norm_nonneg (gaussianKernel c (gaussianRealEmbed x) y))
    _ = B := by
      rw [integral_const_mul, integral_norm_gaussianKernel_real c hc x]
      ring

/-- A bounded measurable input is controlled at a complex Gaussian center by
the exact imaginary Gaussian growth factor. -/
theorem norm_gaussianRegularization_le_imaginary_of_bounded
    (c : ℝ) (hc : 0 < c)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    (z : ι → ℂ) :
    ‖gaussianRegularization c f z‖ ≤
      Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) * B := by
  have hkernel_int :
      Integrable
        (fun y : EuclideanSpace ℝ ι => gaussianKernel c z y) := by
    simpa using
      integrable_gaussianKernel_mul_of_bounded
        c hc z
        (f := fun _ : EuclideanSpace ℝ ι => (1 : ℂ))
        continuous_const.aestronglyMeasurable 1 (by simp)
  have hproduct_int :
      Integrable
        (fun y : EuclideanSpace ℝ ι => gaussianKernel c z y * f y) :=
    integrable_gaussianKernel_mul_of_bounded c hc z hf_meas B hB
  rw [gaussianRegularization]
  calc
    ‖∫ y : EuclideanSpace ℝ ι, gaussianKernel c z y * f y‖ ≤
      ∫ y : EuclideanSpace ℝ ι, ‖gaussianKernel c z y * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ ι,
        B * ‖gaussianKernel c z y‖ := by
          apply integral_mono hproduct_int.norm
            (hkernel_int.norm.const_mul B)
          intro y
          dsimp only
          rw [norm_mul]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left (hB y)
              (norm_nonneg (gaussianKernel c z y))
    _ = Real.exp (Real.pi ^ 2 * c * ∑ i, (z i).im ^ 2) * B := by
      rw [integral_const_mul, integral_norm_gaussianKernel c hc z]
      ring

/-- Positive-scale Gaussian regularizations of bounded measurable inputs are
bounded on every complex interpolation strip between horizontal directions. -/
theorem hasBoundedHorizontalSegments_gaussianRegularization_of_bounded
    (c : ℝ) (hc : 0 < c)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B) :
    HasBoundedHorizontalSegments (gaussianRegularization c f) := by
  intro x y₀ y₁
  let Y : ℝ := ∑ i, (|y₀ i| + |y₁ i|) ^ 2
  refine
    ⟨Real.exp (Real.pi ^ 2 * c * Y) * B, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have him :=
    sum_sq_horizontalSegmentLine_im_le x y₀ y₁ w hw
  have hexp :
      Real.exp
          (Real.pi ^ 2 * c *
            ∑ i, (horizontalSegmentLine x y₀ y₁ w i).im ^ 2) ≤
        Real.exp (Real.pi ^ 2 * c * Y) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left him (by positivity)
  have hB_nonneg : 0 ≤ B :=
    (norm_nonneg (f 0)).trans (hB 0)
  exact
    (norm_gaussianRegularization_le_imaginary_of_bounded
      c hc hf_meas B hB
      (horizontalSegmentLine x y₀ y₁ w)).trans
        (mul_le_mul_of_nonneg_right hexp hB_nonneg)

/-- Uniform horizontal bounds for bounded-input Gaussian regularizations
propagate from a generating set of imaginary directions to its convex hull. -/
theorem gaussianRegularization_horizontalBound_convexHull_of_bounded
    (c : ℝ) (hc : 0 < c)
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_meas : AEStronglyMeasurable f)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    {C : ℝ} (hC : 0 < C)
    {S : Set (ι → ℝ)}
    (hS :
      S ⊆ horizontalBoundSet (gaussianRegularization c f) C) :
    convexHull ℝ S ⊆
      horizontalBoundSet (gaussianRegularization c f) C := by
  exact
    horizontalBound_convexHull
      (gaussianRegularization c f)
      (differentiable_gaussianRegularization_of_bounded
        c hc hf_meas B hB)
      (hasBoundedHorizontalSegments_gaussianRegularization_of_bounded
        c hc hf_meas B hB)
      hC hS

/-- Away from its real center, the normalized Gaussian kernel has vanishing
mass as the scale tends to infinity. -/
theorem tendsto_setIntegral_norm_gaussianKernel_real_compl_ball
    (x : EuclideanSpace ℝ ι) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto
      (fun c : ℝ =>
        ∫ y : EuclideanSpace ℝ ι in (Metric.ball x δ)ᶜ,
          ‖gaussianKernel c (gaussianRealEmbed x) y‖)
      atTop (nhds 0) := by
  let p : ℝ := Module.finrank ℝ (EuclideanSpace ℝ ι) / 2
  let b : ℝ := Real.pi ^ 2 * δ ^ 2 / 2
  let upper : ℝ → ℝ := fun c => 2 ^ p * Real.exp (-b * c)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hexp :
        Tendsto (fun c : ℝ => Real.exp (-(b * c))) atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hbc : Tendsto (fun c : ℝ => b * c) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
      simpa only [Function.comp_apply] using
        (tendsto_neg_atTop_atBot.comp hbc)
    simpa [upper, neg_mul] using hexp.const_mul (2 ^ p)
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Filter.Eventually.of_forall fun c =>
        integral_nonneg fun _ => norm_nonneg _)
      ?_
  filter_upwards [Ioi_mem_atTop 0] with c hc
  have hcpos : 0 < c := hc
  show
    (∫ y : EuclideanSpace ℝ ι in (Metric.ball x δ)ᶜ,
      ‖gaussianKernel c (gaussianRealEmbed x) y‖) ≤ upper c
  ·
    let P : ℝ :=
      ‖((Real.pi * c : ℂ) ^
          (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖
    let half : EuclideanSpace ℝ ι → ℝ :=
      fun y => Real.exp (-Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2)
    have hhalf_int : Integrable half := by
      have hbase :=
        integrable_rexp_neg_sq_translate
          (ι := ι) (c / 2) (by positivity) x
      simpa [half] using hbase
    have hkernel_int :
        Integrable
          (fun y : EuclideanSpace ℝ ι =>
            ‖gaussianKernel c (gaussianRealEmbed x) y‖) := by
      exact
        (integrable_gaussianKernel_mul_of_bounded
          c hc (gaussianRealEmbed x)
          (show AEStronglyMeasurable
              (fun _ : EuclideanSpace ℝ ι => (1 : ℂ)) by fun_prop)
          1 (by intro y; simp)).norm.congr
          (Filter.Eventually.of_forall fun y => by simp)
    have hpoint :
        ∀ y ∈ (Metric.ball x δ)ᶜ,
          ‖gaussianKernel c (gaussianRealEmbed x) y‖ ≤
            (P * Real.exp (-b * c)) * half y := by
      intro y hy
      have hdist : δ ≤ ‖x - y‖ := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
      have hsq : δ ^ 2 ≤ ‖x - y‖ ^ 2 :=
        pow_le_pow_left₀ hδ.le hdist 2
      rw [norm_gaussianKernel, Finset.sum_sub_distrib]
      simp only [gaussianRealEmbed, ofReal_re, ofReal_im]
      rw [show
        (∑ i, (x i - y i) ^ 2) = ‖x - y‖ ^ 2 by
          simp [EuclideanSpace.real_norm_sq_eq]]
      rw [show (∑ _i : ι, (0 : ℝ) ^ 2) = 0 by simp, sub_zero]
      dsimp [P]
      change
        ‖((Real.pi * c : ℂ) ^
            (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))‖ *
              Real.exp (-Real.pi ^ 2 * c * ‖x - y‖ ^ 2) ≤
          (P * Real.exp (-b * c)) * half y
      have hexp :
          Real.exp (-Real.pi ^ 2 * c * ‖x - y‖ ^ 2) ≤
            Real.exp (-b * c) *
              Real.exp (-Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hscaled :
            Real.pi ^ 2 * (c / 2) * δ ^ 2 ≤
              Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        calc
          -Real.pi ^ 2 * c * ‖x - y‖ ^ 2 =
              -(2 * (Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2)) := by ring
          _ ≤ -(Real.pi ^ 2 * (c / 2) * δ ^ 2 +
                Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2) := by
                  linarith
          _ = -b * c +
                -Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2 := by
                  dsimp [b]
                  ring
      simpa [half, mul_assoc, P] using
        mul_le_mul_of_nonneg_left hexp
          (norm_nonneg
            (((Real.pi * c : ℂ) ^
              (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ))))
    calc
      (∫ y : EuclideanSpace ℝ ι in (Metric.ball x δ)ᶜ,
          ‖gaussianKernel c (gaussianRealEmbed x) y‖)
          ≤ ∫ y : EuclideanSpace ℝ ι in (Metric.ball x δ)ᶜ,
              (P * Real.exp (-b * c)) * half y := by
            apply setIntegral_mono_on
            · exact hkernel_int.integrableOn
            · exact (hhalf_int.const_mul
                (P * Real.exp (-b * c))).integrableOn
            · exact Metric.isOpen_ball.measurableSet.compl
            · exact hpoint
      _ ≤ ∫ y : EuclideanSpace ℝ ι,
              (P * Real.exp (-b * c)) * half y := by
            apply setIntegral_le_integral
            · exact hhalf_int.const_mul (P * Real.exp (-b * c))
            · filter_upwards with y
              exact mul_nonneg (by positivity) (Real.exp_nonneg _)
      _ = upper c := by
        rw [integral_const_mul]
        have hhalf :
            ∫ y : EuclideanSpace ℝ ι, half y =
              (Real.pi / (Real.pi ^ 2 * (c / 2))) ^ p := by
          have htranslate :
              (∫ y : EuclideanSpace ℝ ι, half y) =
                ∫ v : EuclideanSpace ℝ ι,
                  Real.exp (-Real.pi ^ 2 * (c / 2) * ‖v‖ ^ 2) := by
            calc
              (∫ y : EuclideanSpace ℝ ι, half y) =
                  ∫ y : EuclideanSpace ℝ ι,
                    Real.exp
                      (-Real.pi ^ 2 * (c / 2) * ‖x - y‖ ^ 2) := by
                        rfl
              _ = ∫ v : EuclideanSpace ℝ ι,
                    Real.exp (-Real.pi ^ 2 * (c / 2) * ‖v‖ ^ 2) :=
                integral_sub_left_eq_self
                  (fun v : EuclideanSpace ℝ ι =>
                    Real.exp (-Real.pi ^ 2 * (c / 2) * ‖v‖ ^ 2))
                  volume x
          rw [htranslate]
          simpa [p] using
            (GaussianFourier.integral_rexp_neg_mul_sq_norm
              (V := EuclideanSpace ℝ ι)
              (show 0 < Real.pi ^ 2 * (c / 2) by positivity))
        rw [hhalf]
        have hP : P = (Real.pi * c) ^ p := by
          dsimp [P, p]
          rw [← Complex.ofReal_mul]
          have hexponent :
              ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℂ) / 2) =
                (((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / 2 : ℝ) : ℂ) := by
            norm_num
          rw [hexponent, Complex.norm_cpow_real]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (mul_pos Real.pi_pos hcpos)]
        rw [hP]
        have hinside :
            (Real.pi * c) *
                (Real.pi / (Real.pi ^ 2 * (c / 2))) = 2 := by
          field_simp [Real.pi_ne_zero, ne_of_gt hcpos]
        calc
          (Real.pi * c) ^ p * Real.exp (-b * c) *
              (Real.pi / (Real.pi ^ 2 * (c / 2))) ^ p =
            ((Real.pi * c) ^ p *
              (Real.pi / (Real.pi ^ 2 * (c / 2))) ^ p) *
                Real.exp (-b * c) := by ring
          _ = ((Real.pi * c) *
              (Real.pi / (Real.pi ^ 2 * (c / 2)))) ^ p *
                Real.exp (-b * c) := by
            rw [Real.mul_rpow (by positivity : 0 ≤ Real.pi * c)
              (by positivity :
                0 ≤ Real.pi / (Real.pi ^ 2 * (c / 2)))]
          _ = upper c := by rw [hinside]

/-- Gaussian regularization converges pointwise to an integrable function at
each point of continuity on the real locus. -/
theorem tendsto_gaussianRegularization_real
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf : Integrable f)
    {x : EuclideanSpace ℝ ι}
    (hfx : ContinuousAt f x) :
    Tendsto
      (fun c : ℝ =>
        gaussianRegularization c f (gaussianRealEmbed x))
      atTop
      (nhds (f x)) := by
  simpa [gaussianRegularization, gaussianKernel_real, smul_eq_mul] using
    (Real.tendsto_integral_gaussian_smul'
      (V := EuclideanSpace ℝ ι) hf hfx)

/-- Gaussian regularization converges pointwise on the real locus for every
bounded continuous function, without a global integrability assumption. -/
theorem tendsto_gaussianRegularization_real_of_bounded
    {f : EuclideanSpace ℝ ι → ℂ}
    (hf_cont : Continuous f)
    (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    (x : EuclideanSpace ℝ ι) :
    Tendsto
      (fun c : ℝ =>
        gaussianRegularization c f (gaussianRealEmbed x))
      atTop (nhds (f x)) := by
  let bump : ContDiffBump x := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let g : EuclideanSpace ℝ ι → ℂ := fun y => (bump y : ℂ) * f y
  let h : EuclideanSpace ℝ ι → ℂ := fun y => f y - g y
  have hbump_cont : Continuous fun y : EuclideanSpace ℝ ι => (bump y : ℂ) :=
    Complex.continuous_ofReal.comp (bump.contDiff (n := 0)).continuous
  have hg_cont : Continuous g := by
    exact hbump_cont.mul hf_cont
  have hh_cont : Continuous h := hf_cont.sub hg_cont
  have hbump_compact :
      HasCompactSupport (fun y : EuclideanSpace ℝ ι => (bump y : ℂ)) :=
    bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hg_compact : HasCompactSupport g := hbump_compact.mul_right
  have hg_int : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport hg_compact
  have hgx : g x = f x := by
    have hxball : x ∈ Metric.closedBall x bump.rIn :=
      Metric.mem_closedBall_self bump.rIn_pos.le
    simp [g, bump.one_of_mem_closedBall hxball]
  have hg_tendsto :
      Tendsto
        (fun c : ℝ =>
          gaussianRegularization c g (gaussianRealEmbed x))
        atTop (nhds (f x)) := by
    simpa [hgx] using
      tendsto_gaussianRegularization_real
        (x := x) hg_int hg_cont.continuousAt
  have hB_nonneg : 0 ≤ B :=
    (norm_nonneg (f x)).trans (hB x)
  have hbump_bound : ∀ y, ‖(bump y : ℂ)‖ ≤ 1 := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
    exact bump.le_one
  have hg_bound : ∀ y, ‖g y‖ ≤ B := by
    intro y
    change ‖(bump y : ℂ) * f y‖ ≤ B
    rw [norm_mul]
    calc
      ‖(bump y : ℂ)‖ * ‖f y‖ ≤ 1 * B :=
        mul_le_mul (hbump_bound y) (hB y) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hh_bound : ∀ y, ‖h y‖ ≤ 2 * B := by
    intro y
    calc
      ‖h y‖ = ‖f y - g y‖ := rfl
      _ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB y) (hg_bound y)
      _ = 2 * B := by ring
  have hh_zero_ball :
      ∀ y ∈ Metric.ball x 1, h y = 0 := by
    intro y hy
    have hyclosed : y ∈ Metric.closedBall x bump.rIn := by
      simpa [bump] using Metric.ball_subset_closedBall hy
    simp [h, g, bump.one_of_mem_closedBall hyclosed]
  have htail :
      Tendsto
        (fun c : ℝ =>
          (2 * B) *
            ∫ y : EuclideanSpace ℝ ι in (Metric.ball x 1)ᶜ,
              ‖gaussianKernel c (gaussianRealEmbed x) y‖)
        atTop (nhds 0) := by
    simpa using
      (tendsto_setIntegral_norm_gaussianKernel_real_compl_ball
        (ι := ι) x 1 zero_lt_one).const_mul (2 * B)
  have hdiff_bound :
      ∀ᶠ c : ℝ in atTop,
        ‖gaussianRegularization c f (gaussianRealEmbed x) -
            gaussianRegularization c g (gaussianRealEmbed x)‖ ≤
          (2 * B) *
            ∫ y : EuclideanSpace ℝ ι in (Metric.ball x 1)ᶜ,
              ‖gaussianKernel c (gaussianRealEmbed x) y‖ := by
    filter_upwards [Ioi_mem_atTop 0] with c hc
    have hf_int :
        Integrable (fun y =>
          gaussianKernel c (gaussianRealEmbed x) y * f y) :=
      integrable_gaussianKernel_mul_of_bounded
        c hc (gaussianRealEmbed x) hf_cont.aestronglyMeasurable B hB
    have hg_int' :
        Integrable (fun y =>
          gaussianKernel c (gaussianRealEmbed x) y * g y) :=
      integrable_gaussianKernel_mul_of_bounded
        c hc (gaussianRealEmbed x) hg_cont.aestronglyMeasurable B hg_bound
    have hh_int :
        Integrable (fun y =>
          gaussianKernel c (gaussianRealEmbed x) y * h y) :=
      integrable_gaussianKernel_mul_of_bounded
        c hc (gaussianRealEmbed x) hh_cont.aestronglyMeasurable
        (2 * B) hh_bound
    have hkernel_int :
        Integrable
          (fun y : EuclideanSpace ℝ ι =>
            ‖gaussianKernel c (gaussianRealEmbed x) y‖) := by
      exact
        (integrable_gaussianKernel_mul_of_bounded
          c hc (gaussianRealEmbed x)
          (show AEStronglyMeasurable
              (fun _ : EuclideanSpace ℝ ι => (1 : ℂ)) by fun_prop)
          1 (by intro y; simp)).norm.congr
          (Filter.Eventually.of_forall fun y => by simp)
    have hdiff :
        gaussianRegularization c f (gaussianRealEmbed x) -
            gaussianRegularization c g (gaussianRealEmbed x) =
          ∫ y : EuclideanSpace ℝ ι,
            gaussianKernel c (gaussianRealEmbed x) y * h y := by
      rw [gaussianRegularization, gaussianRegularization,
        ← integral_sub hf_int hg_int']
      apply integral_congr_ae
      filter_upwards with y
      simp [h, g]
      ring
    rw [hdiff]
    calc
      ‖∫ y : EuclideanSpace ℝ ι,
          gaussianKernel c (gaussianRealEmbed x) y * h y‖ ≤
          ∫ y : EuclideanSpace ℝ ι,
            ‖gaussianKernel c (gaussianRealEmbed x) y * h y‖ :=
        norm_integral_le_of_norm_le hh_int.norm
          (Filter.Eventually.of_forall fun _ => le_rfl)
      _ = ∫ y : EuclideanSpace ℝ ι in (Metric.ball x 1)ᶜ,
            ‖gaussianKernel c (gaussianRealEmbed x) y * h y‖ := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro y hy
          have hyball : y ∈ Metric.ball x 1 := by simpa using hy
          rw [hh_zero_ball y hyball, mul_zero, norm_zero]
      _ ≤ ∫ y : EuclideanSpace ℝ ι in (Metric.ball x 1)ᶜ,
            (2 * B) * ‖gaussianKernel c (gaussianRealEmbed x) y‖ := by
          apply setIntegral_mono_on
          · exact hh_int.norm.integrableOn
          · exact (hkernel_int.const_mul (2 * B)).integrableOn
          · exact Metric.isOpen_ball.measurableSet.compl
          · intro y _hy
            rw [norm_mul]
            calc
              ‖gaussianKernel c (gaussianRealEmbed x) y‖ * ‖h y‖ ≤
                  ‖gaussianKernel c (gaussianRealEmbed x) y‖ * (2 * B) :=
                mul_le_mul_of_nonneg_left (hh_bound y) (norm_nonneg _)
              _ = (2 * B) *
                    ‖gaussianKernel c (gaussianRealEmbed x) y‖ := mul_comm _ _
      _ = (2 * B) *
            ∫ y : EuclideanSpace ℝ ι in (Metric.ball x 1)ᶜ,
              ‖gaussianKernel c (gaussianRealEmbed x) y‖ := by
          rw [integral_const_mul]
  have hdiff_zero :
      Tendsto
        (fun c : ℝ =>
          gaussianRegularization c f (gaussianRealEmbed x) -
            gaussianRegularization c g (gaussianRealEmbed x))
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds htail
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hdiff_bound
  convert hg_tendsto.add hdiff_zero using 1 <;> simp

end OSReconstruction.SCV
