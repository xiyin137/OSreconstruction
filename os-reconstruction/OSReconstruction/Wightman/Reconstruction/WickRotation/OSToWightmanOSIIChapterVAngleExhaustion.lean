/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.MetricSpace.Thickening
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeParametricContinuation


















noncomputable section

open Complex Set Topology Filter
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The angle parameters `hᵢᴺ` from OS II `(5.27)`.

The paper starts at `i = 1`; index zero is fixed to zero only to make this a
total function on natural numbers.  At each successor stage the first angle
is averaged with `π / 2`, while every later angle is averaged with its
left-hand neighbor from the preceding stage. -/
def recursiveAngle : ℕ → ℕ → ℝ
  | _, 0 => 0
  | 0, _ + 1 => 0
  | 1, N + 1 => (recursiveAngle 1 N + Real.pi / 2) / 2
  | i + 2, N + 1 =>
      (recursiveAngle (i + 2) N + recursiveAngle (i + 1) N) / 2

@[simp] theorem recursiveAngle_zero_stage (i : ℕ) :
    recursiveAngle i 0 = 0 :=
  rfl

@[simp] theorem recursiveAngle_zero_index (N : ℕ) :
    recursiveAngle 0 N = 0 := by
  cases N <;> rfl

@[simp] theorem recursiveAngle_one_succ (N : ℕ) :
    recursiveAngle 1 (N + 1) =
      (recursiveAngle 1 N + Real.pi / 2) / 2 :=
  rfl

@[simp] theorem recursiveAngle_succ_succ (i N : ℕ) :
    recursiveAngle (i + 2) (N + 1) =
      (recursiveAngle (i + 2) N + recursiveAngle (i + 1) N) / 2 :=
  rfl

theorem recursiveAngle_nonneg (i N : ℕ) :
    0 ≤ recursiveAngle i N := by
  induction N generalizing i with
  | zero => simp
  | succ N ih =>
      rcases i with _ | _ | i
      · simp
      · rw [recursiveAngle_one_succ]
        exact div_nonneg
          (add_nonneg (ih 1) (le_of_lt (by positivity)))
          (by norm_num)
      · rw [recursiveAngle_succ_succ]
        exact div_nonneg (add_nonneg (ih (i + 2)) (ih (i + 1)))
          (by norm_num)

/-- Before coordinate i + 1 has entered the recursion, its aperture is still
zero. -/
theorem recursiveAngle_succ_eq_zero_of_stage_lt
    (i N : ℕ)
    (hdepth : N < i + 1) :
    recursiveAngle (i + 1) N = 0 := by
  induction N generalizing i with
  | zero =>
      simp
  | succ N ih =>
      cases i with
      | zero =>
          omega
      | succ i =>
          rw [show i + 1 + 1 = i + 2 by omega,
            recursiveAngle_succ_succ]
          have hleft : N < i + 2 := by omega
          have hright : N < i + 1 := by omega
          rw [ih (i + 1) hleft, ih i hright]
          norm_num

/-- The partial binomial sum appearing in the explicit formula of OS II
Lemma 5.2. -/
def binomialPartialSum (i N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range i, (Nat.choose N t : ℝ)

private theorem binomialPartialSum_succ_stage (i N : ℕ) :
    binomialPartialSum (i + 1) (N + 1) =
      binomialPartialSum (i + 1) N + binomialPartialSum i N := by
  induction i with
  | zero => simp [binomialPartialSum]
  | succ i ih =>
      simp [binomialPartialSum, Finset.sum_range_succ,
        Nat.choose_succ_succ, Nat.cast_add] at ih ⊢
      linarith

/-- The explicit binomial expression `ρ(i,N)` in OS II Lemma 5.2.  As in the
recursive definition, the auxiliary index zero is fixed to zero. -/
def binomialAngle : ℕ → ℕ → ℝ
  | 0, _ => 0
  | i + 1, N =>
      Real.pi / 2 *
        (1 - binomialPartialSum (i + 1) N / (2 : ℝ) ^ N)

@[simp] theorem binomialAngle_zero (N : ℕ) :
    binomialAngle 0 N = 0 :=
  rfl

@[simp] theorem binomialAngle_succ (i N : ℕ) :
    binomialAngle (i + 1) N =
      Real.pi / 2 *
        (1 - binomialPartialSum (i + 1) N / (2 : ℝ) ^ N) :=
  rfl

private theorem binomialPartialSum_zero_stage (i : ℕ) :
    binomialPartialSum (i + 1) 0 = 1 := by
  induction i with
  | zero => simp [binomialPartialSum]
  | succ i ih =>
      change
        (∑ t ∈ Finset.range (i + 2), (Nat.choose 0 t : ℝ)) = 1
      rw [show i + 2 = (i + 1) + 1 by omega,
        Finset.sum_range_succ]
      change
        binomialPartialSum (i + 1) 0 +
          (Nat.choose 0 (i + 1) : ℝ) = 1
      rw [ih]
      simp [Nat.choose_eq_zero_of_lt]

theorem binomialAngle_zero_stage (i : ℕ) :
    binomialAngle i 0 = 0 := by
  cases i with
  | zero => rfl
  | succ i =>
      rw [binomialAngle_succ, binomialPartialSum_zero_stage]
      ring

theorem binomialAngle_one_succ (N : ℕ) :
    binomialAngle 1 (N + 1) =
      (binomialAngle 1 N + Real.pi / 2) / 2 := by
  simp only [binomialAngle_succ]
  have hsum (M : ℕ) : binomialPartialSum 1 M = 1 := by
    simp [binomialPartialSum]
  rw [hsum, hsum, pow_succ]
  have hpow : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]
  ring

theorem binomialAngle_succ_succ (i N : ℕ) :
    binomialAngle (i + 2) (N + 1) =
      (binomialAngle (i + 2) N + binomialAngle (i + 1) N) / 2 := by
  rw [show i + 2 = (i + 1) + 1 by omega]
  simp only [binomialAngle_succ]
  rw [binomialPartialSum_succ_stage (i + 1) N, pow_succ]
  have hpow : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]
  ring

/-- The primitive recursion used by the formalization is exactly the
binomial formula `ρ(i,N)` displayed in OS II Lemma 5.2. -/
theorem recursiveAngle_eq_binomialAngle (i N : ℕ) :
    recursiveAngle i N = binomialAngle i N := by
  induction N generalizing i with
  | zero =>
      rw [recursiveAngle_zero_stage, binomialAngle_zero_stage]
  | succ N ih =>
      rcases i with _ | _ | i
      · simp
      · rw [recursiveAngle_one_succ, binomialAngle_one_succ, ih]
      · rw [recursiveAngle_succ_succ, binomialAngle_succ_succ, ih, ih]

@[simp] theorem binomialPartialSum_one (N : ℕ) :
    binomialPartialSum 1 N = 1 := by
  simp [binomialPartialSum]

/-- An explicit coordinate-dependent binomial bound compatible with the
square-root-two continuation scale. -/
theorem binomialPartialSum_le_three_pow_mul_sqrtTwo_pow
    (i N : ℕ) :
    binomialPartialSum (i + 1) N ≤
      (3 : ℝ) ^ i * (Real.sqrt 2) ^ N := by
  induction N generalizing i with
  | zero =>
      rw [binomialPartialSum_zero_stage, pow_zero, mul_one]
      exact one_le_pow₀ (by norm_num)
  | succ N ih =>
      cases i with
      | zero =>
          simp only [zero_add, binomialPartialSum_one, pow_zero, one_mul]
          exact one_le_pow₀ (Real.one_le_sqrt.mpr (by norm_num))
      | succ i =>
          have hleft := ih (i + 1)
          have hright := ih i
          have hsqrt : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
            have hroot : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
              (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
            nlinarith
          have hfactor :
              0 ≤ (3 : ℝ) ^ i * (Real.sqrt 2) ^ N := by
            positivity
          change
            binomialPartialSum (i + 2) (N + 1) ≤
              (3 : ℝ) ^ (i + 1) * (Real.sqrt 2) ^ (N + 1)
          rw [show i + 2 = (i + 1) + 1 by omega,
            binomialPartialSum_succ_stage (i + 1) N]
          calc
            binomialPartialSum ((i + 1) + 1) N +
                  binomialPartialSum (i + 1) N ≤
                (3 : ℝ) ^ (i + 1) * (Real.sqrt 2) ^ N +
                  (3 : ℝ) ^ i * (Real.sqrt 2) ^ N :=
              add_le_add hleft hright
            _ = 4 * ((3 : ℝ) ^ i * (Real.sqrt 2) ^ N) := by
              rw [pow_succ]
              ring
            _ ≤ (3 * Real.sqrt 2) *
                    ((3 : ℝ) ^ i * (Real.sqrt 2) ^ N) :=
              mul_le_mul_of_nonneg_right hsqrt hfactor
            _ = (3 : ℝ) ^ (i + 1) *
                  (Real.sqrt 2) ^ (N + 1) := by
              rw [pow_succ, pow_succ]
              ring

/-- The recursive-angle deficit has an explicit coefficient `3^i`, so its
dependence on the coordinate and arity remains controlled. -/
theorem recursiveAngle_three_pow_quantitative_lower_bound
    (i N : ℕ) :
    Real.pi / 2 *
        (1 - (3 : ℝ) ^ i / (Real.sqrt 2) ^ N) ≤
      recursiveAngle (i + 1) N := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpow_pos : 0 < (Real.sqrt 2) ^ N := pow_pos hsqrt_pos N
  have htwo_pow :
      (2 : ℝ) ^ N = (Real.sqrt 2) ^ N * (Real.sqrt 2) ^ N := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  have htail :
      binomialPartialSum (i + 1) N / (2 : ℝ) ^ N ≤
        (3 : ℝ) ^ i / (Real.sqrt 2) ^ N := by
    rw [htwo_pow]
    apply
      (div_le_div_iff₀ (mul_pos hpow_pos hpow_pos) hpow_pos).2
    calc
      binomialPartialSum (i + 1) N * (Real.sqrt 2) ^ N ≤
          ((3 : ℝ) ^ i * (Real.sqrt 2) ^ N) *
            (Real.sqrt 2) ^ N :=
        mul_le_mul_of_nonneg_right
          (binomialPartialSum_le_three_pow_mul_sqrtTwo_pow i N)
          hpow_pos.le
      _ = (3 : ℝ) ^ i *
            ((Real.sqrt 2) ^ N * (Real.sqrt 2) ^ N) := by
        ring
  rw [recursiveAngle_eq_binomialAngle, binomialAngle_succ]
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left htail 1) (by positivity)

/-- The first recursive aperture has the exact dyadic deficit from the
limiting angle. -/
theorem recursiveAngle_one_eq_explicit (N : ℕ) :
    recursiveAngle 1 N =
      Real.pi / 2 * (1 - 1 / (2 : ℝ) ^ N) := by
  rw [recursiveAngle_eq_binomialAngle, binomialAngle_succ,
    binomialPartialSum_one]

/-- The gap between adjacent positive recursive apertures is one binomial
coefficient divided by the dyadic stage factor. -/
theorem recursiveAngle_succ_gap_eq_choose (i N : ℕ) :
    recursiveAngle (i + 1) N - recursiveAngle (i + 2) N =
      Real.pi / 2 * ((N.choose (i + 1) : ℝ) / (2 : ℝ) ^ N) := by
  rw [recursiveAngle_eq_binomialAngle, recursiveAngle_eq_binomialAngle]
  simp only [binomialAngle_succ]
  have hsum :
      binomialPartialSum (i + 2) N =
        binomialPartialSum (i + 1) N + (N.choose (i + 1) : ℝ) := by
    rw [show i + 2 = (i + 1) + 1 by omega]
    simp only [binomialPartialSum, Finset.sum_range_succ]
  rw [hsum]
  ring

/-- A fixed binomial coefficient divided by `2ᴺ` tends to zero. -/
theorem tendsto_choose_div_two_pow (j : ℕ) :
    Tendsto
      (fun N : ℕ => (N.choose j : ℝ) / (2 : ℝ) ^ N)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro N
    positivity
  · intro N
    have hchoose : (N.choose j : ℝ) ≤ (N : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow N j
    exact div_le_div_of_nonneg_right hchoose (by positivity)
  · exact tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num)

/-- The lower binomial tail in the explicit angle formula vanishes for every
fixed coordinate. -/
theorem tendsto_binomialPartialSum_div_two_pow (i : ℕ) :
    Tendsto
      (fun N : ℕ => binomialPartialSum i N / (2 : ℝ) ^ N)
      atTop (𝓝 0) := by
  rw [show
      (fun N : ℕ => binomialPartialSum i N / (2 : ℝ) ^ N) =
        fun N => ∑ j ∈ Finset.range i,
          (N.choose j : ℝ) / (2 : ℝ) ^ N by
    funext N
    simp [binomialPartialSum, Finset.sum_div]]
  simpa using
    (tendsto_finset_sum (Finset.range i) fun j _ =>
      tendsto_choose_div_two_pow j)

/-- The explicit quantitative constant for coordinate `i + 1`. -/
noncomputable def recursiveAngleQuantitativeConstant (i : ℕ) : ℝ :=
  (3 : ℝ) ^ i

theorem recursiveAngleQuantitativeConstant_nonneg (i : ℕ) :
    0 ≤ recursiveAngleQuantitativeConstant i := by
  unfold recursiveAngleQuantitativeConstant
  positivity

theorem recursiveAngle_quantitative_lower_bound (i N : ℕ) :
    Real.pi / 2 *
        (1 - recursiveAngleQuantitativeConstant i /
          (Real.sqrt 2) ^ N) ≤
      recursiveAngle (i + 1) N := by
  simpa [recursiveAngleQuantitativeConstant] using
    recursiveAngle_three_pow_quantitative_lower_bound i N

/-- Every fixed positive coordinate aperture converges to the boundary angle
`π / 2`.  This is the cofinality consequence of the exact binomial formula. -/
theorem tendsto_recursiveAngle_succ (i : ℕ) :
    Tendsto (recursiveAngle (i + 1)) atTop (𝓝 (Real.pi / 2)) := by
  rw [show recursiveAngle (i + 1) =
      fun N =>
        Real.pi / 2 *
          (1 - binomialPartialSum (i + 1) N / (2 : ℝ) ^ N) by
    funext N
    rw [recursiveAngle_eq_binomialAngle, binomialAngle_succ]]
  convert tendsto_const_nhds.mul
    (tendsto_const_nhds.sub
      (tendsto_binomialPartialSum_div_two_pow (i + 1))) using 1
  ring

/-- The explicit dyadic radial contraction used at recursive depth N + 1 is
positive. -/
theorem recursiveAngle_explicitContraction_pos (N : ℕ) :
    0 < 1 - 1 / (2 : ℝ) ^ (N + 1) := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ (N + 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hinv : 1 / (2 : ℝ) ^ (N + 1) < 1 :=
    (div_lt_one (by positivity)).2 hpow
  linarith

/-- The explicit dyadic radial contraction is strictly below one. -/
theorem recursiveAngle_explicitContraction_lt_one (N : ℕ) :
    1 - 1 / (2 : ℝ) ^ (N + 1) < 1 := by
  have hinv : 0 < 1 / (2 : ℝ) ^ (N + 1) := by positivity
  linarith

/-- The first successor aperture is exactly the explicit dyadic contraction
of the full generator angle. -/
theorem recursiveAngle_one_succ_eq_explicitContraction (N : ℕ) :
    recursiveAngle 1 (N + 1) =
      (1 - 1 / (2 : ℝ) ^ (N + 1)) * (Real.pi / 2) := by
  rw [recursiveAngle_one_eq_explicit]
  ring

theorem binomialPartialSum_mono_index (i N : ℕ) :
    binomialPartialSum (i + 1) N ≤
      binomialPartialSum (i + 2) N := by
  rw [show i + 2 = (i + 1) + 1 by omega]
  simp only [binomialPartialSum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- At a fixed stage, later coordinates have no larger aperture than earlier
coordinates. -/
theorem recursiveAngle_succ_le_prev (i N : ℕ) :
    recursiveAngle (i + 2) N ≤ recursiveAngle (i + 1) N := by
  rw [recursiveAngle_eq_binomialAngle, recursiveAngle_eq_binomialAngle]
  simp only [binomialAngle_succ]
  have hpow : 0 ≤ (2 : ℝ) ^ N := by positivity
  have hdiv :
      binomialPartialSum (i + 1) N / (2 : ℝ) ^ N ≤
        binomialPartialSum (i + 2) N / (2 : ℝ) ^ N :=
    div_le_div_of_nonneg_right (binomialPartialSum_mono_index i N) hpow
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left hdiv 1) (by positivity)

theorem recursiveAngle_le_pi_div_two (i N : ℕ) :
    recursiveAngle i N ≤ Real.pi / 2 := by
  cases i with
  | zero =>
      simp
      positivity
  | succ i =>
      rw [recursiveAngle_eq_binomialAngle, binomialAngle_succ]
      have htail :
          0 ≤ binomialPartialSum (i + 1) N / (2 : ℝ) ^ N := by
        unfold binomialPartialSum
        positivity
      nlinarith [Real.pi_pos]

/-- Once coordinate i + 1 is live, the successor aperture in the next
coordinate is bounded by the same explicit dyadic contraction as the first
coordinate. -/
theorem recursiveAngle_succ_succ_le_prev_explicitContraction_of_succ_le
    (i N : ℕ)
    (hdepth : i + 1 ≤ N) :
    recursiveAngle (i + 2) (N + 1) ≤
      (1 - 1 / (2 : ℝ) ^ (N + 1)) * recursiveAngle (i + 1) N := by
  have hchoose : (1 : ℝ) ≤ (N.choose (i + 1) : ℝ) := by
    exact_mod_cast
      (Nat.succ_le_iff.mpr (Nat.choose_pos hdepth))
  have hpow_succ_pos : 0 < (2 : ℝ) ^ (N + 1) := by positivity
  have hratio :
      1 / (2 : ℝ) ^ (N + 1) ≤
        ((N.choose (i + 1) : ℝ) / (2 : ℝ) ^ N) / 2 := by
    calc
      1 / (2 : ℝ) ^ (N + 1) ≤
          (N.choose (i + 1) : ℝ) / (2 : ℝ) ^ (N + 1) :=
        div_le_div_of_nonneg_right hchoose hpow_succ_pos.le
      _ = ((N.choose (i + 1) : ℝ) / (2 : ℝ) ^ N) / 2 := by
        rw [pow_succ]
        field_simp
  have hrelative :
      1 / (2 : ℝ) ^ (N + 1) * recursiveAngle (i + 1) N ≤
        (recursiveAngle (i + 1) N - recursiveAngle (i + 2) N) / 2 := by
    calc
      1 / (2 : ℝ) ^ (N + 1) * recursiveAngle (i + 1) N ≤
          1 / (2 : ℝ) ^ (N + 1) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left
          (recursiveAngle_le_pi_div_two (i + 1) N) (by positivity)
      _ = Real.pi / 2 * (1 / (2 : ℝ) ^ (N + 1)) := by
        ring
      _ ≤ Real.pi / 2 *
          (((N.choose (i + 1) : ℝ) / (2 : ℝ) ^ N) / 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (recursiveAngle (i + 1) N -
          recursiveAngle (i + 2) N) / 2 := by
        rw [recursiveAngle_succ_gap_eq_choose]
        ring
  rw [recursiveAngle_succ_succ]
  nlinarith

theorem recursiveAngle_le_succ_stage (i N : ℕ) :
    recursiveAngle i N ≤ recursiveAngle i (N + 1) := by
  cases i with
  | zero => simp
  | succ i =>
      cases i with
      | zero =>
          rw [recursiveAngle_one_succ]
          have h := recursiveAngle_le_pi_div_two 1 N
          linarith
      | succ i =>
          rw [recursiveAngle_succ_succ]
          have h := recursiveAngle_succ_le_prev i N
          linarith

theorem monotone_recursiveAngle (i : ℕ) :
    Monotone (recursiveAngle i) :=
  monotone_nat_of_le_succ (recursiveAngle_le_succ_stage i)

/-- A coordinatewise angular sector inside the product right half-plane. -/
def osiiTimeArgumentSector
    {k : ℕ} (aperture : Fin k → ℝ) :
    Set (OSIITimeGapSpace k) :=
  {ζ | ζ ∈ osiiTimeRightHalfPlane k ∧
    ∀ i : Fin k, |Complex.arg (ζ i)| < aperture i}

/-- A monotone family of finite-stage apertures that eventually exceeds every
angle strictly below `π / 2`, coordinate by coordinate. -/
structure CofinalAngleApertures (k : ℕ) where
  aperture : ℕ → Fin k → ℝ
  monotone : Monotone aperture
  eventually_above :
    ∀ i : Fin k, ∀ θ : ℝ, θ < Real.pi / 2 →
      ∃ N, θ < aperture N i

namespace CofinalAngleApertures

variable {k : ℕ}

/-- Every point of the product right half-plane lies in one finite angular
sector.  Finiteness of `Fin k` turns coordinatewise stage choices into one
common stage. -/
theorem exists_stage
    (A : CofinalAngleApertures k)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    ∃ N, ζ ∈ osiiTimeArgumentSector (A.aperture N) := by
  classical
  have harg :
      ∀ i : Fin k, |Complex.arg (ζ i)| < Real.pi / 2 := by
    intro i
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl (hζ i))
  choose stage hstage using
    fun i : Fin k =>
      A.eventually_above i |Complex.arg (ζ i)| (harg i)
  let N : ℕ := Finset.univ.sup stage
  refine ⟨N, hζ, ?_⟩
  intro i
  have hiN : stage i ≤ N := by
    exact Finset.le_sup (f := stage) (Finset.mem_univ i)
  exact (hstage i).trans_le (A.monotone hiN i)

end CofinalAngleApertures

/-- The concrete finite-stage apertures produced by the OS II recursive-angle
system.  The binomial formula proves both monotonicity and coordinatewise
cofinality below `π / 2`. -/
noncomputable def recursiveAngleCofinalApertures
    (k : ℕ) :
    CofinalAngleApertures k where
  aperture N i := recursiveAngle (i.val + 1) N
  monotone := by
    intro M N hMN i
    exact monotone_recursiveAngle (i.val + 1) hMN
  eventually_above := by
    intro i θ hθ
    have hlim :
        Tendsto (recursiveAngle (i.val + 1))
          atTop (𝓝 (Real.pi / 2)) := by
      simpa using tendsto_recursiveAngle_succ i.val
    exact (hlim.eventually (lt_mem_nhds hθ)).exists

/-- The geometric input needed to turn a sequence of continuation stages into
an exhausting ladder: stage `N` contains the sector supplied by a cofinal
aperture family. -/
structure StageAngleSectorCover
    {d k : ℕ}
    (stage : ℕ → OSIITimeContinuationStage d k) where
  apertures : CofinalAngleApertures k
  sector_subset_stage :
    ∀ N, osiiTimeArgumentSector (apertures.aperture N) ⊆
      (stage N).carrier

namespace StageAngleSectorCover

variable {d k : ℕ}
  {stage : ℕ → OSIITimeContinuationStage d k}

theorem exhausts
    (C : StageAngleSectorCover stage) :
    osiiTimeRightHalfPlane k ⊆ ⋃ N, (stage N).carrier := by
  intro ζ hζ
  obtain ⟨N, hN⟩ := C.apertures.exists_stage ζ hζ
  exact Set.mem_iUnion_of_mem N (C.sector_subset_stage N hN)

end StageAngleSectorCover

/-- Once Lemma 5.2 supplies containment of the concrete recursive-angle
sector in each stage, no additional quantitative premise is needed for the
cofinal cover. -/
noncomputable def stageAngleSectorCoverOfRecursiveAngles
    {d k : ℕ}
    (stage : ℕ → OSIITimeContinuationStage d k)
    (sector_subset_stage :
      ∀ N,
        osiiTimeArgumentSector
            (fun i : Fin k => recursiveAngle (i.val + 1) N) ⊆
          (stage N).carrier) :
    StageAngleSectorCover stage where
  apertures := recursiveAngleCofinalApertures k
  sector_subset_stage := sector_subset_stage

/-- Package monotone compatible stages as a full Chapter V ladder once the
recursive-angle sector geometry supplies finite-stage coverage. -/
def timeContinuationLadderOfAngleSectorCover
    {d k : ℕ}
    (stage : ℕ → OSIITimeContinuationStage d k)
    (carrier_mono : Monotone fun N => (stage N).carrier)
    (extends_succ :
      ∀ N, Set.EqOn
        (stage (N + 1)).distribution
        (stage N).distribution
        (stage N).carrier)
    (cover : StageAngleSectorCover stage) :
    OSIITimeContinuationLadder d k where
  stage := stage
  carrier_mono := carrier_mono
  extends_succ := extends_succ
  exhausts := cover.exhausts

end OSIIChapterV
end OSReconstruction
