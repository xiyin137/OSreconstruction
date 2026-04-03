import OSReconstruction.vNA.Bochner.CfcInfrastructure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open scoped NNReal

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For bounded nonnegative operators, a positive natural-power equation determines the
corresponding `q`-th root uniquely via the continuous functional calculus. -/
theorem positive_qroot_unique
    (A B : H →L[ℂ] H) (n : ℕ) (hn : 0 < n)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hpow : B ^ n = A) :
    CFC.nnrpow A ((n : ℝ≥0)⁻¹) = B := by
  have hpos : (0 : ℝ≥0) < n := by
    exact_mod_cast hn
  have hn_ne : (n : ℝ≥0) ≠ 0 := ne_of_gt hpos
  have hpow' : CFC.nnrpow B (n : ℝ≥0) = A := by
    rw [CFC.nnrpow_eq_pow]
    rw [CFC.nnrpow_eq_rpow (A := H →L[ℂ] H) hpos]
    change B ^ (n : ℝ) = A
    rw [CFC.rpow_natCast (a := B) n (ha := hB_nonneg)]
    simpa using hpow
  exact (CFC.nnrpow_inv_eq A B (x := (n : ℝ≥0)) hn_ne
    (ha := hA_nonneg) (hb := hB_nonneg)).2 hpow'

/-- On bounded nonnegative operators, natural powers are the same as `ℝ≥0`-powers
at positive integer exponents. -/
theorem natPow_eq_nnrpow_natCast
    (A : H →L[ℂ] H) (n : ℕ) (hn : 0 < n) (hA_nonneg : 0 ≤ A) :
    A ^ n = CFC.nnrpow A (n : ℝ≥0) := by
  symm
  rw [CFC.nnrpow_eq_pow]
  rw [CFC.nnrpow_eq_rpow (A := H →L[ℂ] H) (by exact_mod_cast hn)]
  change A ^ (n : ℝ) = A ^ n
  rw [CFC.rpow_natCast (a := A) n (ha := hA_nonneg)]

/-- Positive real functional-calculus powers vary continuously in operator norm away from the
endpoint `0`, where the nonunital calculus forces `a ^ 0 = 0`. -/
theorem continuousOn_nnrpow_pos
    (A : H →L[ℂ] H) :
    ContinuousOn (fun t : ℝ≥0 => CFC.nnrpow A t) (Set.Ioi 0) := by
  intro t₀ ht₀
  let K : Set ℝ≥0 := quasispectrum ℝ≥0 A
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (quasispectrum.isCompact_nnreal A)
  have hpow_cont :
      ContinuousOn
        (fun p : ℝ≥0 × K => (p.2 : ℝ≥0) ^ (p.1 : ℝ))
        (Set.Ioi (0 : ℝ≥0) ×ˢ Set.univ) := by
    intro p hp
    have hp₁ : 0 < (p.1 : ℝ) := by
      exact_mod_cast hp.1
    have hg₁ : ContinuousAt (fun q : ℝ≥0 × K => (q.2 : ℝ≥0)) p := by
      exact continuousAt_subtype_val.comp continuousAt_snd
    have hg₂ : ContinuousAt (fun q : ℝ≥0 × K => (q.1 : ℝ)) p := by
      exact continuous_subtype_val.continuousAt.comp continuousAt_fst
    simpa using
      (ContinuousAt.comp₂
        (f := fun q : ℝ≥0 × ℝ => q.1 ^ q.2)
        (g := fun q : ℝ≥0 × K => (q.2 : ℝ≥0))
        (h := fun q : ℝ≥0 × K => (q.1 : ℝ))
        (x := p)
        (NNReal.continuousAt_rpow
          (x := (p.2 : ℝ≥0))
          (y := (p.1 : ℝ))
          (Or.inr hp₁))
        hg₁ hg₂).continuousWithinAt
  have hxU : Set.Ioi (0 : ℝ≥0) ∈ nhds t₀ := Ioi_mem_nhds ht₀
  have h_tendsto :
      TendstoUniformlyOn
        (fun t : ℝ≥0 => fun x : ℝ≥0 => x ^ (t : ℝ))
        (fun x : ℝ≥0 => x ^ (t₀ : ℝ))
        (nhds t₀)
        K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [K] using
      (ContinuousOn.tendstoUniformly
        (f := fun t : ℝ≥0 => fun x : K => (x : ℝ≥0) ^ (t : ℝ))
        hxU hpow_cont)
  set_option backward.isDefEq.respectTransparency false in
  have hcont :
      ContinuousAt
        (fun t : ℝ≥0 => cfcₙ (fun x : ℝ≥0 => x ^ (t : ℝ)) A)
        t₀ :=
    continuousAt_cfcₙ_fun
      (a := A)
      (f := fun t : ℝ≥0 => fun x : ℝ≥0 => x ^ (t : ℝ))
      (x₀ := t₀)
      h_tendsto
      (Filter.Eventually.of_forall fun t =>
        (NNReal.continuous_rpow_const (show 0 ≤ (t : ℝ) by exact_mod_cast t.2)).continuousOn)
      (by
        filter_upwards [Ioi_mem_nhds ht₀] with t ht
        have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        simp [NNReal.zero_rpow ht'.ne'])
  simpa [CFC.nnrpow_def] using hcont.continuousWithinAt

/-- The same positive-time continuity, expressed on real times via `Real.toNNReal`. This is the
form used by the OS semigroup, whose parameter lives in `ℝ` with a positivity proof. -/
theorem continuousOn_nnrpow_posReal
    (A : H →L[ℂ] H) :
    ContinuousOn (fun t : ℝ => CFC.nnrpow A (Real.toNNReal t)) (Set.Ioi 0) := by
  refine (continuousOn_nnrpow_pos (A := A)).comp continuous_real_toNNReal.continuousOn ?_
  intro t ht
  simpa [Real.toNNReal_of_nonneg ht.le] using ht

omit [CompleteSpace H] in
/-- The `(n+1)`-fold product of a positive-time semigroup element is the value at
time `(n+1) * t`. This is the algebraic input needed for reciprocal-time roots. -/
theorem semigroup_nat_pow_succ
    (T : ∀ t : ℝ, 0 < t → H →L[ℂ] H)
    (hsemigroup : ∀ s hs t ht,
      T (s + t) (add_pos hs ht) = T s hs * T t ht)
    (t : ℝ) (ht : 0 < t) :
    ∀ n : ℕ,
      (T t ht) ^ (n + 1) =
        T (((n + 1 : ℕ) : ℝ) * t)
          (mul_pos (by exact_mod_cast Nat.succ_pos n) ht) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnpos : 0 < (((n + 1 : ℕ) : ℝ) * t) := by
        exact mul_pos (by exact_mod_cast Nat.succ_pos n) ht
      have htimeOp :
          T ((((n + 1 : ℕ) : ℝ) * t) + t) (add_pos hnpos ht) =
            T (((n + 1 + 1 : ℕ) : ℝ) * t)
              (mul_pos (by exact_mod_cast Nat.succ_pos (n + 1)) ht) := by
        congr 1
        calc
          (((n + 1 : ℕ) : ℝ) * t) + t = (((n : ℝ) + 1) * t) + t := by norm_num
          _ = ((n : ℝ) + 2) * t := by ring
          _ = (((n + 1 + 1 : ℕ) : ℝ) * t) := by
              congr 1
              have hcoeff : (((n + 1 + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 + 1 := by
                norm_num [Nat.cast_add]
              linarith
      calc
        (T t ht) ^ (n + 1 + 1) = (T t ht) ^ (n + 1) * T t ht := by rw [pow_succ]
        _ = T (((n + 1 : ℕ) : ℝ) * t) hnpos * T t ht := by rw [ih]
        _ = T ((((n + 1 : ℕ) : ℝ) * t) + t) (add_pos hnpos ht) := by
            rw [(hsemigroup _ _ _ _).symm]
        _ = T (((n + 1 + 1 : ℕ) : ℝ) * t)
              (mul_pos (by exact_mod_cast Nat.succ_pos (n + 1)) ht) := htimeOp

/-- In a positive-time semigroup of bounded nonnegative operators, the reciprocal
time value is the unique positive `n`-th root of the time-one operator. -/
theorem semigroup_reciprocal_eq_positive_qroot
    (T : ∀ t : ℝ, 0 < t → H →L[ℂ] H)
    (hsemigroup : ∀ s hs t ht,
      T (s + t) (add_pos hs ht) = T s hs * T t ht)
    (hnonneg : ∀ t ht, 0 ≤ T t ht)
    (n : ℕ) (hn : 0 < n) :
    T ((n : ℝ)⁻¹) (inv_pos.mpr (by exact_mod_cast hn)) =
      CFC.nnrpow (T 1 one_pos) ((n : ℝ≥0)⁻¹) := by
  cases n with
  | zero =>
      cases Nat.not_lt_zero 0 hn
  | succ m =>
      have htn : 0 < (((m + 1 : ℕ) : ℝ)⁻¹) := by
        exact inv_pos.mpr (by exact_mod_cast Nat.succ_pos m)
      have hpow : (T (((m + 1 : ℕ) : ℝ)⁻¹) htn) ^ (m + 1) = T 1 one_pos := by
        have hpow' := semigroup_nat_pow_succ T hsemigroup (((m + 1 : ℕ) : ℝ)⁻¹) htn m
        have htimeOp :
            T ((((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ)⁻¹)))
                (mul_pos (by exact_mod_cast Nat.succ_pos m) htn) =
              T 1 one_pos := by
          congr 1
          field_simp
        exact hpow'.trans htimeOp
      simpa using
        (positive_qroot_unique
          (A := T 1 one_pos)
          (B := T (((m + 1 : ℕ) : ℝ)⁻¹) htn)
          (n := m + 1)
          (hn := Nat.succ_pos m)
          (hA_nonneg := hnonneg 1 one_pos)
          (hB_nonneg := hnonneg (((m + 1 : ℕ) : ℝ)⁻¹) htn)
          hpow).symm

/-- Positive rational times in a nonnegative semigroup are the corresponding
nonnegative real powers of the time-one operator. -/
theorem semigroup_rational_eq_positive_qroot
    (T : ∀ t : ℝ, 0 < t → H →L[ℂ] H)
    (hsemigroup : ∀ s hs t ht,
      T (s + t) (add_pos hs ht) = T s hs * T t ht)
    (hnonneg : ∀ t ht, 0 ≤ T t ht)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    T ((p : ℝ) * (q : ℝ)⁻¹)
        (mul_pos (by exact_mod_cast hp) (inv_pos.mpr (by exact_mod_cast hq))) =
      CFC.nnrpow (T 1 one_pos) ((p : ℝ≥0) * (q : ℝ≥0)⁻¹) := by
  cases p with
  | zero =>
      cases Nat.not_lt_zero 0 hp
  | succ m =>
      have hqinv : 0 < (q : ℝ)⁻¹ := by
        exact inv_pos.mpr (by exact_mod_cast hq)
      calc
        T (((m + 1 : ℕ) : ℝ) * (q : ℝ)⁻¹)
            (mul_pos (by exact_mod_cast Nat.succ_pos m) hqinv)
          = (T ((q : ℝ)⁻¹) hqinv) ^ (m + 1) := by
              symm
              exact semigroup_nat_pow_succ T hsemigroup ((q : ℝ)⁻¹) hqinv m
        _ = (CFC.nnrpow (T 1 one_pos) ((q : ℝ≥0)⁻¹)) ^ (m + 1) := by
              rw [semigroup_reciprocal_eq_positive_qroot T hsemigroup hnonneg q hq]
        _ = CFC.nnrpow (CFC.nnrpow (T 1 one_pos) ((q : ℝ≥0)⁻¹))
              (((m + 1 : ℕ) : ℝ≥0)) := by
              rw [← natPow_eq_nnrpow_natCast
                (CFC.nnrpow (T 1 one_pos) ((q : ℝ≥0)⁻¹))
                (m + 1) (Nat.succ_pos m)]
              exact CFC.nnrpow_nonneg
        _ = CFC.nnrpow (T 1 one_pos) (((q : ℝ≥0)⁻¹) * (((m + 1 : ℕ) : ℝ≥0))) := by
              simpa [CFC.nnrpow_eq_pow] using
                (CFC.nnrpow_nnrpow
                  (a := T 1 one_pos)
                  (x := ((q : ℝ≥0)⁻¹))
                  (y := (((m + 1 : ℕ) : ℝ≥0))))
        _ = CFC.nnrpow (T 1 one_pos) ((((m + 1 : ℕ) : ℝ≥0) * (q : ℝ≥0)⁻¹)) := by
              rw [mul_comm]

end ContinuousLinearMap
