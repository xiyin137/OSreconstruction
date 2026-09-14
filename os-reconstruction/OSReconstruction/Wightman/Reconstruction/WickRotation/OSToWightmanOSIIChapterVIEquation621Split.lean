import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery

/-!
# OS II equation (6.21) under a generator split

The recursive Schwarz estimate uses self-pair families at two different
lower arities.  The epsilon part of equation `(6.21)` is controlled by OS II
`(6.25)`.  Its time-average part is point-dependent and is controlled by
`(6.24)`.  This module keeps those two obligations separate and combines
them only after both have been proved.

The weighted arithmetic-mean hypothesis below is the reduced form `(6.26)`
of the time-average comparison.  Geometry-specific modules should prove that
hypothesis for their actual parent and reflected lower-arity points.
-/

noncomputable section

open Complex
open scoped BigOperators

namespace OSReconstruction

/-! ## The weighted AM--GM core -/

/-- If the weighted arithmetic mean of two nonnegative bases is bounded by a
target base, then the corresponding integer powers satisfy the split bound.

The weights are `a / (2 * k)` and `b / (2 * k)`.  The arity identity
`a + b = 2 * k` says that they add to one.  This is the abstract convexity
calculation used in both OS II `(6.24)` and `(6.25)`. -/
theorem weightedGeometricMean_split_pow_le_of_weightedArithmeticMean_le
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {A B K : Real}
    (hA : 0 <= A) (hB : 0 <= B)
    (hmean :
      ((a : Real) / (2 * k : Nat)) * A +
          ((b : Real) / (2 * k : Nat)) * B <= K) :
    A ^ a * B ^ b <= K ^ (2 * k) := by
  let wa : Real := (a : Real) / (2 * k : Nat)
  let wb : Real := (b : Real) / (2 * k : Nat)
  let p : Real := (2 * k : Nat)
  have habR : (a : Real) + b = 2 * k := by
    exact_mod_cast hab
  have hweights : wa + wb = 1 := by
    dsimp [wa, wb]
    have hk0 : (k : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at *
    nlinarith [habR]
  have hweighted : A ^ wa * B ^ wb <= K := by
    apply (Real.geom_mean_le_arith_mean2_weighted
      (show 0 <= wa by positivity)
      (show 0 <= wb by positivity)
      hA hB hweights).trans
    simpa [wa, wb] using hmean
  have hpow : (A ^ wa * B ^ wb) ^ p <= K ^ p :=
    Real.rpow_le_rpow (by positivity) hweighted (by positivity)
  have hwa : wa * p = a := by
    dsimp [wa, p]
    have hk0 : (k : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  have hwb : wb * p = b := by
    dsimp [wb, p]
    have hk0 : (k : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  calc
    A ^ a * B ^ b = (A ^ wa * B ^ wb) ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA wa)
        (Real.rpow_nonneg hB wb)]
      rw [← Real.rpow_mul hA, ← Real.rpow_mul hB, hwa, hwb]
      rw [Real.rpow_natCast, Real.rpow_natCast]
    _ <= K ^ p := hpow
    _ = K ^ (2 * k) := by
      rw [show p = ((2 * k : Nat) : Real) by rfl,
        Real.rpow_natCast]

/-! ## The point-dependent time factor -/

/-- Reduced `(6.26)` form of the time-average split comparison. -/
def OSIIEquation621TimeAverageSplitCondition
    {a b k : Nat}
    (zetaLeft : OSIITimeGapSpace a)
    (zetaRight : OSIITimeGapSpace b)
    (zetaTarget : OSIITimeGapSpace k) : Prop :=
  ((a : Real) / (2 * k : Nat)) *
        ‖osiiVI2TimeAverageBase a zetaLeft‖ +
      ((b : Real) / (2 * k : Nat)) *
        ‖osiiVI2TimeAverageBase b zetaRight‖ <=
    ‖osiiVI2TimeAverageBase k zetaTarget‖

/-- Numerator form of the time-average split condition.  The arity weights
cancel the denominators in `osiiVI2TimeAverageBase`, so this is the
geometry-specific inequality that recursive callers actually need to prove. -/
def OSIIEquation621TimeAverageNumeratorSplitCondition
    {a b k : Nat}
    (zetaLeft : OSIITimeGapSpace a)
    (zetaRight : OSIITimeGapSpace b)
    (zetaTarget : OSIITimeGapSpace k) : Prop :=
  ‖1 + ∑ i : Fin a, zetaLeft i‖ +
      ‖1 + ∑ i : Fin b, zetaRight i‖ <=
    2 * ‖1 + ∑ i : Fin k, zetaTarget i‖

/-- OS II `(6.26)` in the form most convenient for rooted geometry.  If the
two lower numerators are nonnegative real numbers and their sum is bounded
by twice the real part of the target numerator, the complex norm comparison
follows from `re z <= ‖z‖`.

Using an inequality rather than equality here accommodates finite packet
anchors while retaining the exact printed argument as the equality case. -/
theorem OSIIEquation621TimeAverageNumeratorSplitCondition.of_nonnegativeRealNumerators
    {a b k : Nat}
    {zetaLeft : OSIITimeGapSpace a}
    {zetaRight : OSIITimeGapSpace b}
    {zetaTarget : OSIITimeGapSpace k}
    (hleft_im : (1 + ∑ i : Fin a, zetaLeft i).im = 0)
    (hright_im : (1 + ∑ i : Fin b, zetaRight i).im = 0)
    (hleft_nonneg : 0 <= (1 + ∑ i : Fin a, zetaLeft i).re)
    (hright_nonneg : 0 <= (1 + ∑ i : Fin b, zetaRight i).re)
    (hsum :
      (1 + ∑ i : Fin a, zetaLeft i).re +
          (1 + ∑ i : Fin b, zetaRight i).re <=
        2 * (1 + ∑ i : Fin k, zetaTarget i).re) :
    OSIIEquation621TimeAverageNumeratorSplitCondition
      zetaLeft zetaRight zetaTarget := by
  unfold OSIIEquation621TimeAverageNumeratorSplitCondition
  have hleft :
      1 + ∑ i : Fin a, zetaLeft i =
        ((1 + ∑ i : Fin a, zetaLeft i).re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hleft_im
  have hright :
      1 + ∑ i : Fin b, zetaRight i =
        ((1 + ∑ i : Fin b, zetaRight i).re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hright_im
  rw [hleft, hright, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
    abs_of_nonneg hright_nonneg]
  exact hsum.trans
    (mul_le_mul_of_nonneg_left
      (Complex.re_le_norm (1 + ∑ i : Fin k, zetaTarget i)) (by positivity))

/-- The numerator comparison is exactly sufficient for the weighted
time-average comparison after cancelling the positive arity denominators. -/
theorem OSIIEquation621TimeAverageNumeratorSplitCondition.toTimeAverageSplitCondition
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    {zetaLeft : OSIITimeGapSpace a}
    {zetaRight : OSIITimeGapSpace b}
    {zetaTarget : OSIITimeGapSpace k}
    (hnum : OSIIEquation621TimeAverageNumeratorSplitCondition
      zetaLeft zetaRight zetaTarget) :
    OSIIEquation621TimeAverageSplitCondition
      zetaLeft zetaRight zetaTarget := by
  unfold OSIIEquation621TimeAverageNumeratorSplitCondition at hnum
  unfold OSIIEquation621TimeAverageSplitCondition
  simp only [osiiVI2TimeAverageBase, norm_div,
    Complex.norm_natCast]
  have haR : 0 < (a : Real) := by exact_mod_cast ha
  have hbR : 0 < (b : Real) := by exact_mod_cast hb
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  calc
    (a : Real) / (2 * k : Nat) *
          (‖1 + ∑ i : Fin a, zetaLeft i‖ / (a : Real)) +
        (b : Real) / (2 * k : Nat) *
          (‖1 + ∑ i : Fin b, zetaRight i‖ / (b : Real)) =
        (‖1 + ∑ i : Fin a, zetaLeft i‖ +
          ‖1 + ∑ i : Fin b, zetaRight i‖) /
            (2 * (k : Real)) := by
      field_simp [haR.ne', hbR.ne', hkR.ne']
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ <= (2 * ‖1 + ∑ i : Fin k, zetaTarget i‖) /
          (2 * (k : Real)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = ‖1 + ∑ i : Fin k, zetaTarget i‖ / (k : Real) := by
      field_simp [hkR.ne']

/-- The reduced weighted arithmetic-mean comparison implies OS II `(6.24)`
in the integer-power form used by the recursive Schwarz estimate. -/
theorem osiiVI2TimeAverageBase_split_pow_le
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {zetaLeft : OSIITimeGapSpace a}
    {zetaRight : OSIITimeGapSpace b}
    {zetaTarget : OSIITimeGapSpace k}
    (hsplit : OSIIEquation621TimeAverageSplitCondition
      zetaLeft zetaRight zetaTarget) :
    ‖osiiVI2TimeAverageBase a zetaLeft‖ ^ a *
        ‖osiiVI2TimeAverageBase b zetaRight‖ ^ b <=
      ‖osiiVI2TimeAverageBase k zetaTarget‖ ^ (2 * k) := by
  exact
    weightedGeometricMean_split_pow_le_of_weightedArithmeticMean_le
      ha hb hk hab (norm_nonneg _) (norm_nonneg _) hsplit

/-- Raising `(6.24)` to the common exponent `t` bounds the product of the two
lower time denormalizations by the square of the target denormalization. -/
theorem norm_osiiVI2TimeDenormalization_split_mul_le_sq
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {zetaLeft : OSIITimeGapSpace a}
    {zetaRight : OSIITimeGapSpace b}
    {zetaTarget : OSIITimeGapSpace k}
    (hsplit : OSIIEquation621TimeAverageSplitCondition
      zetaLeft zetaRight zetaTarget)
    (t : Nat) :
    ‖osiiVI2TimeDenormalization t a zetaLeft‖ *
        ‖osiiVI2TimeDenormalization t b zetaRight‖ <=
      ‖osiiVI2TimeDenormalization t k zetaTarget‖ ^ 2 := by
  have hbase := osiiVI2TimeAverageBase_split_pow_le
    ha hb hk hab hsplit
  simp only [osiiVI2TimeDenormalization, Complex.norm_pow]
  calc
    ‖osiiVI2TimeAverageBase a zetaLeft‖ ^ (a * t) *
        ‖osiiVI2TimeAverageBase b zetaRight‖ ^ (b * t) =
        (‖osiiVI2TimeAverageBase a zetaLeft‖ ^ a *
          ‖osiiVI2TimeAverageBase b zetaRight‖ ^ b) ^ t := by
      rw [mul_pow, pow_mul, pow_mul]
    _ <= (‖osiiVI2TimeAverageBase k zetaTarget‖ ^ (2 * k)) ^ t :=
      pow_le_pow_left₀
        (mul_nonneg (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg (norm_nonneg _) _)) hbase t
    _ = (‖osiiVI2TimeAverageBase k zetaTarget‖ ^ (k * t)) ^ 2 := by
      have hexp : (2 * k) * t = (k * t) * 2 := by ring
      rw [← pow_mul, ← pow_mul, hexp]

/-! ## Complete equation (6.21) split -/

/-- Combining the point-dependent time comparison `(6.24)` with the
epsilon comparison `(6.25)` bounds the product of the complete lower-arity
denormalizations by the square of the complete target denormalization. -/
theorem norm_osiiVI2Equation621Denormalization_split_mul_le_sq
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {zetaLeft : OSIITimeGapSpace a}
    {zetaRight : OSIITimeGapSpace b}
    {zetaTarget : OSIITimeGapSpace k}
    (hsplit : OSIIEquation621TimeAverageSplitCondition
      zetaLeft zetaRight zetaTarget)
    (t : Nat) :
    ‖osiiVI2Equation621Denormalization t a epsilon zetaLeft‖ *
        ‖osiiVI2Equation621Denormalization t b epsilon zetaRight‖ <=
      ‖osiiVI2Equation621Denormalization t k epsilon zetaTarget‖ ^ 2 := by
  have htime := norm_osiiVI2TimeDenormalization_split_mul_le_sq
    ha hb hk hab hsplit t
  have heps := osiiVI2Denormalization_split_mul_le_sq
    ha hb hk hab hepsilon t
  have hDa : 0 <= osiiVI2Denormalization t a epsilon :=
    (osiiVI2Denormalization_pos ha hepsilon t).le
  have hDb : 0 <= osiiVI2Denormalization t b epsilon :=
    (osiiVI2Denormalization_pos hb hepsilon t).le
  have hDk : 0 <= osiiVI2Denormalization t k epsilon :=
    (osiiVI2Denormalization_pos hk hepsilon t).le
  simp only [osiiVI2Equation621Denormalization, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDa,
    abs_of_nonneg hDb, abs_of_nonneg hDk]
  calc
    (‖osiiVI2TimeDenormalization t a zetaLeft‖ *
          osiiVI2Denormalization t a epsilon) *
        (‖osiiVI2TimeDenormalization t b zetaRight‖ *
          osiiVI2Denormalization t b epsilon) =
        (‖osiiVI2TimeDenormalization t a zetaLeft‖ *
          ‖osiiVI2TimeDenormalization t b zetaRight‖) *
        (osiiVI2Denormalization t a epsilon *
          osiiVI2Denormalization t b epsilon) := by ring
    _ <= ‖osiiVI2TimeDenormalization t k zetaTarget‖ ^ 2 *
        osiiVI2Denormalization t k epsilon ^ 2 := by
      exact mul_le_mul htime heps (mul_nonneg hDa hDb)
        (sq_nonneg ‖osiiVI2TimeDenormalization t k zetaTarget‖)
    _ = (‖osiiVI2TimeDenormalization t k zetaTarget‖ *
        osiiVI2Denormalization t k epsilon) ^ 2 := by ring

end OSReconstruction
