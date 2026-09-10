import OSReconstruction.Wightman.Reconstruction.UniversalProjection
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# Euclidean Rotations for OS-II Axis-Pair Directions

The axis-pair geometry uses the genuine spacetime directions `(T, ±e_j)`.
This file supplies a proper Euclidean rotation identifying each such direction
with a positive pure-time shift.  It is the covariance bridge required before
the one-variable OS time semigroup can be used along a spatially sensitive
axis-pair slice.
-/

noncomputable section

open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Euclidean length of every direction `(T, ±e_j)`. -/
def osiiAxisPairRadius (T : ℝ) : ℝ :=
  Real.sqrt (T ^ 2 + 1)

/-- Unit normalization of an OS-II axis-pair direction. -/
def osiiAxisPairUnitDir (T : ℝ) (a : osiiAxisPairIndex d) :
    Fin (d + 1) → ℝ :=
  (osiiAxisPairRadius T)⁻¹ • osiiAxisPairDir (d := d) T a

/-- Reverse the spatial sign while retaining the selected axis. -/
def osiiAxisPairOpposite (a : osiiAxisPairIndex d) :
    osiiAxisPairIndex d :=
  (a.1, !a.2)

omit [NeZero d] in
@[simp] theorem osiiAxisPairOpposite_fst
    (a : osiiAxisPairIndex d) :
    (osiiAxisPairOpposite a).1 = a.1 := rfl

omit [NeZero d] in
@[simp] theorem osiiAxisPairOpposite_snd
    (a : osiiAxisPairIndex d) :
    (osiiAxisPairOpposite a).2 = !a.2 := rfl

omit [NeZero d] in
@[simp] theorem osiiAxisPairOpposite_opposite
    (a : osiiAxisPairIndex d) :
    osiiAxisPairOpposite (osiiAxisPairOpposite a) = a := by
  rcases a with ⟨j, s⟩
  cases s <;> rfl

theorem osiiAxisPairRadius_pos (T : ℝ) :
    0 < osiiAxisPairRadius T := by
  apply Real.sqrt_pos.2
  positivity

omit [NeZero d] in
theorem osiiAxisPairDir_sq_sum (T : ℝ) (a : osiiAxisPairIndex d) :
    ∑ μ : Fin (d + 1), osiiAxisPairDir (d := d) T a μ ^ 2 = T ^ 2 + 1 := by
  rw [Fin.sum_univ_succ]
  simp only [osiiAxisPairDir, Fin.cases_zero, Fin.cases_succ]
  rw [Finset.sum_eq_single a.1]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

omit [NeZero d] in
/-- The product-space norm of an axis-pair direction is bounded by its
Euclidean normalization radius. -/
theorem norm_osiiAxisPairDir_le_radius
    (T : ℝ) (a : osiiAxisPairIndex d) :
    ‖osiiAxisPairDir (d := d) T a‖ ≤ osiiAxisPairRadius T := by
  change
    ‖osiiAxisPairDir (d := d) T a‖ ≤ Real.sqrt (T ^ 2 + 1)
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro μ
  have hsq :
      osiiAxisPairDir (d := d) T a μ ^ 2 ≤ T ^ 2 + 1 := by
    rw [← osiiAxisPairDir_sq_sum T a]
    exact
      Finset.single_le_sum
        (fun ν _ => sq_nonneg (osiiAxisPairDir (d := d) T a ν))
        (Finset.mem_univ μ)
  have habs :
      |osiiAxisPairDir (d := d) T a μ| ≤
        Real.sqrt (T ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  simpa [osiiAxisPairRadius, Real.norm_eq_abs] using habs

omit [NeZero d] in
theorem osiiAxisPairDir_dot
    (T : ℝ) (a b : osiiAxisPairIndex d) :
    (∑ μ : Fin (d + 1),
        osiiAxisPairDir (d := d) T a μ *
          osiiAxisPairDir (d := d) T b μ) =
      T ^ 2 +
        if a.1 = b.1 then
          if a.2 = b.2 then 1 else -1
        else 0 := by
  rcases a with ⟨a, sa⟩
  rcases b with ⟨b, sb⟩
  rw [Fin.sum_univ_succ]
  simp only [osiiAxisPairDir, Fin.cases_zero, Fin.cases_succ]
  by_cases hab : a = b
  · subst b
    rw [Finset.sum_eq_single a]
    · cases sa <;> cases sb <;> simp [pow_two]
    · intro j _ hja
      simp [Ne.symm hja]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hab, pow_two]
    · intro j _
      by_cases haj : a = j
      · subst j
        simp [Ne.symm hab]
      · simp [haj]

omit [NeZero d] in
theorem osiiAxisPairDir_dot_lower
    (T : ℝ) (a b : osiiAxisPairIndex d) :
    T ^ 2 - 1 ≤
      ∑ μ : Fin (d + 1),
        osiiAxisPairDir (d := d) T a μ *
          osiiAxisPairDir (d := d) T b μ := by
  rw [osiiAxisPairDir_dot]
  split_ifs <;> linarith

omit [NeZero d] in
theorem osiiAxisPairUnitDir_sq_sum (T : ℝ) (a : osiiAxisPairIndex d) :
    ∑ μ : Fin (d + 1), osiiAxisPairUnitDir (d := d) T a μ ^ 2 = 1 := by
  have hr_pos : 0 < osiiAxisPairRadius T := osiiAxisPairRadius_pos T
  have hr_sq : osiiAxisPairRadius T ^ 2 = T ^ 2 + 1 := by
    exact Real.sq_sqrt (by positivity)
  simp only [osiiAxisPairUnitDir, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, osiiAxisPairDir_sq_sum, ← hr_sq]
  field_simp [ne_of_gt hr_pos]

/-- Every axis-pair unit direction is the first row of a proper orthogonal
matrix. -/
theorem exists_osiiAxisPairRotation
    (T : ℝ) (a : osiiAxisPairIndex d) :
    ∃ R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      R.transpose * R = 1 ∧
      R.det = 1 ∧
      (∀ μ, R 0 μ = osiiAxisPairUnitDir (d := d) T a μ) := by
  exact exists_orthogonal_matrix_with_first_row
    (d := d) (osiiAxisPairUnitDir (d := d) T a)
    (osiiAxisPairUnitDir_sq_sum (d := d) T a)

/-- After transposing the proper rotation, a pure positive-time shift of
length `sqrt (T² + 1)` becomes the genuine axis-pair direction `(T, ±e_j)`. -/
theorem exists_osiiAxisPairRotation_transpose_timeShift
    (T : ℝ) (a : osiiAxisPairIndex d) :
    ∃ R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      R.transpose * R = 1 ∧
      R.det = 1 ∧
      R.transpose.mulVec (timeShiftVec d (osiiAxisPairRadius T)) =
        osiiAxisPairDir (d := d) T a := by
  obtain ⟨R, hR, hdet, hrow⟩ := exists_osiiAxisPairRotation (d := d) T a
  refine ⟨R, hR, hdet, ?_⟩
  ext μ
  have hr_pos : 0 < osiiAxisPairRadius T := osiiAxisPairRadius_pos T
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, timeShiftVec]
  rw [Fin.sum_univ_succ]
  simp only [if_neg (Fin.succ_ne_zero _), mul_zero, Finset.sum_const_zero, add_zero]
  rw [hrow]
  simp only [osiiAxisPairUnitDir, Pi.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hr_pos]
  simp [mul_comm]

/-- The proper rotation and its direction certificate, bundled so later
axis-pair families cannot accidentally combine data from different
directions. -/
structure OSIIAxisPairRotationData
    (T : ℝ) (a : osiiAxisPairIndex d) where
  matrix : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ
  orthogonal : matrix.transpose * matrix = 1
  det_one : matrix.det = 1
  transpose_timeShift :
    matrix.transpose.mulVec (timeShiftVec d (osiiAxisPairRadius T)) =
      osiiAxisPairDir (d := d) T a

/-- A fixed proper rotation for every signed OS-II axis-pair direction. -/
noncomputable def osiiAxisPairRotationData
    (T : ℝ) (a : osiiAxisPairIndex d) :
    OSIIAxisPairRotationData T a :=
  let h := exists_osiiAxisPairRotation_transpose_timeShift (d := d) T a
  { matrix := Classical.choose h
    orthogonal := (Classical.choose_spec h).1
    det_one := (Classical.choose_spec h).2.1
    transpose_timeShift := (Classical.choose_spec h).2.2 }

omit [NeZero d] in
/-- The canonical rotation has the selected normalized direction as its first
row. This is recovered from its pure-time transpose certificate. -/
theorem OSIIAxisPairRotationData.first_row
    (D : OSIIAxisPairRotationData (d := d) T a)
    (μ : Fin (d + 1)) :
    D.matrix 0 μ = osiiAxisPairUnitDir (d := d) T a μ := by
  have hr_pos : 0 < osiiAxisPairRadius T := osiiAxisPairRadius_pos T
  have hcoord := congrFun D.transpose_timeShift μ
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, timeShiftVec] at hcoord
  rw [Fin.sum_univ_succ] at hcoord
  simp only [if_neg (Fin.succ_ne_zero _), mul_zero, Finset.sum_const_zero,
    add_zero] at hcoord
  simp only [osiiAxisPairUnitDir, Pi.smul_apply, smul_eq_mul]
  rw [show (osiiAxisPairRadius T)⁻¹ * osiiAxisPairDir (d := d) T a μ =
      osiiAxisPairDir (d := d) T a μ / osiiAxisPairRadius T by
    simp [div_eq_mul_inv, mul_comm]]
  apply (eq_div_iff (ne_of_gt hr_pos)).2
  simpa using hcoord

omit [NeZero d] in
/-- The time coordinate in an axis-pair frame is the normalized signed
`T x⁰ ± xʲ` functional. -/
theorem OSIIAxisPairRotationData.mulVec_time
    (D : OSIIAxisPairRotationData (d := d) T a)
    (x : SpacetimeDim d) :
    (D.matrix.mulVec x) 0 =
      (osiiAxisPairRadius T)⁻¹ *
        (T * x 0 +
          if a.2 then x (Fin.succ a.1) else -x (Fin.succ a.1)) := by
  rcases a with ⟨j, s⟩
  simp only [Matrix.mulVec, dotProduct, D.first_row, osiiAxisPairUnitDir,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, Fin.sum_univ_succ]
  simp only [osiiAxisPairDir, Fin.cases_zero, Fin.cases_succ]
  rw [Finset.sum_eq_single j]
  · cases s <;> simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

omit [NeZero d] in
/-- Time reflection in one signed axis-pair frame is minus the time
coordinate in the opposite signed frame. -/
theorem OSIIAxisPairRotationData.mulVec_timeReflection_eq_neg_opposite
    (D : OSIIAxisPairRotationData (d := d) T a)
    (Dop : OSIIAxisPairRotationData (d := d) T (osiiAxisPairOpposite a))
    (x : SpacetimeDim d) :
    (D.matrix.mulVec (timeReflection d x)) 0 =
      -(Dop.matrix.mulVec x) 0 := by
  rw [D.mulVec_time, Dop.mulVec_time]
  rcases a with ⟨j, s⟩
  cases s <;> simp [osiiAxisPairOpposite, timeReflection] <;> ring

/-- Canonical-rotation specialization of
`OSIIAxisPairRotationData.mulVec_timeReflection_eq_neg_opposite`. -/
theorem osiiAxisPairRotationData_mulVec_timeReflection_eq_neg_opposite
    (T : ℝ) (a : osiiAxisPairIndex d) (x : SpacetimeDim d) :
    ((osiiAxisPairRotationData T a).matrix.mulVec (timeReflection d x)) 0 =
      -((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec x) 0 :=
  (osiiAxisPairRotationData T a).mulVec_timeReflection_eq_neg_opposite
    (osiiAxisPairRotationData T (osiiAxisPairOpposite a)) x

omit [NeZero d] in
/-- The selected rotation sees every axis-pair direction through the Euclidean
dot product with its normalized first row. -/
theorem OSIIAxisPairRotationData.mulVec_dir_time
    (D : OSIIAxisPairRotationData (d := d) T a)
    (b : osiiAxisPairIndex d) :
    (D.matrix.mulVec (osiiAxisPairDir (d := d) T b)) 0 =
      (osiiAxisPairRadius T)⁻¹ *
        ∑ μ : Fin (d + 1),
          osiiAxisPairDir (d := d) T a μ *
            osiiAxisPairDir (d := d) T b μ := by
  simp only [Matrix.mulVec, dotProduct, D.first_row, osiiAxisPairUnitDir,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  ring

omit [NeZero d] in
/-- If `T > 1`, every axis-pair direction has strictly positive time
component in every selected axis-pair frame. -/
theorem OSIIAxisPairRotationData.mulVec_dir_time_pos
    (D : OSIIAxisPairRotationData (d := d) T a)
    (hT : 1 < T)
    (b : osiiAxisPairIndex d) :
    0 < (D.matrix.mulVec (osiiAxisPairDir (d := d) T b)) 0 := by
  rw [D.mulVec_dir_time]
  apply mul_pos
  · exact inv_pos.mpr (osiiAxisPairRadius_pos T)
  · have hlower := osiiAxisPairDir_dot_lower (d := d) T a b
    have hbase : 0 < T ^ 2 - 1 := by nlinarith
    linarith

/-- Sum of all axis-pair translations except the coefficient selected as the
active one-variable semigroup parameter. -/
def osiiAxisPairFrozenTranslation
    (T : ℝ) (c : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    SpacetimeDim d :=
  ∑ b ∈ (Finset.univ : Finset (osiiAxisPairIndex d)).erase a,
    c b • osiiAxisPairDir (d := d) T b

omit [NeZero d] in
theorem osiiAxisPairFrozenTranslation_add_selected
    (T : ℝ) (c : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    osiiAxisPairFrozenTranslation (d := d) T c a +
        c a • osiiAxisPairDir (d := d) T a =
      ∑ b : osiiAxisPairIndex d,
        c b • osiiAxisPairDir (d := d) T b := by
  rw [osiiAxisPairFrozenTranslation, Finset.sum_erase_add]
  exact Finset.mem_univ a

omit [NeZero d] in
theorem osiiAxisPairFrozenTranslation_congr_of_eq_off_selected
    (T : ℝ) {c e : osiiAxisPairIndex d → ℝ}
    (a : osiiAxisPairIndex d)
    (h : ∀ b, b ≠ a → c b = e b) :
    osiiAxisPairFrozenTranslation (d := d) T c a =
      osiiAxisPairFrozenTranslation (d := d) T e a := by
  unfold osiiAxisPairFrozenTranslation
  apply Finset.sum_congr rfl
  intro b hb
  have hba : b ≠ a := by
    exact Finset.ne_of_mem_erase hb
  rw [h b hba]

omit [NeZero d] in
/-- Freezing nonnegative coefficients preserves nonnegative time in every
selected rotated frame. -/
theorem OSIIAxisPairRotationData.mulVec_frozenTranslation_time_nonneg
    (D : OSIIAxisPairRotationData (d := d) T a)
    (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b) :
    0 ≤
      (D.matrix.mulVec
        (osiiAxisPairFrozenTranslation (d := d) T c a)) 0 := by
  simp only [osiiAxisPairFrozenTranslation, Matrix.mulVec_sum,
    Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (hc b)
    (le_of_lt (D.mulVec_dir_time_pos hT b))

end OSReconstruction
