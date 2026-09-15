/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairRotation










noncomputable section

open scoped Classical

namespace OSReconstruction

variable {d n : ℕ} [NeZero d]

/-- The inverse-coordinate action `x |-> R^T x` as a continuous linear
equivalence. -/
noncomputable def osiiEuclideanRotationInvCLE
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' R.transpose
          invFun := Matrix.toLin' R
          left_inv := fun v => by
            show (Matrix.toLin' R) ((Matrix.toLin' R.transpose) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hR', Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' R.transpose) ((Matrix.toLin' R) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

/-- Apply `x_i |-> R^T x_i` in every point coordinate. -/
noncomputable def osiiEuclideanRotateNPointCLE
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  ContinuousLinearEquiv.piCongrRight
    (fun _ : Fin n => osiiEuclideanRotationInvCLE R hR)

/-- Pull a Schwartz test back by the diagonal inverse rotation. -/
noncomputable def osiiEuclideanRotateSchwartz
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (osiiEuclideanRotateNPointCLE (n := n) R hR) φ

omit [NeZero d] in
@[simp] theorem osiiEuclideanRotateSchwartz_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) (x : NPointDomain d n) :
    osiiEuclideanRotateSchwartz R hR φ x =
      φ (fun i => R.transpose.mulVec (x i)) := by
  rfl

/-- Pull a Schwartz test back by the forward rotation. This is the inverse of
`osiiEuclideanRotateSchwartz R hR`. -/
noncomputable def osiiEuclideanUnrotateSchwartz
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  osiiEuclideanRotateSchwartz R.transpose (mul_eq_one_comm.mpr hR) φ

omit [NeZero d] in
@[simp] theorem osiiEuclideanUnrotateSchwartz_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) (x : NPointDomain d n) :
    osiiEuclideanUnrotateSchwartz R hR φ x =
      φ (fun i => R.mulVec (x i)) := by
  rfl

omit [NeZero d] in
/-- Rotating an inverse-rotated Schwartz source recovers the source. -/
@[simp] theorem osiiEuclideanRotateSchwartz_unrotate
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    osiiEuclideanRotateSchwartz R hR
        (osiiEuclideanUnrotateSchwartz R hR φ) = φ := by
  ext x
  simp only [osiiEuclideanRotateSchwartz_apply,
    osiiEuclideanUnrotateSchwartz_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mpr hR]
  simp

omit [NeZero d] in
/-- Inverse-rotating a rotated Schwartz source recovers the source. -/
@[simp] theorem osiiEuclideanUnrotateSchwartz_rotate
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    osiiEuclideanUnrotateSchwartz R hR
        (osiiEuclideanRotateSchwartz R hR φ) = φ := by
  ext x
  simp only [osiiEuclideanUnrotateSchwartz_apply,
    osiiEuclideanRotateSchwartz_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_mulVec, hR]
  simp

/-- Time reflection transported back through a Euclidean rotation. This is the
left-block involution visible after an axis-direction semigroup edge is
returned to the original Euclidean coordinates. -/
def osiiEuclideanRotatedTimeReflection
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : SpacetimeDim d) :
    SpacetimeDim d :=
  R.transpose.mulVec (timeReflection d (R.mulVec x))

theorem osiiEuclideanRotatedTimeReflection_involutive
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (x : SpacetimeDim d) :
    osiiEuclideanRotatedTimeReflection R
        (osiiEuclideanRotatedTimeReflection R x) = x := by
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  simp only [osiiEuclideanRotatedTimeReflection, Matrix.mulVec_mulVec]
  rw [hR']
  simp only [Matrix.one_mulVec]
  rw [timeReflection_timeReflection, Matrix.mulVec_mulVec, hR]
  simp

/-- Configurations which become ordered positive-time after applying `R`
diagonally. -/
def osiiEuclideanRotationOrderedPositiveTimeRegion
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Set (NPointDomain d n) :=
  {x | (fun i => R.mulVec (x i)) ∈ OrderedPositiveTimeRegion d n}

/-- Configurations which become ordered negative-time after applying `R`
diagonally. -/
def osiiEuclideanRotationOrderedNegativeTimeRegion
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Set (NPointDomain d n) :=
  {x | (fun i => R.mulVec (x i)) ∈ OrderedNegativeTimeRegion d n}

omit [NeZero d] in
theorem osiiContinuousTimeReflectionN :
    Continuous (timeReflectionN d (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simp only [timeReflectionN, timeReflection, ↓reduceIte]
    fun_prop
  · simp only [timeReflectionN, timeReflection, hμ, ↓reduceIte]
    fun_prop

/- Time reflection sends ordered negative support to ordered positive
support. -/
theorem SchwartzNPoint.timeReflect_tsupport_orderedPositive
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n) :
    tsupport ((φ.timeReflect : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      timeReflectionN d x ∈
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (osiiContinuousTimeReflectionN (d := d) (n := n)) hx
  have hneg := hφ hxpre
  intro i
  constructor
  · simpa [timeReflectionN, timeReflection] using (hneg i).1
  · intro j hij
    simpa [timeReflectionN, timeReflection] using (hneg i).2 j hij

omit [NeZero d] in
theorem tsupport_osiiEuclideanRotateSchwartz
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    tsupport ((osiiEuclideanRotateSchwartz R hR φ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) =
      (osiiEuclideanRotateNPointCLE (n := n) R hR).toHomeomorph ⁻¹'
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
  simpa [osiiEuclideanRotateSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    (tsupport_comp_eq_preimage
      (g := ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (osiiEuclideanRotateNPointCLE (n := n) R hR).toHomeomorph)

/- A source supported in the `R`-oriented ordered cone becomes an ordinary
ordered positive-time source after rotation. -/
omit [NeZero d] in
theorem osiiEuclideanRotateSchwartz_tsupport_orderedPositive
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R) :
    tsupport ((osiiEuclideanRotateSchwartz R hR φ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => R.transpose.mulVec (x i)) ∈
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    rw [tsupport_osiiEuclideanRotateSchwartz R hR φ] at hx
    exact hx
  have hrot := hφ hxpre
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  simpa [osiiEuclideanRotationOrderedPositiveTimeRegion,
    Matrix.mulVec_mulVec, hR'] using hrot

/- A source supported in the `R`-oriented ordered negative cone becomes an
ordinary ordered negative-time source after rotation. -/
omit [NeZero d] in
theorem osiiEuclideanRotateSchwartz_tsupport_orderedNegative
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion (d := d) (n := n) R) :
    tsupport ((osiiEuclideanRotateSchwartz R hR φ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆
      OrderedNegativeTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => R.transpose.mulVec (x i)) ∈
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    rw [tsupport_osiiEuclideanRotateSchwartz R hR φ] at hx
    exact hx
  have hrot := hφ hxpre
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  simpa [osiiEuclideanRotationOrderedNegativeTimeRegion,
    Matrix.mulVec_mulVec, hR'] using hrot

omit [NeZero d] in
theorem tsupport_osiiEuclideanUnrotateSchwartz
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    tsupport ((osiiEuclideanUnrotateSchwartz R hR φ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) =
      {x | (fun i => R.mulVec (x i)) ∈
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ)} := by
  rw [osiiEuclideanUnrotateSchwartz,
    tsupport_osiiEuclideanRotateSchwartz]
  rfl

omit [NeZero d] in
/- An ordinary ordered positive-time source becomes an `R`-oriented source
after inverse rotation. -/
theorem osiiEuclideanUnrotateSchwartz_tsupport_orderedPositive
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) :
    tsupport ((osiiEuclideanUnrotateSchwartz R hR φ :
        SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := n) R := by
  intro x hx
  rw [tsupport_osiiEuclideanUnrotateSchwartz R hR φ] at hx
  exact hφ hx

omit [NeZero d] in
/- An ordinary ordered negative-time source becomes an `R`-oriented source
after inverse rotation. -/

/-- Modify a common left source so that inverse rotation of its OS-reflected
edge recovers the original source, independently of the chosen rotation. -/
noncomputable def osiiEuclideanCompensatedLeftSchwartz
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  osiiEuclideanUnrotateSchwartz R hR
    ((osiiEuclideanRotateSchwartz R hR φ).timeReflect)

@[simp] theorem osiiEuclideanCompensatedLeftSchwartz_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n) (x : NPointDomain d n) :
    osiiEuclideanCompensatedLeftSchwartz R hR φ x =
      φ (fun i => osiiEuclideanRotatedTimeReflection R (x i)) := by
  rfl

/- Rotating the compensated source gives exactly the time reflection of the
rotated common source. -/

/- The compensated source is admissible in the positive cone whenever the
common source lies in the oppositely oriented negative cone. -/
theorem osiiEuclideanCompensatedLeftSchwartz_tsupport_orderedPositive
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) R) :
    tsupport
        ((osiiEuclideanCompensatedLeftSchwartz R hR φ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := n) R := by
  have hrot :
      tsupport
          ((osiiEuclideanRotateSchwartz R hR φ : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n :=
    osiiEuclideanRotateSchwartz_tsupport_orderedNegative R hR φ hφ
  have hreflect :
      tsupport
          ((((osiiEuclideanRotateSchwartz R hR φ).timeReflect) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR φ) hrot
  intro x hx
  rw [osiiEuclideanCompensatedLeftSchwartz,
    tsupport_osiiEuclideanUnrotateSchwartz] at hx
  exact hreflect hx

omit [NeZero d] in
/-- Diagonal spacetime translation preserves the honest zero-diagonal
Schwartz test space. The converse is included because a translation is
invertible and later E1 comparisons often discover vanishing only after an
auxiliary centering translation. -/
theorem VanishesToInfiniteOrderOnCoincidence.translateSchwartzNPoint_iff
    (a : SpacetimeDim d) (φ : SchwartzNPoint d n) :
    VanishesToInfiniteOrderOnCoincidence
        (translateSchwartzNPoint (d := d) a φ) ↔
      VanishesToInfiniteOrderOnCoincidence φ := by
  constructor
  · intro hφ r x hx
    let aN : NPointDomain d n := fun _ => a
    have hxadd : x + aN ∈ CoincidenceLocus d n := by
      rcases hx with ⟨i, j, hij, hEq⟩
      exact ⟨i, j, hij, by simp [aN, hEq]⟩
    have hzero := hφ r (x + aN) hxadd
    change
      iteratedFDeriv ℝ r
          (fun z : NPointDomain d n => φ (z - aN)) (x + aN) = 0 at hzero
    rw [iteratedFDeriv_comp_sub] at hzero
    simpa [aN] using hzero
  · intro hφ r x hx
    let aN : NPointDomain d n := fun _ => a
    have hxsub : x - aN ∈ CoincidenceLocus d n := by
      rcases hx with ⟨i, j, hij, hEq⟩
      exact ⟨i, j, hij, by simp [aN, hEq]⟩
    change
      iteratedFDeriv ℝ r
          (fun z : NPointDomain d n => φ (z - aN)) x = 0
    rw [iteratedFDeriv_comp_sub]
    exact hφ r (x - aN) hxsub

omit [NeZero d] in
theorem osiiEuclideanTranslation_preserves_orientedPositive
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a : SpacetimeDim d)
    (ha : 0 ≤ (R.mulVec a) 0)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n) R) :
    tsupport
        (((translateSchwartzNPoint (d := d) a φ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) ⊆
      osiiEuclideanRotationOrderedPositiveTimeRegion
        (d := d) (n := n) R := by
  intro x hx
  have hcontinuous :
      Continuous (fun y : NPointDomain d n => fun i => y i - a) := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub continuous_const
  have hxpre :
      (fun i => x i - a) ∈
        tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        hcontinuous hx
  have hrot := hφ hxpre
  intro i
  constructor
  · have hi := (hrot i).1
    have hi' : 0 < (R.mulVec (x i)) 0 - (R.mulVec a) 0 := by
      simpa [osiiEuclideanRotationOrderedPositiveTimeRegion,
        Matrix.mulVec_sub] using hi
    linarith
  · intro j hij
    have hij' := (hrot i).2 j hij
    have hij'' :
        (R.mulVec (x i)) 0 - (R.mulVec a) 0 <
          (R.mulVec (x j)) 0 - (R.mulVec a) 0 := by
      simpa [osiiEuclideanRotationOrderedPositiveTimeRegion,
        Matrix.mulVec_sub] using hij'
    linarith

omit [NeZero d] in
/-- An arbitrary spacetime translation with nonnegative time component
preserves ordinary ordered positive-time support. -/
theorem osiiEuclideanTranslation_preserves_orderedPositive
    (a : SpacetimeDim d) (ha : 0 ≤ a 0)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) :
    tsupport
        (((translateSchwartzNPoint (d := d) a φ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n := by
  have hφ' :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := n)
          (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
    intro x hx
    simpa [osiiEuclideanRotationOrderedPositiveTimeRegion] using hφ hx
  intro x hx
  have h :=
    osiiEuclideanTranslation_preserves_orientedPositive
      (d := d) (n := n)
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      a (by simpa using ha) φ hφ' hx
  simpa [osiiEuclideanRotationOrderedPositiveTimeRegion] using h

/-- The concentrated positive-time Borchers vector obtained from a source in
an `R`-oriented ordered cone. -/
noncomputable def osiiEuclideanRotatePositiveTimeSingle
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : SchwartzNPoint d n)
    (hφ :
      tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion (d := d) (n := n) R) :
    PositiveTimeBorchersSequence d :=
  PositiveTimeBorchersSequence.single n
    (osiiEuclideanRotateSchwartz R hR φ)
    (osiiEuclideanRotateSchwartz_tsupport_orderedPositive R hR φ hφ)

omit [NeZero d] in
private theorem osiiEuclideanRotateNPoint_mem_coincidence
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    {x : NPointDomain d n}
    (hx : x ∈ CoincidenceLocus d n) :
    osiiEuclideanRotateNPointCLE R hR x ∈ CoincidenceLocus d n := by
  rcases hx with ⟨i, j, hij, hEq⟩
  refine ⟨i, j, hij, ?_⟩
  change R.transpose.mulVec (x i) = R.transpose.mulVec (x j)
  rw [hEq]

/- Diagonal Euclidean rotations preserve infinite-order vanishing on every
coincidence diagonal. -/
omit [NeZero d] in
theorem VanishesToInfiniteOrderOnCoincidence.osiiEuclideanRotate
    {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {hR : R.transpose * R = 1}
    {φ : SchwartzNPoint d n}
    (hφ : VanishesToInfiniteOrderOnCoincidence φ) :
    VanishesToInfiniteOrderOnCoincidence
      (osiiEuclideanRotateSchwartz R hR φ) := by
  intro k x hx
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    osiiEuclideanRotateNPointCLE R hR
  have hcomp :
      iteratedFDeriv ℝ k
          ((osiiEuclideanRotateSchwartz R hR φ : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) x =
        (iteratedFDeriv ℝ k (φ : NPointDomain d n → ℂ) (e x)).compContinuousLinearMap
          (fun _ : Fin k => e.toContinuousLinearMap) := by
    simpa [e, osiiEuclideanRotateSchwartz] using
      e.toContinuousLinearMap.iteratedFDeriv_comp_right
        (f := (φ : NPointDomain d n → ℂ))
        ((φ : SchwartzNPoint d n).smooth k) (x := x) (i := k) le_rfl
  have hzero :
      iteratedFDeriv ℝ k (φ : NPointDomain d n → ℂ) (e x) = 0 := by
    exact hφ k (e x)
      (osiiEuclideanRotateNPoint_mem_coincidence R hR hx)
  rw [hcomp, hzero]
  ext u
  simp

/- Inverse rotation also preserves infinite-order vanishing on every
coincidence diagonal. -/
omit [NeZero d] in
theorem VanishesToInfiniteOrderOnCoincidence.osiiEuclideanUnrotate
    {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {hR : R.transpose * R = 1}
    {φ : SchwartzNPoint d n}
    (hφ : VanishesToInfiniteOrderOnCoincidence φ) :
    VanishesToInfiniteOrderOnCoincidence
      (osiiEuclideanUnrotateSchwartz R hR φ) := by
  exact
    VanishesToInfiniteOrderOnCoincidence.osiiEuclideanRotate
      (R := R.transpose) (hR := mul_eq_one_comm.mpr hR) hφ

/-- Rotation of an honest OS-I zero-diagonal test function. -/
noncomputable def osiiEuclideanRotateZeroDiagonal
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (φ : ZeroDiagonalSchwartz d n) :
    ZeroDiagonalSchwartz d n :=
  ⟨osiiEuclideanRotateSchwartz R hR φ.1,
    VanishesToInfiniteOrderOnCoincidence.osiiEuclideanRotate
      (R := R) (hR := hR) φ.2⟩

/-- The OS Schwinger functional is invariant under the packaged rotation. -/
theorem osiiEuclideanRotateZeroDiagonal_schwinger_eq
    (OS : OsterwalderSchraderAxioms d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (hdet : R.det = 1)
    (φ : ZeroDiagonalSchwartz d n) :
    OS.S n (osiiEuclideanRotateZeroDiagonal R hR φ) = OS.S n φ := by
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hRt : R.transpose.transpose * R.transpose = 1 := by
    simpa using hR'
  have hdett : R.transpose.det = 1 := by
    simpa [Matrix.det_transpose] using hdet
  symm
  refine OS.E1_rotation_invariant n R.transpose hRt hdett
    φ (osiiEuclideanRotateZeroDiagonal R hR φ) ?_
  intro x
  rfl

/-- E1 removes an inverse-rotation wrapper from any admissible Schwartz
source. This form is convenient when a positive-time semigroup first produces
a rotated real-edge source. -/
theorem osiiEuclideanUnrotateSchwartz_schwinger_eq
    (OS : OsterwalderSchraderAxioms d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (hdet : R.det = 1)
    (φ : SchwartzNPoint d n)
    (hφ : VanishesToInfiniteOrderOnCoincidence φ) :
    OS.S n (ZeroDiagonalSchwartz.ofClassical φ) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical
        (osiiEuclideanUnrotateSchwartz R hR φ)) := by
  have hunrotate :
      VanishesToInfiniteOrderOnCoincidence
        (osiiEuclideanUnrotateSchwartz R hR φ) :=
    VanishesToInfiniteOrderOnCoincidence.osiiEuclideanUnrotate hφ
  refine OS.E1_rotation_invariant n R hR hdet
    (ZeroDiagonalSchwartz.ofClassical φ)
    (ZeroDiagonalSchwartz.ofClassical
      (osiiEuclideanUnrotateSchwartz R hR φ)) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes (f := φ) hφ,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := osiiEuclideanUnrotateSchwartz R hR φ) hunrotate]
  rfl

/- Rotating a translated source translates the rotated source by `R a`. -/
omit [NeZero d] in
theorem osiiEuclideanRotateSchwartz_translate
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (a : SpacetimeDim d)
    (φ : SchwartzNPoint d n) :
    osiiEuclideanRotateSchwartz R hR
        (translateSchwartzNPoint (d := d) a φ) =
      translateSchwartzNPoint (d := d) (R.mulVec a)
        (osiiEuclideanRotateSchwartz R hR φ) := by
  ext x
  simp only [osiiEuclideanRotateSchwartz_apply, translateSchwartzNPoint_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR]
  simp

/- The transpose shift identity from the axis-pair rotation module also gives
the forward identity `R (T, ±e_j) = (sqrt (T^2 + 1), 0)`. -/
omit [NeZero d] in
theorem osiiAxisPairRotation_mulVec_dir
    {T : ℝ} {a : osiiAxisPairIndex d}
    {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR : R.transpose * R = 1)
    (hdir :
      R.transpose.mulVec (timeShiftVec d (osiiAxisPairRadius T)) =
        osiiAxisPairDir (d := d) T a) :
    R.mulVec (osiiAxisPairDir (d := d) T a) =
      timeShiftVec d (osiiAxisPairRadius T) := by
  rw [← hdir, Matrix.mulVec_mulVec]
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  rw [hR']
  simp

omit [NeZero d] in
theorem osiiAxisPairRotation_mulVec_smul_dir
    {T u : ℝ} {a : osiiAxisPairIndex d}
    {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR : R.transpose * R = 1)
    (hdir :
      R.transpose.mulVec (timeShiftVec d (osiiAxisPairRadius T)) =
        osiiAxisPairDir (d := d) T a) :
    R.mulVec (u • osiiAxisPairDir (d := d) T a) =
      timeShiftVec d (u * osiiAxisPairRadius T) := by
  rw [Matrix.mulVec_smul, osiiAxisPairRotation_mulVec_dir hR hdir]
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
  · simp [timeShiftVec, hμ]

end OSReconstruction
