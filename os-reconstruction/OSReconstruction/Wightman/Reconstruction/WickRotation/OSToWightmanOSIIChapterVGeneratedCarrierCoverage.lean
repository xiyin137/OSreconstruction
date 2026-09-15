/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedContinuationChain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedLogarithmicDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51CoordinateEstimate


















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Adding a nonnegative real number to a point of the right half-plane can
only decrease the absolute principal argument. -/
theorem abs_arg_add_ofReal_le
    {z : ℂ} (hz : 0 < z.re)
    {t : ℝ} (ht : 0 ≤ t) :
    |Complex.arg (z + t)| ≤ |Complex.arg z| := by
  have hzt : 0 < (z + t).re := by
    simpa using add_pos_of_pos_of_nonneg hz ht
  rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hzt,
    osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hz]
  apply Real.arctan_mono
  simp only [Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero, abs_div]
  have hden : 0 < z.re + t := by linarith
  rw [abs_of_pos hden, abs_of_pos hz]
  exact
    div_le_div_of_nonneg_left
      (abs_nonneg z.im) hz (by linarith)

/-- The scalar-stage point obtained from a reflected Hilbert Cauchy center
after translating by one real cutoff parameter. -/
def reflectedCauchyShiftedStagePoint
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ) :
    Fin (m + (m + 1)) → ℂ :=
  -(reflectedReducedTimeDisplacementCLM m
      (reflectedCauchyCenter z)) +
    osiiPositiveRealTimeEmbed τ

@[simp]
theorem reflectedCauchyShiftedStagePoint_left
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (i : Fin m) :
    reflectedCauchyShiftedStagePoint τ z
        (Fin.castAdd (m + 1) i) =
      starRingEnd ℂ (z (Fin.rev i)) +
        τ (Fin.castAdd (m + 1) i) := by
  simp [reflectedCauchyShiftedStagePoint,
    reflectedReducedTimeDisplacementCLM_apply,
    osiiPositiveRealTimeEmbed]

@[simp]
theorem reflectedCauchyShiftedStagePoint_bridge
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ) :
    reflectedCauchyShiftedStagePoint τ z
        (Fin.natAdd m (0 : Fin (m + 1))) =
      τ (Fin.natAdd m (0 : Fin (m + 1))) := by
  simp [reflectedCauchyShiftedStagePoint,
    reflectedReducedTimeDisplacementCLM_apply,
    osiiPositiveRealTimeEmbed]

@[simp]
theorem reflectedCauchyShiftedStagePoint_right
    {m : ℕ}
    (τ : Fin (m + (m + 1)) → ℝ)
    (z : Fin m → ℂ)
    (i : Fin m) :
    reflectedCauchyShiftedStagePoint τ z
        (Fin.natAdd m i.succ) =
      z i + τ (Fin.natAdd m i.succ) := by
  rw [reflectedCauchyShiftedStagePoint]
  simp only [Pi.add_apply, Pi.neg_apply,
    reflectedReducedTimeDisplacementCLM_apply,
    reflectedReducedTimeDisplacement_right, neg_neg,
    osiiPositiveRealTimeEmbed]
  rw [reflectedCauchyCenter_right]

/-- The mixed logarithmic argument attached to one Hilbert point, including
the distinguished leading zero. -/
def reflectedMixedArgument
    {m : ℕ} (z : Fin m → ℂ) :
    Fin (m + 1) → ℝ :=
  Fin.cons 0 (osiiTimeArgumentVector z)

/-- The reflected scalar diagonal associated to a Hilbert point, reindexed
to the scalar stage's `m + (m + 1)` coordinates. -/
def reflectedMixedDiagonal
    {m : ℕ} (z : Fin m → ℂ) :
    Fin (m + (m + 1)) → ℝ :=
  fun j =>
    osiiArgumentDiagonal (n := m + 1) (by omega)
      (reflectedMixedArgument z)
      ((finCongr (by omega :
        2 * (m + 1) - 1 = m + (m + 1))).symm j)

@[simp]
theorem reflectedMixedDiagonal_left
    {m : ℕ}
    (z : Fin m → ℂ)
    (i : Fin m) :
    reflectedMixedDiagonal z (Fin.castAdd (m + 1) i) =
      -Complex.arg (z (Fin.rev i)) := by
  simp [reflectedMixedDiagonal, osiiArgumentDiagonal,
    reflectedMixedArgument]
  have hidx :
      (⟨m - i.val, by omega⟩ : Fin (m + 1)) =
        (Fin.rev i).succ := by
    apply Fin.ext
    simp
    omega
  rw [hidx]
  rfl

@[simp]
theorem reflectedMixedDiagonal_bridge
    {m : ℕ}
    (z : Fin m → ℂ) :
    reflectedMixedDiagonal z
        (Fin.natAdd m (0 : Fin (m + 1))) =
      0 := by
  simp [reflectedMixedDiagonal, osiiArgumentDiagonal,
    reflectedMixedArgument]

@[simp]
theorem reflectedMixedDiagonal_right
    {m : ℕ}
    (z : Fin m → ℂ)
    (i : Fin m) :
    reflectedMixedDiagonal z (Fin.natAdd m i.succ) =
      Complex.arg (z i) := by
  simp [reflectedMixedDiagonal, osiiArgumentDiagonal,
    reflectedMixedArgument]
  have hidx :
      (⟨i.val + 1, by omega⟩ : Fin (m + 1)) =
        i.succ := by
    apply Fin.ext
    rfl
  rw [hidx]
  rfl

/-- Strict positivity of the cutoff parameter and the original Hilbert point
places the shifted reflected center in the scalar product right half-plane. -/
theorem reflectedCauchyShiftedStagePoint_mem_rightHalfPlane
    {m : ℕ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    (hτ :
      τ ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    (hz : z ∈ osiiTimeRightHalfPlane m) :
    reflectedCauchyShiftedStagePoint τ z ∈
      osiiTimeRightHalfPlane (m + (m + 1)) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedCauchyShiftedStagePoint_left]
    simpa using add_pos (hz (Fin.rev i))
      (hτ (Fin.castAdd (m + 1) i))
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedCauchyShiftedStagePoint_bridge]
      simpa using hτ (Fin.natAdd m (0 : Fin (m + 1)))
    · rw [reflectedCauchyShiftedStagePoint_right]
      simpa using add_pos (hz i) (hτ (Fin.natAdd m i.succ))

theorem abs_arg_conj_eq_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    |Complex.arg (starRingEnd ℂ z)| = |Complex.arg z| := by
  rw [Complex.arg_conj, if_neg]
  · exact abs_neg _
  · intro hpi
    have hneg := (Complex.arg_eq_pi_iff.mp hpi).1
    linarith

/-- The argument vector of the shifted reflected center is coordinatewise
bounded by the target's reflected mixed diagonal. -/
theorem abs_argumentVector_reflectedCauchyShiftedStagePoint_le
    {m : ℕ}
    {τ : Fin (m + (m + 1)) → ℝ}
    {z : Fin m → ℂ}
    (hτ :
      τ ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    (hz : z ∈ osiiTimeRightHalfPlane m) :
    ∀ j,
      |osiiTimeArgumentVector
          (reflectedCauchyShiftedStagePoint τ z) j| ≤
        |reflectedMixedDiagonal z j| := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedMixedDiagonal_left]
    simp only [osiiTimeArgumentVector,
      reflectedCauchyShiftedStagePoint_left, abs_neg]
    calc
      |Complex.arg
          (starRingEnd ℂ (z (Fin.rev i)) +
            τ (Fin.castAdd (m + 1) i))| ≤
          |Complex.arg (starRingEnd ℂ (z (Fin.rev i)))| :=
        abs_arg_add_ofReal_le
          (by simpa using hz (Fin.rev i))
          (hτ (Fin.castAdd (m + 1) i)).le
      _ = |Complex.arg (z (Fin.rev i))| :=
        abs_arg_conj_eq_of_re_pos (hz (Fin.rev i))
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [reflectedMixedDiagonal_bridge]
      simp only [osiiTimeArgumentVector,
        reflectedCauchyShiftedStagePoint_bridge, abs_zero]
      rw [Complex.arg_ofReal_of_nonneg
        (hτ (Fin.natAdd m (0 : Fin (m + 1)))).le]
      simp
    · rw [reflectedMixedDiagonal_right]
      simp only [osiiTimeArgumentVector,
        reflectedCauchyShiftedStagePoint_right]
      exact
        abs_arg_add_ofReal_le
          (hz i) (hτ (Fin.natAdd m i.succ)).le

private theorem generatedLogarithmicArgument_reindex
    {kind : OSIILogarithmicArgumentKind}
    {n n' N : ℕ}
    (h : n = n')
    {x : Fin n → ℝ}
    (hx :
      OSIIGeneratedLogarithmicArgument kind n N x) :
    OSIIGeneratedLogarithmicArgument kind n' N
      (fun j => x ((finCongr h).symm j)) := by
  subst n'
  simpa using hx

/-- A generated mixed Hilbert argument supplies its full reflected scalar
diagonal at the same induction depth. -/
theorem reflectedMixedDiagonal_generated
    {m N : ℕ}
    {z : Fin m → ℂ}
    (hz :
      reflectedMixedArgument z ∈
        osiiGeneratedMixedLogarithmicBase (m + 1) N) :
    OSIIGeneratedLogarithmicArgument .scalar
      (m + (m + 1)) N (reflectedMixedDiagonal z) := by
  have hdiag :=
    OSIIGeneratedLogarithmicArgument.mixed_diagonal_mem_scalar
      (n := m + 1) (by omega) hz
  have hreindexed :=
    generatedLogarithmicArgument_reindex
      (by omega :
        2 * (m + 1) - 1 = m + (m + 1))
      hdiag
  exact hreindexed

/-- Scalar realization of the generated base places the reflected Cauchy
endpoint of every generated mixed point in the moving-slice carrier. -/
theorem reflectedCauchyCenter_mem_reflectedMovingSliceCarrier_of_generated
    {d m N : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (η : SchwartzMap (Fin (m + (m + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η : (Fin (m + (m + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase (m + (m + 1)) N) ⊆
        A.carrier)
    {z : Fin m → ℂ}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase (m + 1) N)) :
    reflectedCauchyCenter z ∈
      reflectedMovingSliceCarrier A η := by
  intro τ hτ
  change reflectedCauchyShiftedStagePoint τ z ∈ A.carrier
  apply hgenerated
  have hτpos := hη_support hτ
  refine
    ⟨reflectedCauchyShiftedStagePoint_mem_rightHalfPlane
        hτpos hz.1,
      ?_⟩
  apply
    OSIIGeneratedLogarithmicArgument.scalar_hyperrectangle
      (reflectedMixedDiagonal_generated
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_reflectedCauchyShiftedStagePoint_le
      hτpos hz.1

/-- The same scalar realization places the radial basepoint in the reflected
moving-slice carrier. -/
theorem zero_mem_reflectedMovingSliceCarrier_of_generated
    {d m N : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (η : SchwartzMap (Fin (m + (m + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η : (Fin (m + (m + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase (m + (m + 1)) N) ⊆
        A.carrier) :
    (0 : Fin (m + m) → ℂ) ∈
      reflectedMovingSliceCarrier A η := by
  apply
    zero_mem_reflectedMovingSliceCarrier A η
      (section43TimeStrictPositiveRegion (m + (m + 1)))
      hη_support
  intro τ hτ
  apply hgenerated
  refine
    ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff τ).2 hτ,
      ?_⟩
  have harg :
      osiiTimeArgumentVector (osiiPositiveRealTimeEmbed τ) =
        (0 : Fin (m + (m + 1)) → ℝ) := by
    funext j
    rw [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
      Complex.arg_ofReal_of_nonneg (hτ j).le]
    rfl
  rw [harg]
  exact
    OSIIGeneratedLogarithmicArgument.scalar_zero_mem
      (m + (m + 1)) N

/-- The reflected Cauchy-center map preserves real radial line maps. -/
theorem reflectedCauchyCenter_lineMap_zero
    {m : ℕ}
    (z : Fin m → ℂ)
    (t : ℝ) :
    reflectedCauchyCenter
        (AffineMap.lineMap (k := ℝ)
          (0 : Fin m → ℂ) z t) =
      AffineMap.lineMap (k := ℝ)
        (0 : Fin (m + m) → ℂ)
        (reflectedCauchyCenter z) t := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [AffineMap.lineMap_apply_module, Pi.zero_apply,
      Pi.smul_apply, Pi.add_apply, smul_zero, zero_add]
    rw [reflectedCauchyCenter_left]
    simp
  · intro i
    simp only [AffineMap.lineMap_apply_module, Pi.zero_apply,
      Pi.smul_apply, Pi.add_apply, smul_zero, zero_add]
    rw [reflectedCauchyCenter_right, reflectedCauchyCenter_right]
    simp

/-- Generated-base realization fills the complete reflected radial segment
required by finite Cauchy continuation. No convexity of the ambient stage
carrier is needed: every nonzero radial point has the same principal
arguments as the target. -/
theorem reflected_segment_subset_reflectedMovingSliceCarrier_of_generated
    {d m N : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (η : SchwartzMap (Fin (m + (m + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η : (Fin (m + (m + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase (m + (m + 1)) N) ⊆
        A.carrier)
    {z : Fin m → ℂ}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase (m + 1) N)) :
    ∀ center ∈ segment ℝ (0 : Fin m → ℂ) z,
      reflectedCauchyCenter center ∈
        reflectedMovingSliceCarrier A η := by
  intro center hcenter
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter
  by_cases ht0 : t = 0
  · subst t
    have hzero :
        reflectedCauchyCenter (0 : Fin m → ℂ) =
          (0 : Fin (m + m) → ℂ) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp
      · rw [reflectedCauchyCenter_right]
        rfl
    rw [AffineMap.lineMap_apply_zero, hzero]
    exact
      zero_mem_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated
  · apply
      reflectedCauchyCenter_mem_reflectedMovingSliceCarrier_of_generated
        A η hη_support hgenerated
    simpa [AffineMap.lineMap_apply_module] using
      real_smul_mem_osiiMixedTailArgumentCarrier_of_pos
        hz (lt_of_le_of_ne ht.1 (Ne.symm ht0))

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q N : ℕ} [NeZero d]

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
