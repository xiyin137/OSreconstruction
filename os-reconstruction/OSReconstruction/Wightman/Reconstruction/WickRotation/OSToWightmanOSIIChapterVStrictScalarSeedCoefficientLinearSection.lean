import Mathlib.Analysis.Normed.Module.ContinuousInverse
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientFullRank

/-!
# Target-adapted linear sections of strict coefficient charts

A full-rank strict-seed coefficient map is a surjective continuous
complex-linear map between finite-dimensional spaces. An arbitrary right
inverse need not return a prescribed coefficient representative of one
target. This file corrects a chosen right inverse by a rank-one kernel-valued
map so that it fixes both zero and the selected target.

The only obstruction occurs when a nonzero coefficient vector represents the
zero ambient target. The section-regular presentation theorem in the
full-rank module excludes exactly that case.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The finite strict-seed coefficient map as a continuous complex-linear
map. -/
noncomputable def osiiStrictScalarSeedCoefficientCLM
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real) :
    (Fin n -> Complex) →L[Complex] (Fin k -> Complex) :=
  LinearMap.toContinuousLinearMap
    (Fintype.linearCombination Complex
      (fun i j => (seed i j : Complex)))

@[simp]
theorem osiiStrictScalarSeedCoefficientCLM_apply
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real)
    (r : Fin n -> Complex) :
    osiiStrictScalarSeedCoefficientCLM seed r =
      osiiStrictScalarSeedCoefficientMap seed r := by
  funext j
  simp [osiiStrictScalarSeedCoefficientCLM,
    osiiStrictScalarSeedCoefficientMap,
    Fintype.linearCombination_apply]

/-- A continuous linear right inverse which also sends the represented
ambient target back to the prescribed coefficient target. -/
structure StrictCoefficientTargetSectionData
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real)
    (r0 : Fin n -> Complex) where
  lift :
    (Fin k -> Complex) →L[Complex] (Fin n -> Complex)
  rightInverse :
    forall z,
      osiiStrictScalarSeedCoefficientCLM seed (lift z) = z
  target :
    lift (osiiStrictScalarSeedCoefficientCLM seed r0) = r0

/-- A surjective coefficient map admits a target-adapted continuous linear
section whenever the chosen coefficient target is zero or represents a
nonzero ambient target. -/
theorem nonempty_strictCoefficientTargetSectionData
    {n k : Nat}
    (seed : Fin n -> Fin k -> Real)
    (r0 : Fin n -> Complex)
    (hsurj :
      Function.Surjective
        (osiiStrictScalarSeedCoefficientMap seed))
    (htarget :
      r0 = 0 ∨
        osiiStrictScalarSeedCoefficientMap seed r0 ≠ 0) :
    Nonempty
      (StrictCoefficientTargetSectionData seed r0) := by
  let L := osiiStrictScalarSeedCoefficientCLM seed
  have hLsurj : Function.Surjective L := by
    intro z
    obtain ⟨r, hr⟩ := hsurj z
    exact ⟨r, by simpa [L] using hr⟩
  let split :
      ContinuousLinearMap.HasRightInverse L :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
      hLsurj
  let g0 := split.rightInverse
  have hg0 : forall z, L (g0 z) = z :=
    split.rightInverse_rightInverse
  rcases htarget with hr0 | hz0
  · subst r0
    exact
      ⟨{
        lift := g0
        rightInverse := by
          intro z
          exact hg0 z
        target := by
          change g0 (L 0) = 0
          simp }⟩
  · let z0 := L r0
    have hz0' : z0 ≠ 0 := by
      simpa [z0, L] using hz0
    obtain ⟨j, hj⟩ : ∃ j, z0 j ≠ 0 := by
      by_contra h
      push Not at h
      apply hz0'
      funext i
      exact h i
    let phi : (Fin k -> Complex) →L[Complex] Complex :=
      (z0 j)⁻¹ •
        (ContinuousLinearMap.proj
          (R := Complex) (ι := Fin k)
          (φ := fun _ => Complex) j)
    have hphi : phi z0 = 1 := by
      simp [phi, hj]
    let h : Fin n -> Complex := r0 - g0 z0
    have hker : L h = 0 := by
      rw [show h = r0 - g0 z0 by rfl, map_sub, hg0]
      exact sub_self z0
    let lift :
        (Fin k -> Complex) →L[Complex] (Fin n -> Complex) :=
      g0 + ContinuousLinearMap.smulRight phi h
    refine
      ⟨{
        lift := lift
        rightInverse := ?_
        target := ?_ }⟩
    · intro z
      change L (lift z) = z
      calc
        L (lift z) =
            L (g0 z + phi z • h) := by rfl
        _ = L (g0 z) + phi z • L h := by
          rw [map_add, map_smul]
        _ = z := by rw [hg0, hker, smul_zero, add_zero]
    · change lift (L r0) = r0
      calc
        lift (L r0) =
            g0 z0 + phi z0 • h := by rfl
        _ = g0 z0 + h := by rw [hphi, one_smul]
        _ = r0 := by simp [h]

end OSIIChapterV
end OSReconstruction
