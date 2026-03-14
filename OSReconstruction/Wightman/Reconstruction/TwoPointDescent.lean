import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.BlockIntegral

/-!
# Two-Point Center Descent

This file packages the basic center-variable descent map for two-point
Schwartz tests. In center/difference coordinates `(u, xi)`, the descent
integrates out the center block `u` and produces a Schwartz test in the
difference variable `xi`.

The intended downstream use is the `E -> R` two-point continuation blocker,
where the remaining missing input is exactly a comparison between the
semigroup-side center-shear shell and the admissible center/difference shell.
-/

noncomputable section

open scoped SchwartzMap

namespace OSReconstruction

variable {d : ℕ}

/-- Rewrite a two-point Schwartz test in center/difference coordinates. -/
abbrev twoPointCenterDiffSchwartzCLM :
    SchwartzNPoint d 2 →L[ℂ] SchwartzNPoint d 2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d)

@[simp] theorem twoPointCenterDiffSchwartzCLM_apply
    (F : SchwartzNPoint d 2) (x : NPointDomain d 2) :
    twoPointCenterDiffSchwartzCLM (d := d) F x = F ((twoPointCenterDiffCLE d) x) := rfl

@[simp] theorem twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h) =
      χ.prependField (onePointToFin1CLM d h) := by
  ext x
  simp [twoPointDifferenceLift, SchwartzMap.prependField_apply]

@[simp] theorem twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply
    (χ g : SchwartzSpacetime d) (x : NPointDomain d 2) :
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g) x =
      χ (x 0) * g (x 0 + x 1) := by
  simp [twoPointCenterDiffSchwartzCLM, twoPointProductLift_apply,
    twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

private theorem reindex_flatten_twoPointCenterShell
    (χ h : SchwartzSpacetime d) :
    reindexSchwartzFin (by ring)
        (flattenSchwartzNPoint (d := d)
          (χ.prependField (onePointToFin1CLM d h))) =
      χ.tensorProduct h := by
  ext x
  simpa [SchwartzMap.tensorProduct_apply, SchwartzMap.prependField_apply,
      onePointToFin1CLM_apply] using
    reindex_flattenSchwartzNPoint_two_apply
      (d := d) (f := χ.prependField (onePointToFin1CLM d h)) x

/-- The basic two-point center descent map: rewrite in center/difference
coordinates, flatten to ordinary Euclidean Schwartz space, and integrate out
the full center block of `d + 1` real coordinates. -/
noncomputable def twoPointCenterDescent
    (F : SchwartzNPoint d 2) : SchwartzSpacetime d := by
  let Fcd : SchwartzNPoint d 2 := twoPointCenterDiffSchwartzCLM (d := d) F
  let Fflat : SchwartzMap (Fin (2 * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) Fcd
  let Fflat' : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring) Fflat
  exact integrateHeadBlock (m := d + 1) (n := d + 1) Fflat'

/-- On the admissible two-point center/difference shell, center descent is
exactly repeated block integration of the tensor product `χ(u) h(ξ)` after the
correct center/difference rewrite. This isolates the remaining gap to a single
block-integration theorem, rather than more Wick-rotation bookkeeping. -/
theorem twoPointCenterDescent_twoPointDifferenceLift
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDescent (d := d) (twoPointDifferenceLift χ h) =
      integrateHeadBlock (m := d + 1) (n := d + 1) (χ.tensorProduct h) := by
  simp [twoPointCenterDescent, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift,
    reindex_flatten_twoPointCenterShell]

private theorem integral_twoPointCenterDiffSchwartz
    (F : SchwartzNPoint d 2) :
    ∫ x : NPointDomain d 2, twoPointCenterDiffSchwartzCLM (d := d) F x =
      ∫ x : NPointDomain d 2, F x := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have he :
      MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
    simpa [e] using twoPointCenterDiff_measurePreserving (d := d)
  rw [show (fun x : NPointDomain d 2 => twoPointCenterDiffSchwartzCLM (d := d) F x) =
      (fun x : NPointDomain d 2 => F (e x)) by
        funext x
        simp [twoPointCenterDiffSchwartzCLM, e]]
  simpa [e] using (he.integral_comp' (f := e) (g := fun x : NPointDomain d 2 => F x))

/-- Total integration is preserved by two-point center descent. This is the
basic consistency check: integrating first over the center block and then over
the difference block recovers the original two-point integral. -/
theorem integral_twoPointCenterDescent
    (F : SchwartzNPoint d 2) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
        (twoPointCenterDescent (d := d) F)
      =
    ∫ x : NPointDomain d 2, F x := by
  let Fcd : SchwartzNPoint d 2 := twoPointCenterDiffSchwartzCLM (d := d) F
  let Fflat : SchwartzMap (Fin (2 * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) Fcd
  let Fflat' : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring) Fflat
  calc
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
        (twoPointCenterDescent (d := d) F)
      =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (Fin ((d + 1) + (d + 1)) → ℝ)))
            Fflat' := by
              simpa [twoPointCenterDescent, Fcd, Fflat, Fflat']
                using integral_integrateHeadBlock (m := d + 1) (n := d + 1) Fflat'
    _ =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (Fin (2 * (d + 1)) → ℝ)))
            Fflat := by
              simpa [Fflat'] using integral_reindexSchwartzFin (by ring) Fflat
    _ = ∫ x : NPointDomain d 2, Fcd x := integral_flattenSchwartzNPoint (d := d) Fcd
    _ = ∫ x : NPointDomain d 2, F x := integral_twoPointCenterDiffSchwartz (d := d) F

end OSReconstruction
