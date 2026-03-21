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

@[simp] theorem prependField_onePointToFin1CLM_eq_productTensor
    (χ h : SchwartzSpacetime d) :
    χ.prependField (onePointToFin1CLM d h) = SchwartzMap.productTensor ![χ, h] := by
  ext x
  simp [SchwartzMap.prependField_apply, onePointToFin1CLM_apply,
    SchwartzMap.productTensor_apply]

@[simp] theorem twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift_eq_productTensor
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h) =
      SchwartzMap.productTensor ![χ, h] := by
  rw [twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift,
    prependField_onePointToFin1CLM_eq_productTensor]

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

private theorem reindex_flatten_twoPointProductShell_apply
    (χ g : SchwartzSpacetime d) (x : Fin ((d + 1) + (d + 1)) → ℝ) :
    reindexSchwartzFin (by ring)
        (flattenSchwartzNPoint (d := d)
          (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))) x =
      χ (splitFirst (d + 1) (d + 1) x) *
        g (splitFirst (d + 1) (d + 1) x + splitLast (d + 1) (d + 1) x) := by
  rw [reindex_flattenSchwartzNPoint_two_apply]
  let y : NPointDomain d 2 :=
    fun i =>
      Fin.cases (splitFirst (d + 1) (d + 1) x)
        (fun _ => splitLast (d + 1) (d + 1) x) i
  have h0 : y 0 = splitFirst (d + 1) (d + 1) x := by
    simp [y]
  have h1 : y 1 = splitLast (d + 1) (d + 1) x := by
    change Fin.cases (splitFirst (d + 1) (d + 1) x)
        (fun _ => splitLast (d + 1) (d + 1) x) (Fin.succ 0) =
      splitLast (d + 1) (d + 1) x
    rfl
  simpa [y, h0, h1] using
    twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply (d := d) χ g y

theorem reindex_flatten_twoPointProductLift_eq_tensorProduct
    (χ g : SchwartzSpacetime d) :
    reindexSchwartzFin (by ring)
        (flattenSchwartzNPoint (d := d) (twoPointProductLift χ g)) =
      χ.tensorProduct g := by
  ext x
  let y : NPointDomain d 2 :=
    fun i =>
      Fin.cases (splitFirst (d + 1) (d + 1) x)
        (fun _ => splitLast (d + 1) (d + 1) x) i
  have h0 : y 0 = splitFirst (d + 1) (d + 1) x := by
    simp [y]
  have h1 : y 1 = splitLast (d + 1) (d + 1) x := by
    change Fin.cases (splitFirst (d + 1) (d + 1) x)
        (fun _ => splitLast (d + 1) (d + 1) x) (Fin.succ 0) =
      splitLast (d + 1) (d + 1) x
    rfl
  rw [reindex_flattenSchwartzNPoint_two_apply, SchwartzMap.tensorProduct_apply]
  rw [twoPointProductLift_apply]
  simp [y, h0, h1]

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

/-- Two-point center descent commutes with subtraction. -/
theorem twoPointCenterDescent_sub
    (F G : SchwartzNPoint d 2) :
    twoPointCenterDescent (d := d) (F - G) =
      twoPointCenterDescent (d := d) F - twoPointCenterDescent (d := d) G := by
  simp [twoPointCenterDescent, integrateHeadBlock_sub]

/-- On the admissible two-point center/difference shell, center descent is
exactly repeated block integration of the tensor product `χ(u) h(ξ)` after the
correct center/difference rewrite. This isolates the remaining gap to a single
block-integration theorem, rather than more Wick-rotation bookkeeping. -/
theorem twoPointCenterDescent_twoPointDifferenceLift
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDescent (d := d) (twoPointDifferenceLift χ h) =
      integrateHeadBlock (m := d + 1) (n := d + 1) (χ.tensorProduct h) := by
  rw [twoPointCenterDescent, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift]
  simpa using
    congrArg (integrateHeadBlock (m := d + 1) (n := d + 1))
      (reindex_flatten_twoPointCenterShell (d := d) χ h)

/-- On the admissible two-point center/difference shell, integrating out the
full center block leaves exactly the difference-variable Schwartz test scaled
by the center integral. This is the blocker-facing form of two-point descent. -/
theorem twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDescent (d := d) (twoPointDifferenceLift χ h) =
      (∫ u : SpacetimeDim d, χ u) • h := by
  rw [twoPointCenterDescent_twoPointDifferenceLift]
  simpa [SchwartzMap.integralCLM_apply] using
    integrateHeadBlock_tensorProduct (m := d + 1) (n := d + 1) χ h

/-- The semigroup-side center-shear shell descends to a genuine difference
variable Schwartz test. This is the canonical admissible representative
associated to the product shell `(u, ξ) ↦ χ(u) g(u + ξ)`. -/
abbrev twoPointCenterShearDescent
    (χ g : SchwartzSpacetime d) : SchwartzSpacetime d :=
  twoPointCenterDescent (d := d) (twoPointProductLift χ g)

@[simp] theorem twoPointCenterShearDescent_eq
    (χ g : SchwartzSpacetime d) :
    twoPointCenterShearDescent (d := d) χ g =
      twoPointCenterDescent (d := d) (twoPointProductLift χ g) := rfl

/-- A normalized center cutoff gives a genuine section of two-point center
descent on the admissible shell. -/
theorem twoPointCenterDescent_twoPointDifferenceLift_eq_self
    (χ h : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1) :
    twoPointCenterDescent (d := d) (twoPointDifferenceLift χ h) = h := by
  simpa [hχ] using
    twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul (d := d) χ h

/-- For a normalized center cutoff, the semigroup-side center-shear shell and
its canonical admissible representative have the same descent. This isolates
the remaining `E -> R` two-point gap to proving that the relevant witness
depends only on the descended difference-variable Schwartz test. -/
theorem twoPointCenterDescent_twoPointProductLift_eq_differenceRepresentative
    (χ g : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1) :
    twoPointCenterDescent (d := d) (twoPointProductLift χ g) =
      twoPointCenterDescent (d := d)
        (twoPointDifferenceLift χ (twoPointCenterShearDescent (d := d) χ g)) := by
  rw [twoPointCenterShearDescent_eq]
  symm
  exact twoPointCenterDescent_twoPointDifferenceLift_eq_self
    (d := d) χ (twoPointCenterShearDescent (d := d) χ g) hχ

/-- The canonical residual between the semigroup/product shell and its
normalized admissible representative. The remaining two-point `E -> R` gap is
exactly to prove that the relevant witness annihilates this kernel element. -/
abbrev twoPointCenterShearResidual
    (χ g : SchwartzSpacetime d) : SchwartzNPoint d 2 :=
  twoPointProductLift χ g -
    twoPointDifferenceLift χ (twoPointCenterShearDescent (d := d) χ g)

@[simp] theorem twoPointCenterDiffSchwartzCLM_twoPointCenterShearResidual_apply
    (χ g : SchwartzSpacetime d) (x : NPointDomain d 2) :
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointCenterShearResidual (d := d) χ g) x =
      χ (x 0) * g (x 0 + x 1) -
        χ (x 0) * (twoPointCenterShearDescent (d := d) χ g) (x 1) := by
  rw [twoPointCenterShearResidual]
  change
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g) x -
      twoPointCenterDiffSchwartzCLM (d := d)
        (twoPointDifferenceLift χ (twoPointCenterShearDescent (d := d) χ g)) x =
      χ (x 0) * g (x 0 + x 1) -
        χ (x 0) * (twoPointCenterShearDescent (d := d) χ g) (x 1)
  rw [twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply]
  simp [twoPointCenterShearDescent_eq,
    twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift, SchwartzMap.prependField_apply,
    onePointToFin1CLM_apply]

/-- For a normalized center cutoff, the canonical center-shear residual lies in
the kernel of two-point center descent. -/
theorem twoPointCenterDescent_twoPointCenterShearResidual_eq_zero
    (χ g : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1) :
    twoPointCenterDescent (d := d) (twoPointCenterShearResidual (d := d) χ g) = 0 := by
  rw [twoPointCenterShearResidual, twoPointCenterDescent_sub]
  exact sub_eq_zero.2
    (twoPointCenterDescent_twoPointProductLift_eq_differenceRepresentative
      (d := d) χ g hχ)

/-- Translating the one-point test on the semigroup/product shell translates
the descended difference-variable representative by the same amount. This makes
`twoPointCenterShearDescent` behave like the expected convolution operator in
the difference variable. -/
theorem twoPointCenterShearDescent_translate_right
    (χ g : SchwartzSpacetime d) (a : SpacetimeDim d) :
    twoPointCenterShearDescent (d := d) χ (SCV.translateSchwartz a g) =
      SCV.translateSchwartz a (twoPointCenterShearDescent (d := d) χ g) := by
  let F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))
  let F' : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d)
          (twoPointProductLift χ (SCV.translateSchwartz a g))))
  have hF' :
      F' =
        SCV.translateSchwartz
          (zeroHeadBlockShift (m := d + 1) (n := d + 1) a) F := by
    ext x
    unfold F F'
    rw [reindex_flatten_twoPointProductShell_apply]
    have htranslate :
        (SCV.translateSchwartz
            (zeroHeadBlockShift (m := d + 1) (n := d + 1) a)
            (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))))) x =
          (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))))
            (x + zeroHeadBlockShift (m := d + 1) (n := d + 1) a) := by
      rfl
    rw [htranslate]
    have hshifted :=
      reindex_flatten_twoPointProductShell_apply (d := d) χ g
        (x + zeroHeadBlockShift (m := d + 1) (n := d + 1) a)
    simpa [splitFirst_zeroHeadBlockShift, splitLast_zeroHeadBlockShift, add_assoc] using
      hshifted.symm
  rw [twoPointCenterShearDescent_eq, twoPointCenterShearDescent_eq,
    twoPointCenterDescent, twoPointCenterDescent]
  change integrateHeadBlock (m := d + 1) (n := d + 1) F' =
    SCV.translateSchwartz a (integrateHeadBlock (m := d + 1) (n := d + 1) F)
  rw [hF']
  simpa using
    integrateHeadBlock_translateSchwartz_tail
      (m := d + 1) (n := d + 1) a F

/-- Translating the center cutoff on the raw product shell is equivalent, after
descent, to translating the right factor in the opposite direction. This is the
honest center-shear identity behind the product-shell mismatch in the `E -> R`
two-point reduction. -/
theorem twoPointCenterShearDescent_translate_left
    (χ g : SchwartzSpacetime d) (a : SpacetimeDim d) :
    twoPointCenterShearDescent (d := d) (SCV.translateSchwartz a χ) g =
      twoPointCenterShearDescent (d := d) χ (SCV.translateSchwartz (-a) g) := by
  let F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d)
          (twoPointProductLift χ (SCV.translateSchwartz (-a) g))))
  let F' : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d)
          (twoPointProductLift (SCV.translateSchwartz a χ) g)))
  have hF' :
      F' =
        SCV.translateSchwartz
          (zeroTailBlockShift (m := d + 1) (n := d + 1) a) F := by
    ext x
    unfold F F'
    have htranslate :
        (SCV.translateSchwartz
            (zeroTailBlockShift (m := d + 1) (n := d + 1) a)
            (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift χ (SCV.translateSchwartz (-a) g)))))) x =
          (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ (SCV.translateSchwartz (-a) g)))))
            (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a) := by
      rfl
    rw [htranslate]
    have hshifted :=
      reindex_flatten_twoPointProductShell_apply (d := d) χ
        (SCV.translateSchwartz (-a) g)
        (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a)
    have hleft :
        (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (SCV.translateSchwartz a χ) g)))) x =
          χ (splitFirst (d + 1) (d + 1) x + a) *
            g (splitFirst (d + 1) (d + 1) x + splitLast (d + 1) (d + 1) x) := by
      rw [reindex_flatten_twoPointProductShell_apply]
      simp [SCV.translateSchwartz_apply]
    have hright :
        (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ (SCV.translateSchwartz (-a) g)))))
            (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a) =
          χ (splitFirst (d + 1) (d + 1) x + a) *
            g (splitFirst (d + 1) (d + 1) x + splitLast (d + 1) (d + 1) x) := by
      calc
        (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ (SCV.translateSchwartz (-a) g)))))
            (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a)
          = χ
              (splitFirst (d + 1) (d + 1)
                (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a)) *
              (SCV.translateSchwartz (-a) g)
                (splitFirst (d + 1) (d + 1)
                    (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a) +
                  splitLast (d + 1) (d + 1)
                    (x + zeroTailBlockShift (m := d + 1) (n := d + 1) a)) := by
                exact hshifted
        _ = χ (splitFirst (d + 1) (d + 1) x + a) *
              g (splitFirst (d + 1) (d + 1) x + splitLast (d + 1) (d + 1) x) := by
                rw [splitFirst_zeroTailBlockShift, splitLast_zeroTailBlockShift]
                rw [SCV.translateSchwartz_apply]
                have hg :
                    g
                        ((splitFirst (d + 1) (d + 1) x + a +
                            splitLast (d + 1) (d + 1) x) +
                          -a) =
                      g
                        (splitFirst (d + 1) (d + 1) x +
                          splitLast (d + 1) (d + 1) x) := by
                  congr 1
                  ext i
                  simp
                  abel_nf
                rw [hg]
    exact hleft.trans hright.symm
  have hInt :=
    congrArg (integrateHeadBlock (m := d + 1) (n := d + 1)) hF'
  rw [integrateHeadBlock_translateSchwartz_head
      (m := d + 1) (n := d + 1) a F] at hInt
  simpa [twoPointCenterShearDescent_eq, twoPointCenterDescent, F, F'] using hInt

/-- Translating the center cutoff acts on the descended center-shear parameter
by the opposite translation in the difference variable. This is the practical
covariance form of the product-shell shear identity. -/
theorem twoPointCenterShearDescent_translate_center
    (χ g : SchwartzSpacetime d) (a : SpacetimeDim d) :
    twoPointCenterShearDescent (d := d) (SCV.translateSchwartz a χ) g =
      SCV.translateSchwartz (-a) (twoPointCenterShearDescent (d := d) χ g) := by
  rw [twoPointCenterShearDescent_translate_left]
  simpa using
    twoPointCenterShearDescent_translate_right
      (d := d) χ g (-a)

/-- Simultaneously translating the center cutoff and right factor by the same
spatial vector leaves the descended center-shear representative unchanged. This
is the descended counterpart of center-spatial translation invariance of the
raw product shell. -/
theorem twoPointCenterShearDescent_translate_both
    (χ g : SchwartzSpacetime d) (a : SpacetimeDim d) :
    twoPointCenterShearDescent (d := d)
      (SCV.translateSchwartz a χ) (SCV.translateSchwartz a g) =
      twoPointCenterShearDescent (d := d) χ g := by
  rw [twoPointCenterShearDescent_translate_left]
  have htrans :
      SCV.translateSchwartz (-a) (SCV.translateSchwartz a g) = g := by
    ext x
    simp [SCV.translateSchwartz_apply]
  simpa [htrans]

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

/-- The raw two-point product shell has the expected total integral: it is the
product of the center and right-factor integrals. This is the unsheared
sanity check behind the descended center-shear averaging operator. -/
theorem integral_twoPointProductLift_eq_mul
    (χ g : SchwartzSpacetime d) :
    ∫ x : NPointDomain d 2, twoPointProductLift χ g x =
      (∫ u : SpacetimeDim d, χ u) * ∫ v : SpacetimeDim d, g v := by
  calc
    ∫ x : NPointDomain d 2, twoPointProductLift χ g x
      =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume :
            MeasureTheory.Measure (Fin ((d + 1) + (d + 1)) → ℝ)))
          (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d) (twoPointProductLift χ g))) := by
          rw [integral_reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d) (twoPointProductLift χ g))]
          exact (integral_flattenSchwartzNPoint (d := d) (twoPointProductLift χ g)).symm
    _ =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume :
            MeasureTheory.Measure (Fin ((d + 1) + (d + 1)) → ℝ)))
          (χ.tensorProduct g) := by
            rw [reindex_flatten_twoPointProductLift_eq_tensorProduct]
    _ =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
          (integrateHeadBlock (m := d + 1) (n := d + 1) (χ.tensorProduct g)) := by
            simpa [SchwartzMap.integralCLM_apply] using
              (integral_integrateHeadBlock (m := d + 1) (n := d + 1)
                (χ.tensorProduct g)).symm
    _ =
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
          (((SchwartzMap.integralCLM ℂ
              (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))) χ) • g) := by
            rw [integrateHeadBlock_tensorProduct (m := d + 1) (n := d + 1) χ g]
    _ = (∫ u : SpacetimeDim d, χ u) * ∫ v : SpacetimeDim d, g v := by
          simp [SchwartzMap.integralCLM_apply, smul_eq_mul]

/-- The descended center-shear representative preserves the total integral of
the raw product shell, hence its total mass is the product of the center and
right-factor integrals. This is the first concrete sign that
`twoPointCenterShearDescent` is behaving like a genuine averaging operator in
the difference variable. -/
theorem integral_twoPointCenterShearDescent_eq_mul
    (χ g : SchwartzSpacetime d) :
    ∫ ξ : SpacetimeDim d, twoPointCenterShearDescent (d := d) χ g ξ =
      (∫ u : SpacetimeDim d, χ u) * ∫ v : SpacetimeDim d, g v := by
  rw [twoPointCenterShearDescent_eq]
  calc
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
        (twoPointCenterDescent (d := d) (twoPointProductLift χ g))
      =
        ∫ x : NPointDomain d 2, twoPointProductLift χ g x := by
          exact integral_twoPointCenterDescent (d := d) (twoPointProductLift χ g)
    _ = (∫ u : SpacetimeDim d, χ u) * ∫ v : SpacetimeDim d, g v := by
          exact integral_twoPointProductLift_eq_mul (d := d) χ g

end OSReconstruction
