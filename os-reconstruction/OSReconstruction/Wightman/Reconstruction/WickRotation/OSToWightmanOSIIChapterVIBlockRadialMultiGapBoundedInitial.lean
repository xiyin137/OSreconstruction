/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedGerm
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientBoundedChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarTargetSuccessor















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

/-- A fixed enumeration of all chronological-gap/axis-pair coordinates. -/
noncomputable def osiiAxisPairMultiGapFinEquiv
    (d k : Nat) :
    osiiAxisPairMultiGapIndex d k ≃
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) :=
  Fintype.equivFin _

/-- Reindex nested multi-gap coordinates by one ordinary finite type. -/
def osiiAxisPairMultiGapFinFlatten
    {d k : Nat} {alpha : Type*}
    (z : Fin k -> osiiAxisPairIndex d -> alpha) :
    Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> alpha :=
  fun j =>
    let q := (osiiAxisPairMultiGapFinEquiv d k).symm j
    z q.1 q.2

/-- Undo `osiiAxisPairMultiGapFinFlatten`. -/
def osiiAxisPairMultiGapFinUnflatten
    {d k : Nat} {alpha : Type*}
    (z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> alpha) :
    Fin k -> osiiAxisPairIndex d -> alpha :=
  fun i a => z (osiiAxisPairMultiGapFinEquiv d k (i, a))

@[simp] theorem osiiAxisPairMultiGapFinUnflatten_flatten
    {d k : Nat} {alpha : Type*}
    (z : Fin k -> osiiAxisPairIndex d -> alpha) :
    osiiAxisPairMultiGapFinUnflatten
        (osiiAxisPairMultiGapFinFlatten z) = z := by
  funext i a
  simp [osiiAxisPairMultiGapFinUnflatten,
    osiiAxisPairMultiGapFinFlatten]

@[simp] theorem osiiAxisPairMultiGapFinFlatten_unflatten
    {d k : Nat} {alpha : Type*}
    (z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> alpha) :
    osiiAxisPairMultiGapFinFlatten
        (osiiAxisPairMultiGapFinUnflatten z) = z := by
  funext j
  simp [osiiAxisPairMultiGapFinUnflatten,
    osiiAxisPairMultiGapFinFlatten]

/-- Complex-linear finite reindexing of the complete multi-gap family. -/
noncomputable def osiiAxisPairMultiGapFinFlattenCLE
    {d k : Nat} :
    (Fin k -> osiiAxisPairIndex d -> Complex) ≃L[Complex]
      (Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact
    { toFun := osiiAxisPairMultiGapFinFlatten
      invFun := osiiAxisPairMultiGapFinUnflatten
      left_inv := osiiAxisPairMultiGapFinUnflatten_flatten
      right_inv := osiiAxisPairMultiGapFinFlatten_unflatten
      map_add' := by
        intro x y
        funext j
        simp [osiiAxisPairMultiGapFinFlatten]
      map_smul' := by
        intro c x
        funext j
        simp [osiiAxisPairMultiGapFinFlatten] }

@[simp] theorem osiiAxisPairMultiGapFinFlattenCLE_symm_apply
    {d k : Nat}
    (z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) :
    (osiiAxisPairMultiGapFinFlattenCLE (d := d) (k := k)).symm z =
      osiiAxisPairMultiGapFinUnflatten z :=
  rfl

/-- The real center of the original-coordinate germ. -/
def osiiStep4MultiGapCenteredCoefficientBase
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    Fin k -> osiiAxisPairIndex d -> Real :=
  fun i a => u i a - shift

/-- Translate displacement coordinates back to the original logarithmic
coordinates of the radial germ. -/
def osiiStep4MultiGapCenteredCoefficientTranslate
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  z + osiiAxisPairSimultaneousLogRealEmbed
    (osiiStep4MultiGapCenteredCoefficientBase shift u)

@[simp] theorem osiiStep4MultiGapCenteredCoefficientOffset_translate
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) :
    osiiStep4MultiGapCenteredCoefficientOffset shift u
        (osiiStep4MultiGapCenteredCoefficientTranslate shift u z) = z := by
  funext i a
  simp [osiiStep4MultiGapCenteredCoefficientOffset,
    osiiStep4MultiGapCenteredCoefficientTranslate,
    osiiStep4MultiGapCenteredCoefficientBase,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed]

theorem differentiable_osiiStep4MultiGapCenteredCoefficientTranslate_fin
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    Differentiable Complex
      (fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
        osiiStep4MultiGapCenteredCoefficientTranslate shift u
          ((osiiAxisPairMultiGapFinFlattenCLE
            (d := d) (k := k)).symm z)) := by
  change Differentiable Complex
    (fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
      (osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm z +
        osiiAxisPairSimultaneousLogRealEmbed
          (osiiStep4MultiGapCenteredCoefficientBase shift u))
  fun_prop

theorem osiiStep4MultiGapCenteredCoefficientTranslate_fin_zero_mem_germDomain
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    {d k : Nat} [NeZero d]
    (u : Fin k -> osiiAxisPairIndex d -> Real) :
    osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm 0) ∈
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u := by
  have hball :
      osiiStep4MultiGapCenteredCoefficientOffset shift u
          (osiiAxisPairSimultaneousLogRealEmbed
            (osiiStep4MultiGapCenteredCoefficientBase shift u)) ∈
        Metric.ball 0 P.radius := by
    have hoffset :
        osiiStep4MultiGapCenteredCoefficientOffset shift u
            (osiiAxisPairSimultaneousLogRealEmbed
              (osiiStep4MultiGapCenteredCoefficientBase shift u)) = 0 := by
      funext i a
      simp [osiiStep4MultiGapCenteredCoefficientOffset,
        osiiStep4MultiGapCenteredCoefficientBase,
        osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed]
    rw [hoffset]
    exact Metric.mem_ball_self P.radius_pos
  have hcenter :=
    osiiAxisPairSimultaneousLogRealEmbed_mem_centeredCoefficientGermDomain
      P shift u
        (osiiStep4MultiGapCenteredCoefficientBase shift u) hball
  have htranslate_zero :
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
          ((osiiAxisPairMultiGapFinFlattenCLE
            (d := d) (k := k)).symm 0) =
        osiiAxisPairSimultaneousLogRealEmbed
          (osiiStep4MultiGapCenteredCoefficientBase shift u) := by
    funext i a
    simp [osiiStep4MultiGapCenteredCoefficientTranslate,
      osiiAxisPairMultiGapFinUnflatten]
  rw [htranslate_zero]
  exact hcenter

theorem osiiStep4MultiGapCenteredCoefficientTranslate_fin_realEmbed
    {d k : Nat}
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (x : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Real) :
    osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm
            (fun j => (x j : Complex))) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiStep4MultiGapCenteredCoefficientBase shift u +
          osiiAxisPairMultiGapFinUnflatten x) := by
  funext i a
  simp [osiiStep4MultiGapCenteredCoefficientTranslate,
    osiiStep4MultiGapCenteredCoefficientBase,
    osiiAxisPairSimultaneousLogRealEmbed,
    osiiAxisPairLogRealEmbed,
    osiiAxisPairMultiGapFinUnflatten]
  ring

/-- A bounded centered radial germ contains a convex finite-coordinate ball
which is a valid initial bounded scalar continuation.  This strengthened form
also retains the ball's inclusion in the germ and its exact complex-valued
agreement with the germ, not only the translated real-edge identity. -/
theorem exists_centeredBoundedScalarContinuationWithAgreement
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (B : Real)
    (hGerm : DifferentiableOn Complex
      (osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma)
      (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u))
    (hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      osiiStep4MultiGapCenteredCoefficientOffset shift u
          (osiiAxisPairSimultaneousLogRealEmbed x) ∈
        Metric.ball 0 P.radius ->
      osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (osiiAxisPairSimultaneousLogRealEmbed x) = X.realEdge x)
    (hbound : forall z,
      z ∈ osiiStep4MultiGapCenteredCoefficientGermDomain P shift u ->
      ‖osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma z‖ <= B) :
    ∃ eps : Real, 0 < eps ∧
      ∃ A : OSIIChapterV.BoundedScalarContinuationData
          (Fintype.card (osiiAxisPairMultiGapIndex d k)) B,
        (forall z, z ∈ A.carrier ->
          osiiStep4MultiGapCenteredCoefficientTranslate shift u
              ((osiiAxisPairMultiGapFinFlattenCLE
                (d := d) (k := k)).symm z) ∈
            osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) ∧
        (forall z, z ∈ A.carrier ->
          A.toFun z =
            osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
              (osiiStep4MultiGapCenteredCoefficientTranslate shift u
                ((osiiAxisPairMultiGapFinFlattenCLE
                  (d := d) (k := k)).symm z))) ∧
        forall x :
          Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Real,
        (fun j => (x j : Complex)) ∈ A.carrier ->
          A.toFun (fun j => (x j : Complex)) =
            X.realEdge
              (osiiStep4MultiGapCenteredCoefficientBase shift u +
                osiiAxisPairMultiGapFinUnflatten x) := by
  let translateFin :=
    fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm z)
  let V : Set
      (Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) :=
    translateFin ⁻¹'
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u
  have htranslate : Differentiable Complex translateFin :=
    differentiable_osiiStep4MultiGapCenteredCoefficientTranslate_fin
      shift u
  have hV_open : IsOpen V :=
    (isOpen_osiiStep4MultiGapCenteredCoefficientGermDomain P shift u
      ).preimage htranslate.continuous
  have hzero :
      (0 : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) ∈
        V := by
    exact
      osiiStep4MultiGapCenteredCoefficientTranslate_fin_zero_mem_germDomain
        P shift u
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.mp hV_open 0 hzero
  let A : OSIIChapterV.BoundedScalarContinuationData
      (Fintype.card (osiiAxisPairMultiGapIndex d k)) B :=
    { carrier := Metric.ball 0 eps
      carrier_open := Metric.isOpen_ball
      carrier_starConvex :=
        (convex_ball (0 :
          Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex)
          eps).starConvex (Metric.mem_ball_self heps)
      zero_mem := Metric.mem_ball_self heps
      toFun := fun z =>
        osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (translateFin z)
      differentiableOn := by
        exact hGerm.comp htranslate.differentiableOn
          (fun z hz => hball hz)
      norm_le := by
        intro z hz
        exact hbound _ (hball hz) }
  refine ⟨eps, heps, A, ?_, ?_, ?_⟩
  · intro z hz
    exact hball hz
  · intro z _hz
    rfl
  intro x hx
  have htranslate_real :=
    osiiStep4MultiGapCenteredCoefficientTranslate_fin_realEmbed
      shift u x
  have htranslate_real' :
      translateFin (fun j => (x j : Complex)) =
        osiiAxisPairSimultaneousLogRealEmbed
          (osiiStep4MultiGapCenteredCoefficientBase shift u +
            osiiAxisPairMultiGapFinUnflatten x) := by
    exact htranslate_real
  have hoffset := (hball hx).1
  rw [htranslate_real'] at hoffset
  change
    osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
        (translateFin (fun j => (x j : Complex))) = _
  rw [show translateFin (fun j => (x j : Complex)) =
      osiiAxisPairSimultaneousLogRealEmbed
        (osiiStep4MultiGapCenteredCoefficientBase shift u +
          osiiAxisPairMultiGapFinUnflatten x) by
    exact htranslate_real]
  apply hreal
  exact hoffset

/-- If the centered radial germ contains the complete finite-coordinate
segment from zero to a target, the same bounded germ supplies both the
initial continuation and an exact bound-preserving target chart. -/
theorem exists_centeredBoundedScalarContinuationWithTargetChart
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (B : Real)
    (hGerm : DifferentiableOn Complex
      (osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma)
      (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u))
    (hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      osiiStep4MultiGapCenteredCoefficientOffset shift u
          (osiiAxisPairSimultaneousLogRealEmbed x) ∈
        Metric.ball 0 P.radius ->
      osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (osiiAxisPairSimultaneousLogRealEmbed x) = X.realEdge x)
    (hbound : forall z,
      z ∈ osiiStep4MultiGapCenteredCoefficientGermDomain P shift u ->
      ‖osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma z‖ <= B)
    (target :
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex)
    (hsegment : forall z, z ∈ segment Real 0 target ->
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
          ((osiiAxisPairMultiGapFinFlattenCLE
            (d := d) (k := k)).symm z) ∈
        osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) :
    ∃ eps : Real, 0 < eps ∧
      ∃ A : OSIIChapterV.BoundedScalarContinuationData
          (Fintype.card (osiiAxisPairMultiGapIndex d k)) B,
        (forall x :
            Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Real,
          (fun j => (x j : Complex)) ∈ A.carrier ->
            A.toFun (fun j => (x j : Complex)) =
              X.realEdge
                (osiiStep4MultiGapCenteredCoefficientBase shift u +
                  osiiAxisPairMultiGapFinUnflatten x)) ∧
        ∃ D : OSIIChapterV.BoundedScalarTargetChartData A target,
          (D.toFun = fun z =>
              osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
                (osiiStep4MultiGapCenteredCoefficientTranslate shift u
                  ((osiiAxisPairMultiGapFinFlattenCLE
                    (d := d) (k := k)).symm z))) ∧
          (forall z, z ∈ D.domain ->
            osiiStep4MultiGapCenteredCoefficientTranslate shift u
                ((osiiAxisPairMultiGapFinFlattenCLE
                  (d := d) (k := k)).symm z) ∈
              osiiStep4MultiGapCenteredCoefficientGermDomain P shift u) := by
  obtain ⟨eps, heps, A, hcarrier, hagrees, hrealA⟩ :=
    exists_centeredBoundedScalarContinuationWithAgreement
      X P shift u Gamma B hGerm hreal hbound
  let translateFin :=
    fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm z)
  let V : Set
      (Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex) :=
    translateFin ⁻¹'
      osiiStep4MultiGapCenteredCoefficientGermDomain P shift u
  let F := fun z :
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
    osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
      (translateFin z)
  have htranslate : Differentiable Complex translateFin :=
    differentiable_osiiStep4MultiGapCenteredCoefficientTranslate_fin
      shift u
  have hV_open : IsOpen V :=
    (isOpen_osiiStep4MultiGapCenteredCoefficientGermDomain P shift u
      ).preimage htranslate.continuous
  have hF : DifferentiableOn Complex F V := by
    exact hGerm.comp htranslate.differentiableOn (fun _ hz => hz)
  have hFbound : forall z, z ∈ V -> ‖F z‖ <= B := by
    intro z hz
    exact hbound _ hz
  obtain ⟨D, hDtoFun, hDdomain⟩ :=
    OSIIChapterV.BoundedScalarTargetChartData.exists_ofBoundedHolomorphicExtension
      (A := A) (target := target)
      V hV_open (fun z hz => hsegment z hz) F hF hFbound
      A.carrier A.carrier_open A.zero_mem
      (by
        intro z hz
        exact ⟨hcarrier z hz, hz⟩)
      (by
        intro z hz
        exact (hagrees z hz).symm)
  refine ⟨eps, heps, A, hrealA, D, ?_, ?_⟩
  · simpa only [F, translateFin] using hDtoFun
  · intro z hz
    exact hDdomain hz

namespace OSIIStep4MultiGapSelectedCommonSlopeData

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
