/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedGeneratorBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeGeometry
import OSReconstruction.SCV.EuclideanWeylPairing
import OSReconstruction.SCV.HeadFiberFubini
import OSReconstruction.SCV.SchwartzExternalProduct

















noncomputable section

open Complex Filter MeasureTheory Set
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

theorem generatorBridgeVariation_eq_of_ne_bridge
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ)
    (j : Fin k)
    (hj : j ≠ i.bridgeGlobalIndex) :
    generatorBridgeVariation i τ t j = τ j := by
  by_cases hleft : j.val < i.n - 1
  · let a : Fin (i.n - 1) := Fin.rev ⟨j.val, hleft⟩
    have hja : j = i.leftGlobalIndex a := by
      apply Fin.ext
      simp [a, GeneratorIndex.leftGlobalIndex]
    rw [hja, generatorBridgeVariation_left]
  · have hbridgeVal :
        j.val ≠ i.n - 1 := by
      intro h
      apply hj
      apply Fin.ext
      simpa [GeneratorIndex.bridgeGlobalIndex] using h
    have hjright : i.n ≤ j.val := by omega
    have hb : j.val - i.n < i.m - 1 := by
      have hjlt := j.isLt
      have hnm := i.hnm
      omega
    let b : Fin (i.m - 1) := ⟨j.val - i.n, hb⟩
    have hjb : j = i.rightGlobalIndex b := by
      apply Fin.ext
      change j.val = i.n + b.val
      dsimp [b]
      omega
    rw [hjb, generatorBridgeVariation_right]

theorem generatorBlockGlobalTimeAffine_headFiber
    (i : GeneratorIndex k)
    (s t a : ℝ)
    (τ : Fin k → ℝ) :
    let ξ := generatorBridgeVariation i τ t
    let t₀ :=
      s - ∑ b : Fin (i.n - 1), τ (i.leftGlobalIndex b)
    let u := t₀ - a
    let v := τ i.bridgeGlobalIndex - t - u
    osiiAxisPairBlockGlobalTimeAffine
        i.n i.m s t
        (generatorBlockTimeDisplacement i
            (generatorChronologicalParameter i ξ) +
          axisPairBlockHeadDisplacement i.n i.m u v) =
      fun c =>
        generatorPhysicalTimePoint a τ
          (Fin.cast i.pointArity_add c) := by
  dsimp only
  let ξ := generatorBridgeVariation i τ t
  let t₀ :=
    s - ∑ b : Fin (i.n - 1), τ (i.leftGlobalIndex b)
  let u := t₀ - a
  let v := τ i.bridgeGlobalIndex - t - u
  change
    osiiAxisPairBlockGlobalTimeAffine
        i.n i.m s t
        (generatorBlockTimeDisplacement i
            (generatorChronologicalParameter i ξ) +
          axisPairBlockHeadDisplacement i.n i.m u v) =
      fun c =>
        generatorPhysicalTimePoint a τ
          (Fin.cast i.pointArity_add c)
  have hs :
      generatorChronologicalCommonShift i t₀ ξ = s := by
    simp only [generatorChronologicalCommonShift, t₀, ξ,
      generatorBridgeVariation_left]
    ring
  have ht :
      ξ i.bridgeGlobalIndex = t := by
    change generatorBridgeVariation i τ t i.bridgeGlobalIndex = t
    exact generatorBridgeVariation_bridge i τ t
  rw [← hs, ← ht]
  rw [generatorBlockGlobalTimeAffine_chronologicalParameter_add_heads]
  ext c
  have hbase : t₀ - u = a := by
    dsimp [u]
    ring
  rw [hbase]
  congr 1
  funext j
  by_cases hj : j = i.bridgeGlobalIndex
  · subst j
    rw [if_pos rfl]
    simp only [ξ, generatorBridgeVariation_bridge]
    dsimp [v]
    ring
  · rw [if_neg hj]
    exact generatorBridgeVariation_eq_of_ne_bridge i τ t j hj

private theorem rooted_cast_fin_function_apply'
    {n m : ℕ}
    (h : n = m)
    (x : Fin n → ℝ)
    (j : Fin m) :
    (cast (congrArg (fun q => Fin q → ℝ) h) x) j =
      x (Fin.cast h.symm j) := by
  subst m
  rfl

theorem splitFirst_generatorBlockTimeDisplacement_chronological_add_head
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ)
    (u v : ℝ) :
    splitFirst i.n i.m
        (generatorBlockTimeDisplacement i
            (generatorChronologicalParameter i ξ) +
          axisPairBlockHeadDisplacement i.n i.m u v) =
      cast
        (congrArg (fun q => Fin q → ℝ)
          (Nat.sub_add_cancel i.hn))
        (Fin.cons u (fun a => ξ (i.leftGlobalIndex a))) := by
  funext a
  rw [rooted_cast_fin_function_apply'
    (Nat.sub_add_cancel i.hn)]
  let a' : Fin ((i.n - 1) + 1) :=
    Fin.cast (Nat.sub_add_cancel i.hn).symm a
  have ha :
      a = Fin.cast (Nat.sub_add_cancel i.hn) a' := by
    apply Fin.ext
    rfl
  rw [ha]
  refine Fin.cases ?_ ?_ a'
  · have hzero :
        Fin.cast (Nat.sub_add_cancel i.hn)
            (0 : Fin ((i.n - 1) + 1)) =
          (⟨0, i.hn⟩ : Fin i.n) := by
      apply Fin.ext
      rfl
    rw [hzero]
    simp only [splitFirst, Pi.add_apply]
    rw [generatorBlockTimeDisplacement_left_zero,
      axisPairBlockHeadDisplacement_left]
    simp
  · intro b
    simp [splitFirst, Pi.add_apply]

theorem splitLast_generatorBlockTimeDisplacement_chronological_add_head
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ)
    (u v : ℝ) :
    splitLast i.n i.m
        (generatorBlockTimeDisplacement i
            (generatorChronologicalParameter i ξ) +
          axisPairBlockHeadDisplacement i.n i.m u v) =
      cast
        (congrArg (fun q => Fin q → ℝ)
          (Nat.sub_add_cancel i.hm))
        (Fin.cons v (fun b => ξ (i.rightGlobalIndex b))) := by
  funext b
  rw [rooted_cast_fin_function_apply'
    (Nat.sub_add_cancel i.hm)]
  let b' : Fin ((i.m - 1) + 1) :=
    Fin.cast (Nat.sub_add_cancel i.hm).symm b
  have hb :
      b = Fin.cast (Nat.sub_add_cancel i.hm) b' := by
    apply Fin.ext
    rfl
  rw [hb]
  refine Fin.cases ?_ ?_ b'
  · have hzero :
        Fin.cast (Nat.sub_add_cancel i.hm)
            (0 : Fin ((i.m - 1) + 1)) =
          (⟨0, i.hm⟩ : Fin i.m) := by
      apply Fin.ext
      rfl
    rw [hzero]
    simp only [splitLast, Pi.add_apply]
    rw [generatorBlockTimeDisplacement_right_zero,
      axisPairBlockHeadDisplacement_right]
    simp
  · intro c
    simp [splitLast, Pi.add_apply]

private theorem rooted_cast_schwartz_apply
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (x : Fin n → ℝ) :
    (cast
        (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) h)
        φ)
        (cast (congrArg (fun q => Fin q → ℝ) h) x) =
      φ x := by
  subst m
  rfl

/-- Evaluating a translated rooted-left profile leaves its bridge head fixed
and translates only the internal-gap tail. -/
theorem rootedLeftTranslatedTimeProfile_apply_cast_cons
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (u : ℝ)
    (x : Fin (i.n - 1) → ℝ) :
    D.rootedLeftTranslatedTimeProfile i timeScale ξ
        (cast
          (congrArg (fun q => Fin q → ℝ)
            (Nat.sub_add_cancel i.hn))
          (Fin.cons u x)) =
      (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f u *
        (A.leftInternalSource i
          (timeScale + D.commonTailStart i)).f
            (x - i.leftRealCoordinates ξ) := by
  rw [D.rootedLeftTranslatedTimeProfile_eq_cast_prepend]
  rw [rooted_cast_schwartz_apply (Nat.sub_add_cancel i.hn)]
  simp only [SCV.prependField_apply, SCV.translateSchwartz_apply]
  congr 2

/-- Evaluating a translated rooted-right profile leaves its bridge head fixed
and translates only the internal-gap tail. -/
theorem rootedRightTranslatedTimeProfile_apply_cast_cons
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (v : ℝ)
    (x : Fin (i.m - 1) → ℝ) :
    D.rootedRightTranslatedTimeProfile i timeScale ξ
        (cast
          (congrArg (fun q => Fin q → ℝ)
            (Nat.sub_add_cancel i.hm))
          (Fin.cons v x)) =
      (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f v *
        (A.rightInternalSource i
          (timeScale + D.commonTailStart i)).f
            (x - i.rightRealCoordinates ξ) := by
  rw [D.rootedRightTranslatedTimeProfile_eq_cast_prepend]
  rw [rooted_cast_schwartz_apply (Nat.sub_add_cancel i.hm)]
  simp only [SCV.prependField_apply, SCV.translateSchwartz_apply]
  congr 2

theorem leftInternalSource_real
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (x : Fin (i.n - 1) → ℝ) :
    ((A.leftInternalSource i N).f x).im = 0 := by
  rw [A.leftInternalSource_f_eq_translateApproximateIdentity]
  exact
    (A.leftInternalApproximateIdentity i).real N
      (x + -(fun a => anchor (i.leftGlobalIndex a)))

/-- The translated rooted global cutoff has the same absolute-time fiber as
the centered cutoff, with the internal gaps translated by the generator
parameter and the bridge centered at the translated bridge coordinate. -/
theorem rootedTranslatedGlobalTimeCutoff_apply_physicalPoint
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s t a : ℝ)
    (ξ τ : Fin k → ℝ) :
    let t₀ :=
      s - ∑ b : Fin (i.n - 1), τ (i.leftGlobalIndex b)
    let u := t₀ - a
    let v := τ i.bridgeGlobalIndex -
      (ξ i.bridgeGlobalIndex + t) - u
    osiiAxisPairGlobalTimeCutoff i.n i.m
        (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
        (D.rootedRightTranslatedTimeProfile i timeScale ξ)
        s (ξ i.bridgeGlobalIndex + t)
        (fun c =>
          generatorPhysicalTimePoint a τ
            (Fin.cast i.pointArity_add c)) =
      (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f u *
        (A.leftInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.leftGlobalIndex b) +
                ξ (i.leftGlobalIndex b)) *
        ((A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f v *
          (A.rightInternalSource i
            (timeScale + D.commonTailStart i)).f
              (fun b =>
                τ (i.rightGlobalIndex b) -
                  ξ (i.rightGlobalIndex b))) := by
  dsimp only
  let η :=
    generatorBridgeVariation i τ
      (ξ i.bridgeGlobalIndex + t)
  let t₀ :=
    s - ∑ b : Fin (i.n - 1), τ (i.leftGlobalIndex b)
  let u := t₀ - a
  let v := τ i.bridgeGlobalIndex -
    (ξ i.bridgeGlobalIndex + t) - u
  change
    osiiAxisPairGlobalTimeCutoff i.n i.m
        (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
        (D.rootedRightTranslatedTimeProfile i timeScale ξ)
        s (ξ i.bridgeGlobalIndex + t)
        (fun c =>
          generatorPhysicalTimePoint a τ
            (Fin.cast i.pointArity_add c)) =
      (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f u *
        (A.leftInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.leftGlobalIndex b) +
                ξ (i.leftGlobalIndex b)) *
        ((A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f v *
          (A.rightInternalSource i
            (timeScale + D.commonTailStart i)).f
              (fun b =>
                τ (i.rightGlobalIndex b) -
                  ξ (i.rightGlobalIndex b)))
  rw [← generatorBlockGlobalTimeAffine_headFiber
    i s (ξ i.bridgeGlobalIndex + t) a τ]
  rw [osiiAxisPairGlobalTimeCutoff_affine]
  rw [splitFirst_generatorBlockTimeDisplacement_chronological_add_head
    i η u v]
  rw [splitLast_generatorBlockTimeDisplacement_chronological_add_head
    i η u v]
  simp only [SchwartzMap.conj_apply]
  rw [D.rootedLeftTranslatedTimeProfile_apply_cast_cons]
  rw [D.rootedRightTranslatedTimeProfile_apply_cast_cons]
  simp only [η, generatorBridgeVariation_left,
    generatorBridgeVariation_right]
  have hleftCoord :
      (fun b => τ (i.leftGlobalIndex b)) -
          i.leftRealCoordinates ξ =
        fun b =>
          τ (i.leftGlobalIndex b) +
            ξ (i.leftGlobalIndex b) := by
    funext b
    simp [GeneratorIndex.leftRealCoordinates]
  have hrightCoord :
      (fun b => τ (i.rightGlobalIndex b)) -
          i.rightRealCoordinates ξ =
        fun b =>
          τ (i.rightGlobalIndex b) -
            ξ (i.rightGlobalIndex b) := by
    funext b
    simp [GeneratorIndex.rightRealCoordinates]
  rw [hleftCoord, hrightCoord]
  have hroot :
      star
          ((A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f u) =
        (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f u := by
    exact Complex.conj_eq_iff_im.mpr
      (A.rootedBridgeHead_real R i
        (timeScale + D.commonTailStart i) u)
  have hleft :
      star
          ((A.leftInternalSource i
            (timeScale + D.commonTailStart i)).f
              (fun b =>
                τ (i.leftGlobalIndex b) +
                  ξ (i.leftGlobalIndex b))) =
        (A.leftInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.leftGlobalIndex b) +
                ξ (i.leftGlobalIndex b)) := by
    exact Complex.conj_eq_iff_im.mpr
      (leftInternalSource_real A i
        (timeScale + D.commonTailStart i)
        (fun b =>
          τ (i.leftGlobalIndex b) +
            ξ (i.leftGlobalIndex b)))
  change
    star
        ((A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f u *
          (A.leftInternalSource i
            (timeScale + D.commonTailStart i)).f
              (fun b =>
                τ (i.leftGlobalIndex b) +
                  ξ (i.leftGlobalIndex b))) *
      ((A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f v *
        (A.rightInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.rightGlobalIndex b) -
                ξ (i.rightGlobalIndex b))) = _
  rw [star_mul']
  change
    star
          ((A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f u) *
        star
          ((A.leftInternalSource i
            (timeScale + D.commonTailStart i)).f
              (fun b =>
                τ (i.leftGlobalIndex b) +
                  ξ (i.leftGlobalIndex b))) *
      _ = _
  rw [hroot, hleft]

private theorem section43TimeTupleTransport_cast_symm
    {n m : ℕ}
    (h : n = m)
    (y : Fin m → ℝ) :
    section43TimeTupleTransport h
        (cast (congrArg (fun q => Fin q → ℝ) h.symm) y) =
      y := by
  subst m
  rfl

/-- Absolute-time integration of the translated global cutoff produces the
translated internal factors and the two-root bridge convolution centered at
the translated bridge coordinate. -/
theorem rootedTranslatedGlobalTimeCutoff_sliceIntegral
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s t : ℝ)
    (ξ τ : Fin k → ℝ) :
    SCV.sliceIntegral
        (section43TimeSchwartzTransport i.pointArity_add
          (osiiAxisPairGlobalTimeCutoff i.n i.m
            (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
            (D.rootedRightTranslatedTimeProfile i timeScale ξ)
            s (ξ i.bridgeGlobalIndex + t)))
        τ =
      (A.leftInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.leftGlobalIndex b) +
                ξ (i.leftGlobalIndex b)) *
        (section43CompactPositiveTimeSource1D_convolution
          (A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i))
          (A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i))).f
              (τ i.bridgeGlobalIndex -
                (ξ i.bridgeGlobalIndex + t)) *
        (A.rightInternalSource i
          (timeScale + D.commonTailStart i)).f
            (fun b =>
              τ (i.rightGlobalIndex b) -
                ξ (i.rightGlobalIndex b)) := by
  let root :=
    A.rootedBridgeHead R i
      (timeScale + D.commonTailStart i)
  let left :=
    (A.leftInternalSource i
      (timeScale + D.commonTailStart i)).f
        (fun b =>
          τ (i.leftGlobalIndex b) +
            ξ (i.leftGlobalIndex b))
  let right :=
    (A.rightInternalSource i
      (timeScale + D.commonTailStart i)).f
        (fun b =>
          τ (i.rightGlobalIndex b) -
            ξ (i.rightGlobalIndex b))
  let c :=
    τ i.bridgeGlobalIndex - (ξ i.bridgeGlobalIndex + t)
  let t₀ :=
    s - ∑ b : Fin (i.n - 1), τ (i.leftGlobalIndex b)
  rw [SCV.sliceIntegral_apply]
  simp only [SCV.sliceIntegralRaw]
  calc
    (∫ a : ℝ,
        section43TimeSchwartzTransport i.pointArity_add
          (osiiAxisPairGlobalTimeCutoff i.n i.m
            (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
            (D.rootedRightTranslatedTimeProfile i timeScale ξ)
            s (ξ i.bridgeGlobalIndex + t))
          (Fin.cons a τ)) =
      ∫ a : ℝ,
        root.f (t₀ - a) * left *
          (root.f (c - (t₀ - a)) * right) := by
        apply integral_congr_ae
        filter_upwards with a
        let x : Fin (i.n + i.m) → ℝ :=
          fun q =>
            generatorPhysicalTimePoint a τ
              (Fin.cast i.pointArity_add q)
        have hx :
            section43TimeTupleTransport i.pointArity_add x =
              Fin.cons a τ := by
          have hxcast :
              x =
                cast
                  (congrArg (fun q => Fin q → ℝ)
                    i.pointArity_add.symm)
                  (Fin.cons a τ) := by
            funext q
            rw [rooted_cast_fin_function_apply'
              i.pointArity_add.symm]
            rfl
          rw [hxcast]
          exact
            section43TimeTupleTransport_cast_symm
              i.pointArity_add (Fin.cons a τ)
        rw [← hx, section43TimeSchwartzTransport_apply]
        simpa [root, left, right, c, t₀] using
          D.rootedTranslatedGlobalTimeCutoff_apply_physicalPoint
            i timeScale s t a ξ τ
    _ =
      ∫ a : ℝ,
        (root.f (t₀ - a) *
          root.f (c - (t₀ - a))) * (left * right) := by
        apply integral_congr_ae
        filter_upwards with a
        ring
    _ =
      (∫ a : ℝ,
        root.f (t₀ - a) *
          root.f (c - (t₀ - a))) * (left * right) := by
        exact
          MeasureTheory.integral_mul_const
            (left * right)
            (fun a : ℝ =>
              root.f (t₀ - a) *
                root.f (c - (t₀ - a)))
    _ =
      (∫ u : ℝ, root.f u * root.f (c - u)) *
        (left * right) := by
        rw [MeasureTheory.integral_sub_left_eq_self
          (fun u : ℝ => root.f u * root.f (c - u))
          (volume : Measure ℝ) t₀]
    _ =
      (section43CompactPositiveTimeSource1D_convolution
        root root).f c * (left * right) := by
        rw [section43CompactPositiveTimeSource1D_convolution_apply]
    _ = _ := by
      dsimp [root, left, right, c]
      ring

theorem rootedBridgeHead_integral_convolution_eq_bridgeFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (u : ℝ) :
    (∫ t : ℝ,
        (A.rootedBridgeHead R i N).f t *
          (section43CompactPositiveTimeSource1D_convolution
            (A.rootedBridgeHead R i N)
            (A.rootedBridgeHead R i N)).f (u - t)) =
      (A.bridgeFactor i N).f u := by
  rw [← section43CompactPositiveTimeSource1D_convolution_apply]
  have h :=
    congrArg
      (fun g : Section43CompactPositiveTimeSource1D => g.f u)
      (A.rootedBridgeFactorization R i N
        ).physical_eq_totalConvolution
  simpa using h.symm

/-- Replacing the distinguished bridge coordinate by its current value
reconstructs the original global reduced-time tuple. -/
theorem generatorBridgeVariation_self
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    generatorBridgeVariation i τ (τ i.bridgeGlobalIndex) = τ := by
  funext j
  by_cases hj : j = i.bridgeGlobalIndex
  · subst j
    exact generatorBridgeVariation_bridge i τ _
  · exact generatorBridgeVariation_eq_of_ne_bridge i τ _ j hj

private abbrev RootedJointTimeCoordinates (i : GeneratorIndex k) :=
  ℝ ×
    ((Fin (i.n - 1) → ℝ) ×
      (ℝ × (Fin (i.m - 1) → ℝ)))

/-- Joint coordinates for the middle root, the two internal gap blocks, and
the residual two-root bridge convolution. -/
private def rootedJointTimeCoordLinearEquiv
    (i : GeneratorIndex k) :
    (Fin (k + 1) → ℝ) ≃ₗ[ℝ] RootedJointTimeCoordinates i where
  toFun := fun x =>
    (x 0,
      ((fun a => Fin.tail x (i.leftGlobalIndex a)),
        (Fin.tail x i.bridgeGlobalIndex - x 0,
          fun b => Fin.tail x (i.rightGlobalIndex b))))
  invFun := fun p =>
    Fin.cons p.1
      (generatorSplitTimeTuple i p.2.1
        (p.2.2.1 + p.1) p.2.2.2)
  left_inv := by
    intro x
    have htail :
        generatorSplitTimeTuple i
            (fun a => Fin.tail x (i.leftGlobalIndex a))
            (Fin.tail x i.bridgeGlobalIndex)
            (fun b => Fin.tail x (i.rightGlobalIndex b)) =
          Fin.tail x := by
      simpa [generatorBridgeVariation] using
        generatorBridgeVariation_self i (Fin.tail x)
    change
      Fin.cons (x 0)
          (generatorSplitTimeTuple i
            (fun a => Fin.tail x (i.leftGlobalIndex a))
            ((Fin.tail x i.bridgeGlobalIndex - x 0) + x 0)
            (fun b => Fin.tail x (i.rightGlobalIndex b))) =
        x
    rw [sub_add_cancel, htail]
    exact Fin.cons_self_tail x
  right_inv := by
    rintro ⟨t, xL, c, xR⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext a
        simp
      · apply Prod.ext
        · change
            generatorSplitTimeTuple i xL (c + t) xR
                i.bridgeGlobalIndex - t =
              c
          rw [generatorSplitTimeTuple_bridge]
          ring
        · funext b
          simp
  map_add' := by
    intro x y
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext a
        rfl
      · apply Prod.ext
        · change
            (Fin.tail x i.bridgeGlobalIndex +
                Fin.tail y i.bridgeGlobalIndex) -
                (x 0 + y 0) =
              (Fin.tail x i.bridgeGlobalIndex - x 0) +
                (Fin.tail y i.bridgeGlobalIndex - y 0)
          ring
        · funext b
          rfl
  map_smul' := by
    intro c x
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext a
        rfl
      · apply Prod.ext
        · change
            c * Fin.tail x i.bridgeGlobalIndex - c * x 0 =
              c * (Fin.tail x i.bridgeGlobalIndex - x 0)
          ring
        · funext b
          rfl

private noncomputable def rootedJointTimeCoordCLE
    (i : GeneratorIndex k) :
    (Fin (k + 1) → ℝ) ≃L[ℝ] RootedJointTimeCoordinates i :=
  (rootedJointTimeCoordLinearEquiv i).toContinuousLinearEquiv

/-- One joint Schwartz test whose head parameter is the middle convolution
root and whose tail is the complete reduced rooted time source. -/
noncomputable def rootedMiddleSmearingTimeKernel
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SchwartzMap (Fin (k + 1) → ℝ) ℂ :=
  let root := A.rootedBridgeHead R i N
  let pair := section43CompactPositiveTimeSource1D_convolution root root
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (rootedJointTimeCoordCLE i))
      (SCV.schwartzExternalProduct root.f
        (SCV.schwartzExternalProduct
          (A.leftInternalSource i N).f
          (SCV.schwartzExternalProduct pair.f
            (A.rightInternalSource i N).f)))

@[simp]
theorem rootedMiddleSmearingTimeKernel_apply
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (t : ℝ)
    (τ : Fin k → ℝ) :
    rootedMiddleSmearingTimeKernel A R i N (Fin.cons t τ) =
      (A.rootedBridgeHead R i N).f t *
        ((A.leftInternalSource i N).f
            (fun a => τ (i.leftGlobalIndex a)) *
          ((section43CompactPositiveTimeSource1D_convolution
              (A.rootedBridgeHead R i N)
              (A.rootedBridgeHead R i N)).f
                (τ i.bridgeGlobalIndex - t) *
            (A.rightInternalSource i N).f
              (fun b => τ (i.rightGlobalIndex b)))) := by
  rfl

/-- Head integration of the joint three-root kernel is exactly the canonical
anchored reduced-time Schwartz test. -/
theorem sliceIntegral_rootedMiddleSmearingTimeKernel
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SCV.sliceIntegral (rootedMiddleSmearingTimeKernel A R i N) =
      A.timeTest N := by
  ext τ
  rw [SCV.sliceIntegral_apply]
  simp only [SCV.sliceIntegralRaw,
    rootedMiddleSmearingTimeKernel_apply]
  let root := A.rootedBridgeHead R i N
  let left :=
    (A.leftInternalSource i N).f
      (fun a => τ (i.leftGlobalIndex a))
  let right :=
    (A.rightInternalSource i N).f
      (fun b => τ (i.rightGlobalIndex b))
  calc
    (∫ t : ℝ,
        root.f t *
          (left *
            ((section43CompactPositiveTimeSource1D_convolution
                root root).f (τ i.bridgeGlobalIndex - t) *
              right))) =
      ∫ t : ℝ,
        (left * right) *
          (root.f t *
            (section43CompactPositiveTimeSource1D_convolution
              root root).f (τ i.bridgeGlobalIndex - t)) := by
        apply integral_congr_ae
        filter_upwards with t
        ring
    _ =
      (left * right) *
        ∫ t : ℝ,
          root.f t *
            (section43CompactPositiveTimeSource1D_convolution
              root root).f (τ i.bridgeGlobalIndex - t) := by
        exact MeasureTheory.integral_const_mul
          (left * right)
          (fun t : ℝ =>
            root.f t *
              (section43CompactPositiveTimeSource1D_convolution
                root root).f (τ i.bridgeGlobalIndex - t))
    _ =
      (left * right) *
        (A.bridgeFactor i N).f (τ i.bridgeGlobalIndex) := by
      rw [rootedBridgeHead_integral_convolution_eq_bridgeFactor
        A R i N (τ i.bridgeGlobalIndex)]
    _ = A.timeTest N τ := by
      rw [A.timeTest_apply_eq_left_bridge_right i N τ]
      dsimp [left, right]
      ring

/-- Translate only the physical reduced-time tail of the joint three-root
kernel. The integration head remains the normalized middle root. -/
noncomputable def rootedTranslatedMiddleSmearingTimeKernel
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (ξ : Fin k → ℝ) :
    SchwartzMap (Fin (k + 1) → ℝ) ℂ :=
  SCV.translateSchwartz
    (Fin.cons 0 (-ξ))
    (rootedMiddleSmearingTimeKernel A R i N)

/-- The translated joint kernel evaluates by shifting every physical gap,
while leaving the middle integration root unchanged. In particular, the
bridge convolution is evaluated at
`τ_bridge - (ξ_bridge + t)`, which is the corrected semigroup coordinate for
the translated real edge. -/
@[simp]
theorem rootedTranslatedMiddleSmearingTimeKernel_apply
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (ξ τ : Fin k → ℝ)
    (t : ℝ) :
    rootedTranslatedMiddleSmearingTimeKernel A R i N ξ (Fin.cons t τ) =
      (A.rootedBridgeHead R i N).f t *
        ((A.leftInternalSource i N).f
            (fun a => τ (i.leftGlobalIndex a) -
              ξ (i.leftGlobalIndex a)) *
          ((section43CompactPositiveTimeSource1D_convolution
              (A.rootedBridgeHead R i N)
              (A.rootedBridgeHead R i N)).f
                (τ i.bridgeGlobalIndex -
                  (ξ i.bridgeGlobalIndex + t)) *
            (A.rightInternalSource i N).f
              (fun b => τ (i.rightGlobalIndex b) -
                ξ (i.rightGlobalIndex b)))) := by
  rw [rootedTranslatedMiddleSmearingTimeKernel,
    SCV.translateSchwartz_apply]
  have hcons :
      Fin.cons t τ + Fin.cons 0 (-ξ) =
        (Fin.cons t (fun a => τ a - ξ a) :
          Fin (k + 1) → ℝ) := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [Pi.add_apply]
    · intro a
      simp [Pi.add_apply, sub_eq_add_neg]
  rw [hcons, rootedMiddleSmearingTimeKernel_apply]
  congr 3
  ring_nf

/-- Head integration of the translated joint kernel is exactly the translated
canonical anchored time test. This is the full physical real-edge identity,
not merely its centered specialization. -/
theorem sliceIntegral_rootedTranslatedMiddleSmearingTimeKernel
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (ξ : Fin k → ℝ) :
    SCV.sliceIntegral
        (rootedTranslatedMiddleSmearingTimeKernel A R i N ξ) =
      SCV.translateSchwartz (-ξ) (A.timeTest N) := by
  rw [rootedTranslatedMiddleSmearingTimeKernel]
  ext τ
  rw [SCV.translateSchwartz_apply]
  change
    (∫ t : ℝ,
      (SCV.translateSchwartz (Fin.cons 0 (-ξ))
        (rootedMiddleSmearingTimeKernel A R i N)) (Fin.cons t τ)) =
      A.timeTest N (τ + -ξ)
  simp_rw [SCV.translateSchwartz_apply]
  have hfun :
      (fun t : ℝ =>
        rootedMiddleSmearingTimeKernel A R i N
          (Fin.cons t τ + Fin.cons 0 (-ξ))) =
        (fun t : ℝ =>
          rootedMiddleSmearingTimeKernel A R i N
            (Fin.cons t (τ + -ξ))) := by
    funext t
    congr 1
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [Pi.add_apply]
    · intro a
      simp [Pi.add_apply]
  rw [hfun]
  change
    SCV.sliceIntegral (rootedMiddleSmearingTimeKernel A R i N)
        (τ + -ξ) =
      A.timeTest N (τ + -ξ)
  rw [sliceIntegral_rootedMiddleSmearingTimeKernel]

/-- Every fixed middle-root section of the translated joint kernel is the
literal translated global-cutoff slice. The generator parameter is converted
to chronological reduced-time coordinates before translating the canonical
joint source. -/
theorem rootedTranslatedMiddleSmearingTimeKernel_eq_globalCutoffSlice
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s t : ℝ)
    (ξ τ : Fin k → ℝ) :
    rootedTranslatedMiddleSmearingTimeKernel A R i
        (timeScale + D.commonTailStart i)
        (generatorChronologicalParameter i ξ)
        (Fin.cons t τ) =
      (A.rootedBridgeHead R i
        (timeScale + D.commonTailStart i)).f t *
        SCV.sliceIntegral
          (section43TimeSchwartzTransport i.pointArity_add
            (osiiAxisPairGlobalTimeCutoff i.n i.m
              (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
              (D.rootedRightTranslatedTimeProfile i timeScale ξ)
              s (ξ i.bridgeGlobalIndex + t)))
          τ := by
  rw [rootedTranslatedMiddleSmearingTimeKernel_apply]
  rw [D.rootedTranslatedGlobalTimeCutoff_sliceIntegral
    i timeScale s t ξ τ]
  simp only [generatorChronologicalParameter_left,
    generatorChronologicalParameter_bridge,
    generatorChronologicalParameter_right]
  ring

/-- Weak scalar Fubini for the translated rooted source. Every continuous
reduced-time Schwartz functional evaluates the middle-root integral of the
literal translated global-cutoff slices as the correspondingly translated
canonical packet test. -/
theorem rootedTranslatedMiddleSmearing_weak_globalCutoffSlice_eq_timeTest
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (s : ℝ → ℝ)
    (ξ : Fin k → ℝ)
    (T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ) :
    (∫ t : ℝ,
        (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f t *
          T
            (SCV.sliceIntegral
              (section43TimeSchwartzTransport i.pointArity_add
                (osiiAxisPairGlobalTimeCutoff i.n i.m
                  (D.rootedLeftTranslatedTimeProfile
                    i timeScale ξ).conj
                  (D.rootedRightTranslatedTimeProfile
                    i timeScale ξ)
                  (s t) (ξ i.bridgeGlobalIndex + t))))) =
      T (SCV.translateSchwartz
        (-(generatorChronologicalParameter i ξ))
        (A.timeTest (timeScale + D.commonTailStart i))) := by
  let K : SchwartzMap (Fin (k + 1) → ℝ) ℂ :=
    rootedTranslatedMiddleSmearingTimeKernel A R i
      (timeScale + D.commonTailStart i)
      (generatorChronologicalParameter i ξ)
  have hfubini :=
    SCV.continuousLinearMap_apply_sliceIntegralCLM_eq_integral T K
  have hslice :
      SCV.sliceIntegralCLM k K =
        SCV.translateSchwartz
          (-(generatorChronologicalParameter i ξ))
          (A.timeTest (timeScale + D.commonTailStart i)) := by
    rw [SCV.sliceIntegralCLM_apply]
    exact
      sliceIntegral_rootedTranslatedMiddleSmearingTimeKernel
        A R i (timeScale + D.commonTailStart i)
          (generatorChronologicalParameter i ξ)
  calc
    (∫ t : ℝ,
        (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f t *
          T
            (SCV.sliceIntegral
              (section43TimeSchwartzTransport i.pointArity_add
                (osiiAxisPairGlobalTimeCutoff i.n i.m
                  (D.rootedLeftTranslatedTimeProfile
                    i timeScale ξ).conj
                  (D.rootedRightTranslatedTimeProfile
                    i timeScale ξ)
                  (s t) (ξ i.bridgeGlobalIndex + t))))) =
      ∫ t : ℝ,
        T (SCV.schwartzPartialEval₁
          (SCV.headTailProductSchwartzCLM k K) t) := by
        apply integral_congr_ae
        filter_upwards with t
        have hsection :
            SCV.schwartzPartialEval₁
                (SCV.headTailProductSchwartzCLM k K) t =
              (A.rootedBridgeHead R i
                (timeScale + D.commonTailStart i)).f t •
                SCV.sliceIntegral
                  (section43TimeSchwartzTransport i.pointArity_add
                    (osiiAxisPairGlobalTimeCutoff i.n i.m
                      (D.rootedLeftTranslatedTimeProfile
                        i timeScale ξ).conj
                      (D.rootedRightTranslatedTimeProfile
                        i timeScale ξ)
                      (s t) (ξ i.bridgeGlobalIndex + t))) := by
          ext τ
          exact
            rootedTranslatedMiddleSmearingTimeKernel_eq_globalCutoffSlice
              D i timeScale (s t) t ξ τ
        rw [hsection, map_smul]
        rfl
    _ = T (SCV.sliceIntegralCLM k K) := hfubini.symm
    _ = T (SCV.translateSchwartz
        (-(generatorChronologicalParameter i ξ))
        (A.timeTest (timeScale + D.commonTailStart i))) := by
      rw [hslice]

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
