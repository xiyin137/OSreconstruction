/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedA0TranslatedFields
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketGeneratorBridge












noncomputable section

open Complex Filter MeasureTheory Set
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

namespace RootedA0BlockContinuousTranslationData

/-- One cofinal scale shift shared by the rooted left block, rooted right
block, and the distinguished bridge root. -/
def commonTailStart
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) : ℕ :=
  max (D.leftTailStart i) (D.rightTailStart i)

/-- Field index selecting physical rooted packet scale
`N + D.commonTailStart i` on the left. -/
def leftCofinalIndex
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N : ℕ) : ℕ :=
  N + (D.commonTailStart i - D.leftTailStart i)

/-- Field index selecting physical rooted packet scale
`N + D.commonTailStart i` on the right. -/
def rightCofinalIndex
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N : ℕ) : ℕ :=
  N + (D.commonTailStart i - D.rightTailStart i)

@[simp]
theorem leftCofinalIndex_add_tailStart
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N : ℕ) :
    D.leftCofinalIndex i N + D.leftTailStart i =
      N + D.commonTailStart i := by
  simp only [leftCofinalIndex, commonTailStart]
  omega

@[simp]
theorem rightCofinalIndex_add_tailStart
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N : ℕ) :
    D.rightCofinalIndex i N + D.rightTailStart i =
      N + D.commonTailStart i := by
  simp only [rightCofinalIndex, commonTailStart]
  omega

/-- The complete rooted-left time profile at the generator's native left
particle count. -/
noncomputable def rootedLeftTimeProfile
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    SchwartzMap (Fin i.n → ℝ) ℂ :=
  cast
    (congrArg
      (fun q => SchwartzMap (Fin q → ℝ) ℂ)
      (Nat.sub_add_cancel i.hn))
    ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (timeScale + D.commonTailStart i)).f

/-- The complete rooted-right time profile at the generator's native right
particle count. -/
noncomputable def rootedRightTimeProfile
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    SchwartzMap (Fin i.m → ℝ) ℂ :=
  cast
    (congrArg
      (fun q => SchwartzMap (Fin q → ℝ) ℂ)
      (Nat.sub_add_cancel i.hm))
    ((A.rootedRightBlockApproximateIdentity R i).translatedSource
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (timeScale + D.commonTailStart i)).f

private theorem rooted_cast_compactTimeSource_f
    {n m : ℕ}
    (h : n = m)
    (g : Section43CompactStrictPositiveTimeSource n) :
    (cast
        (congrArg Section43CompactStrictPositiveTimeSource h)
        g).f =
      cast
        (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) h)
        g.f := by
  subst m
  rfl

/-- The rooted-left profile as a compact strict-positive source at the
generator's native left particle count. -/
noncomputable def rootedLeftTimeProfileNative
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    Section43CompactStrictPositiveTimeSource i.n :=
  cast
    (congrArg Section43CompactStrictPositiveTimeSource
      (Nat.sub_add_cancel i.hn))
    ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (timeScale + D.commonTailStart i))

/-- The rooted-right profile as a compact strict-positive source at the
generator's native right particle count. -/
noncomputable def rootedRightTimeProfileNative
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    Section43CompactStrictPositiveTimeSource i.m :=
  cast
    (congrArg Section43CompactStrictPositiveTimeSource
      (Nat.sub_add_cancel i.hm))
    ((A.rootedRightBlockApproximateIdentity R i).translatedSource
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (timeScale + D.commonTailStart i))

@[simp]
theorem rootedLeftTimeProfileNative_f
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    (D.rootedLeftTimeProfileNative i timeScale).f =
      D.rootedLeftTimeProfile i timeScale := by
  unfold rootedLeftTimeProfileNative rootedLeftTimeProfile
  exact
    rooted_cast_compactTimeSource_f
      (Nat.sub_add_cancel i.hn)
      ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
        (timeScale + D.commonTailStart i))

@[simp]
theorem rootedRightTimeProfileNative_f
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    (D.rootedRightTimeProfileNative i timeScale).f =
      D.rootedRightTimeProfile i timeScale := by
  unfold rootedRightTimeProfileNative rootedRightTimeProfile
  exact
    rooted_cast_compactTimeSource_f
      (Nat.sub_add_cancel i.hm)
      ((A.rootedRightBlockApproximateIdentity R i).translatedSource
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
        (timeScale + D.commonTailStart i))

/-- The rooted-left time profile after the generator's internal
chronological translation. -/
noncomputable def rootedLeftTranslatedTimeProfile
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) :
    SchwartzMap (Fin i.n → ℝ) ℂ :=
  SCV.translateSchwartz
    (chronologicalTimeProfileDisplacementOfPositive i.hn
      (i.leftRealCoordinates τ))
    (D.rootedLeftTimeProfile i timeScale)

/-- The rooted-right time profile after the generator's internal
chronological translation. -/
noncomputable def rootedRightTranslatedTimeProfile
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) :
    SchwartzMap (Fin i.m → ℝ) ℂ :=
  SCV.translateSchwartz
    (chronologicalTimeProfileDisplacementOfPositive i.hm
      (i.rightRealCoordinates τ))
    (D.rootedRightTimeProfile i timeScale)

/-- Both synchronized rooted time profiles remain in their strict-positive
orthants after the generator's chronological translations. -/
def RootedTranslatedTimeProfilesPositive
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) : Prop :=
  tsupport
      (D.rootedLeftTranslatedTimeProfile i timeScale τ :
        (Fin i.n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.n ∧
    tsupport
      (D.rootedRightTranslatedTimeProfile i timeScale τ :
        (Fin i.m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.m

/-- Translating a rooted-left block moves only its internal-gap tail. The
bridge root remains the distinguished head factor. -/
theorem rootedLeftBlock_translatedTimeProfile_f
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (x : Fin (i.n - 1) → ℝ) :
    SCV.translateSchwartz
        (fun j : Fin ((i.n - 1) + 1) => -Fin.cases 0 x j)
        ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i)
          (timeScale + D.commonTailStart i)).f =
      SCV.prependField
        (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f
        (SCV.translateSchwartz (-x)
          (A.leftInternalSource i
            (timeScale + D.commonTailStart i)).f) := by
  rw [A.rootedLeftBlock_translatedSource_f]
  ext y
  simp only [SCV.translateSchwartz_apply, SCV.prependField_apply,
    Pi.add_apply, Fin.cases_zero, Fin.cases_succ,
    neg_zero, add_zero]
  apply congrArg₂ (fun a b : ℂ => a * b) rfl
  exact congrArg
    (A.leftInternalSource i
      (timeScale + D.commonTailStart i)).f (by
        funext j
        rfl)

/-- Rooted-right analogue of
`rootedLeftBlock_translatedTimeProfile_f`. -/
theorem rootedRightBlock_translatedTimeProfile_f
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (x : Fin (i.m - 1) → ℝ) :
    SCV.translateSchwartz
        (fun j : Fin ((i.m - 1) + 1) => -Fin.cases 0 x j)
        ((A.rootedRightBlockApproximateIdentity R i).translatedSource
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i)
          (timeScale + D.commonTailStart i)).f =
      SCV.prependField
        (A.rootedBridgeHead R i
          (timeScale + D.commonTailStart i)).f
        (SCV.translateSchwartz (-x)
          (A.rightInternalSource i
            (timeScale + D.commonTailStart i)).f) := by
  rw [A.rootedRightBlock_translatedSource_f]
  ext y
  simp only [SCV.translateSchwartz_apply, SCV.prependField_apply,
    Pi.add_apply, Fin.cases_zero, Fin.cases_succ,
    neg_zero, add_zero]
  apply congrArg₂ (fun a b : ℂ => a * b) rfl
  exact congrArg
    (A.rightInternalSource i
      (timeScale + D.commonTailStart i)).f (by
        funext j
        rfl)

/-- The rooted left Hermite field, reindexed to the common physical packet
scale. -/
noncomputable def leftSpatialHermiteGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N mode : ℕ) :
    (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    (D.left i).field (D.leftCofinalIndex i N) z
      (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
        (d := d) i mode)

/-- The rooted right Hermite field, reindexed to the same physical packet
scale as the left field. -/
noncomputable def rightSpatialHermiteGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N mode : ℕ) :
    (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS :=
  fun z =>
    (D.right i).field (D.rightCofinalIndex i N) z
      (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
        (d := d) i mode)

/-- The exact rooted finite-scale generator mode.  Its left field, right
field, and bridge root all belong to physical packet scale
`N + D.commonTailStart i`. -/
noncomputable def spatialHermiteGeneratorModeOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N mode : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  fun w =>
    osiiSemigroupMixedHilbertPairing OS
      (D.leftSpatialHermiteGeneratorField i N mode)
      (D.rightSpatialHermiteGeneratorField i N mode)
      (i.splitCoordinatesCLM w)

@[simp]
theorem spatialHermiteGeneratorModeOfOS_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N mode : ℕ)
    (w : OSIITimeGapSpace k) :
    D.spatialHermiteGeneratorModeOfOS i N mode w =
      @inner ℂ (OSHilbertSpace OS) _
        (D.leftSpatialHermiteGeneratorField i N mode
          (fun a => -star (w (i.leftGlobalIndex a))))
        (osiiOriginalOSHilbertComplex OS (w i.bridgeGlobalIndex)
          (D.rightSpatialHermiteGeneratorField i N mode
            (fun b => w (i.rightGlobalIndex b)))) := by
  rfl

/-- On the positive real generator edge, the genuine original-OS mode is
the Schwinger pairing of the synchronized rooted translated blocks. -/
theorem spatialHermiteGeneratorModeOfOS_positiveReal_eq_schwinger
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (N mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hleft :
      i.leftRealCoordinates τ ∈ (D.left i).realRegion)
    (hright :
      i.rightRealCoordinates τ ∈ (D.right i).realRegion) :
    D.spatialHermiteGeneratorModeOfOS i N mode
        (osiiPositiveRealTimeEmbed τ) =
      OS.S (((i.n - 1) + 1) + ((i.m - 1) + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((A.rootedLeftBlockTranslatedSpatialSource R i
              (N + D.commonTailStart i)
              (i.leftRealCoordinates τ)
              (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
                (d := d) i mode)).1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (τ i.bridgeGlobalIndex)
              (A.rootedRightBlockTranslatedSpatialSource R i
                (N + D.commonTailStart i)
                (i.rightRealCoordinates τ)
                (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
                  (d := d) i mode)).1))) := by
  rw [spatialHermiteGeneratorModeOfOS,
    osiiSemigroupMixedHilbertPairing, bridgedMixedHilbertPairing]
  have hleftField :
      D.leftSpatialHermiteGeneratorField i N mode
          (fun a =>
            -star
              (osiiPositiveRealTimeEmbed τ
                (i.leftGlobalIndex a))) =
        osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)
          (A.rootedLeftBlockTranslatedSpatialSource R i
            (N + D.commonTailStart i)
            (i.leftRealCoordinates τ)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i mode)) := by
    simpa [leftSpatialHermiteGeneratorField,
      GeneratorIndex.leftRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      (D.left i).realEdge
        (D.leftCofinalIndex i N)
        (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
          (d := d) i mode)
        (i.leftRealCoordinates τ) hleft
  have hrightField :
      D.rightSpatialHermiteGeneratorField i N mode
          (fun b =>
            osiiPositiveRealTimeEmbed τ
              (i.rightGlobalIndex b)) =
        osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)
          (A.rootedRightBlockTranslatedSpatialSource R i
            (N + D.commonTailStart i)
            (i.rightRealCoordinates τ)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i mode)) := by
    simpa [rightSpatialHermiteGeneratorField,
      GeneratorIndex.rightRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      (D.right i).realEdge
        (D.rightCofinalIndex i N)
        (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
          (d := d) i mode)
        (i.rightRealCoordinates τ) hright
  have hleftCoordinates :
      star (i.splitCoordinatesCLM
        (osiiPositiveRealTimeEmbed τ)).2.1 =
        fun a =>
          -star (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)) := by
    ext a
    simp
  have hrightCoordinates :
      (i.splitCoordinatesCLM
        (osiiPositiveRealTimeEmbed τ)).2.2 =
        fun b =>
          osiiPositiveRealTimeEmbed τ
            (i.rightGlobalIndex b) := by
    ext b
    rfl
  rw [hleftCoordinates, hrightCoordinates,
    GeneratorIndex.splitCoordinatesCLM_fst,
    hleftField, hrightField]
  exact
    osiiOriginalOSPositiveTimeSemigroupPairing_ofReal_eq_schwinger
      OS ((i.n - 1) + 1) ((i.m - 1) + 1)
      (τ i.bridgeGlobalIndex) hbridge
      (A.rootedLeftBlockTranslatedSpatialSource R i
        (N + D.commonTailStart i)
        (i.leftRealCoordinates τ)
        (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
          (d := d) i mode))
      (A.rootedRightBlockTranslatedSpatialSource R i
        (N + D.commonTailStart i)
        (i.rightRealCoordinates τ)
        (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
          (d := d) i mode))

private theorem rooted_cast_translateSchwartz
    {n m : ℕ}
    (h : n = m)
    (u : Fin n → ℝ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    cast
        (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) h)
        (SCV.translateSchwartz u φ) =
      SCV.translateSchwartz
        (cast (congrArg (fun q => Fin q → ℝ) h) u)
        (cast
          (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) h)
          φ) := by
  subst m
  rfl

private theorem rooted_cast_fin_function_apply
    {n m : ℕ}
    (h : n = m)
    (u : Fin n → ℝ)
    (j : Fin m) :
    (cast (congrArg (fun q => Fin q → ℝ) h) u) j =
      u (Fin.cast h.symm j) := by
  subst m
  rfl

private theorem rooted_cast_prepend_displacement
    {n : ℕ}
    (hn : 0 < n)
    (u : Fin (n - 1) → ℝ) :
    cast
        (congrArg (fun q => Fin q → ℝ)
          (Nat.sub_add_cancel hn))
        (fun j : Fin ((n - 1) + 1) => -Fin.cases 0 u j) =
      chronologicalTimeProfileDisplacementOfPositive hn u := by
  funext j
  rw [rooted_cast_fin_function_apply (Nat.sub_add_cancel hn)]
  rfl

/-- Native-arity rooted-left profiles split into the bridge head and the
translated internal-gap tail. -/
theorem rootedLeftTranslatedTimeProfile_eq_cast_prepend
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) :
    D.rootedLeftTranslatedTimeProfile i timeScale τ =
      cast
        (congrArg
          (fun q => SchwartzMap (Fin q → ℝ) ℂ)
          (Nat.sub_add_cancel i.hn))
        (SCV.prependField
          (A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f
          (SCV.translateSchwartz
            (-(i.leftRealCoordinates τ))
            (A.leftInternalSource i
              (timeScale + D.commonTailStart i)).f)) := by
  simp only [rootedLeftTranslatedTimeProfile, rootedLeftTimeProfile]
  rw [← rooted_cast_prepend_displacement
    i.hn (i.leftRealCoordinates τ)]
  rw [← rooted_cast_translateSchwartz
    (Nat.sub_add_cancel i.hn)]
  congr 1
  exact
    D.rootedLeftBlock_translatedTimeProfile_f i timeScale
      (i.leftRealCoordinates τ)

/-- Native-arity rooted-right profiles split into the bridge head and the
translated internal-gap tail. -/
theorem rootedRightTranslatedTimeProfile_eq_cast_prepend
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) :
    D.rootedRightTranslatedTimeProfile i timeScale τ =
      cast
        (congrArg
          (fun q => SchwartzMap (Fin q → ℝ) ℂ)
          (Nat.sub_add_cancel i.hm))
        (SCV.prependField
          (A.rootedBridgeHead R i
            (timeScale + D.commonTailStart i)).f
          (SCV.translateSchwartz
            (-(i.rightRealCoordinates τ))
            (A.rightInternalSource i
              (timeScale + D.commonTailStart i)).f)) := by
  simp only [rootedRightTranslatedTimeProfile, rootedRightTimeProfile]
  rw [← rooted_cast_prepend_displacement
    i.hm (i.rightRealCoordinates τ)]
  rw [← rooted_cast_translateSchwartz
    (Nat.sub_add_cancel i.hm)]
  congr 1
  exact
    D.rootedRightBlock_translatedTimeProfile_f i timeScale
      (i.rightRealCoordinates τ)

private theorem rooted_cast_cast_symm
    {ι : Sort*}
    {α : ι → Sort*}
    {a b : ι}
    (h : a = b)
    (x : α b) :
    cast (congrArg α h) (cast (congrArg α h.symm) x) = x := by
  subst b
  rfl

private theorem rooted_reindex_axisPairTwoBlockTimeSpatialSource_cast
    {n n' m m' : ℕ}
    (hn : n = n')
    (hm : m = m')
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (t : ℝ) :
    reindexSchwartz
        (d := d)
        (finCongr (congrArg₂ (fun a b => a + b) hn hm))
        (axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t) =
      axisPairTwoBlockTimeSpatialSource n' m'
        (cast
          (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) hn)
          η₁)
        (cast
          (congrArg
            (fun q => SchwartzMap (Section43SpatialSpace d q) ℂ)
            hn)
          χ₁)
        (cast
          (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) hm)
          η₂)
        (cast
          (congrArg
            (fun q => SchwartzMap (Section43SpatialSpace d q) ℂ)
            hm)
          χ₂)
        t := by
  subst n'
  subst m'
  rfl

theorem
    spatialHermiteGeneratorModeOfOS_positiveReal_eq_timeProfiles_of_source_eq
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hleftSource :
      (A.rootedLeftBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.leftRealCoordinates τ)
        (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
          (d := d) i mode)).1 =
        section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.n - 1) + 1)
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.leftRealCoordinates τ) j)
            ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f))
    (hrightSource :
      (A.rootedRightBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.rightRealCoordinates τ)
        (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
          (d := d) i mode)).1 =
        section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.m - 1) + 1)
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.rightRealCoordinates τ) j)
            ((A.rootedRightBlockApproximateIdentity R i).translatedSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f))
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hleft : i.leftRealCoordinates τ ∈ (D.left i).realRegion)
    (hright : i.rightRealCoordinates τ ∈ (D.right i).realRegion) :
    D.spatialHermiteGeneratorModeOfOS i timeScale mode
        (osiiPositiveRealTimeEmbed τ) =
      OS.S (i.n + i.m)
        (ZeroDiagonalSchwartz.ofClassical
          (axisPairTwoBlockTimeSpatialSource i.n i.m
            (D.rootedLeftTranslatedTimeProfile i timeScale τ)
            (leftSpatialHermiteBlock d i mode)
            (D.rootedRightTranslatedTimeProfile i timeScale τ)
            (rightSpatialHermiteBlock d i mode)
            (τ i.bridgeGlobalIndex))) := by
  rw [D.spatialHermiteGeneratorModeOfOS_positiveReal_eq_schwinger
    i timeScale mode τ hbridge hleft hright,
    hleftSource, hrightSource]
  let hn := Nat.sub_add_cancel i.hn
  let hm := Nat.sub_add_cancel i.hm
  have hsource :
      reindexSchwartz
          (d := d)
          (finCongr (congrArg₂ (fun a b => a + b) hn hm))
          (axisPairTwoBlockTimeSpatialSource
            ((i.n - 1) + 1) ((i.m - 1) + 1)
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 (i.leftRealCoordinates τ) j)
              ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
                (A.rootedLeftBlockAnchor i)
                (A.rootedLeftBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i mode)
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 (i.rightRealCoordinates τ) j)
              ((A.rootedRightBlockApproximateIdentity R i).translatedSource
                (A.rootedRightBlockAnchor i)
                (A.rootedRightBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i mode)
            (τ i.bridgeGlobalIndex)) =
        axisPairTwoBlockTimeSpatialSource i.n i.m
          (D.rootedLeftTranslatedTimeProfile i timeScale τ)
          (leftSpatialHermiteBlock d i mode)
          (D.rootedRightTranslatedTimeProfile i timeScale τ)
          (rightSpatialHermiteBlock d i mode)
          (τ i.bridgeGlobalIndex) := by
    rw [rooted_reindex_axisPairTwoBlockTimeSpatialSource_cast
      (d := d) hn hm]
    congr 4
    · rw [rooted_cast_translateSchwartz]
      simp only [rootedLeftTranslatedTimeProfile, rootedLeftTimeProfile]
      rw [rooted_cast_prepend_displacement]
      exact hn
    · rw [
        ReflectedA0BlockContinuousTranslationData.leftHeadSpatialHermiteBlock_eq_cast_leftSpatialHermiteBlock]
      exact
        rooted_cast_cast_symm
          (α := fun q =>
            SchwartzMap (Section43SpatialSpace d q) ℂ)
          hn (leftSpatialHermiteBlock d i mode)
    · rw [rooted_cast_translateSchwartz]
      simp only [rootedRightTranslatedTimeProfile, rootedRightTimeProfile]
      rw [rooted_cast_prepend_displacement]
      exact hm
    · rw [
        ReflectedA0BlockContinuousTranslationData.rightHeadSpatialHermiteBlock_eq_cast_rightSpatialHermiteBlock]
      exact
        rooted_cast_cast_symm
          (α := fun q =>
            SchwartzMap (Section43SpatialSpace d q) ℂ)
          hm (rightSpatialHermiteBlock d i mode)
  exact
    osiiSchwinger_ofClassical_eq_of_reindex_finCongr
      OS (congrArg₂ (fun a b => a + b) hn hm) _ _ hsource

/-- One left chronological neighborhood gives the rooted source formula for
every packet scale and absolute Hermite mode. -/
theorem
    eventually_rootedLeftBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_mode
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ x : Fin (i.n - 1) → ℝ in 𝓝 0,
      ∀ timeScale mode : ℕ,
        (A.rootedLeftBlockTranslatedSpatialSource R i
          (timeScale + D.commonTailStart i) x
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)).1 =
          section43OrderedPullbackTimeSpatialTensorCLM
            d ((i.n - 1) + 1)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i mode)
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 x j)
              ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
                (A.rootedLeftBlockAnchor i)
                (A.rootedLeftBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f) := by
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun p : ℕ × ℕ =>
          (A.rootedLeftBlockSpatialSource R i
            (p.1 + D.commonTailStart i)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i p.2)).1) := by
    obtain ⟨K, hK_compact, hK_positive, hK⟩ :=
      rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales
        A R i
    refine ⟨K, hK_compact, hK_positive, ?_⟩
    intro p q hq
    exact
      hK
        (p.1 + D.commonTailStart i,
          ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i p.2)
        q hq
  filter_upwards
    [eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      (fun p : ℕ × ℕ =>
        A.rootedLeftBlockSpatialSource R i
          (p.1 + D.commonTailStart i)
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i p.2))
      hf] with x hx
  intro timeScale mode
  change
    (localPositiveTimeParameterTranslate
      (A.rootedLeftBlockSpatialSource R i
        (timeScale + D.commonTailStart i)
        (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
          (d := d) i mode))
      (fun a : Fin (i.n - 1) =>
        chronologicalTimeSourceDirection (d := d) a) x).1 = _
  rw [hx (timeScale, mode)]
  change
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun a : Fin (i.n - 1) =>
            chronologicalTimeSourceDirection (d := d) a) x)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.n - 1) + 1)
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)
          ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
            (A.rootedLeftBlockAnchor i)
            (A.rootedLeftBlockAnchor_positive i)
            (timeScale + D.commonTailStart i)).f) =
      _
  exact
    translate_chronologicalSource_orderedPullbackTimeSpatialTensor
      (d := d) (k := i.n - 1) x
      (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
        (d := d) i mode)
      ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
        (timeScale + D.commonTailStart i)).f

/-- One right chronological neighborhood gives the rooted source formula for
every packet scale and absolute Hermite mode. -/
theorem
    eventually_rootedRightBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_mode
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ x : Fin (i.m - 1) → ℝ in 𝓝 0,
      ∀ timeScale mode : ℕ,
        (A.rootedRightBlockTranslatedSpatialSource R i
          (timeScale + D.commonTailStart i) x
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)).1 =
          section43OrderedPullbackTimeSpatialTensorCLM
            d ((i.m - 1) + 1)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i mode)
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 x j)
              ((A.rootedRightBlockApproximateIdentity R i).translatedSource
                (A.rootedRightBlockAnchor i)
                (A.rootedRightBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f) := by
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun p : ℕ × ℕ =>
          (A.rootedRightBlockSpatialSource R i
            (p.1 + D.commonTailStart i)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i p.2)).1) := by
    obtain ⟨K, hK_compact, hK_positive, hK⟩ :=
      rootedRightBlockSpatialSource_uniformCompactSupport_all_scales
        A R i
    refine ⟨K, hK_compact, hK_positive, ?_⟩
    intro p q hq
    exact
      hK
        (p.1 + D.commonTailStart i,
          ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i p.2)
        q hq
  filter_upwards
    [eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      (fun p : ℕ × ℕ =>
        A.rootedRightBlockSpatialSource R i
          (p.1 + D.commonTailStart i)
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i p.2))
      hf] with x hx
  intro timeScale mode
  change
    (localPositiveTimeParameterTranslate
      (A.rootedRightBlockSpatialSource R i
        (timeScale + D.commonTailStart i)
        (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
          (d := d) i mode))
      (fun a : Fin (i.m - 1) =>
        chronologicalTimeSourceDirection (d := d) a) x).1 = _
  rw [hx (timeScale, mode)]
  change
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun a : Fin (i.m - 1) =>
            chronologicalTimeSourceDirection (d := d) a) x)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.m - 1) + 1)
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)
          ((A.rootedRightBlockApproximateIdentity R i).translatedSource
            (A.rootedRightBlockAnchor i)
            (A.rootedRightBlockAnchor_positive i)
            (timeScale + D.commonTailStart i)).f) =
      _
  exact
    translate_chronologicalSource_orderedPullbackTimeSpatialTensor
      (d := d) (k := i.m - 1) x
      (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
        (d := d) i mode)
      ((A.rootedRightBlockApproximateIdentity R i).translatedSource
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
        (timeScale + D.commonTailStart i)).f

/-- A canonical common translation larger than the full time span of the
translated rooted-left profile. -/
noncomputable def rootedLeftTranslatedCommonShift
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) : ℝ :=
  Classical.choose
    (exists_osiiAxisPairCommonShift_gt_leftTimeSpan
      i.hn (D.rootedLeftTranslatedTimeProfile i timeScale τ)
      (by
        simpa [rootedLeftTranslatedTimeProfile] using
          (_root_.OSReconstruction.OSIIChapterV.GeneratorHermiteHilbertFieldFamilyData.hasCompactSupport_translatedTimeProfile
            i.hn (D.rootedLeftTimeProfileNative i timeScale)
            (i.leftRealCoordinates τ))))

theorem rootedLeftTranslatedCommonShift_span
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (τ : Fin k → ℝ) :
    ∀ δ ∈ tsupport
        (D.rootedLeftTranslatedTimeProfile i timeScale τ :
          (Fin i.n → ℝ) → ℂ),
      (section43ScalarDiffCLE i.n).symm δ
          (Fin.rev ⟨0, i.hn⟩) <
        D.rootedLeftTranslatedCommonShift i timeScale τ :=
  (Classical.choose_spec
    (exists_osiiAxisPairCommonShift_gt_leftTimeSpan
      i.hn (D.rootedLeftTranslatedTimeProfile i timeScale τ)
      (by
        simpa [rootedLeftTranslatedTimeProfile] using
          (_root_.OSReconstruction.OSIIChapterV.GeneratorHermiteHilbertFieldFamilyData.hasCompactSupport_translatedTimeProfile
            i.hn (D.rootedLeftTimeProfileNative i timeScale)
            (i.leftRealCoordinates τ))))).2

/-- Once the internal chronological coordinates lie in the common rooted
source neighborhood, the original-OS absolute-Hermite real-edge identity
holds uniformly in packet scale and along the entire positive bridge axis. -/
theorem
    eventually_spatialHermiteGeneratorModeOfOS_positiveBridge_eq_absoluteHermite_uniform_scale_mode
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale : ℕ,
      ∀ hpositive :
        D.RootedTranslatedTimeProfilesPositive i timeScale τ,
      ∀ mode : ℕ,
      ∀ (t : ℝ), ∀ (ht : 0 < t),
      i.leftRealCoordinates τ ∈ (D.left i).realRegion →
      i.rightRealCoordinates τ ∈ (D.right i).realRegion →
        D.spatialHermiteGeneratorModeOfOS i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ t)) =
          generatorSplitAbsoluteSpatialSchwingerCLM
            OS i
            (D.rootedLeftTranslatedTimeProfile i timeScale τ)
            hpositive.1
            (D.rootedRightTranslatedTimeProfile i timeScale τ)
            hpositive.2
            (D.rootedLeftTranslatedCommonShift i timeScale τ)
            t
            ht.le
            (D.rootedLeftTranslatedCommonShift_span i timeScale τ)
            (spatialHermite d (k + 1) (Nat.succ_pos k) mode) := by
  have hleftTendsto :=
    GeneratorHermiteHilbertFieldFamilyData.tendsto_leftRealCoordinates_zero i
  have hrightTendsto :=
    GeneratorHermiteHilbertFieldFamilyData.tendsto_rightRealCoordinates_zero i
  filter_upwards
    [hleftTendsto.eventually
      (D.eventually_rootedLeftBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_mode
        i),
    hrightTendsto.eventually
      (D.eventually_rootedRightBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_mode
        i)]
      with τ hleftSource hrightSource
  intro timeScale hpositive mode t ht hleft hright
  let τt := generatorBridgeVariation i τ t
  have hpositive_t :
      D.RootedTranslatedTimeProfilesPositive i timeScale τt := by
    simpa [τt, RootedTranslatedTimeProfilesPositive,
      rootedLeftTranslatedTimeProfile,
      rootedRightTranslatedTimeProfile]
      using hpositive
  have hleft_t :
      i.leftRealCoordinates τt ∈ (D.left i).realRegion := by
    simpa [τt] using hleft
  have hright_t :
      i.rightRealCoordinates τt ∈ (D.right i).realRegion := by
    simpa [τt] using hright
  have hτt_bridge : τt i.bridgeGlobalIndex = t :=
    generatorBridgeVariation_bridge i τ t
  have htimeProfiles :=
    D.spatialHermiteGeneratorModeOfOS_positiveReal_eq_timeProfiles_of_source_eq
      i timeScale mode τt
      (by simpa [τt] using hleftSource timeScale mode)
      (by simpa [τt] using hrightSource timeScale mode)
      (by rw [hτt_bridge]; exact ht)
      hleft_t hright_t
  rw [hτt_bridge] at htimeProfiles
  rw [htimeProfiles]
  simpa [τt, rootedLeftTranslatedTimeProfile,
    rootedRightTranslatedTimeProfile,
    rootedLeftTranslatedCommonShift]
    using
      (axisPairTwoBlockTimeSpatialSource_schwinger_eq_absoluteHermite
        OS i mode
        (D.rootedLeftTranslatedTimeProfile i timeScale τ)
        hpositive.1
        (D.rootedRightTranslatedTimeProfile i timeScale τ)
        hpositive.2
        (D.rootedLeftTranslatedCommonShift i timeScale τ)
        t ht
        (D.rootedLeftTranslatedCommonShift_span i timeScale τ))

/-- The synchronized rooted-left Hermite field has one polynomial mode
bound, uniform in the common physical packet scale and on compact subsets of
its complex parameter domain. -/
theorem
    exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin (i.n - 1) → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ (D.left i).domain) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (N : ℕ) (z : Fin (i.n - 1) → ℂ), z ∈ K → ∀ mode,
        ‖D.leftSpatialHermiteGeneratorField i N mode z‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin i.n => SchwartzMap (Fin d → ℝ) ℂ)
        (SchwartzMap
          (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :=
    fun _ =>
      cast
        (congrArg
          (fun r =>
            ContinuousMultilinearMap ℂ
              (fun _ : Fin i.n => SchwartzMap (Fin d → ℝ) ℂ)
              (SchwartzMap (Section43SpatialSpace d r) ℂ))
          (Nat.sub_add_cancel i.hn).symm)
        ((section43SpatialSchwartzParticleCLE d i.n).symm.toContinuousLinearMap
          |>.compContinuousMultilinearMap
            (SchwartzMap.productTensorMLM i.n))
  have hΦ :
      ∀ fs : Fin i.n → SchwartzMap (Fin d → ℝ) ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs) := by
    intro fs
    simpa [Φ] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Φ 0 fs) atTop (𝓝 (Φ 0 fs))
        ).isVonNBounded_range ℝ
  let βs : ℕ → Fin i.n → ℕ :=
    fun mode a =>
      GaussianField.productBasisIndices
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
        (i.leftAbsoluteIndex a)
  have hβ :
      ∃ Denc > 0, ∃ q : ℕ, ∀ mode a,
        (βs mode a : ℝ) ≤ Denc * (1 + (mode : ℝ)) ^ q := by
    obtain ⟨Denc, hDenc, q, hbound⟩ :=
      GaussianField.productBasisIndices_polyGrowth
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
    exact
      ⟨Denc, hDenc, q,
        fun mode a => hbound mode (i.leftAbsoluteIndex a)⟩
  obtain ⟨C, hC, q, hbound⟩ :=
    (D.left i).toLocalReflectedA0ContinuousFieldData
      |>.encodedHermite_polyBounded_on_compact
        K hK_compact hK_domain Φ hΦ βs hβ
  refine ⟨C, hC, q, ?_⟩
  intro N z hz mode
  have h :=
    hbound (D.leftCofinalIndex i N) 0 z hz mode
  simpa only [leftSpatialHermiteGeneratorField, Φ, βs,
    ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock] using h

/-- Right-hand analogue of
`exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact`. -/
theorem
    exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin (i.m - 1) → ℂ))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ (D.right i).domain) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (N : ℕ) (z : Fin (i.m - 1) → ℂ), z ∈ K → ∀ mode,
        ‖D.rightSpatialHermiteGeneratorField i N mode z‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin i.m => SchwartzMap (Fin d → ℝ) ℂ)
        (SchwartzMap
          (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :=
    fun _ =>
      cast
        (congrArg
          (fun r =>
            ContinuousMultilinearMap ℂ
              (fun _ : Fin i.m => SchwartzMap (Fin d → ℝ) ℂ)
              (SchwartzMap (Section43SpatialSpace d r) ℂ))
          (Nat.sub_add_cancel i.hm).symm)
        ((section43SpatialSchwartzParticleCLE d i.m).symm.toContinuousLinearMap
          |>.compContinuousMultilinearMap
            (SchwartzMap.productTensorMLM i.m))
  have hΦ :
      ∀ fs : Fin i.m → SchwartzMap (Fin d → ℝ) ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs) := by
    intro fs
    simpa [Φ] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Φ 0 fs) atTop (𝓝 (Φ 0 fs))
        ).isVonNBounded_range ℝ
  let βs : ℕ → Fin i.m → ℕ :=
    fun mode b =>
      GaussianField.productBasisIndices
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
        (i.rightAbsoluteIndex b)
  have hβ :
      ∃ Denc > 0, ∃ q : ℕ, ∀ mode b,
        (βs mode b : ℝ) ≤ Denc * (1 + (mode : ℝ)) ^ q := by
    obtain ⟨Denc, hDenc, q, hbound⟩ :=
      GaussianField.productBasisIndices_polyGrowth
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
    exact
      ⟨Denc, hDenc, q,
        fun mode b => hbound mode (i.rightAbsoluteIndex b)⟩
  obtain ⟨C, hC, q, hbound⟩ :=
    (D.right i).toLocalReflectedA0ContinuousFieldData
      |>.encodedHermite_polyBounded_on_compact
        K hK_compact hK_domain Φ hΦ βs hβ
  refine ⟨C, hC, q, ?_⟩
  intro N z hz mode
  have h :=
    hbound (D.rightCofinalIndex i N) 0 z hz mode
  simpa only [rightSpatialHermiteGeneratorField, Φ, βs,
    ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock] using h

/-- The synchronized rooted-left Hermite field has one polynomial mode
bound, uniform in the common physical packet scale and on compact real
chronological-translation sets. -/
theorem
    exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin (i.n - 1) → ℝ))
    (hK_compact : IsCompact K)
    (hK_real : K ⊆ (D.left i).realRegion) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (N : ℕ) (x : Fin (i.n - 1) → ℝ), x ∈ K → ∀ mode,
        ‖D.leftSpatialHermiteGeneratorField i N mode
            (fun a => (x a : ℂ))‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin i.n => SchwartzMap (Fin d → ℝ) ℂ)
        (SchwartzMap
          (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :=
    fun _ =>
      cast
        (congrArg
          (fun r =>
            ContinuousMultilinearMap ℂ
              (fun _ : Fin i.n => SchwartzMap (Fin d → ℝ) ℂ)
              (SchwartzMap (Section43SpatialSpace d r) ℂ))
          (Nat.sub_add_cancel i.hn).symm)
        ((section43SpatialSchwartzParticleCLE d i.n).symm.toContinuousLinearMap
          |>.compContinuousMultilinearMap
            (SchwartzMap.productTensorMLM i.n))
  have hΦ :
      ∀ fs : Fin i.n → SchwartzMap (Fin d → ℝ) ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs) := by
    intro fs
    simpa [Φ] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Φ 0 fs) atTop (𝓝 (Φ 0 fs))
        ).isVonNBounded_range ℝ
  let βs : ℕ → Fin i.n → ℕ :=
    fun mode a =>
      GaussianField.productBasisIndices
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
        (i.leftAbsoluteIndex a)
  have hβ :
      ∃ Denc > 0, ∃ q : ℕ, ∀ mode a,
        (βs mode a : ℝ) ≤ Denc * (1 + (mode : ℝ)) ^ q := by
    obtain ⟨Denc, hDenc, q, hbound⟩ :=
      GaussianField.productBasisIndices_polyGrowth
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
    exact
      ⟨Denc, hDenc, q,
        fun mode a => hbound mode (i.leftAbsoluteIndex a)⟩
  obtain ⟨C, hC, q, hbound⟩ :=
    (D.left i).translated_encodedHermite_polyBounded_on_compact
      K hK_compact hK_real Φ hΦ βs hβ
  refine ⟨C, hC, q, ?_⟩
  intro N x hx mode
  rw [leftSpatialHermiteGeneratorField]
  rw [(D.left i).realEdge
    (D.leftCofinalIndex i N)
    (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
      (d := d) i mode)
    x (hK_real hx)]
  have h :=
    hbound (D.leftCofinalIndex i N) 0 x hx mode
  simpa only [Φ, βs,
    ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock] using h

/-- Right-hand analogue of
`exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_compact`. -/
theorem
    exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin (i.m - 1) → ℝ))
    (hK_compact : IsCompact K)
    (hK_real : K ⊆ (D.right i).realRegion) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (N : ℕ) (x : Fin (i.m - 1) → ℝ), x ∈ K → ∀ mode,
        ‖D.rightSpatialHermiteGeneratorField i N mode
            (fun b => (x b : ℂ))‖ ≤
          C * (1 + (mode : ℝ)) ^ q := by
  let Φ : ℕ →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin i.m => SchwartzMap (Fin d → ℝ) ℂ)
        (SchwartzMap
          (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :=
    fun _ =>
      cast
        (congrArg
          (fun r =>
            ContinuousMultilinearMap ℂ
              (fun _ : Fin i.m => SchwartzMap (Fin d → ℝ) ℂ)
              (SchwartzMap (Section43SpatialSpace d r) ℂ))
          (Nat.sub_add_cancel i.hm).symm)
        ((section43SpatialSchwartzParticleCLE d i.m).symm.toContinuousLinearMap
          |>.compContinuousMultilinearMap
            (SchwartzMap.productTensorMLM i.m))
  have hΦ :
      ∀ fs : Fin i.m → SchwartzMap (Fin d → ℝ) ℂ,
        Bornology.IsVonNBounded ℝ
          (Set.range fun level => Φ level fs) := by
    intro fs
    simpa [Φ] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Φ 0 fs) atTop (𝓝 (Φ 0 fs))
        ).isVonNBounded_range ℝ
  let βs : ℕ → Fin i.m → ℕ :=
    fun mode b =>
      GaussianField.productBasisIndices
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k) mode
        (i.rightAbsoluteIndex b)
  have hβ :
      ∃ Denc > 0, ∃ q : ℕ, ∀ mode b,
        (βs mode b : ℝ) ≤ Denc * (1 + (mode : ℝ)) ^ q := by
    obtain ⟨Denc, hDenc, q, hbound⟩ :=
      GaussianField.productBasisIndices_polyGrowth
        (D := Fin d → ℝ) (k + 1) (Nat.succ_pos k)
    exact
      ⟨Denc, hDenc, q,
        fun mode b => hbound mode (i.rightAbsoluteIndex b)⟩
  obtain ⟨C, hC, q, hbound⟩ :=
    (D.right i).translated_encodedHermite_polyBounded_on_compact
      K hK_compact hK_real Φ hΦ βs hβ
  refine ⟨C, hC, q, ?_⟩
  intro N x hx mode
  rw [rightSpatialHermiteGeneratorField]
  rw [(D.right i).realEdge
    (D.rightCofinalIndex i N)
    (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
      (d := d) i mode)
    x (hK_real hx)]
  have h :=
    hbound (D.rightCofinalIndex i N) 0 x hx mode
  simpa only [Φ, βs,
    ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock] using h

/-- A compact set of real generator coordinates gives one scale-uniform
polynomial Hermite bound for the genuine original-OS generator mode. -/
theorem
    exists_spatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin k → ℝ))
    (hK_compact : IsCompact K)
    (hleft :
      Set.MapsTo i.leftRealCoordinates K (D.left i).realRegion)
    (hright :
      Set.MapsTo i.rightRealCoordinates K (D.right i).realRegion) :
    ∃ C > 0, ∃ q : ℕ,
      ∀ (N mode : ℕ) (τ : Fin k → ℝ), τ ∈ K →
        0 < τ i.bridgeGlobalIndex →
          ‖D.spatialHermiteGeneratorModeOfOS i N mode
              (osiiPositiveRealTimeEmbed τ)‖ ≤
            C * (1 + (mode : ℝ)) ^ q := by
  let KL : Set (Fin (i.n - 1) → ℝ) :=
    i.leftRealCoordinates '' K
  let KR : Set (Fin (i.m - 1) → ℝ) :=
    i.rightRealCoordinates '' K
  have hleftContinuous : Continuous i.leftRealCoordinates := by
    unfold GeneratorIndex.leftRealCoordinates
    fun_prop
  have hrightContinuous : Continuous i.rightRealCoordinates := by
    unfold GeneratorIndex.rightRealCoordinates
    fun_prop
  have hKL_compact : IsCompact KL :=
    hK_compact.image hleftContinuous
  have hKR_compact : IsCompact KR :=
    hK_compact.image hrightContinuous
  have hKL_real : KL ⊆ (D.left i).realRegion := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact hleft hτ
  have hKR_real : KR ⊆ (D.right i).realRegion := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact hright hτ
  obtain ⟨CL, hCL, qL, hleftBound⟩ :=
    D.exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_compact
      i KL hKL_compact hKL_real
  obtain ⟨CR, hCR, qR, hrightBound⟩ :=
    D.exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_compact
      i KR hKR_compact hKR_real
  refine ⟨2 * CL * CR, by positivity, qL + qR, ?_⟩
  intro N mode τ hτ hbridge
  let u : OSHilbertSpace OS :=
    D.leftSpatialHermiteGeneratorField i N mode
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)))
  let v : OSHilbertSpace OS :=
    D.rightSpatialHermiteGeneratorField i N mode
      (fun b =>
        osiiPositiveRealTimeEmbed τ
          (i.rightGlobalIndex b))
  have hu :
      ‖u‖ ≤ CL * (1 + (mode : ℝ)) ^ qL := by
    simpa [u, GeneratorIndex.leftRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      hleftBound N (i.leftRealCoordinates τ) ⟨τ, hτ, rfl⟩ mode
  have hv :
      ‖v‖ ≤ CR * (1 + (mode : ℝ)) ^ qR := by
    simpa [v, GeneratorIndex.rightRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      hrightBound N (i.rightRealCoordinates τ) ⟨τ, hτ, rfl⟩ mode
  have hmode_eq :
      D.spatialHermiteGeneratorModeOfOS i N mode
          (osiiPositiveRealTimeEmbed τ) =
        @inner ℂ (OSHilbertSpace OS) _ u
          ((osiiOriginalOSHilbertComplex OS
            (osiiPositiveRealTimeEmbed τ i.bridgeGlobalIndex)) v) := by
    rw [spatialHermiteGeneratorModeOfOS,
      osiiSemigroupMixedHilbertPairing,
      bridgedMixedHilbertPairing,
      GeneratorIndex.splitCoordinatesCLM_fst]
    have hleftCoordinates :
        star (i.splitCoordinatesCLM
          (osiiPositiveRealTimeEmbed τ)).2.1 =
          fun a =>
            -star (osiiPositiveRealTimeEmbed τ
              (i.leftGlobalIndex a)) := by
      ext a
      simp
    have hrightCoordinates :
        (i.splitCoordinatesCLM
          (osiiPositiveRealTimeEmbed τ)).2.2 =
          fun b =>
            osiiPositiveRealTimeEmbed τ
              (i.rightGlobalIndex b) := by
      ext b
      rfl
    rw [hleftCoordinates, hrightCoordinates]
  rw [hmode_eq]
  have hsemigroup :
      ‖osiiOriginalOSHilbertComplex OS
          (osiiPositiveRealTimeEmbed τ i.bridgeGlobalIndex)‖ ≤ 2 := by
    apply osiiOriginalOSHilbertComplex_norm_le OS
    simpa [osiiPositiveRealTimeEmbed] using hbridge
  calc
    ‖@inner ℂ (OSHilbertSpace OS) _ u
        ((osiiOriginalOSHilbertComplex OS
          (osiiPositiveRealTimeEmbed τ i.bridgeGlobalIndex)) v)‖
        ≤ ‖u‖ *
            ‖(osiiOriginalOSHilbertComplex OS
              (osiiPositiveRealTimeEmbed τ i.bridgeGlobalIndex)) v‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ *
          (‖osiiOriginalOSHilbertComplex OS
              (osiiPositiveRealTimeEmbed τ i.bridgeGlobalIndex)‖ * ‖v‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤
        (CL * (1 + (mode : ℝ)) ^ qL) *
          (2 * (CR * (1 + (mode : ℝ)) ^ qR)) := by
      gcongr
    _ =
        (2 * CL * CR) *
          (1 + (mode : ℝ)) ^ (qL + qR) := by
      rw [pow_add]
      ring

/-- The finite exact-rooted generator shell in the split's block-global
spatial Hermite chart. -/
noncomputable def spatialHermiteGeneratorFiniteShellOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d (k + 1) :=
  ∑ mode ∈ Finset.range shell,
    (D.spatialHermiteGeneratorModeOfOS
      i timeScale mode z) •
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode

@[simp]
theorem spatialHermiteGeneratorFiniteShellOfOS_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.spatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell z F =
      ∑ mode ∈ Finset.range shell,
        D.spatialHermiteGeneratorModeOfOS
            i timeScale mode z *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F := by
  simp [spatialHermiteGeneratorFiniteShellOfOS]

/-- On one internal chronological neighborhood, every rooted finite shell
has its exact split absolute-spatial source formula along the whole positive
bridge axis, uniformly in packet scale and without an extra OS hypothesis. -/
theorem
    eventually_spatialHermiteGeneratorFiniteShellOfOS_positiveBridge_eq_absolutePartialSum_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale : ℕ,
      ∀ hpositive :
        D.RootedTranslatedTimeProfilesPositive i timeScale τ,
      i.leftRealCoordinates τ ∈ (D.left i).realRegion →
      i.rightRealCoordinates τ ∈ (D.right i).realRegion →
      ∀ (t : ℝ), ∀ (ht : 0 < t),
      ∀ (shell : ℕ)
        (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
        D.spatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ t)) F =
          generatorSplitAbsoluteSpatialSchwingerCLM
            OS i
            (D.rootedLeftTranslatedTimeProfile i timeScale τ)
            hpositive.1
            (D.rootedRightTranslatedTimeProfile i timeScale τ)
            hpositive.2
            (D.rootedLeftTranslatedCommonShift i timeScale τ)
            t
            ht.le
            (D.rootedLeftTranslatedCommonShift_span i timeScale τ)
            (spatialHermitePartialSum
              d (k + 1) (Nat.succ_pos k) shell
              (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
                (d := d) i F)) := by
  filter_upwards
    [D.eventually_spatialHermiteGeneratorModeOfOS_positiveBridge_eq_absoluteHermite_uniform_scale_mode
      i]
      with τ hmode
  intro timeScale hpositive hleft hright t ht shell F
  let G :=
    GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
      (d := d) i F
  let L :=
    generatorSplitAbsoluteSpatialSchwingerCLM
      OS i
      (D.rootedLeftTranslatedTimeProfile i timeScale τ)
      hpositive.1
      (D.rootedRightTranslatedTimeProfile i timeScale τ)
      hpositive.2
      (D.rootedLeftTranslatedCommonShift i timeScale τ)
      t ht.le
      (D.rootedLeftTranslatedCommonShift_span i timeScale τ)
  rw [D.spatialHermiteGeneratorFiniteShellOfOS_apply]
  simp_rw [hmode timeScale hpositive _ t ht hleft hright]
  change
    (∑ mode ∈ Finset.range shell,
        L (spatialHermite d (k + 1) (Nat.succ_pos k) mode) *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F) =
      L (spatialHermitePartialSum
        d (k + 1) (Nat.succ_pos k) shell G)
  calc
    (∑ mode ∈ Finset.range shell,
        L (spatialHermite d (k + 1) (Nat.succ_pos k) mode) *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F) =
      ∑ mode ∈ Finset.range shell,
        GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode F *
          L (spatialHermite d (k + 1) (Nat.succ_pos k) mode) := by
            apply Finset.sum_congr rfl
            intro mode _hmode_mem
            exact mul_comm _ _
    _ =
      L (∑ mode ∈ Finset.range shell,
        GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
              (d := d) i mode F •
          spatialHermite d (k + 1) (Nat.succ_pos k) mode) := by
            simp only [map_sum, map_smul, smul_eq_mul]
    _ =
      L (spatialHermitePartialSum
        d (k + 1) (Nat.succ_pos k) shell G) := by
            congr 1

/-- The rooted finite shells converge along the whole positive bridge axis
on one internal chronological neighborhood independent of packet scale,
using only the original OS axioms. -/
theorem
    eventually_tendsto_spatialHermiteGeneratorFiniteShellOfOS_positiveBridge_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale : ℕ,
      ∀ hpositive :
        D.RootedTranslatedTimeProfilesPositive i timeScale τ,
      i.leftRealCoordinates τ ∈ (D.left i).realRegion →
      i.rightRealCoordinates τ ∈ (D.right i).realRegion →
      ∀ (t : ℝ), ∀ (ht : 0 < t),
      ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
        Tendsto
          (fun shell =>
            D.spatialHermiteGeneratorFiniteShellOfOS
              i timeScale shell
              (osiiPositiveRealTimeEmbed
                (generatorBridgeVariation i τ t)) F)
          atTop
          (𝓝
            (generatorSplitAbsoluteSpatialSchwingerCLM
              OS i
              (D.rootedLeftTranslatedTimeProfile i timeScale τ)
              hpositive.1
              (D.rootedRightTranslatedTimeProfile i timeScale τ)
              hpositive.2
              (D.rootedLeftTranslatedCommonShift i timeScale τ)
              t
              ht.le
              (D.rootedLeftTranslatedCommonShift_span i timeScale τ)
              (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
                (d := d) i F))) := by
  filter_upwards
    [D.eventually_spatialHermiteGeneratorFiniteShellOfOS_positiveBridge_eq_absolutePartialSum_uniform_scale
      i]
      with τ hshell
  intro timeScale hpositive hleft hright t ht F
  let G :=
    GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
      (d := d) i F
  let L :=
    generatorSplitAbsoluteSpatialSchwingerCLM
      OS i
      (D.rootedLeftTranslatedTimeProfile i timeScale τ)
      hpositive.1
      (D.rootedRightTranslatedTimeProfile i timeScale τ)
      hpositive.2
      (D.rootedLeftTranslatedCommonShift i timeScale τ)
      t ht.le
      (D.rootedLeftTranslatedCommonShift_span i timeScale τ)
  have hprojector :=
    tendsto_spatialHermitePartialSum
      d (k + 1) (Nat.succ_pos k) G
  have hL :
      Tendsto (fun H => L H) (𝓝 G) (𝓝 (L G)) :=
    L.continuous.continuousAt
  change Tendsto
    (fun shell =>
      D.spatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell
        (osiiPositiveRealTimeEmbed
          (generatorBridgeVariation i τ t)) F)
    atTop (𝓝 (L G))
  rw [show
      (fun shell =>
        D.spatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell
          (osiiPositiveRealTimeEmbed
            (generatorBridgeVariation i τ t)) F) =
        fun shell =>
          L (spatialHermitePartialSum
            d (k + 1) (Nat.succ_pos k) shell G) by
      funext shell
      exact hshell timeScale hpositive hleft hright t ht shell F]
  exact hL.comp hprojector

/-- Every exact-rooted finite Hermite shell is bounded uniformly in the
common packet scale and shell cutoff on a compact positive-real generator
region under the original OS axioms. -/
theorem
    exists_spatialHermiteGeneratorFiniteShellOfOS_apply_norm_bound_on_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (Fin k → ℝ))
    (hK_compact : IsCompact K)
    (hleft :
      Set.MapsTo i.leftRealCoordinates K (D.left i).realRegion)
    (hright :
      Set.MapsTo i.rightRealCoordinates K (D.right i).realRegion)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ∃ M : ℝ,
      ∀ (timeScale shell : ℕ) (τ : Fin k → ℝ), τ ∈ K →
        0 < τ i.bridgeGlobalIndex →
          ‖D.spatialHermiteGeneratorFiniteShellOfOS
              i timeScale shell
              (osiiPositiveRealTimeEmbed τ) F‖ ≤ M := by
  obtain ⟨C, hC, q, hmode⟩ :=
    D.exists_spatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_compact
      i K hK_compact hleft hright
  let coefficient : ℕ → ℂ :=
    fun mode =>
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F
  let majorant : ℕ → ℝ :=
    fun mode => ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q
  have hmajorant : Summable majorant := by
    simpa [majorant, coefficient,
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM]
      using
        (summable_norm_coefficient_mul_weight q
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F))
  refine ⟨C * ∑' mode, majorant mode, ?_⟩
  intro timeScale shell τ hτ hbridge
  rw [D.spatialHermiteGeneratorFiniteShellOfOS_apply]
  calc
    ‖∑ mode ∈ Finset.range shell,
        D.spatialHermiteGeneratorModeOfOS
            i timeScale mode (osiiPositiveRealTimeEmbed τ) *
          coefficient mode‖
        ≤ ∑ mode ∈ Finset.range shell,
            ‖D.spatialHermiteGeneratorModeOfOS
                i timeScale mode (osiiPositiveRealTimeEmbed τ) *
              coefficient mode‖ := norm_sum_le _ _
    _ ≤ ∑ mode ∈ Finset.range shell,
          (C * (1 + (mode : ℝ)) ^ q) * ‖coefficient mode‖ := by
          apply Finset.sum_le_sum
          intro mode hmode_mem
          rw [norm_mul]
          exact
            mul_le_mul_of_nonneg_right
              (hmode timeScale mode τ hτ hbridge)
              (norm_nonneg _)
    _ = C * ∑ mode ∈ Finset.range shell, majorant mode := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mode hmode_mem
          simp only [majorant]
          ring
    _ ≤ C * ∑' mode, majorant mode := by
          exact
            mul_le_mul_of_nonneg_left
              (hmajorant.sum_le_tsum
                (Finset.range shell)
                (fun mode hmode_mem => by
                  exact mul_nonneg (norm_nonneg _)
                    (pow_nonneg (by positivity) q)))
              hC.le

/-- Along the positive bridge axis, a finite exact-rooted shell is
continuous. The synchronized left and right Hilbert vectors remain fixed;
only the genuine original-OS time semigroup varies. -/
theorem continuousOn_spatialHermiteGeneratorFiniteShellOfOS_bridge
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (τ : Fin k → ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ContinuousOn
      (fun t : ℝ =>
        D.spatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell
          (osiiPositiveRealTimeEmbed
            (generatorBridgeVariation i τ t)) F)
      (Set.Ioi 0) := by
  rw [show
      (fun t : ℝ =>
        D.spatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell
          (osiiPositiveRealTimeEmbed
            (generatorBridgeVariation i τ t)) F) =
        fun t : ℝ =>
          ∑ mode ∈ Finset.range shell,
            D.spatialHermiteGeneratorModeOfOS
                i timeScale mode
                (osiiPositiveRealTimeEmbed
                  (generatorBridgeVariation i τ t)) *
              GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
                (d := d) i mode F by
      funext t
      exact D.spatialHermiteGeneratorFiniteShellOfOS_apply
        i timeScale shell
        (osiiPositiveRealTimeEmbed
          (generatorBridgeVariation i τ t)) F]
  refine continuousOn_finset_sum (Finset.range shell) ?_
  intro mode hmode
  let leftVector : OSHilbertSpace OS :=
    D.leftSpatialHermiteGeneratorField i timeScale mode
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)))
  let rightVector : OSHilbertSpace OS :=
    D.rightSpatialHermiteGeneratorField i timeScale mode
      (fun b =>
        osiiPositiveRealTimeEmbed τ
          (i.rightGlobalIndex b))
  have hsemigroup :
      ContinuousOn
        (fun t : ℝ =>
          osiiOriginalOSHilbertComplex OS (t : ℂ) rightVector)
        (Set.Ioi 0) := by
    exact
      (continuousOn_osiiOriginalOSHilbertComplex_apply OS rightVector).comp
        Complex.continuous_ofReal.continuousOn
        (by
          intro t ht
          simpa using ht)
  have hmodeContinuous :
      ContinuousOn
        (fun t : ℝ =>
          D.spatialHermiteGeneratorModeOfOS
            i timeScale mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ t)))
        (Set.Ioi 0) := by
    simpa [spatialHermiteGeneratorModeOfOS_apply,
      leftVector, rightVector, osiiPositiveRealTimeEmbed] using
        (continuous_const.continuousOn.inner hsemigroup)
  exact hmodeContinuous.mul continuous_const.continuousOn

/-- The middle convolution root used to smear the semigroup bridge at the
same physical packet scale as the synchronized rooted block fields. -/
noncomputable def semigroupBridgeRootWeight
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    SchwartzMap ℝ ℂ :=
  (A.rootedBridgeHead R i (timeScale + D.commonTailStart i)).f

@[simp]
theorem semigroupBridgeRootWeight_apply
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (t : ℝ) :
    D.semigroupBridgeRootWeight i timeScale t =
      (A.rootedBridgeHead R i
        (timeScale + D.commonTailStart i)).f t := rfl

theorem semigroupBridgeRootWeight_nonnegative
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (t : ℝ) :
    0 ≤ (D.semigroupBridgeRootWeight i timeScale t).re :=
  A.rootedBridgeHead_nonnegative R i
    (timeScale + D.commonTailStart i) t

theorem semigroupBridgeRootWeight_real
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (t : ℝ) :
    (D.semigroupBridgeRootWeight i timeScale t).im = 0 :=
  A.rootedBridgeHead_real R i
    (timeScale + D.commonTailStart i) t

theorem semigroupBridgeRootWeight_integral_one
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    ∫ t : ℝ, D.semigroupBridgeRootWeight i timeScale t = 1 :=
  A.rootedBridgeHead_integral_one R i
    (timeScale + D.commonTailStart i)

theorem semigroupBridgeRootWeight_integral_norm_one
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ) :
    ∫ t : ℝ, ‖D.semigroupBridgeRootWeight i timeScale t‖ = 1 := by
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  have hnorm_re : ∀ t : ℝ, ‖weight t‖ = (weight t).re := by
    intro t
    rw [← Complex.re_eq_norm.mpr]
    exact
      ⟨D.semigroupBridgeRootWeight_nonnegative i timeScale t,
        (D.semigroupBridgeRootWeight_real i timeScale t).symm⟩
  simp_rw [show
      ∀ t : ℝ,
        ‖D.semigroupBridgeRootWeight i timeScale t‖ =
          (D.semigroupBridgeRootWeight i timeScale t).re by
    simpa [weight] using hnorm_re]
  rw [show
      (fun t : ℝ =>
        (D.semigroupBridgeRootWeight i timeScale t).re) =
      (fun t : ℝ =>
        RCLike.re (D.semigroupBridgeRootWeight i timeScale t)) from rfl]
  rw [integral_re
    (SchwartzMap.integrable
      (D.semigroupBridgeRootWeight i timeScale))]
  have hreal :=
    congrArg Complex.re
      (D.semigroupBridgeRootWeight_integral_one i timeScale)
  simpa using hreal

/-- All synchronized middle roots lie in one compact subset of the positive
bridge axis. -/
theorem exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∃ J : Set ℝ,
      IsCompact J ∧
        J ⊆ Set.Ioi 0 ∧
          ∀ timeScale,
            tsupport
                (D.semigroupBridgeRootWeight i timeScale : ℝ → ℂ) ⊆
              J := by
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_range_of_tendsto I.radius I.radius_tendsto
      ).subset_closedBall (0 : ℝ)
  let center : ℝ := anchor i.bridgeGlobalIndex / 3
  let radiusBound : ℝ := |R0| + 1
  let J : Set ℝ :=
    Metric.closedBall center radiusBound ∩ Set.Ici center
  have hcenter : 0 < center := by
    dsimp [center]
    exact div_pos (A.anchor_positive i.bridgeGlobalIndex) (by positivity)
  have hJ_compact : IsCompact J := by
    dsimp [J]
    exact
      (isCompact_closedBall center radiusBound).inter_right isClosed_Ici
  refine ⟨J, hJ_compact, ?_, ?_⟩
  · intro t ht
    exact lt_of_lt_of_le hcenter ht.2
  · intro timeScale
    refine closure_minimal ?_ hJ_compact.isClosed
    intro t ht
    let physicalScale := timeScale + D.commonTailStart i
    have hroot :
        t + -center ∈
          Function.support
            ((R.root
              (physicalScale + A.carrierData.tailStart)
              i.bridgeGlobalIndex).f : ℝ → ℂ) := by
      simpa [Function.mem_support, semigroupBridgeRootWeight,
        rootedBridgeHead, center,
        section43CompactPositiveTimeSource1D_translateRight,
        section43TranslateSchwartzReal_apply, physicalScale] using ht
    have hrange :
        I.radius (physicalScale + A.carrierData.tailStart) ∈
          Set.range I.radius :=
      ⟨physicalScale + A.carrierData.tailStart, rfl⟩
    have hradius_abs :
        |I.radius (physicalScale + A.carrierData.tailStart)| ≤ R0 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hR0 hrange
    have hradius :
        I.radius (physicalScale + A.carrierData.tailStart) ≤
          radiusBound := by
      calc
        I.radius (physicalScale + A.carrierData.tailStart) ≤
            |I.radius (physicalScale + A.carrierData.tailStart)| :=
          le_abs_self _
        _ ≤ R0 := hradius_abs
        _ ≤ |R0| := le_abs_self _
        _ ≤ radiusBound := by dsimp [radiusBound]; linarith
    have hroot_ball :=
      R.root_support
        (physicalScale + A.carrierData.tailStart)
        i.bridgeGlobalIndex hroot
    have hroot_positive :
        0 < t + -center :=
      (R.root
        (physicalScale + A.carrierData.tailStart)
        i.bridgeGlobalIndex).positive
          (subset_tsupport _ hroot)
    constructor
    · rw [Metric.mem_closedBall, Real.dist_eq]
      have hdist :
          |t - center| <
            I.radius (physicalScale + A.carrierData.tailStart) := by
        simpa [Metric.mem_ball, Real.dist_eq, sub_eq_add_neg] using
          hroot_ball
      exact (le_of_lt hdist).trans hradius
    · exact (le_of_lt (by linarith : center < t))

end RootedA0BlockContinuousTranslationData

namespace RootedA0BlockRealTraceCauchyData

end RootedA0BlockRealTraceCauchyData

namespace RootedA0BlockRealTraceGramLimitData

end RootedA0BlockRealTraceGramLimitData

namespace RootedA0BlockRealTraceGramKernelData

end RootedA0BlockRealTraceGramKernelData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
