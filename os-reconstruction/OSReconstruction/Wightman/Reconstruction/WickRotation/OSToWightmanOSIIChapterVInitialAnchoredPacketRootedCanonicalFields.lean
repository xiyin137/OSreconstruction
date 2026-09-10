/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedSpatialCanonicalField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedHilbertGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchyContinuation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedCauchyContinuation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedA0TranslatedFields














noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- A nontrivial left block has the translated-canonical arity expected by
the q-indexed field package. -/
theorem rootedLeftNontrivialBlockArity_eq
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.n = q + 2) :
    i.n - 1 + 1 = (q + 1) + 1 := by
  omega

/-- Transport the rooted-left approximate identity, anchor, and positivity
proof together across the nontrivial block arity equality.  Moving this
dependent package as one object keeps the anchor proof aligned with the
transported anchor. -/
noncomputable def rootedLeftNontrivialCanonicalInput
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.n = q + 2) :
    Section43ProductTimeApproximateIdentity ((q + 1) + 1) ×
      {tau' : Fin ((q + 1) + 1) → ℝ //
        tau' ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)} :=
  let h := rootedLeftNontrivialBlockArity_eq i hi
  h ▸
    ((A.rootedLeftBlockApproximateIdentity R i,
      ⟨A.rootedLeftBlockAnchor i,
        A.rootedLeftBlockAnchor_positive i⟩) :
      Section43ProductTimeApproximateIdentity (i.n - 1 + 1) ×
        {tau' : Fin (i.n - 1 + 1) → ℝ //
          tau' ∈ section43TimeStrictPositiveRegion (i.n - 1 + 1)})

/-- Right-block analogue of rootedLeftNontrivialBlockArity_eq. -/
theorem rootedRightNontrivialBlockArity_eq
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.m = q + 2) :
    i.m - 1 + 1 = (q + 1) + 1 := by
  omega

/-- Transport the rooted-right approximate identity and anchor data across
the nontrivial block arity equality. -/
noncomputable def rootedRightNontrivialCanonicalInput
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.m = q + 2) :
    Section43ProductTimeApproximateIdentity ((q + 1) + 1) ×
      {tau' : Fin ((q + 1) + 1) → ℝ //
        tau' ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)} :=
  let h := rootedRightNontrivialBlockArity_eq i hi
  h ▸
    ((A.rootedRightBlockApproximateIdentity R i,
      ⟨A.rootedRightBlockAnchor i,
        A.rootedRightBlockAnchor_positive i⟩) :
      Section43ProductTimeApproximateIdentity (i.m - 1 + 1) ×
        {tau' : Fin (i.m - 1 + 1) → ℝ //
          tau' ∈ section43TimeStrictPositiveRegion (i.m - 1 + 1)})

/-- The retained translated-canonical witness for a nontrivial rooted left
block.  Naming this choice keeps its diagonal Cauchy/Taylor provenance
available after the rooted constructor packages only the holomorphic field. -/
noncomputable def rootedLeftNontrivialTranslatedSpatialCanonicalFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.n = q + 2) :
    let P := A.rootedLeftNontrivialCanonicalInput R i hi
    TranslatedSpatialCanonicalFieldData (q := q) L OS
      P.1 P.2.1 P.2.2 :=
  let P := A.rootedLeftNontrivialCanonicalInput R i hi
  Classical.choice
    (nonempty_translatedSpatialCanonicalFieldData
      (q := q) L OS H P.1 P.2.1 P.2.2)

/-- Right-block analogue of the retained nontrivial left canonical choice. -/
noncomputable def rootedRightNontrivialTranslatedSpatialCanonicalFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.m = q + 2) :
    let P := A.rootedRightNontrivialCanonicalInput R i hi
    TranslatedSpatialCanonicalFieldData (q := q) L OS
      P.1 P.2.1 P.2.2 :=
  let P := A.rootedRightNontrivialCanonicalInput R i hi
  Classical.choice
    (nonempty_translatedSpatialCanonicalFieldData
      (q := q) L OS H P.1 P.2.1 P.2.2)

/-- The named one-particle predecessor retained by the canonical rooted-left
field constructor.  Naming the choice preserves endpoint source provenance
for the equation-`(6.21)` density induction. -/
noncomputable def rootedLeftOneParticleTranslatedMixedDeltaPredecessorData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (m : Nat) (hn : 1 <= 1) (hm : 1 <= m)
    (hnm : k = 1 + m - 1) :
    let i : GeneratorIndex k := ⟨1, m, hn, hm, hnm⟩
    OneParticleTranslatedMixedDeltaPredecessorData
      L OS (A.rootedLeftBlockApproximateIdentity R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i) :=
  Classical.choice
    (L.exists_oneParticleTranslatedMixedDeltaPredecessorData H)

/-- Right endpoint form of the named canonical one-particle predecessor. -/
noncomputable def rootedRightOneParticleTranslatedMixedDeltaPredecessorData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (n : Nat) (hn : 1 <= n) (hm : 1 <= 1)
    (hnm : k = n + 1 - 1) :
    let i : GeneratorIndex k := ⟨n, 1, hn, hm, hnm⟩
    OneParticleTranslatedMixedDeltaPredecessorData
      L OS (A.rootedRightBlockApproximateIdentity R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i) :=
  Classical.choice
    (L.exists_oneParticleTranslatedMixedDeltaPredecessorData H)

/-- Canonical compact-edge choice for one rooted left block, retaining the
tail index together with the holomorphic translated field it produces. -/
noncomputable def rootedLeftBlockHolomorphicTranslationFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Σ N0 : ℕ,
      LocalReflectedA0HolomorphicTranslationFieldData
        OS ((i.n - 1) + 1) (i.n - 1)
        (fun N x χ =>
          A.rootedLeftBlockTranslatedSpatialSource R i
            (N + N0) x χ) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : n = 1
  · subst n
    let i : GeneratorIndex k := ⟨1, m, hn, hm, hnm⟩
    let D := A.rootedLeftOneParticleTranslatedMixedDeltaPredecessorData
      L OS H R m hn hm hnm
    exact
      ⟨D.tailStart,
        D.toHolomorphicTranslationFieldData.congrTranslatedSource (by
          intro N x χ
          rfl)⟩
  · cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
        let D :=
          A.rootedLeftNontrivialTranslatedSpatialCanonicalFieldData
            L OS H R i rfl
        exact
          ⟨D.predecessor.tailStart,
            D.toHolomorphicTranslationFieldData.congrTranslatedSource (by
              intro N x χ
              rfl)⟩

/-- Canonical compact-edge choice for one rooted right block, retaining the
tail index together with the holomorphic translated field it produces. -/
noncomputable def rootedRightBlockHolomorphicTranslationFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Σ N0 : ℕ,
      LocalReflectedA0HolomorphicTranslationFieldData
        OS ((i.m - 1) + 1) (i.m - 1)
        (fun N x χ =>
          A.rootedRightBlockTranslatedSpatialSource R i
            (N + N0) x χ) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : m = 1
  · subst m
    let i : GeneratorIndex k := ⟨n, 1, hn, hm, hnm⟩
    let D := A.rootedRightOneParticleTranslatedMixedDeltaPredecessorData
      L OS H R n hn hm hnm
    exact
      ⟨D.tailStart,
        D.toHolomorphicTranslationFieldData.congrTranslatedSource (by
          intro N x χ
          rfl)⟩
  · cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
        let D :=
          A.rootedRightNontrivialTranslatedSpatialCanonicalFieldData
            L OS H R i rfl
        exact
          ⟨D.predecessor.tailStart,
            D.toHolomorphicTranslationFieldData.congrTranslatedSource (by
              intro N x χ
              rfl)⟩

/-- Canonical rooted block fields with their finite-scale holomorphy
retained. -/
structure RootedA0BlockHolomorphicTranslationData
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I) where
  leftTailStart : GeneratorIndex k → ℕ
  rightTailStart : GeneratorIndex k → ℕ
  left :
    ∀ i,
      LocalReflectedA0HolomorphicTranslationFieldData
        OS ((i.n - 1) + 1) (i.n - 1)
        (fun N x χ =>
          A.rootedLeftBlockTranslatedSpatialSource
            R i (N + leftTailStart i) x χ)
  right :
    ∀ i,
      LocalReflectedA0HolomorphicTranslationFieldData
        OS ((i.m - 1) + 1) (i.m - 1)
        (fun N x χ =>
          A.rootedRightBlockTranslatedSpatialSource
            R i (N + rightTailStart i) x χ)

namespace RootedA0BlockHolomorphicTranslationData

variable
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- Forget holomorphy only at the boundary consumed by the existing rooted
real-edge and compact-bound API. -/
noncomputable def toContinuousTranslationData
    (D : RootedA0BlockHolomorphicTranslationData OS A R) :
    RootedA0BlockContinuousTranslationData OS A R where
  leftTailStart := D.leftTailStart
  rightTailStart := D.rightTailStart
  left i :=
    (D.left i).toLocalReflectedA0ContinuousTranslationFieldData
  right i :=
    (D.right i).toLocalReflectedA0ContinuousTranslationFieldData

end RootedA0BlockHolomorphicTranslationData

/-- The proved canonical compact edges construct all rooted block fields
with their analytic structure retained. -/
noncomputable def rootedA0BlockHolomorphicTranslationData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I) :
    RootedA0BlockHolomorphicTranslationData OS A R := by
  exact {
    leftTailStart := fun i =>
      (A.rootedLeftBlockHolomorphicTranslationFieldData L OS H R i).1
    rightTailStart := fun i =>
      (A.rootedRightBlockHolomorphicTranslationFieldData L OS H R i).1
    left := fun i =>
      (A.rootedLeftBlockHolomorphicTranslationFieldData L OS H R i).2
    right := fun i =>
      (A.rootedRightBlockHolomorphicTranslationFieldData L OS H R i).2 }

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
