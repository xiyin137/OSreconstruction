/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeSmearingRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPacketTimeShell














noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimeCarrierPartitionData

variable {timeCarrier : Set (Fin k → ℝ)}

end InitialBaseTimeCarrierPartitionData

namespace Section43ProductTimeApproximateIdentity

/-- A translated tail of a shrinking product approximate identity together
with one chronological base/time partition reused at every scale. -/
structure AnchoredPacketTimeShellFamilyData
    (I : Section43ProductTimeApproximateIdentity k)
    (anchor : Fin k → ℝ) where
  anchor_positive :
    anchor ∈ section43TimeStrictPositiveRegion k
  carrierData : AnchoredCompactTimeCarrierData I anchor
  partition :
    InitialBaseTimeCarrierPartitionData
      (d := d) carrierData.carrier

/-- Anchored packet time-shell family data may be chosen without discarding
any approximate-identity scales. -/
theorem exists_anchoredPacketTimeShellFamilyData_zeroTail
    (I : Section43ProductTimeApproximateIdentity k)
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    ∃ A : AnchoredPacketTimeShellFamilyData (d := d) I anchor,
      A.carrierData.tailStart = 0 := by
  obtain ⟨C, hC⟩ :=
    I.exists_anchoredCompactTimeCarrierData_zeroTail anchor hanchor
  obtain ⟨D⟩ :=
    nonempty_initialBaseTimeCarrierPartitionData
      (d := d) C.carrier C.carrier_compact C.carrier_positive
  exact ⟨{
    anchor_positive := hanchor
    carrierData := C
    partition := D }, hC⟩

namespace AnchoredPacketTimeShellFamilyData

variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The scale-`N` coupled time test, translated to the fixed positive
anchor. -/
noncomputable def timeTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    SchwartzMap (Fin k → ℝ) ℂ :=
  SCV.translateSchwartz (-anchor)
    (I.test (N + A.carrierData.tailStart))

/-- The one-dimensional translated factors whose product is the anchored
multitime test.  Retaining these factors is the source-level input for the
left/bridge/right reflected Gram decomposition at a packet split. -/
noncomputable def translatedFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (i : Fin k) :
    Section43CompactPositiveTimeSource1D :=
  section43CompactPositiveTimeSource1D_translateRight
    (I.factors (N + A.carrierData.tailStart) i)
    (anchor i) (A.anchor_positive i).le

/-- The translated factors belonging to the reflected-left internal gaps of
one generator split.  The reversal is already encoded by
`GeneratorIndex.leftGlobalIndex`. -/
noncomputable def leftInternalFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (a : Fin (i.n - 1)) :
    Section43CompactPositiveTimeSource1D :=
  A.translatedFactor N (i.leftGlobalIndex a)

/-- The translated one-dimensional factor at the distinguished semigroup
bridge of one generator split.  It remains separate from both Hilbert blocks. -/
noncomputable def bridgeFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    Section43CompactPositiveTimeSource1D :=
  A.translatedFactor N i.bridgeGlobalIndex

/-- The translated factors belonging to the right internal gaps of one
generator split. -/
noncomputable def rightInternalFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (b : Fin (i.m - 1)) :
    Section43CompactPositiveTimeSource1D :=
  A.translatedFactor N (i.rightGlobalIndex b)

/-- Compact positive-time product source formed by the left internal gaps. -/
noncomputable def leftInternalSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource (i.n - 1) :=
  section43TimeProductSource (A.leftInternalFactor i N)

/-- Compact positive-time product source formed by the right internal gaps. -/
noncomputable def rightInternalSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource (i.m - 1) :=
  section43TimeProductSource (A.rightInternalFactor i N)

/-- The zero-centered approximate identity underlying the anchored left
internal-gap source. The finite tail shift is the same one used by the full
anchored time shell. -/
noncomputable def leftInternalApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    SchwartzTimeApproximateIdentity (i.n - 1) :=
  (I.reindex i.leftGlobalIndex).toSchwartzTimeApproximateIdentity.tail
    A.carrierData.tailStart

/-- The zero-centered approximate identity underlying the anchored right
internal-gap source. -/
noncomputable def rightInternalApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    SchwartzTimeApproximateIdentity (i.m - 1) :=
  (I.reindex i.rightGlobalIndex).toSchwartzTimeApproximateIdentity.tail
    A.carrierData.tailStart

/-- Evaluating the anchored left internal source at its block anchor plus a
deviation recovers the corresponding zero-centered approximate identity. -/
theorem leftInternalSource_apply_anchor_add
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (y : Fin (i.n - 1) → ℝ) :
    (A.leftInternalSource i N).f
        (fun a => anchor (i.leftGlobalIndex a) + y a) =
      (A.leftInternalApproximateIdentity i).test N y := by
  simp [leftInternalSource, leftInternalFactor, translatedFactor,
    leftInternalApproximateIdentity, SchwartzTimeApproximateIdentity.tail,
    Section43ProductTimeApproximateIdentity.reindex,
    Section43ProductTimeApproximateIdentity.toSchwartzTimeApproximateIdentity,
    Section43ProductTimeApproximateIdentity.test,
    Section43ProductTimeApproximateIdentity.source,
    section43TimeProductSource, section43TimeProductTensor,
    SchwartzMap.productTensor_apply,
    section43CompactPositiveTimeSource1D_translateRight]

/-- The anchored left internal source is exactly the zero-centered
approximate identity translated to the left block anchor. -/
theorem leftInternalSource_f_eq_translateApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    (A.leftInternalSource i N).f =
      SCV.translateSchwartz
        (-(fun a => anchor (i.leftGlobalIndex a)))
        ((A.leftInternalApproximateIdentity i).test N) := by
  ext x
  let τ : Fin (i.n - 1) → ℝ :=
    fun a => anchor (i.leftGlobalIndex a)
  have h :=
    A.leftInternalSource_apply_anchor_add i N (x - τ)
  simpa [τ, SCV.translateSchwartz_apply, sub_eq_add_neg,
    add_assoc] using h

/-- The anchored coupled test is exactly the product of its translated
one-dimensional approximate-identity factors.  The equality is recorded at
the Schwartz-source level so later block decompositions can reindex the
factors without changing the complete time shell. -/
theorem timeTest_eq_translatedProductSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    A.timeTest N =
      (section43TimeProductSource
        (fun i => A.translatedFactor N i)).f := by
  ext x
  exact
    section43TimeProductSource_translateRight_apply
      (I.factors (N + A.carrierData.tailStart))
      anchor (fun i => (A.anchor_positive i).le) x

/-- At every generator split, the anchored test factors exactly into the
reflected-left internal gaps, the unsplit semigroup bridge, and the right
internal gaps.  No absolute-time head is inserted here: the two positive
Hilbert heads are independent delta variables whose sum approaches the
bridge in the later reflected Gram limit. -/
theorem timeTest_apply_eq_left_bridge_right
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (x : Fin k → ℝ) :
    A.timeTest N x =
      (A.leftInternalSource i N).f
          (fun a => x (i.leftGlobalIndex a)) *
        (A.bridgeFactor i N).f (x i.bridgeGlobalIndex) *
        (A.rightInternalSource i N).f
          (fun b => x (i.rightGlobalIndex b)) := by
  rw [A.timeTest_eq_translatedProductSource]
  simp only [leftInternalSource, rightInternalSource,
    leftInternalFactor, bridgeFactor, rightInternalFactor,
    section43TimeProductSource, section43TimeProductTensor,
    SchwartzMap.productTensor_apply]
  let leftCount := i.n - 1
  let rightCount := i.m - 1
  have hcard : leftCount + (rightCount + 1) = k := by
    dsimp [leftCount, rightCount]
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  calc
    (∏ j : Fin k, (A.translatedFactor N j).f (x j)) =
        ∏ j : Fin (leftCount + (rightCount + 1)),
          (A.translatedFactor N ((finCongr hcard) j)).f
            (x ((finCongr hcard) j)) := by
          symm
          exact Fintype.prod_equiv
            (finCongr hcard)
            (fun j : Fin (leftCount + (rightCount + 1)) =>
              (A.translatedFactor N ((finCongr hcard) j)).f
                (x ((finCongr hcard) j)))
            (fun j : Fin k => (A.translatedFactor N j).f (x j))
            (fun _ => rfl)
    _ =
        (∏ a : Fin leftCount,
            (A.translatedFactor N ((finCongr hcard)
              (Fin.castAdd (rightCount + 1) a))).f
              (x ((finCongr hcard)
                (Fin.castAdd (rightCount + 1) a)))) *
          ∏ c : Fin (rightCount + 1),
            (A.translatedFactor N ((finCongr hcard)
              (Fin.natAdd leftCount c))).f
              (x ((finCongr hcard)
                (Fin.natAdd leftCount c))) := by
          rw [Fin.prod_univ_add]
    _ =
        (∏ a : Fin leftCount,
            (A.translatedFactor N ((finCongr hcard)
              (Fin.castAdd (rightCount + 1) a))).f
              (x ((finCongr hcard)
                (Fin.castAdd (rightCount + 1) a)))) *
          ((A.translatedFactor N ((finCongr hcard)
              (Fin.natAdd leftCount 0))).f
              (x ((finCongr hcard)
                (Fin.natAdd leftCount 0))) *
            ∏ b : Fin rightCount,
              (A.translatedFactor N ((finCongr hcard)
                (Fin.natAdd leftCount b.succ))).f
                (x ((finCongr hcard)
                  (Fin.natAdd leftCount b.succ)))) := by
          rw [Fin.prod_univ_succ]
    _ = _ := by
      have hleft :
          ∀ a : Fin leftCount,
            (finCongr hcard)
                (Fin.castAdd (rightCount + 1) a) =
              i.leftGlobalIndex (Fin.rev a) := by
        intro a
        apply Fin.ext
        simp [leftCount, GeneratorIndex.leftGlobalIndex]
      have hbridge :
          (finCongr hcard) (Fin.natAdd leftCount 0) =
            i.bridgeGlobalIndex := by
        apply Fin.ext
        simp [leftCount, GeneratorIndex.bridgeGlobalIndex]
      have hright :
          ∀ b : Fin rightCount,
            (finCongr hcard)
                (Fin.natAdd leftCount b.succ) =
              i.rightGlobalIndex b := by
        intro b
        apply Fin.ext
        simp [leftCount, rightCount,
          GeneratorIndex.rightGlobalIndex]
        have hn := i.hn
        omega
      rw [hbridge]
      simp_rw [hleft]
      rw [show
          (∏ a : Fin leftCount,
              (A.translatedFactor N (i.leftGlobalIndex (Fin.rev a))).f
                (x (i.leftGlobalIndex (Fin.rev a)))) =
            ∏ a : Fin leftCount,
              (A.translatedFactor N (i.leftGlobalIndex a)).f
                (x (i.leftGlobalIndex a)) by
        exact Fintype.prod_equiv
          Fin.revPerm
          (fun a : Fin leftCount =>
            (A.translatedFactor N (i.leftGlobalIndex (Fin.rev a))).f
              (x (i.leftGlobalIndex (Fin.rev a))))
          (fun a : Fin leftCount =>
            (A.translatedFactor N (i.leftGlobalIndex a)).f
              (x (i.leftGlobalIndex a)))
          (fun _ => by simp)]
      simp_rw [hright]
      ring

/-- Reassemble left internal coordinates, the distinguished bridge, and
right internal coordinates into the global reduced-time tuple of one
generator split. -/
def generatorSplitTimeTuple
    (i : GeneratorIndex k)
    (xL : Fin (i.n - 1) → ℝ)
    (t : ℝ)
    (xR : Fin (i.m - 1) → ℝ) :
    Fin k → ℝ :=
  let hcard : (i.n - 1) + ((i.m - 1) + 1) = k := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  fun j =>
    Fin.append
      (fun a => xL (Fin.rev a))
      (Fin.cons t xR)
      (Fin.cast hcard.symm j)

@[simp]
theorem generatorSplitTimeTuple_left
    (i : GeneratorIndex k)
    (xL : Fin (i.n - 1) → ℝ)
    (t : ℝ)
    (xR : Fin (i.m - 1) → ℝ)
    (a : Fin (i.n - 1)) :
    generatorSplitTimeTuple i xL t xR (i.leftGlobalIndex a) =
      xL a := by
  let hcard : (i.n - 1) + ((i.m - 1) + 1) = k := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  have hindex :
      Fin.cast hcard.symm (i.leftGlobalIndex a) =
        Fin.castAdd ((i.m - 1) + 1) (Fin.rev a) := by
    apply Fin.ext
    simp [GeneratorIndex.leftGlobalIndex]
  rw [generatorSplitTimeTuple]
  dsimp only
  rw [hindex, Fin.append_left]
  simp

@[simp]
theorem generatorSplitTimeTuple_bridge
    (i : GeneratorIndex k)
    (xL : Fin (i.n - 1) → ℝ)
    (t : ℝ)
    (xR : Fin (i.m - 1) → ℝ) :
    generatorSplitTimeTuple i xL t xR i.bridgeGlobalIndex = t := by
  let hcard : (i.n - 1) + ((i.m - 1) + 1) = k := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  have hindex :
      Fin.cast hcard.symm i.bridgeGlobalIndex =
        Fin.natAdd (i.n - 1) (0 : Fin ((i.m - 1) + 1)) := by
    apply Fin.ext
    simp [GeneratorIndex.bridgeGlobalIndex]
  rw [generatorSplitTimeTuple]
  dsimp only
  rw [hindex, Fin.append_right]
  rfl

@[simp]
theorem generatorSplitTimeTuple_right
    (i : GeneratorIndex k)
    (xL : Fin (i.n - 1) → ℝ)
    (t : ℝ)
    (xR : Fin (i.m - 1) → ℝ)
    (b : Fin (i.m - 1)) :
    generatorSplitTimeTuple i xL t xR (i.rightGlobalIndex b) =
      xR b := by
  let hcard : (i.n - 1) + ((i.m - 1) + 1) = k := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  have hindex :
      Fin.cast hcard.symm (i.rightGlobalIndex b) =
        Fin.natAdd (i.n - 1) b.succ := by
    apply Fin.ext
    simp [GeneratorIndex.rightGlobalIndex]
    have hn := i.hn
    omega
  rw [generatorSplitTimeTuple]
  dsimp only
  rw [hindex, Fin.append_right]
  rfl

/-- Vary only the distinguished bridge coordinate of a global reduced-time
tuple, retaining all left and right internal gaps. -/
def generatorBridgeVariation
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ) :
    Fin k → ℝ :=
  generatorSplitTimeTuple i
    (fun a => τ (i.leftGlobalIndex a))
    t
    (fun b => τ (i.rightGlobalIndex b))

@[simp]
theorem generatorBridgeVariation_left
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ)
    (a : Fin (i.n - 1)) :
    generatorBridgeVariation i τ t (i.leftGlobalIndex a) =
      τ (i.leftGlobalIndex a) := by
  simp [generatorBridgeVariation]

@[simp]
theorem generatorBridgeVariation_bridge
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ) :
    generatorBridgeVariation i τ t i.bridgeGlobalIndex = t := by
  simp [generatorBridgeVariation]

@[simp]
theorem generatorBridgeVariation_right
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ)
    (b : Fin (i.m - 1)) :
    generatorBridgeVariation i τ t (i.rightGlobalIndex b) =
      τ (i.rightGlobalIndex b) := by
  simp [generatorBridgeVariation]

@[simp]
theorem GeneratorIndex.leftRealCoordinates_generatorBridgeVariation
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ) :
    i.leftRealCoordinates (generatorBridgeVariation i τ t) =
      i.leftRealCoordinates τ := by
  funext a
  simp [GeneratorIndex.leftRealCoordinates]

@[simp]
theorem GeneratorIndex.rightRealCoordinates_generatorBridgeVariation
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (t : ℝ) :
    i.rightRealCoordinates (generatorBridgeVariation i τ t) =
      i.rightRealCoordinates τ := by
  funext b
  simp [GeneratorIndex.rightRealCoordinates]

/-- Varying only the distinguished bridge coordinate is a continuous path in
the global reduced-time space. -/
theorem continuous_generatorBridgeVariation
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    Continuous (generatorBridgeVariation i τ) := by
  let hcard : (i.n - 1) + ((i.m - 1) + 1) = k := by
    have hn := i.hn
    have hm := i.hm
    have hnm := i.hnm
    omega
  have hcons :
      Continuous
        (fun t : ℝ =>
          (Fin.cons t (fun b => τ (i.rightGlobalIndex b)) :
            Fin ((i.m - 1) + 1) → ℝ)) := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · change Continuous (fun t : ℝ => t)
      exact continuous_id
    · change Continuous (fun _ : ℝ => τ (i.rightGlobalIndex b))
      exact continuous_const
  have happend :
      Continuous
        (fun t : ℝ =>
          Fin.append
            (fun a => τ (i.leftGlobalIndex (Fin.rev a)))
            (Fin.cons t (fun b => τ (i.rightGlobalIndex b)))) :=
    (Fin.continuous_append (i.n - 1) ((i.m - 1) + 1)).comp
      (continuous_const.prodMk hcons)
  have hreindex :
      Continuous
        (fun f : Fin ((i.n - 1) + ((i.m - 1) + 1)) → ℝ =>
          fun j : Fin k => f (Fin.cast hcard.symm j)) := by
    apply continuous_pi
    intro j
    exact continuous_apply (Fin.cast hcard.symm j)
  change Continuous (fun t =>
    (fun f j => f (Fin.cast hcard.symm j))
      (Fin.append
        (fun a => τ (i.leftGlobalIndex (Fin.rev a)))
        (Fin.cons t (fun b => τ (i.rightGlobalIndex b)))))
  exact hreindex.comp happend

/-- Translating an anchored tail test by a real stage parameter is the
original approximate-identity test centered at `τ + anchor`. -/
theorem translate_timeTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (τ : Fin k → ℝ) :
    SCV.translateSchwartz (-τ) (A.timeTest N) =
      SCV.translateSchwartz (-(τ + anchor))
        (I.test (N + A.carrierData.tailStart)) := by
  rw [timeTest, SCV.translateSchwartz_translateSchwartz]
  congr 1
  module

/-- The single carrier partition specialized to the scale-`N` anchored time
test.  Its index type, centers, and cutoffs are definitionally independent of
`N`. -/
noncomputable def partitionAt
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    InitialBaseTimePartitionData (d := d) (A.timeTest N) :=
  A.partition.toInitialBaseTimePartitionData
    (A.timeTest N) (A.carrierData.translated_support N)

@[simp] theorem partitionAt_index
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    (A.partitionAt N).index = A.partition.index :=
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
