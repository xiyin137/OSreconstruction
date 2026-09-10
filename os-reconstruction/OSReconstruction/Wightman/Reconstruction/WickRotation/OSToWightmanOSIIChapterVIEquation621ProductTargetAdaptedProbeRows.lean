/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorReflectedGramProbeRows










noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable
  {timeApprox : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}

/-- Left nontrivial reflected row in the common target coordinate. -/
theorem tendsto_rootedLeftNontrivialDiagonalScalar_to_distribution_generatorProbe_adapted
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) timeApprox anchor)
    (R : TripleConvolutionRootData timeApprox)
    (q m : Nat)
    (hn : 1 <= q + 2)
    (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (probeScale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz :
      let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
      let D := rootedLeftNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      z ∈ D.reflectedGram.atlas.spatialLinearDomain)
    (physicalTime : Fin ((q + 1) + ((q + 1) + 1)) -> Real)
    (htime :
      let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
      osiiMixedBlockGlobalReducedTime (q + 1)
        (Fin.append (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor i)) = physicalTime)
    (hrho :
      let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
      let D := rootedLeftNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      D.reflectedGram.atlas.sourceStage.germ.η physicalTime = 1)
    (leftTail rightTail : Nat) :
    let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let D := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    let blockApprox := spatialApprox.generatorLeftBlockProductApproxIdentity i
    Tendsto
      (fun N =>
        (D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM (N + leftTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorLeftBlockSpatialPoint d i
                (equation621SplitTargetSpatialPoint i x)) probeScale))
          (D.sourceCLM (N + rightTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorLeftBlockSpatialPoint d i
                (equation621SplitTargetSpatialPoint i x)) probeScale))).scalar
            (reflectedCauchyCenter z))
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter z) physicalTime)
        (blockApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          ((i.equation621TargetAdaptedSpatialSplitData d).leftPoint x)
          probeScale))) := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  have h :=
    tendsto_rootedLeftNontrivialDiagonalScalar_to_distribution_generatorProbe
      P A R q m hn hm hnm spatialApprox
      (equation621SplitTargetSpatialPoint i x) probeScale z
      (by simpa [i] using hz) physicalTime
      (by simpa [i] using htime) (by simpa [i] using hrho)
      leftTail rightTail
  simpa [i] using h

/-- Right nontrivial reflected row in the common target coordinate. -/
theorem tendsto_rootedRightNontrivialDiagonalScalar_to_distribution_generatorProbe_adapted
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) timeApprox anchor)
    (R : TripleConvolutionRootData timeApprox)
    (n q : Nat)
    (hn : 1 <= n)
    (hm : 1 <= q + 2)
    (hnm : k = n + (q + 2) - 1)
    (spatialApprox : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (probeScale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz :
      let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
      let D := rootedRightNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      z ∈ D.reflectedGram.atlas.spatialLinearDomain)
    (physicalTime : Fin ((q + 1) + ((q + 1) + 1)) -> Real)
    (htime :
      let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
      osiiMixedBlockGlobalReducedTime (q + 1)
        (Fin.append (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor i)) = physicalTime)
    (hrho :
      let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
      let D := rootedRightNontrivialReflectedGramSpatialSourceData
        S depth P A R i (q := q) rfl
      D.reflectedGram.atlas.sourceStage.germ.η physicalTime = 1)
    (leftTail rightTail : Nat) :
    let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
    let D := rootedRightNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
    let blockApprox := spatialApprox.generatorRightBlockProductApproxIdentity i
    Tendsto
      (fun N =>
        (D.reflectedGram.atlas.gram.cauchy
          (D.sourceCLM (N + leftTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorRightBlockSpatialPoint d i
                (equation621SplitTargetSpatialPoint i x)) probeScale))
          (D.sourceCLM (N + rightTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorRightBlockSpatialPoint d i
                (equation621SplitTargetSpatialPoint i x)) probeScale))).scalar
            (reflectedCauchyCenter z))
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter z) physicalTime)
        (blockApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          ((i.equation621TargetAdaptedSpatialSplitData d).rightPoint x)
          probeScale))) := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  have h :=
    tendsto_rootedRightNontrivialDiagonalScalar_to_distribution_generatorProbe
      P A R n q hn hm hnm spatialApprox
      (equation621SplitTargetSpatialPoint i x) probeScale z
      (by simpa [i] using hz) physicalTime
      (by simpa [i] using htime) (by simpa [i] using hrho)
      leftTail rightTail
  simpa [i] using h

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
