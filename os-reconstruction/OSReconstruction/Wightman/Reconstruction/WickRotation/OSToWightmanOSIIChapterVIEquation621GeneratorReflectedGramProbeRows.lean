/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedGramProbeRows










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

/-- For a nontrivial left generator block, the retained reflected-Gram
diagonal on the coherent block probe converges to the represented lower
stage evaluated on the exact left self-pair marginal probe. -/
theorem tendsto_rootedLeftNontrivialDiagonalScalar_to_distribution_generatorProbe
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
              (generatorLeftBlockSpatialPoint d i x) probeScale))
          (D.sourceCLM (N + rightTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorLeftBlockSpatialPoint d i x) probeScale))).scalar
            (reflectedCauchyCenter z))
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter z) physicalTime)
        (blockApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          (i.leftReflectedSelfPairSpatialPoint d x) probeScale))) := by
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let D := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  let blockApprox := spatialApprox.generatorLeftBlockProductApproxIdentity i
  have hsource : forall scale spatial,
      UniformCompactTimeSource.source (D.sourceCLM scale spatial) =
        (A.rootedLeftBlockApproximateIdentity R i
          ).translatedPositiveTimeSpatialSource
            (A.rootedLeftBlockAnchor i)
            (A.rootedLeftBlockAnchor_positive i) spatial scale := by
    intro scale spatial
    simpa [D, i, rootedLeftNontrivialReflectedGramSpatialSourceData] using
      A.rootedLeftBlockAnchoredSourceCLM_source_translated
        R i scale spatial
  have hlimit :=
    D.tendsto_diagonalScalar_tailDiagonal_to_distribution_marginalSpatialProbe
      (A.rootedLeftBlockApproximateIdentity R i)
      (A.rootedLeftBlockAnchor i) (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      (A.rootedLeftBlockAnchor_positive i)
      hsource hsource blockApprox
      (generatorLeftBlockSpatialPoint d i x) probeScale
      z (by simpa [D, i] using hz) physicalTime
      (by simpa [i] using htime) (by simpa [D, i] using hrho)
      leftTail rightTail
  have hpoint :
      reflectedSelfPairMarginalSpatialPoint d (q + 1)
          (generatorLeftBlockSpatialPoint d i x) =
        i.leftReflectedSelfPairSpatialPoint d x := by
    simpa [i] using
      generatorLeftBlockSpatialPoint_reflectedSelfPair
        (d := d) i x
  rw [hpoint] at hlimit
  simpa [D, i, blockApprox] using hlimit

/-- Right-block form of
`tendsto_rootedLeftNontrivialDiagonalScalar_to_distribution_generatorProbe`.
-/
theorem tendsto_rootedRightNontrivialDiagonalScalar_to_distribution_generatorProbe
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
              (generatorRightBlockSpatialPoint d i x) probeScale))
          (D.sourceCLM (N + rightTail)
            (blockApprox.toEquation621SpatialApproxIdentity.section43Probe
              (generatorRightBlockSpatialPoint d i x) probeScale))).scalar
            (reflectedCauchyCenter z))
      atTop
      (nhds (D.reflectedGram.atlas.sourceStage.stage.distribution
        (equation621ReflectedMovingSlicePoint
          (reflectedCauchyCenter z) physicalTime)
        (blockApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          (i.rightReflectedSelfPairSpatialPoint d x) probeScale))) := by
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let D := rootedRightNontrivialReflectedGramSpatialSourceData
    S depth P A R i (q := q) rfl
  let blockApprox := spatialApprox.generatorRightBlockProductApproxIdentity i
  have hsource : forall scale spatial,
      UniformCompactTimeSource.source (D.sourceCLM scale spatial) =
        (A.rootedRightBlockApproximateIdentity R i
          ).translatedPositiveTimeSpatialSource
            (A.rootedRightBlockAnchor i)
            (A.rootedRightBlockAnchor_positive i) spatial scale := by
    intro scale spatial
    simpa [D, i, rootedRightNontrivialReflectedGramSpatialSourceData] using
      A.rootedRightBlockAnchoredSourceCLM_source_translated
        R i scale spatial
  have hlimit :=
    D.tendsto_diagonalScalar_tailDiagonal_to_distribution_marginalSpatialProbe
      (A.rootedRightBlockApproximateIdentity R i)
      (A.rootedRightBlockAnchor i) (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      (A.rootedRightBlockAnchor_positive i)
      hsource hsource blockApprox
      (generatorRightBlockSpatialPoint d i x) probeScale
      z (by simpa [D, i] using hz) physicalTime
      (by simpa [i] using htime) (by simpa [D, i] using hrho)
      leftTail rightTail
  have hpoint :
      reflectedSelfPairMarginalSpatialPoint d (q + 1)
          (generatorRightBlockSpatialPoint d i x) =
        i.rightReflectedSelfPairSpatialPoint d x := by
    simpa [i] using
      generatorRightBlockSpatialPoint_reflectedSelfPair
        (d := d) i x
  rw [hpoint] at hlimit
  simpa [D, i, blockApprox] using hlimit

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
