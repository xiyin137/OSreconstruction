/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetCutoffHull










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

namespace OSIIChapterV

variable {d n : Nat} [NeZero d]
variable {K L : Set (Fin n -> Real)}

/-- Inclusion of one fixed-carrier source space into a larger carrier. -/
noncomputable def uniformCompactTimeSourceMonoCLM
    (hKL : K ⊆ L) :
    UniformCompactTimeSource d n K →L[Complex]
      UniformCompactTimeSource d n L :=
  (uniformCompactTimeSourceSubmodule d n K).subtypeL.codRestrict
    (uniformCompactTimeSourceSubmodule d n L)
    (fun a => by
      intro x hx
      exact hKL (a.2 x hx))

@[simp] theorem uniformCompactTimeSourceMonoCLM_source
    (hKL : K ⊆ L)
    (a : UniformCompactTimeSource d n K) :
    UniformCompactTimeSource.source
        (uniformCompactTimeSourceMonoCLM hKL a) =
      UniformCompactTimeSource.source a :=
  rfl

end OSIIChapterV

namespace FixedAxisSplitUniformRankFieldData

variable {d n : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]
variable {S : C} {depth rank : Nat}
variable {P : OSIIChapterV.StageWideStrictGeneratedMixedReflectedGramRankData
  (OS := OS) S depth rank}

end FixedAxisSplitUniformRankFieldData

namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]

namespace FixedAxisSplitUniformTargetCutoffHullData

variable {D : OSIIStep4MultiGapUniformCommonSlopeData
  d k hrho center hcenter}
variable {i : OSIIChapterV.GeneratorIndex k}

/-- The left source-indexed rank field on the cutoff hull. -/
noncomputable def leftRankFieldFamilyData
    (H : FixedAxisSplitUniformTargetCutoffHullData D i)
    (S : C) (depth rank : Nat)
    (P : OSIIChapterV.StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank) :
    FixedAxisSplitUniformRankFieldData OS depth rank i.n H.leftCarrier :=
  FixedAxisSplitUniformRankFieldData.ofCarrier S depth rank i.n P i.hn
    H.leftCarrier H.leftCarrier_isCompact
      H.leftCarrier_subset_strictPositive

/-- A physical left source, regarded as a source on the larger cutoff hull. -/
noncomputable def physicalLeftSource
    (H : FixedAxisSplitUniformTargetCutoffHullData D i)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d i.n H.leftCarrier :=
  OSIIChapterV.uniformCompactTimeSourceMonoCLM
    H.physicalLeftCarrier_subset_leftCarrier
      (D.fixedAxisSplitUniformTargetLeftSource i x hx a p)

/-- A physical right source, regarded as a source on the larger cutoff hull. -/
noncomputable def physicalRightSource
    (H : FixedAxisSplitUniformTargetCutoffHullData D i)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d i.m H.rightCarrier :=
  OSIIChapterV.uniformCompactTimeSourceMonoCLM
    H.physicalRightCarrier_subset_rightCarrier
      (D.fixedAxisSplitUniformTargetRightSource i x hx a p)

@[simp] theorem physicalLeftSource_source
    (H : FixedAxisSplitUniformTargetCutoffHullData D i)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource.source
        (H.physicalLeftSource x hx a p) =
      OSIIChapterV.UniformCompactTimeSource.source
        (D.fixedAxisSplitUniformTargetLeftSource i x hx a p) :=
  rfl

@[simp] theorem physicalRightSource_source
    (H : FixedAxisSplitUniformTargetCutoffHullData D i)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : x ∈ D.fixedAxisAllSplitTargetLogRealCarrier)
    (a : osiiAxisPairIndex d)
    (p : MultiGapSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource.source
        (H.physicalRightSource x hx a p) =
      OSIIChapterV.UniformCompactTimeSource.source
        (D.fixedAxisSplitUniformTargetRightSource i x hx a p) :=
  rfl

end FixedAxisSplitUniformTargetCutoffHullData
end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
