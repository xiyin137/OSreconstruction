/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCommonSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Fixed data for the full-source realization of one chronological multi-gap
real edge. -/
structure OSIIChronologicalFullSourceLocalizationData (d k : ℕ)
    [NeZero d] [NeZero k] where
  factors : OSIIChronologicalCompactFactors d k
  T : ℝ
  hT : 1 < T
  ordered :
    ∀ a : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            ((factors.factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((factors.factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T a).matrix.mulVec z) 0

namespace OSIIChronologicalFullSourceLocalizationData

/-- Localize an arbitrary full Schwartz source at one real multi-gap
parameter. -/
noncomputable def localizedCLM
    (P : OSIIChronologicalFullSourceLocalizationData d k)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d (k + 1) →L[ℂ] SchwartzNPoint d (k + 1) :=
  P.factors.sourcewiseLocalizedTranslatedFullCLM P.T x

/-- The same full-source localization, with its ordered-support
zero-diagonal certificate attached. -/
noncomputable def localizedZeroCLM
    (P : OSIIChronologicalFullSourceLocalizationData d k)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d (k + 1) →L[ℂ]
      ZeroDiagonalSchwartz d (k + 1) :=
  P.factors.sourcewiseLocalizedTranslatedFullZeroCLM
    P.T P.hT P.ordered x

@[simp] theorem localizedZeroCLM_coe
    (P : OSIIChronologicalFullSourceLocalizationData d k)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (f : SchwartzNPoint d (k + 1)) :
    (P.localizedZeroCLM x f).1 = P.localizedCLM x f := rfl

end OSIIChronologicalFullSourceLocalizationData

namespace OSIIChapterV
namespace GeneratorHermiteHilbertFieldFamilyData

variable {OS : OsterwalderSchraderAxioms d}

/-- Reindex an ordinary full configuration Schwartz source along a finite
equivalence of its point labels. -/
noncomputable def reindexSchwartzNPointCLM
    {n m : ℕ} (σ : Fin n ≃ Fin m) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d m :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ
      ).toContinuousLinearEquiv)

@[simp] theorem reindexSchwartzNPointCLM_apply
    {n m : ℕ} (σ : Fin n ≃ Fin m)
    (f : SchwartzNPoint d n) :
    reindexSchwartzNPointCLM (d := d) σ f =
      reindexSchwartz (d := d) σ f := rfl

/-- The split-induced ordinary full source at its native block arity.  This
is the source seen directly by the axis-pair semigroup before common-arity
reindexing. -/
noncomputable def generatorSplitRawAbsoluteSpatialFullSourceCLM
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzNPoint d (i.n + i.m) :=
  (axisPairGlobalAbsoluteSpatialSourceCLM
    i.n i.m
    (B.translatedLeftTimeProfile i τ)
    (B.translatedRightTimeProfile i τ)
    (B.translatedLeftCommonShift i τ)
    (τ i.bridgeGlobalIndex)).comp
      (generatorSplitSpatialPullbackCLM i)

/-- The native split source reindexed to the common k + 1 point arity. -/
noncomputable def generatorSplitAbsoluteSpatialFullSourceCLM
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (reindexSchwartzNPointCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)).comp
      (B.generatorSplitRawAbsoluteSpatialFullSourceCLM i τ)

/-- Forgetting the zero-diagonal certificate in the old split source gives
the proof-independent full source map. -/
@[simp] theorem generatorSplitAbsoluteSpatialSourceZeroCLM_coe
    (B : GeneratorHermiteHilbertFieldFamilyData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hleft :
      tsupport
          (B.translatedLeftTimeProfile i τ :
            (Fin i.n → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.n)
    (hright :
      tsupport
          (B.translatedRightTimeProfile i τ :
            (Fin i.m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.m)
    (ht : 0 ≤ τ i.bridgeGlobalIndex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (B.generatorSplitAbsoluteSpatialSourceZeroCLM
        i τ hleft hright ht F).1 =
      B.generatorSplitAbsoluteSpatialFullSourceCLM i τ F := rfl

namespace CommonFullSourceFactorizationGermData

end CommonFullSourceFactorizationGermData

end GeneratorHermiteHilbertFieldFamilyData
end OSIIChapterV
end OSReconstruction
