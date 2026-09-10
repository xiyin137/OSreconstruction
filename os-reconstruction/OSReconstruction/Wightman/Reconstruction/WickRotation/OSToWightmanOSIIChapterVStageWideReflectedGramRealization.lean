/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialGeneratedLogarithmicRealization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertFieldGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedSpatialCanonicalField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas
























noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The carrier-independent analytic payload used by the rooted
reflected-Gram construction.

Coverage of a particular logarithmic grammar is deliberately omitted.  It
is an external property of this atlas, supplied either by the full generated
package or by one strict finite-rank stratum. -/
structure ReflectedGramAtlasData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (q : ℕ)
    (K : Set (Fin ((q + 1) + 1) → ℝ)) where
  atlas :
    UniversalCompactCarrierAnchoredAtlasData
      (q := q)
        (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
          (OS := OS) S)
        OS K

/-- A stage-wide choice of reflected-Gram atlas for every compact
strict-positive source carrier.

The `depth` parameter is retained as a label so existing rooted APIs keep
their induction index, but the analytic choice itself does not assume any
particular generated-domain predicate. -/
structure StageWideReflectedGramAtlasFamilyData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (_depth : ℕ) where
  forCarrier :
    ∀ (q : ℕ)
      (K : Set (Fin ((q + 1) + 1) → ℝ)),
      IsCompact K →
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1) →
      ReflectedGramAtlasData (OS := OS) S q K

namespace StageWideReflectedGramAtlasFamilyData

variable
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth : ℕ}

/-- Replace one carrier entry of a grammar-independent reflected-Gram atlas
family.  This is the analytic operation underlying both full-generated and
finite-rank target-adapted packages. -/
noncomputable def replaceCarrier
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q₀ : ℕ)
    (K₀ : Set (Fin ((q₀ + 1) + 1) → ℝ))
    (D₀ : ReflectedGramAtlasData (OS := OS) S q₀ K₀) :
    StageWideReflectedGramAtlasFamilyData (OS := OS) S depth where
  forCarrier q K hK_compact hK_positive := by
    classical
    by_cases hq : q = q₀
    · subst q
      by_cases hK : K = K₀
      · subst K
        exact D₀
      · exact P.forCarrier q₀ K hK_compact hK_positive
    · exact P.forCarrier q K hK_compact hK_positive

@[simp]
theorem replaceCarrier_forCarrier_same
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : ℕ)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (D : ReflectedGramAtlasData (OS := OS) S q K)
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1)) :
    (P.replaceCarrier q K D).forCarrier
        q K hK_compact hK_positive = D := by
  simp [replaceCarrier]

@[simp]
theorem replaceCarrier_forCarrier_arity_ne
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q₀ : ℕ)
    (K₀ : Set (Fin ((q₀ + 1) + 1) → ℝ))
    (D₀ : ReflectedGramAtlasData (OS := OS) S q₀ K₀)
    (q : ℕ)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hq : q ≠ q₀) :
    (P.replaceCarrier q₀ K₀ D₀).forCarrier
        q K hK_compact hK_positive =
      P.forCarrier q K hK_compact hK_positive := by
  simp [replaceCarrier, hq]

@[simp]
theorem replaceCarrier_forCarrier_same_arity_carrier_ne
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (q : ℕ)
    (K₀ K : Set (Fin ((q + 1) + 1) → ℝ))
    (D₀ : ReflectedGramAtlasData (OS := OS) S q K₀)
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hK : K ≠ K₀) :
    (P.replaceCarrier q K₀ D₀).forCarrier
        q K hK_compact hK_positive =
      P.forCarrier q K hK_compact hK_positive := by
  simp [replaceCarrier, hK]

end StageWideReflectedGramAtlasFamilyData

/-- The source-indexed reflected-Gram realization of one generated mixed
carrier at the same induction depth.

The analytic tail has dimension `q + 1`, so the mixed source has `q + 2`
particles and its reflected scalar stage has
`(q + 1) + ((q + 1) + 1)` time gaps. -/
structure GeneratedMixedReflectedGramAtlasData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth q : ℕ)
    (K : Set (Fin ((q + 1) + 1) → ℝ)) where
  atlas :
    UniversalCompactCarrierAnchoredAtlasData
      (q := q)
        (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
          (OS := OS) S)
        OS K
  coversGeneratedMixed :
    osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth) ⊆
      atlas.spatialLinearDomain

namespace GeneratedMixedReflectedGramAtlasData

variable
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth q : ℕ}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}

end GeneratedMixedReflectedGramAtlasData

/-- The same-depth reflected-Gram payload at every positive analytic tail
arity, uniformly available for every compact strict-positive source carrier.

The quantification over source carriers is essential: downstream left and
right generator blocks have different carrier spaces, and selecting one
arbitrary source family here would lose the full spatial Schwartz
dependence. -/
structure StageWideGeneratedMixedReflectedGramData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth : ℕ) where
  scalarGenerated :
    ∀ r,
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase r depth) ⊆
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S r).carrier
  forCarrier :
    ∀ (q : ℕ)
      (K : Set (Fin ((q + 1) + 1) → ℝ)),
      IsCompact K →
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1) →
      GeneratedMixedReflectedGramAtlasData
        (OS := OS) S depth q K

namespace StageWideGeneratedMixedReflectedGramData

/-- Forget only the full-generated coverage proof, retaining the complete
carrier-parametric analytic atlas family. -/
noncomputable def toAtlasFamily
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {depth : ℕ}
    (P : StageWideGeneratedMixedReflectedGramData
      (OS := OS) S depth) :
    StageWideReflectedGramAtlasFamilyData (OS := OS) S depth where
  forCarrier q K hK_compact hK_positive :=
    { atlas := (P.forCarrier q K hK_compact hK_positive).atlas }

noncomputable instance
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {depth : ℕ} :
    Coe (StageWideGeneratedMixedReflectedGramData
      (OS := OS) S depth)
      (StageWideReflectedGramAtlasFamilyData (OS := OS) S depth) :=
  ⟨toAtlasFamily⟩

end StageWideGeneratedMixedReflectedGramData

end OSIIChapterV
end OSReconstruction
