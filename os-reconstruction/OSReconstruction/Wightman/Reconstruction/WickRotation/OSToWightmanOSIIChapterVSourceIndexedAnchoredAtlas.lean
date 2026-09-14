/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertFieldGluing
import OSReconstruction.SCV.ConnectedNeighborhood









noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One local reflected-Gram chart carrying a fixed common anchor. -/
structure SourceIndexedAnchoredReflectedGramChart
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Type*) (m : ℕ)
    (scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ)
    (anchorPoint : Fin m → ℂ)
    (anchorField : ι → H) where
  gram :
    SourceIndexedReflectedGramHilbertFieldData
      H ι m scalar
  anchored :
    SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar anchorPoint anchorField gram

namespace SourceIndexedAnchoredReflectedGramChart

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} {m : ℕ}
  {scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ}
  {anchorPoint : Fin m → ℂ}
  {anchorField : ι → H}

/-- The maximal domain covered by all anchored charts with the prescribed
scalar family and anchor data. -/
def coveredDomain :
    Set (Fin m → ℂ) :=
  ⋃ C :
      SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField,
    C.gram.domain

theorem coveredDomain_open :
    IsOpen
      (coveredDomain
        (H := H) (ι := ι) (m := m)
        (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField)) :=
  isOpen_iUnion fun C => C.gram.domain_open

/-- Any two anchored charts agree source by source on their overlap. -/
theorem compatible
    (C D :
      SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField)
    (a : ι) :
    Set.EqOn (C.gram.field a) (D.gram.field a)
      (C.gram.domain ∩ D.gram.domain) :=
  C.anchored.compatible D.anchored a

/-- At one fixed source index, the maximal anchored chart family is a
directly compatible Hilbert-field atlas. -/
def toCompatibleHilbertFieldAtlas
    (a : ι) :
    CompatibleHilbertFieldAtlas H m
      (SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField) where
  domain C := C.gram.domain
  domain_open C := C.gram.domain_open
  field C := C.gram.field a
  field_holomorphic C := C.gram.field_holomorphic a
  compatible C D := compatible C D a

/-- The global source field obtained by gluing all anchored charts. -/
def gluedField
    (a : ι) :
    (Fin m → ℂ) → H :=
  SCV.glued_iUnion
    (fun C :
      SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField =>
      C.gram.domain)
    (fun C => C.gram.field a)

theorem gluedField_eqOn_domain
    (C :
      SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField)
    (a : ι) :
    Set.EqOn
      (gluedField
        (H := H) (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) a)
      (C.gram.field a) C.gram.domain :=
  SCV.glued_iUnion_eqOn
    (fun C D => compatible C D a) C

theorem gluedField_holomorphic
    (a : ι) :
    DifferentiableOn ℂ
      (gluedField
        (H := H) (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) a)
      (coveredDomain
        (H := H) (ι := ι) (m := m)
        (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField)) := by
  exact
    SCV.differentiableOn_glued_iUnion
      (fun _ hz => hz)
      (fun C => C.gram.domain_open)
      (fun C => C.gram.field_holomorphic a)
      (fun C D => compatible C D a)

@[simp]
theorem toCompatibleHilbertFieldAtlas_coveredDomain
    (a : ι) :
    (toCompatibleHilbertFieldAtlas
      (H := H) (scalar := scalar)
      (anchorPoint := anchorPoint)
      (anchorField := anchorField) a).coveredDomain =
        coveredDomain
          (H := H) (ι := ι) (m := m)
          (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField) :=
  rfl

@[simp]
theorem toCompatibleHilbertFieldAtlas_gluedField
    (a : ι) :
    (toCompatibleHilbertFieldAtlas
      (H := H) (scalar := scalar)
      (anchorPoint := anchorPoint)
      (anchorField := anchorField) a).gluedField =
        gluedField
          (H := H) (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField) a :=
  rfl

/-- The glued field remains in the common closed anchor span. -/
theorem gluedField_mem_sourceAnchorSpan
    (a : ι)
    (z : Fin m → ℂ)
    (hz :
      z ∈
        coveredDomain
          (H := H) (ι := ι) (m := m)
          (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField)) :
    gluedField
        (H := H) (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) a z ∈
      sourceAnchorSpan anchorField := by
  rcases Set.mem_iUnion.mp hz with ⟨C, hzC⟩
  rw [gluedField_eqOn_domain C a hzC]
  exact C.anchored.field_mem_sourceAnchorSpan a z hzC

/-- The fixed-anchor scalar identity survives global gluing. -/
theorem scalar_eq_inner_anchor_gluedField
    (a b : ι)
    (z : Fin m → ℂ)
    (hz :
      z ∈
        coveredDomain
          (H := H) (ι := ι) (m := m)
          (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField)) :
    scalar a b (reflectedAnchorPair anchorPoint z) =
      @inner ℂ H _ (anchorField a)
        (gluedField
          (H := H) (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField) b z) := by
  rcases Set.mem_iUnion.mp hz with ⟨C, hzC⟩
  rw [gluedField_eqOn_domain C b hzC]
  exact C.anchored.scalar_eq_inner_anchor a b z hzC

/-- On every local chart, the glued source fields retain the complete
prescribed reflected-Gram identity. -/
theorem scalar_eq_gluedKernel_on_chart
    (C :
      SourceIndexedAnchoredReflectedGramChart
        H ι m scalar anchorPoint anchorField)
    (a b : ι) :
    Set.EqOn (scalar a b)
      (reflectedHilbertPairKernel
        (gluedField
          (H := H) (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField) a)
        (gluedField
          (H := H) (scalar := scalar)
          (anchorPoint := anchorPoint)
          (anchorField := anchorField) b))
      (reflectedHilbertPairKernelDomain
        C.gram.domain C.gram.domain) := by
  intro w hw
  calc
    scalar a b w =
        reflectedHilbertPairKernel
          (C.gram.field a) (C.gram.field b) w :=
      C.gram.scalar_eq_kernel a b hw
    _ =
        reflectedHilbertPairKernel
          (gluedField
            (H := H) (scalar := scalar)
            (anchorPoint := anchorPoint)
            (anchorField := anchorField) a)
          (gluedField
            (H := H) (scalar := scalar)
            (anchorPoint := anchorPoint)
            (anchorField := anchorField) b) w := by
      unfold reflectedHilbertPairKernel
      rw [
        ← gluedField_eqOn_domain C a hw.1,
        ← gluedField_eqOn_domain C b hw.2]

/-- Any family of anchored charts reaching a target set proves coverage by
the maximal anchored atlas. -/
theorem subset_coveredDomain_of_exists_chart
    (U : Set (Fin m → ℂ))
    (hchart :
      ∀ z ∈ U,
        ∃ C :
            SourceIndexedAnchoredReflectedGramChart
              H ι m scalar anchorPoint anchorField,
          z ∈ C.gram.domain) :
    U ⊆
      coveredDomain
        (H := H) (ι := ι) (m := m)
        (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) := by
  intro z hz
  obtain ⟨C, hzC⟩ := hchart z hz
  exact Set.mem_iUnion.mpr ⟨C, hzC⟩

end SourceIndexedAnchoredReflectedGramChart

namespace SourceIndexedAnchoredReflectedGramContinuationChain

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {ι : Type*} {k : ℕ}
  {scalar :
    ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
  {anchorPoint : Fin (k + 1) → ℂ}
  {anchorField : ι → H}
  {P : SourceIndexedReflectedGramHilbertFieldData
    H ι (k + 1) scalar}

end SourceIndexedAnchoredReflectedGramContinuationChain

/-- An anchored chart reached by an actual finite Cauchy continuation chain
from one fixed reflected-Gram seed.

The unrestricted maximal atlas is useful for qualitative gluing, but it can
contain charts with unrelated scalar holomorphy domains.  This provenance-
carrying chart type retains the initial seed, hence the common scalar domain
which every continuation step preserves. -/
structure SourceIndexedReachableAnchoredReflectedGramChart
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    (iota : Type*) (k : Nat)
    (scalar :
      iota -> iota ->
        (Fin ((k + 1) + (k + 1)) -> Complex) -> Complex)
    (anchorPoint : Fin (k + 1) -> Complex)
    (anchorField : iota -> H)
    (P : SourceIndexedReflectedGramHilbertFieldData
      H iota (k + 1) scalar) where
  steps : Nat
  chain : SourceIndexedReflectedGramContinuationChain
    H iota k scalar P steps
  anchored : SourceIndexedAnchoredReflectedGramHilbertFieldData
    scalar anchorPoint anchorField chain.terminal

namespace SourceIndexedReachableAnchoredReflectedGramChart

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [CompleteSpace H]
  {iota : Type*} {k : Nat}
  {scalar :
    iota -> iota ->
      (Fin ((k + 1) + (k + 1)) -> Complex) -> Complex}
  {anchorPoint : Fin (k + 1) -> Complex}
  {anchorField : iota -> H}
  {P : SourceIndexedReflectedGramHilbertFieldData
    H iota (k + 1) scalar}

/-- Forget only the finite-chain provenance, retaining the ordinary anchored
chart consumed by the existing global gluing API. -/
def toAnchoredChart
    (C : SourceIndexedReachableAnchoredReflectedGramChart
      H iota k scalar anchorPoint anchorField P) :
    SourceIndexedAnchoredReflectedGramChart
      H iota (k + 1) scalar anchorPoint anchorField where
  gram := C.chain.terminal
  anchored := C.anchored

/-- The open union of precisely the anchored charts reachable from `P`. -/
def coveredDomain : Set (Fin (k + 1) -> Complex) :=
  ⋃ C : SourceIndexedReachableAnchoredReflectedGramChart
      H iota k scalar anchorPoint anchorField P,
    C.chain.terminal.domain

theorem coveredDomain_open :
    IsOpen (coveredDomain
      (H := H) (iota := iota) (k := k)
      (scalar := scalar)
      (anchorPoint := anchorPoint)
      (anchorField := anchorField) (P := P)) :=
  isOpen_iUnion fun C => C.chain.terminal.domain_open

/-- Reachable coverage is a quantitative subatlas of the existing maximal
anchored atlas. -/
theorem coveredDomain_subset_maximal :
    coveredDomain
        (H := H) (iota := iota) (k := k)
        (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) (P := P) ⊆
      SourceIndexedAnchoredReflectedGramChart.coveredDomain
        (H := H) (ι := iota) (m := k + 1)
        (scalar := scalar)
        (anchorPoint := anchorPoint)
        (anchorField := anchorField) := by
  intro z hz
  obtain ⟨C, hzC⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨C.toAnchoredChart, hzC⟩

end SourceIndexedReachableAnchoredReflectedGramChart

/-- Anchored finite-chain reachability covers the complete generated mixed
carrier inside the quantitative subatlas rooted at the initial Gram seed. -/
theorem generatedMixedCarrier_subset_reachableAnchoredAtlasCoveredDomain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {ι : Type*} {k N : ℕ}
    {scalar :
      ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
    {anchorField : ι → H}
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar (0 : Fin (k + 1) → ℂ) anchorField P)
    {d : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d
      ((k + 1) + ((k + 1) + 1)))
    (η : SchwartzMap
      (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η :
            (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion
          ((k + 1) + ((k + 1) + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((k + 1) + ((k + 1) + 1)) N) ⊆
        A.carrier)
    (hscalarDomain :
      P.scalarDomain = reflectedMovingSliceCarrier A η)
    (hzero : (0 : Fin (k + 1) → ℂ) ∈ P.domain) :
    osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((k + 1) + 1) N) ⊆
      SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain
        (H := H) (iota := ι) (k := k)
        (scalar := scalar)
        (anchorPoint := (0 : Fin (k + 1) → ℂ))
        (anchorField := anchorField) (P := P) := by
  intro z hz
  obtain ⟨n, C, Aterminal, hzC⟩ :=
    exists_anchored_chain_reaching_generatedMixedCarrier
      P A₀ A η hη_support hgenerated hscalarDomain hzero hz
  exact Set.mem_iUnion.mpr
    ⟨{ steps := n, chain := C, anchored := Aterminal }, hzC⟩

/-- Anchored finite-chain reachability gives coverage of the complete
generated mixed carrier by the maximal anchored atlas. -/
theorem generatedMixedCarrier_subset_anchoredAtlasCoveredDomain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {ι : Type*} {k N : ℕ}
    {scalar :
      ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
    {anchorField : ι → H}
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    (A₀ : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar (0 : Fin (k + 1) → ℂ) anchorField P)
    {d : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d
      ((k + 1) + ((k + 1) + 1)))
    (η : SchwartzMap
      (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) ℂ)
    (hη_support :
      tsupport
          (η :
            (Fin ((k + 1) + ((k + 1) + 1)) → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion
          ((k + 1) + ((k + 1) + 1)))
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((k + 1) + ((k + 1) + 1)) N) ⊆
        A.carrier)
    (hscalarDomain :
      P.scalarDomain = reflectedMovingSliceCarrier A η)
    (hzero : (0 : Fin (k + 1) → ℂ) ∈ P.domain) :
    osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((k + 1) + 1) N) ⊆
      SourceIndexedAnchoredReflectedGramChart.coveredDomain
        (H := H) (ι := ι) (m := k + 1)
        (scalar := scalar)
        (anchorPoint := (0 : Fin (k + 1) → ℂ))
    (anchorField := anchorField) :=
  (generatedMixedCarrier_subset_reachableAnchoredAtlasCoveredDomain
      P A₀ A η hη_support hgenerated hscalarDomain hzero).trans
    SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain_subset_maximal

end OSIIChapterV
end OSReconstruction
