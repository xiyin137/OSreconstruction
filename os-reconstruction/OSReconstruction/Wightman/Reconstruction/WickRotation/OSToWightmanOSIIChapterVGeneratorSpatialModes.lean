/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialLift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace GeneratorIndex

variable {k : ℕ} (i : GeneratorIndex k)

/-- An admissible split partitions the `k + 1` absolute points into blocks of
sizes `n` and `m`. -/
theorem absoluteCard_eq :
    k + 1 = i.n + i.m := by
  have hn := i.hn
  have hm := i.hm
  have hOne : 1 ≤ i.n + i.m := by omega
  calc
    k + 1 = (i.n + i.m - 1) + 1 := congrArg (· + 1) i.hnm
    _ = i.n + i.m := Nat.sub_add_cancel hOne

/-- Absolute particle index occupied by the `a`-th left source factor. -/
def leftAbsoluteIndex (a : Fin i.n) : Fin (k + 1) :=
  Fin.cast i.absoluteCard_eq.symm (Fin.castAdd i.m a)

/-- Absolute particle index occupied by the `b`-th right source factor. -/
def rightAbsoluteIndex (b : Fin i.m) : Fin (k + 1) :=
  Fin.cast i.absoluteCard_eq.symm (Fin.natAdd i.n b)

@[simp]
theorem leftAbsoluteIndex_val (a : Fin i.n) :
    (i.leftAbsoluteIndex a).val = a.val := by
  simp [leftAbsoluteIndex]

@[simp]
theorem rightAbsoluteIndex_val (b : Fin i.m) :
    (i.rightAbsoluteIndex b).val = i.n + b.val := by
  simp [rightAbsoluteIndex]

end GeneratorIndex

/-- The left spatial product block of an absolute product-Hermite vector. -/
noncomputable def leftSpatialHermiteBlock
    (d : ℕ) [NeZero d] {k : ℕ}
    (i : GeneratorIndex k) (r : ℕ) :
    SchwartzMap (Section43SpatialSpace d i.n) ℂ :=
  (section43SpatialSchwartzParticleCLE d i.n).symm
    (SchwartzMap.productTensor fun a =>
      spatialHermiteFactor d (k + 1) (Nat.succ_pos k) r
        (i.leftAbsoluteIndex a))

/-- The right spatial product block of an absolute product-Hermite vector. -/
noncomputable def rightSpatialHermiteBlock
    (d : ℕ) [NeZero d] {k : ℕ}
    (i : GeneratorIndex k) (r : ℕ) :
    SchwartzMap (Section43SpatialSpace d i.m) ℂ :=
  (section43SpatialSchwartzParticleCLE d i.m).symm
    (SchwartzMap.productTensor fun b =>
      spatialHermiteFactor d (k + 1) (Nat.succ_pos k) r
        (i.rightAbsoluteIndex b))

@[simp]
theorem leftSpatialHermiteBlock_apply
    (d : ℕ) [NeZero d] {k : ℕ}
    (i : GeneratorIndex k) (r : ℕ)
    (η : Section43SpatialSpace d i.n) :
    leftSpatialHermiteBlock d i r η =
      ∏ a, spatialHermiteFactor d (k + 1) (Nat.succ_pos k) r
        (i.leftAbsoluteIndex a)
        (section43SpatialParticleCLE d i.n η a) := by
  simp [leftSpatialHermiteBlock, SchwartzMap.productTensor_apply]

@[simp]
theorem rightSpatialHermiteBlock_apply
    (d : ℕ) [NeZero d] {k : ℕ}
    (i : GeneratorIndex k) (r : ℕ)
    (η : Section43SpatialSpace d i.m) :
    rightSpatialHermiteBlock d i r η =
      ∏ b, spatialHermiteFactor d (k + 1) (Nat.succ_pos k) r
        (i.rightAbsoluteIndex b)
        (section43SpatialParticleCLE d i.m η b) := by
  simp [rightSpatialHermiteBlock, SchwartzMap.productTensor_apply]

/-- The absolute product-Hermite basis vector is exactly the product of the
left and right spatial blocks selected by an admissible generator split. -/
theorem spatialHermite_eq_leftBlock_mul_rightBlock
    (d : ℕ) [NeZero d] {k : ℕ}
    (i : GeneratorIndex k) (r : ℕ)
    (x : Fin (k + 1) → Fin d → ℝ) :
    spatialHermite d (k + 1) (Nat.succ_pos k) r
        ((section43SpatialParticleCLE d (k + 1)).symm x) =
      leftSpatialHermiteBlock d i r
          ((section43SpatialParticleCLE d i.n).symm
            (fun a => x (i.leftAbsoluteIndex a))) *
        rightSpatialHermiteBlock d i r
          ((section43SpatialParticleCLE d i.m).symm
            (fun b => x (i.rightAbsoluteIndex b))) := by
  rw [spatialHermite_apply, leftSpatialHermiteBlock_apply,
    rightSpatialHermiteBlock_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  let F : Fin (k + 1) → ℂ :=
    fun c =>
      spatialHermiteFactor d (k + 1) (Nat.succ_pos k) r c (x c)
  change (∏ c, F c) =
    (∏ a, F (i.leftAbsoluteIndex a)) *
      ∏ b, F (i.rightAbsoluteIndex b)
  calc
    (∏ c, F c) =
        ∏ c : Fin (i.n + i.m),
          F (Fin.cast i.absoluteCard_eq.symm c) := by
      exact Fintype.prod_equiv
        (finCongr i.absoluteCard_eq)
        F
        (fun c : Fin (i.n + i.m) =>
          F (Fin.cast i.absoluteCard_eq.symm c))
        (fun c => by simp)
    _ = (∏ a, F (i.leftAbsoluteIndex a)) *
        ∏ b, F (i.rightAbsoluteIndex b) := by
      rw [Fin.prod_univ_add]
      rfl

/-- A fixed strict-positive difference-time profile turns arbitrary spatial
Schwartz data into a positive-time Euclidean source continuously and
linearly. Spatial compactness is not required. -/
noncomputable def section43PositiveTimeSpatialSourceCLM
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
      euclideanPositiveTimeSubmodule (d := d) n :=
  (section43OrderedPullbackTimeSpatialTensorSpatialCLM d n g.f).codRestrict
    (euclideanPositiveTimeSubmodule (d := d) n)
    (fun χ =>
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d n χ g.f g.positive)

@[simp]
theorem section43PositiveTimeSpatialSourceCLM_coe
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    (section43PositiveTimeSpatialSourceCLM d n g χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ g.f := rfl

/-- Extend the internal chronological displacement of an `n`-point block by
the fixed absolute-time coordinate. The explicit cast records
`(n - 1) + 1 = n` once, rather than leaking dependent arithmetic into every
source-translation theorem. -/
def chronologicalTimeProfileDisplacementOfPositive
    {n : ℕ}
    (hn : 0 < n)
    (u : Fin (n - 1) → ℝ) :
    Fin n → ℝ :=
  fun j =>
    -Fin.cases 0 u
      (Fin.cast (Nat.sub_add_cancel hn).symm j)

/-- Chronological source translation acts only on the finite time profile of
a Section 4.3 time/spatial tensor. The absolute-time coordinate is fixed, the
internal difference-time coordinates are translated with the source-chart
sign, and the spatial factor is unchanged. -/
theorem translate_chronologicalSource_orderedPullbackTimeSpatialTensor
    {d k : ℕ} [NeZero d]
    (u : Fin k → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ) :
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ φ) =
      section43OrderedPullbackTimeSpatialTensorCLM
        d (k + 1) χ
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 u j) φ) := by
  ext x
  rw [translateSchwartzConfiguration_apply]
  simp only [section43OrderedPullbackTimeSpatialTensorCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply]
  rw [section43NPointTimeSpatialTensor_apply,
    section43NPointTimeSpatialTensor_apply]
  rw [chronologicalSourceParameterDisplacement_diff_time,
    chronologicalSourceParameterDisplacement_diff_spatial]
  simp only [SCV.translateSchwartz_apply]
  congr 1

/-- The genuine scalar Hermite generator uses only the original-OS complex
semigroup and its two Hilbert fields. -/
noncomputable def generatorSpatialHermiteModeOfOS
    {d k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    (left :
      ℕ → (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right :
      ℕ → (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (r : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  fun w => osiiSemigroupMixedHilbertPairing OS (left r) (right r)
    (i.splitCoordinatesCLM w)

/-- Compatibility wrapper for the genuine original-OS Hermite generator. -/
noncomputable def generatorSpatialHermiteMode
    {d k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (left :
      ℕ → (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right :
      ℕ → (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (r : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  generatorSpatialHermiteModeOfOS OS i left right r

/-- Holomorphic Hermite fields give a holomorphic original-OS scalar mode,
without any arity-growth hypothesis. -/
theorem differentiableOn_generatorSpatialHermiteModeOfOS
    {d k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (hU : IsOpen U) (hV : IsOpen V)
    (left :
      ℕ → (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right :
      ℕ → (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (hleft : ∀ r, DifferentiableOn ℂ (left r) U)
    (hright : ∀ r, DifferentiableOn ℂ (right r) V)
    (r : ℕ) :
    DifferentiableOn ℂ
      (generatorSpatialHermiteModeOfOS OS i left right r)
      (generatorSemigroupDomain i U V) :=
  differentiableOn_generatorSemigroupPairing
    OS i hU hV (hleft r) (hright r)

end OSIIChapterV
end OSReconstruction
