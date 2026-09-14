/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialFiniteShell
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchyKernel

















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One scale-indexed family of product-Hermite Hilbert fields on a fixed
open complex domain. -/
structure GeneratorOpenHilbertFieldScaleBlockData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (m : ℕ) where
  domain : Set (Fin m → ℂ)
  domain_open : IsOpen domain
  field : ℕ → ℕ → (Fin m → ℂ) → OSHilbertSpace OS
  field_holomorphic :
    ∀ scale mode,
      DifferentiableOn ℂ (field scale mode) domain
  field_polyBounded_on_compact :
    ∀ K, IsCompact K → K ⊆ domain →
      ∃ C > 0, ∃ p : ℕ,
        ∀ scale z, z ∈ K → ∀ mode,
          ‖field scale mode z‖ ≤
            C * (1 + (mode : ℝ)) ^ p

namespace GeneratorOpenHilbertFieldScaleBlockData

variable {d m : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

end GeneratorOpenHilbertFieldScaleBlockData

/-- Left and right Hilbert fields for every generator split and packet scale
on scale-independent open domains.

Only the product-Hermite fields needed by the generator construction are
stored.  Their source realization is a separate real-edge obligation. -/
structure GeneratorOpenHilbertFieldScaleFamilyData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (k : ℕ) where
  leftDomain :
    (i : GeneratorIndex k) → Set (Fin (i.n - 1) → ℂ)
  rightDomain :
    (i : GeneratorIndex k) → Set (Fin (i.m - 1) → ℂ)
  leftDomain_open :
    ∀ i, IsOpen (leftDomain i)
  rightDomain_open :
    ∀ i, IsOpen (rightDomain i)
  leftField :
    (i : GeneratorIndex k) → ℕ → ℕ →
      (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS
  rightField :
    (i : GeneratorIndex k) → ℕ → ℕ →
      (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS
  leftField_holomorphic :
    ∀ i scale mode,
      DifferentiableOn ℂ
        (leftField i scale mode) (leftDomain i)
  rightField_holomorphic :
    ∀ i scale mode,
      DifferentiableOn ℂ
        (rightField i scale mode) (rightDomain i)
  leftField_polyBounded_on_compact :
    ∀ i K, IsCompact K → K ⊆ leftDomain i →
      ∃ C > 0, ∃ p : ℕ,
        ∀ scale z, z ∈ K → ∀ mode,
          ‖leftField i scale mode z‖ ≤
            C * (1 + (mode : ℝ)) ^ p
  rightField_polyBounded_on_compact :
    ∀ i K, IsCompact K → K ⊆ rightDomain i →
      ∃ C > 0, ∃ p : ℕ,
        ∀ scale z, z ∈ K → ∀ mode,
          ‖rightField i scale mode z‖ ≤
            C * (1 + (mode : ℝ)) ^ p

namespace GeneratorOpenHilbertFieldScaleFamilyData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Assemble the all-split family from one open-domain block package on each
side of every split. -/
def ofBlocks
    (left :
      (i : GeneratorIndex k) →
        GeneratorOpenHilbertFieldScaleBlockData OS (i.n - 1))
    (right :
      (i : GeneratorIndex k) →
        GeneratorOpenHilbertFieldScaleBlockData OS (i.m - 1)) :
    GeneratorOpenHilbertFieldScaleFamilyData OS k where
  leftDomain i := (left i).domain
  rightDomain i := (right i).domain
  leftDomain_open i := (left i).domain_open
  rightDomain_open i := (right i).domain_open
  leftField i := (left i).field
  rightField i := (right i).field
  leftField_holomorphic i := (left i).field_holomorphic
  rightField_holomorphic i := (right i).field_holomorphic
  leftField_polyBounded_on_compact i :=
    (left i).field_polyBounded_on_compact
  rightField_polyBounded_on_compact i :=
    (right i).field_polyBounded_on_compact

/-- The scale-independent semigroup domain associated with one split. -/
def domain
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  generatorSemigroupDomain i (B.leftDomain i) (B.rightDomain i)

theorem domain_open
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k) :
    IsOpen (B.domain i) :=
  isOpen_generatorSemigroupDomain i
    (B.leftDomain_open i) (B.rightDomain_open i)

/-- The genuine scalar semigroup mode uses the original-OS holomorphic
semigroup, with no quantitative growth hypothesis. -/
def modeOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (i : GeneratorIndex k)
    (mode : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  generatorSpatialHermiteModeOfOS OS i
    (B.leftField i scale) (B.rightField i scale) mode

/-- Compatibility presentation of the original-OS scalar semigroup mode. -/
def mode
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (i : GeneratorIndex k)
    (mode : ℕ) :
    OSIITimeGapSpace k → ℂ :=
  generatorSpatialHermiteMode OS lgc i
    (B.leftField i scale) (B.rightField i scale) mode

/-- Open-domain original-OS generator modes are holomorphic at every packet
scale and Hermite index. -/
theorem modeOfOS_holomorphic
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (i : GeneratorIndex k)
    (mode : ℕ) :
    DifferentiableOn ℂ
      (B.modeOfOS scale i mode) (B.domain i) :=
  differentiableOn_generatorSpatialHermiteModeOfOS
    OS i
    (B.leftDomain_open i) (B.rightDomain_open i)
    (B.leftField i scale) (B.rightField i scale)
    (B.leftField_holomorphic i scale)
    (B.rightField_holomorphic i scale)
    mode

theorem mode_holomorphic
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (i : GeneratorIndex k)
    (mode : ℕ) :
    DifferentiableOn ℂ
      (B.mode lgc scale i mode) (B.domain i) :=
  B.modeOfOS_holomorphic scale i mode

/-- Every point of a generator domain has a compact neighborhood still
contained in that domain. -/
theorem exists_compact_generatorNeighborhood
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ B.domain i) :
    ∃ L : Set (OSIITimeGapSpace k),
      IsCompact L ∧ z ∈ interior L ∧ L ⊆ B.domain i := by
  obtain ⟨L, hL_compact, hzL, hL_domain⟩ :=
    exists_compact_between
      (isCompact_singleton : IsCompact ({z} : Set (OSIITimeGapSpace k)))
      (B.domain_open i)
      (by simpa using hz)
  exact ⟨L, hL_compact, hzL (by simp), hL_domain⟩

set_option backward.isDefEq.respectTransparency false in
/-- On each compact generator domain, one original-OS polynomial mode bound
works simultaneously for all packet scales. -/
theorem modeOfOS_polyBounded_on_compact_uniform_scale
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    ∃ C > 0, ∃ p : ℕ,
      ∀ scale mode z, z ∈ K →
        ‖B.modeOfOS scale i mode z‖ ≤
          C * (1 + (mode : ℝ)) ^ p := by
  let KL : Set (Fin (i.n - 1) → ℂ) :=
    (fun w => star (i.leftCoordinatesCLM w)) '' K
  let KR : Set (Fin (i.m - 1) → ℂ) :=
    i.rightCoordinatesCLM '' K
  have hKL_compact : IsCompact KL :=
    hK_compact.image
      (continuous_star.comp i.leftCoordinatesCLM.continuous)
  have hKR_compact : IsCompact KR :=
    hK_compact.image i.rightCoordinatesCLM.continuous
  have hKL_domain : KL ⊆ B.leftDomain i := by
    rintro _ ⟨w, hw, rfl⟩
    have hdom := hK_domain hw
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (B.leftDomain i) (B.rightDomain i) at hdom
    exact hdom.2.1
  have hKR_domain : KR ⊆ B.rightDomain i := by
    rintro _ ⟨w, hw, rfl⟩
    have hdom := hK_domain hw
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (B.leftDomain i) (B.rightDomain i) at hdom
    exact hdom.2.2
  obtain ⟨CL, hCL, pL, hleft⟩ :=
    B.leftField_polyBounded_on_compact
      i KL hKL_compact hKL_domain
  obtain ⟨CR, hCR, pR, hright⟩ :=
    B.rightField_polyBounded_on_compact
      i KR hKR_compact hKR_domain
  refine ⟨CL * CR, by positivity, pL + pR, ?_⟩
  intro scale mode w hw
  have hdom := hK_domain hw
  have hbridge : 0 < (w i.bridgeGlobalIndex).re := by
    change
      i.splitCoordinatesCLM w ∈
        bridgedMixedHilbertPairingDomain
          {u : ℂ | 0 < u.re}
          (B.leftDomain i) (B.rightDomain i) at hdom
    exact hdom.1
  have hleftCoord :
      (fun a => -star (w (i.leftGlobalIndex a))) =
        star (i.leftCoordinatesCLM w) := by
    ext a
    simp
  have hleftBound :
      ‖B.leftField i scale mode
          (fun a => -star (w (i.leftGlobalIndex a)))‖ ≤
        CL * (1 + (mode : ℝ)) ^ pL := by
    rw [hleftCoord]
    exact hleft scale _ ⟨w, hw, rfl⟩ mode
  have hrightCoord :
      (fun b => w (i.rightGlobalIndex b)) =
        i.rightCoordinatesCLM w := by
    ext b
    rfl
  have hrightBound :
      ‖B.rightField i scale mode
          (fun b => w (i.rightGlobalIndex b))‖ ≤
        CR * (1 + (mode : ℝ)) ^ pR := by
    rw [hrightCoord]
    exact hright scale _ ⟨w, hw, rfl⟩ mode
  change
    ‖osiiSemigroupMixedHilbertPairing OS
        (B.leftField i scale mode)
        (B.rightField i scale mode)
        (i.splitCoordinatesCLM w)‖ ≤ _
  calc
    ‖osiiSemigroupMixedHilbertPairing OS
        (B.leftField i scale mode)
        (B.rightField i scale mode)
        (i.splitCoordinatesCLM w)‖ ≤
        ‖B.leftField i scale mode
            (fun a => -star (w (i.leftGlobalIndex a)))‖ *
          ‖B.rightField i scale mode
            (fun b => w (i.rightGlobalIndex b))‖ :=
      norm_generatorSemigroupPairing_le_norm_mul
        OS i _ _ w hbridge
    _ ≤
        (CL * (1 + (mode : ℝ)) ^ pL) *
          (CR * (1 + (mode : ℝ)) ^ pR) := by
      gcongr
    _ =
        (CL * CR) *
          (1 + (mode : ℝ)) ^ (pL + pR) := by
      rw [pow_add]
      ring

/-- Compatibility wrapper for the genuine original-OS compact mode bound. -/
theorem mode_polyBounded_on_compact_uniform_scale
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    ∃ C > 0, ∃ p : ℕ,
      ∀ scale mode z, z ∈ K →
        ‖B.mode lgc scale i mode z‖ ≤
          C * (1 + (mode : ℝ)) ^ p :=
  B.modeOfOS_polyBounded_on_compact_uniform_scale
    i K hK_compact hK_domain

/-- At each packet scale, the genuine original-OS modes assemble into the
existing absolute spatial Hermite-mode package. -/
def toAbsoluteSpatialHermiteModeDataOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    GeneratorAbsoluteSpatialHermiteModeData d k where
  lift := lift
  domain := B.domain
  domain_open := B.domain_open
  mode := B.modeOfOS scale
  mode_holomorphic := B.modeOfOS_holomorphic scale

/-- The growth-free compact mode bound gives the exact local polynomial
contract required for the original-OS finite-shell assembly. -/
theorem toAbsoluteSpatialHermiteModeDataOfOS_locallyPolynomiallyBounded
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (B.toAbsoluteSpatialHermiteModeDataOfOS scale lift
      ).LocallyPolynomiallyBounded := by
  intro i z hz
  obtain ⟨K, hK_compact, hzK, hK_domain⟩ :=
    B.exists_compact_generatorNeighborhood i z hz
  obtain ⟨C, hC, p, hbound⟩ :=
    B.modeOfOS_polyBounded_on_compact_uniform_scale
      i K hK_compact hK_domain
  refine
    ⟨interior K,
      mem_nhdsWithin_of_mem_nhds
        (isOpen_interior.mem_nhds hzK),
      C, hC.le, p, ?_⟩
  intro w hw mode
  exact hbound scale mode w (interior_subset hw)

/-- Original-OS spatial Hermite shells are locally uniformly Cauchy on the
complete scale-independent open generator domain. -/
theorem toFiniteShellDataOfOS_locallyUniformCauchy
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (B.toAbsoluteSpatialHermiteModeDataOfOS scale lift
      ).toFiniteShellData.LocallyUniformCauchy :=
  GeneratorAbsoluteSpatialHermiteModeData.toFiniteShellData_locallyUniformCauchy
    (B.toAbsoluteSpatialHermiteModeDataOfOS scale lift)
    (B.toAbsoluteSpatialHermiteModeDataOfOS_locallyPolynomiallyBounded
      scale lift)

/-- Growth-free original-OS spatial Hermite assembly on a general open
generator domain. -/
noncomputable def toSpatialApproximationFamilyOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    GeneratorSpatialApproximationFamily d k :=
  (B.toAbsoluteSpatialHermiteModeDataOfOS scale lift
    ).toFiniteShellData.toApproximationFamily
      (B.toFiniteShellDataOfOS_locallyUniformCauchy scale lift)

@[simp]
theorem toSpatialApproximationFamilyOfOS_domain
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k) :
    (B.toSpatialApproximationFamilyOfOS scale lift).domain i =
      B.domain i :=
  rfl

/-- At one packet scale, the open-domain modes form the existing absolute
spatial Hermite-mode package. -/
def toAbsoluteSpatialHermiteModeData
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    GeneratorAbsoluteSpatialHermiteModeData d k where
  lift := lift
  domain := B.domain
  domain_open := B.domain_open
  mode := B.mode lgc scale
  mode_holomorphic := B.mode_holomorphic lgc scale

/-- The compact-uniform scale bound implies the local polynomial contract at
each fixed scale. -/
theorem toAbsoluteSpatialHermiteModeData_locallyPolynomiallyBounded
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (B.toAbsoluteSpatialHermiteModeData lgc scale lift
      ).LocallyPolynomiallyBounded := by
  intro i z hz
  obtain ⟨K, hK_compact, hzK, hK_domain⟩ :=
    B.exists_compact_generatorNeighborhood i z hz
  obtain ⟨C, hC, p, hbound⟩ :=
    B.mode_polyBounded_on_compact_uniform_scale
      lgc i K hK_compact hK_domain
  refine
    ⟨interior K,
      mem_nhdsWithin_of_mem_nhds
        (isOpen_interior.mem_nhds hzK),
      C, hC.le, p, ?_⟩
  intro w hw mode
  exact hbound scale mode w (interior_subset hw)

/-- Every fixed packet scale therefore gives locally uniformly Cauchy
spatial Hermite shells on the full open generator domain. -/
theorem toFiniteShellData_locallyUniformCauchy
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (B.toAbsoluteSpatialHermiteModeData lgc scale lift
      ).toFiniteShellData.LocallyUniformCauchy :=
  GeneratorAbsoluteSpatialHermiteModeData.toFiniteShellData_locallyUniformCauchy
    (B.toAbsoluteSpatialHermiteModeData lgc scale lift)
    (B.toAbsoluteSpatialHermiteModeData_locallyPolynomiallyBounded
      lgc scale lift)

/-- Assemble one packet scale into the existing weakly holomorphic
spatial-distribution approximation family. -/
noncomputable def toSpatialApproximationFamily
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    GeneratorSpatialApproximationFamily d k :=
  (B.toAbsoluteSpatialHermiteModeData lgc scale lift
    ).toFiniteShellData.toApproximationFamily
      (B.toFiniteShellData_locallyUniformCauchy lgc scale lift)

@[simp]
theorem toSpatialApproximationFamily_domain
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k) :
    (B.toSpatialApproximationFamily lgc scale lift).domain i =
      B.domain i :=
  rfl

/-- The genuine original-OS two-index family before the packet-scale limit;
the first index is the time scale and the second is the Hermite cutoff. -/
noncomputable def twoScaleApproximationOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale shell : ℕ) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  (B.toSpatialApproximationFamilyOfOS scale lift).approximation i shell

/-- The two-index family before the packet-scale limit: the first index is
the time packet scale and the second is the Hermite shell cutoff. -/
noncomputable def twoScaleApproximation
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale shell : ℕ) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  (B.toSpatialApproximationFamily lgc scale lift).approximation i shell

/-- The complete original-OS spatial Hermite series at one packet scale. -/
noncomputable def spatialHermiteScalarSumOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (z : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ℂ :=
  ∑' mode : ℕ,
    B.modeOfOS scale i mode z *
      complexSpatialHermiteCoefficientCLM
        d (k + 1) (Nat.succ_pos k) mode (lift χ)

/-- The explicit full spatial Hermite series at one packet scale. -/
noncomputable def spatialHermiteScalarSum
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (z : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ℂ :=
  ∑' mode : ℕ,
    B.mode lgc scale i mode z *
      complexSpatialHermiteCoefficientCLM
        d (k + 1) (Nat.succ_pos k) mode (lift χ)

/-- The original-OS complete Hermite series has one compact-local bound
independent of the packet scale, with no arity-growth hypothesis. -/
theorem exists_spatialHermiteScalarSumOfOS_norm_bound_on_compact_uniform_scale
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    ∃ M > 0,
      ∀ scale z, z ∈ K →
        ‖B.spatialHermiteScalarSumOfOS
          lift i scale z χ‖ ≤ M := by
  obtain ⟨C, hC, q, hmode⟩ :=
    B.modeOfOS_polyBounded_on_compact_uniform_scale
      i K hK_compact hK_domain
  let coefficient : ℕ → ℂ :=
    fun mode =>
      complexSpatialHermiteCoefficientCLM
        d (k + 1) (Nat.succ_pos k) mode (lift χ)
  let majorant : ℕ → ℝ :=
    fun mode =>
      C * (‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q)
  have hcoefficient :
      Summable fun mode =>
        ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q := by
    simpa [coefficient] using
      (summable_norm_coefficient_mul_weight q (lift χ))
  have hmajorant : Summable majorant := by
    simpa [majorant] using hcoefficient.mul_left C
  have hmajorant_nonneg : 0 ≤ ∑' mode, majorant mode :=
    tsum_nonneg fun mode =>
      mul_nonneg hC.le
        (mul_nonneg (norm_nonneg _)
          (pow_nonneg (by positivity) q))
  refine ⟨(∑' mode, majorant mode) + 1, by positivity, ?_⟩
  intro scale z hz
  have hnorm_summable :
      Summable fun mode =>
        ‖B.modeOfOS scale i mode z * coefficient mode‖ := by
    exact
      Summable.of_nonneg_of_le
        (fun mode => norm_nonneg _)
        (fun mode => by
          rw [norm_mul]
          exact
            (mul_le_mul_of_nonneg_right
              (hmode scale mode z hz)
              (norm_nonneg _)).trans_eq (by
                simp only [majorant]
                ring))
        hmajorant
  rw [spatialHermiteScalarSumOfOS]
  change
    ‖∑' mode,
        B.modeOfOS scale i mode z * coefficient mode‖ ≤ _
  calc
    ‖∑' mode,
        B.modeOfOS scale i mode z * coefficient mode‖
        ≤ ∑' mode,
            ‖B.modeOfOS scale i mode z * coefficient mode‖ :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' mode, majorant mode := by
      apply hnorm_summable.tsum_le_tsum
      · intro mode
        rw [norm_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hmode scale mode z hz)
            (norm_nonneg _)).trans_eq (by
              simp only [majorant]
              ring)
      · exact hmajorant
    _ ≤ (∑' mode, majorant mode) + 1 := by
      linarith

/-- Compatibility wrapper for the genuine original-OS compact Hermite
bound. -/
theorem exists_spatialHermiteScalarSum_norm_bound_on_compact_uniform_scale
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (_lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    ∃ M > 0,
      ∀ scale z, z ∈ K →
        ‖B.spatialHermiteScalarSum
          _lgc lift i scale z χ‖ ≤ M :=
  B.exists_spatialHermiteScalarSumOfOS_norm_bound_on_compact_uniform_scale
    lift i χ K hK_compact hK_domain

/-- Original-OS Hermite shells converge uniformly on each compact generator
set with one modulus valid for every packet scale. -/
theorem
    tendstoUniformlyOn_twoScaleApproximationOfOS_uniform_scale_on_compact
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    TendstoUniformlyOn
      (fun shell (p : ℕ × OSIITimeGapSpace k) =>
        B.twoScaleApproximationOfOS lift i p.1 shell p.2 χ)
      (fun p =>
        B.spatialHermiteScalarSumOfOS lift i p.1 p.2 χ)
      atTop (Set.univ ×ˢ K) := by
  obtain ⟨C, hC, q, hmode⟩ :=
    B.modeOfOS_polyBounded_on_compact_uniform_scale
      i K hK_compact hK_domain
  let coefficient : ℕ → ℂ :=
    fun mode =>
      complexSpatialHermiteCoefficientCLM
        d (k + 1) (Nat.succ_pos k) mode (lift χ)
  let majorant : ℕ → ℝ :=
    fun mode =>
      C * (‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q)
  have hcoefficient :
      Summable fun mode =>
        ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q := by
    simpa [coefficient] using
      (summable_norm_coefficient_mul_weight q (lift χ))
  have hmajorant : Summable majorant := by
    simpa [majorant] using hcoefficient.mul_left C
  have huniform :=
    tendstoUniformlyOn_tsum_nat hmajorant
      (s := Set.univ ×ˢ K)
      (f := fun mode (p : ℕ × OSIITimeGapSpace k) =>
        B.modeOfOS p.1 i mode p.2 * coefficient mode)
      (fun mode p hp => by
        rw [norm_mul]
        calc
          ‖B.modeOfOS p.1 i mode p.2‖ * ‖coefficient mode‖
              ≤ (C * (1 + (mode : ℝ)) ^ q) *
                  ‖coefficient mode‖ := by
                exact mul_le_mul_of_nonneg_right
                  (hmode p.1 mode p.2 hp.2)
                  (norm_nonneg _)
          _ = majorant mode := by
                simp only [majorant]
                ring)
  simpa only [
    twoScaleApproximationOfOS, toSpatialApproximationFamilyOfOS,
    GeneratorSpatialFiniteShellData.toApproximationFamily_approximation,
    GeneratorSpatialFiniteShellData.finiteShell_apply,
    toAbsoluteSpatialHermiteModeDataOfOS,
    GeneratorAbsoluteSpatialHermiteModeData.toFiniteShellData,
    GeneratorAbsoluteSpatialHermiteModeData.coefficient,
    ContinuousLinearMap.comp_apply,
    spatialHermiteScalarSumOfOS, coefficient] using huniform

/-- Compatibility wrapper for growth-free compact-uniform Hermite shell
convergence. -/
theorem
    tendstoUniformlyOn_twoScaleApproximation_uniform_scale_on_compact
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (_lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain : K ⊆ B.domain i) :
    TendstoUniformlyOn
      (fun shell (p : ℕ × OSIITimeGapSpace k) =>
        B.twoScaleApproximation _lgc lift i p.1 shell p.2 χ)
      (fun p =>
        B.spatialHermiteScalarSum _lgc lift i p.1 p.2 χ)
      atTop (Set.univ ×ˢ K) :=
  B.tendstoUniformlyOn_twoScaleApproximationOfOS_uniform_scale_on_compact
    lift i χ K hK_compact hK_domain

/-- The growth-free fixed-scale distribution selects exactly its complete
absolutely convergent Hermite series. -/
theorem
    toSpatialApproximationFamilyOfOS_scalarLimit_eq_spatialHermiteScalarSumOfOS
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (scale : ℕ)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ B.domain i)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (B.toSpatialApproximationFamilyOfOS scale lift
      ).scalarLimit i z χ =
      B.spatialHermiteScalarSumOfOS lift i scale z χ := by
  let A := B.toSpatialApproximationFamilyOfOS scale lift
  have hselected :
      Tendsto
        (fun shell => A.approximation i shell z χ)
        atTop
        (𝓝 (A.scalarLimit i z χ)) :=
    A.pointwise_tendsto i z (by simpa [A] using hz) χ
  have hsum :
      Tendsto
        (fun shell => A.approximation i shell z χ)
        atTop
        (𝓝 (B.spatialHermiteScalarSumOfOS
          lift i scale z χ)) := by
    have hcompact :=
      B.tendstoUniformlyOn_twoScaleApproximationOfOS_uniform_scale_on_compact
        lift i χ {z} isCompact_singleton (by simpa using hz)
    simpa [A, twoScaleApproximationOfOS] using
      hcompact.tendsto_at
        (show (scale, z) ∈ Set.univ ×ˢ ({z} : Set (OSIITimeGapSpace k)) by
          simp)
  exact tendsto_nhds_unique hselected hsum

/-- The original-OS full spatial Hermite series is holomorphic on the
complete open generator domain, with no growth premise. -/
theorem spatialHermiteScalarSumOfOS_differentiableOn
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    DifferentiableOn ℂ
      (fun z => B.spatialHermiteScalarSumOfOS
        lift i scale z χ)
      (B.domain i) := by
  let S := B.toSpatialApproximationFamilyOfOS scale lift
  have hdist :=
    S.distribution_weaklyHolomorphic i χ
  apply hdist.congr
  intro z hz
  rw [S.distribution_apply_of_mem i z (by simpa [S] using hz) χ]
  simpa [S] using
    (B.toSpatialApproximationFamilyOfOS_scalarLimit_eq_spatialHermiteScalarSumOfOS
      scale lift i z hz χ).symm

/-- The explicit full spatial Hermite series is holomorphic on the complete
open generator domain. -/
theorem spatialHermiteScalarSum_differentiableOn
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    DifferentiableOn ℂ
      (fun z => B.spatialHermiteScalarSum
        lgc lift i scale z χ)
      (B.domain i) :=
  B.spatialHermiteScalarSumOfOS_differentiableOn
    lift i scale χ

/-- Genuine original-OS finite two-index Hermite shells are weakly
holomorphic throughout the open generator domain. -/
theorem twoScaleApproximationOfOS_weaklyHolomorphic
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale shell : ℕ) :
    OSIIWeaklyHolomorphicOn
      (B.twoScaleApproximationOfOS lift i scale shell)
      (B.domain i) :=
  (B.toSpatialApproximationFamilyOfOS scale lift
    ).approximation_weaklyHolomorphic i shell

theorem twoScaleApproximation_weaklyHolomorphic
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (i : GeneratorIndex k)
    (scale shell : ℕ) :
    OSIIWeaklyHolomorphicOn
      (B.twoScaleApproximation lgc lift i scale shell)
      (B.domain i) :=
  (B.toSpatialApproximationFamily lgc scale lift
    ).approximation_weaklyHolomorphic i shell

end GeneratorOpenHilbertFieldScaleFamilyData

end OSIIChapterV
end OSReconstruction
