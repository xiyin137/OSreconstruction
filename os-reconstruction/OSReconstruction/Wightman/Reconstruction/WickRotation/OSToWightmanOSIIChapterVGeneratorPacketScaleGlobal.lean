import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldScales
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.LocallyUniformLimit

/-!
# Connected packet-scale continuation for open generator fields

This file isolates the family-independent Vitali--Montel argument used after
a packet-scale limit has been identified on one connected complex germ.

The input is deliberately split into two layers:

* `GeneratorPacketScaleGermData` contains only domain geometry and is
  independent of the spatial test;
* `GeneratorPacketScaleSeedData` supplies the locally uniform limit for one
  spatial test on that germ.

The selected connected branch, its openness and connectedness, and the
global holomorphic packet-scale limit are then constructed once for every
open generator field family.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- A connected packet-scale seed germ inside one open generator-field
domain, together with a nonempty real patch used to identify the limit. -/
structure GeneratorPacketScaleGermData
    (B : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k) where
  germ : Set (OSIITimeGapSpace k)
  germ_open : IsOpen germ
  germ_preconnected : IsPreconnected germ
  center : Fin k → ℝ
  center_mem_germ : SCV.realToComplex center ∈ germ
  germ_subset_domain : germ ⊆ B.domain i
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  center_mem_realRegion : center ∈ realRegion

namespace GeneratorPacketScaleGermData

variable
  {B : GeneratorOpenHilbertFieldScaleFamilyData OS k}
  {i : GeneratorIndex k}

/-- The connected component of the global field domain containing the seed
center. -/
def branch
    (G : GeneratorPacketScaleGermData B i) :
    Set (OSIITimeGapSpace k) :=
  connectedComponentIn (B.domain i) (SCV.realToComplex G.center)

/-- The real seed patch retained inside the complex germ. -/
def realSeedRegion
    (G : GeneratorPacketScaleGermData B i) :
    Set (Fin k → ℝ) :=
  G.realRegion ∩ SCV.realToComplex ⁻¹' G.germ

theorem branch_open
    (G : GeneratorPacketScaleGermData B i) :
    IsOpen G.branch := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hy_domain :
      y ∈ B.domain i :=
    connectedComponentIn_subset
      (B.domain i) (SCV.realToComplex G.center) hy
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (B.domain_open i) y hy_domain
  have hball_component :
      Metric.ball y r ⊆ connectedComponentIn (B.domain i) y :=
    (convex_ball y r).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hr) hball
  rw [← connectedComponentIn_eq hy] at hball_component
  exact
    Filter.mem_of_superset
      (Metric.ball_mem_nhds y hr)
      hball_component

theorem branch_connected
    (G : GeneratorPacketScaleGermData B i) :
    IsConnected G.branch :=
  isConnected_connectedComponentIn_iff.mpr
    (G.germ_subset_domain G.center_mem_germ)

theorem branch_subset_domain
    (G : GeneratorPacketScaleGermData B i) :
    G.branch ⊆ B.domain i :=
  connectedComponentIn_subset _ _

/-- The whole connected seed germ, not just its center, lies in the selected
global branch. -/
theorem germ_subset_branch
    (G : GeneratorPacketScaleGermData B i) :
    G.germ ⊆ G.branch :=
  G.germ_preconnected.subset_connectedComponentIn
    G.center_mem_germ G.germ_subset_domain

theorem realSeedRegion_open
    (G : GeneratorPacketScaleGermData B i) :
    IsOpen G.realSeedRegion := by
  have hrealToComplex :
      Continuous (SCV.realToComplex (m := k)) :=
    continuous_pi fun j =>
      Complex.continuous_ofReal.comp (continuous_apply j)
  exact
    G.realRegion_open.inter
      (hrealToComplex.isOpen_preimage G.germ G.germ_open)

theorem realSeedRegion_nonempty
    (G : GeneratorPacketScaleGermData B i) :
    G.realSeedRegion.Nonempty :=
  ⟨G.center, G.center_mem_realRegion, G.center_mem_germ⟩

end GeneratorPacketScaleGermData

/-- Locally uniform original-OS packet-scale convergence on a genuine
connected source germ for one spatial test. -/
structure GeneratorPacketScaleSeedDataOfOS
    {B : GeneratorOpenHilbertFieldScaleFamilyData OS k}
    {i : GeneratorIndex k}
    (G : GeneratorPacketScaleGermData B i)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) where
  limit : OSIITimeGapSpace k → ℂ
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        B.spatialHermiteScalarSumOfOS
          lift i timeScale z χ)
      limit atTop G.germ

namespace GeneratorPacketScaleSeedDataOfOS

variable
  {B : GeneratorOpenHilbertFieldScaleFamilyData OS k}
  {i : GeneratorIndex k}
  {G : GeneratorPacketScaleGermData B i}
  {lift :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ}
  {χ : SchwartzMap (Section43SpatialSpace d k) ℂ}

/-- A growth-free holomorphic packet-scale limit on the full connected
generator branch, identified with its prescribed real source germ. -/
structure BranchLimitData
    (D : GeneratorPacketScaleSeedDataOfOS G lift χ) where
  limit : OSIITimeGapSpace k → ℂ
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        B.spatialHermiteScalarSumOfOS
          lift i timeScale z χ)
      limit atTop G.branch
  holomorphic :
    DifferentiableOn ℂ limit G.branch
  seed_eq :
    ∀ x ∈ G.realSeedRegion,
      limit (SCV.realToComplex x) =
        D.limit (SCV.realToComplex x)

/-- Original-OS Vitali--Montel extends the source-compatible packet seed to
its entire connected open generator branch. -/
theorem branchLimitData_nonempty
    (D : GeneratorPacketScaleSeedDataOfOS G lift χ) :
    Nonempty D.BranchLimitData := by
  have hholomorphic :
      ∀ timeScale,
        DifferentiableOn ℂ
          (fun z =>
            B.spatialHermiteScalarSumOfOS
              lift i timeScale z χ)
          G.branch := by
    intro timeScale
    exact
      (B.spatialHermiteScalarSumOfOS_differentiableOn
        lift i timeScale χ).mono
          G.branch_subset_domain
  have hbound :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K → K ⊆ G.branch →
          ∃ M : ℝ, 0 < M ∧
            ∀ timeScale z, z ∈ K →
              ‖B.spatialHermiteScalarSumOfOS
                lift i timeScale z χ‖ ≤ M := by
    intro K hK_compact hK_sub
    exact
      B.exists_spatialHermiteScalarSumOfOS_norm_bound_on_compact_uniform_scale
        lift i χ K hK_compact
        (hK_sub.trans G.branch_subset_domain)
  have hreal :
      ∀ x ∈ G.realSeedRegion,
        Tendsto
          (fun timeScale =>
            B.spatialHermiteScalarSumOfOS
              lift i timeScale
                (SCV.realToComplex x) χ)
          atTop
          (𝓝 (D.limit (SCV.realToComplex x))) := by
    intro x hx
    exact D.locallyUniform.tendsto_at hx.2
  obtain ⟨limit, hlimit, hlimit_holomorphic, hlimit_seed⟩ :=
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_tendsto_on_open_real
      G.branch_open G.branch_connected
      G.realSeedRegion_open G.realSeedRegion_nonempty
      (fun x hx => G.germ_subset_branch hx.2)
      hholomorphic hbound hreal
  exact
    ⟨{
      limit := limit
      locallyUniform := hlimit
      holomorphic := hlimit_holomorphic
      seed_eq := hlimit_seed
    }⟩

/-- Choose the canonical original-OS packet-scale limit on the full
connected generator branch. -/
noncomputable def branchLimitData
    (D : GeneratorPacketScaleSeedDataOfOS G lift χ) :
    D.BranchLimitData :=
  Classical.choice D.branchLimitData_nonempty

end GeneratorPacketScaleSeedDataOfOS

/-- Locally uniform packet-scale convergence on one seed germ for one
spatial test. -/
structure GeneratorPacketScaleSeedData
    {B : GeneratorOpenHilbertFieldScaleFamilyData OS k}
    {i : GeneratorIndex k}
    (G : GeneratorPacketScaleGermData B i)
    (lgc : OSLinearGrowthCondition d OS)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) where
  limit : OSIITimeGapSpace k → ℂ
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        B.spatialHermiteScalarSum
          lgc lift i timeScale z χ)
      limit atTop G.germ

namespace GeneratorPacketScaleSeedData

variable
  {B : GeneratorOpenHilbertFieldScaleFamilyData OS k}
  {i : GeneratorIndex k}
  {G : GeneratorPacketScaleGermData B i}
  {lgc : OSLinearGrowthCondition d OS}
  {lift :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ}
  {χ : SchwartzMap (Section43SpatialSpace d k) ℂ}

/-- A selected holomorphic packet-scale limit on the connected global
branch, identified with the seed limit on the real seed patch. -/
structure BranchLimitData
    (D : GeneratorPacketScaleSeedData G lgc lift χ) where
  limit : OSIITimeGapSpace k → ℂ
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        B.spatialHermiteScalarSum
          lgc lift i timeScale z χ)
      limit atTop G.branch
  holomorphic :
    DifferentiableOn ℂ limit G.branch
  seed_eq :
    ∀ x ∈ G.realSeedRegion,
      limit (SCV.realToComplex x) =
        D.limit (SCV.realToComplex x)

/-- Vitali--Montel extends any locally uniform packet-scale seed to the
complete connected component of the global open-field domain. -/
theorem branchLimitData_nonempty
    (D : GeneratorPacketScaleSeedData G lgc lift χ) :
    Nonempty D.BranchLimitData := by
  have hholomorphic :
      ∀ timeScale,
        DifferentiableOn ℂ
          (fun z =>
            B.spatialHermiteScalarSum
              lgc lift i timeScale z χ)
          G.branch := by
    intro timeScale
    exact
      (B.spatialHermiteScalarSum_differentiableOn
        lgc lift i timeScale χ).mono
          G.branch_subset_domain
  have hbound :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K → K ⊆ G.branch →
          ∃ M : ℝ, 0 < M ∧
            ∀ timeScale z, z ∈ K →
              ‖B.spatialHermiteScalarSum
                lgc lift i timeScale z χ‖ ≤ M := by
    intro K hK_compact hK_sub
    exact
      B.exists_spatialHermiteScalarSum_norm_bound_on_compact_uniform_scale
        lgc lift i χ K hK_compact
        (hK_sub.trans G.branch_subset_domain)
  have hreal :
      ∀ x ∈ G.realSeedRegion,
        Tendsto
          (fun timeScale =>
            B.spatialHermiteScalarSum
              lgc lift i timeScale
                (SCV.realToComplex x) χ)
          atTop
          (𝓝 (D.limit (SCV.realToComplex x))) := by
    intro x hx
    exact D.locallyUniform.tendsto_at hx.2
  obtain ⟨limit, hlimit, hlimit_holomorphic, hlimit_seed⟩ :=
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_tendsto_on_open_real
      G.branch_open G.branch_connected
      G.realSeedRegion_open G.realSeedRegion_nonempty
      (fun x hx => G.germ_subset_branch hx.2)
      hholomorphic hbound hreal
  exact
    ⟨{
      limit := limit
      locallyUniform := hlimit
      holomorphic := hlimit_holomorphic
      seed_eq := hlimit_seed
    }⟩

/-- The canonical chosen packet-scale limit on the connected global branch. -/
noncomputable def branchLimitData
    (D : GeneratorPacketScaleSeedData G lgc lift χ) :
    D.BranchLimitData :=
  Classical.choice D.branchLimitData_nonempty

end GeneratorPacketScaleSeedData
end OSIIChapterV
end OSReconstruction
