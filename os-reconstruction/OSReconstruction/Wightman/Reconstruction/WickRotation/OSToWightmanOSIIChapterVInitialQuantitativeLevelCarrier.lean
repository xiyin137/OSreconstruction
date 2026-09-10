/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialExplicitLevelCarrier














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- A norm radius for the support of one base/time partition cutoff.

Unlike `LevelCarrierBaseRadiusData`, this datum depends only on the cutoff
itself.  It can therefore be reused definitionally when one carrier partition
is specialized to a family of shrinking time tests. -/
structure SchwartzCutoffRadiusData
    (χ : SchwartzMap (InitialBaseTimeSpace d k) ℂ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  bound :
    ∀ p ∈ tsupport (χ : InitialBaseTimeSpace d k → ℂ),
      ‖p‖ ≤ radius

theorem nonempty_schwartzCutoffRadiusData
    (χ : SchwartzMap (InitialBaseTimeSpace d k) ℂ)
    (hχ_compact :
      HasCompactSupport
        (χ : InitialBaseTimeSpace d k → ℂ)) :
    Nonempty (SchwartzCutoffRadiusData χ) := by
  obtain ⟨R, hR⟩ :=
    hχ_compact.isCompact.isBounded.subset_closedBall
      (0 : InitialBaseTimeSpace d k)
  let R₀ : ℝ := max R 0
  refine ⟨{
    radius := R₀
    radius_nonneg := le_max_right R 0
    bound := ?_ }⟩
  intro p hp
  have hpR : ‖p‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hp
  exact hpR.trans (le_max_left R 0)

/-- Canonical radius selected from a compact Schwartz cutoff. -/
noncomputable def schwartzCutoffRadiusData
    (χ : SchwartzMap (InitialBaseTimeSpace d k) ℂ)
    (hχ_compact :
      HasCompactSupport
        (χ : InitialBaseTimeSpace d k → ℂ)) :
    SchwartzCutoffRadiusData χ :=
  Classical.choice (nonempty_schwartzCutoffRadiusData χ hχ_compact)

/-- A fixed norm radius for the compact base/time footprint of one member of
the time partition. -/
structure LevelCarrierBaseRadiusData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  bound :
    ∀ p ∈
        initialBaseTimeFootprint (d := d) φ ∩
          tsupport (D.cutoff a : InitialBaseTimeSpace d k → ℂ),
      ‖p‖ ≤ radius

/-- Canonical route-local selection of the fixed base/time radius. -/
noncomputable def levelCarrierBaseRadiusData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    D.LevelCarrierBaseRadiusData a :=
  let R :=
    schwartzCutoffRadiusData (D.cutoff a) (D.cutoff_compact a)
  {
    radius := R.radius
    radius_nonneg := R.radius_nonneg
    bound := fun p hp => R.bound p hp.2 }

/-- Fixed time slab used by every level carrier for one time-partition
piece. -/
noncomputable def levelCarrierTimeRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    ℝ :=
  ‖initialBaseTimeConfigurationCLM d k‖ *
      (D.levelCarrierBaseRadiusData a hφ_compact).radius + 1

theorem levelCarrierTimeRadius_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    0 < D.levelCarrierTimeRadius a hφ_compact := by
  dsimp [levelCarrierTimeRadius]
  have hnonneg :
      0 ≤ ‖initialBaseTimeConfigurationCLM d k‖ *
        (D.levelCarrierBaseRadiusData a hφ_compact).radius :=
    mul_nonneg (norm_nonneg _)
      (D.levelCarrierBaseRadiusData a hφ_compact).radius_nonneg
  linarith

/-- Inner norm radius on which the coherent radial cutoff at level `N` will
equal one. -/
noncomputable def levelCarrierInnerNormRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  ‖initialFullConfigurationFromBaseTimeSpatialCLM d k‖ *
      ((D.levelCarrierBaseRadiusData a hφ_compact).radius +
        2 *
          ‖(section43SpatialFlatCLE d k).symm.toContinuousLinearMap‖ *
            bumpTruncationRadiusValue N) +
    2

theorem levelCarrierInnerNormRadius_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    0 < D.levelCarrierInnerNormRadius a hφ_compact N := by
  have hbase :
      0 ≤ (D.levelCarrierBaseRadiusData a hφ_compact).radius :=
    (D.levelCarrierBaseRadiusData a hφ_compact).radius_nonneg
  have hR : 0 ≤ bumpTruncationRadiusValue N :=
    (bumpTruncationRadiusValue_pos N).le
  have hterm :
      0 ≤ ‖initialFullConfigurationFromBaseTimeSpatialCLM d k‖ *
        ((D.levelCarrierBaseRadiusData a hφ_compact).radius +
          2 *
            ‖(section43SpatialFlatCLE d k).symm.toContinuousLinearMap‖ *
              bumpTruncationRadiusValue N) := by
    positivity
  dsimp [levelCarrierInnerNormRadius]
  linarith

theorem one_lt_levelCarrierInnerNormRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    1 < D.levelCarrierInnerNormRadius a hφ_compact N := by
  have hbase :
      0 ≤ (D.levelCarrierBaseRadiusData a hφ_compact).radius :=
    (D.levelCarrierBaseRadiusData a hφ_compact).radius_nonneg
  have hR : 0 ≤ bumpTruncationRadiusValue N :=
    (bumpTruncationRadiusValue_pos N).le
  have hterm :
      0 ≤ ‖initialFullConfigurationFromBaseTimeSpatialCLM d k‖ *
        ((D.levelCarrierBaseRadiusData a hφ_compact).radius +
          2 *
            ‖(section43SpatialFlatCLE d k).symm.toContinuousLinearMap‖ *
              bumpTruncationRadiusValue N) := by
    positivity
  dsimp [levelCarrierInnerNormRadius]
  linarith

/-- Radius used by the explicit coherent carrier bump. The quantitative
inner radius contains one spare unit, so this smaller radius still contains
the source carrier while leaving a strict margin inside the declared outer
support radius. -/
noncomputable def levelCarrierRadialNormRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  D.levelCarrierInnerNormRadius a hφ_compact N - 1

theorem levelCarrierRadialNormRadius_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    0 < D.levelCarrierRadialNormRadius a hφ_compact N := by
  dsimp [levelCarrierRadialNormRadius]
  linarith [D.one_lt_levelCarrierInnerNormRadius a hφ_compact N]

/-- Explicit outer norm radius for the support of the coherent radial cutoff
at level `N`. -/
noncomputable def levelCarrierNormRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  2 * D.levelCarrierInnerNormRadius a hφ_compact N + 1

theorem levelCarrierNormRadius_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    0 < D.levelCarrierNormRadius a hφ_compact N := by
  dsimp [levelCarrierNormRadius]
  have hinner := D.levelCarrierInnerNormRadius_pos a hφ_compact N
  linarith

/-- One finite-partition time radius dominating every fixed time piece. -/
noncomputable def commonLevelCarrierTimeRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    ℝ :=
  ∑ a, D.levelCarrierTimeRadius a hφ_compact

theorem levelCarrierTimeRadius_le_common
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    D.levelCarrierTimeRadius a hφ_compact ≤
      D.commonLevelCarrierTimeRadius hφ_compact := by
  exact
    Finset.single_le_sum
      (fun b _hb => (D.levelCarrierTimeRadius_pos b hφ_compact).le)
      (Finset.mem_univ a)

theorem commonLevelCarrierTimeRadius_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    0 < D.commonLevelCarrierTimeRadius hφ_compact :=
  (D.levelCarrierTimeRadius_pos a hφ_compact).trans_le
    (D.levelCarrierTimeRadius_le_common a hφ_compact)

/-- One level-dependent norm radius dominating every member of the fixed
finite time partition. -/
noncomputable def commonLevelCarrierNormRadius
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  ∑ a, D.levelCarrierNormRadius a hφ_compact N

theorem levelCarrierNormRadius_le_common
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.levelCarrierNormRadius a hφ_compact N ≤
      D.commonLevelCarrierNormRadius hφ_compact N := by
  exact
    Finset.single_le_sum
      (fun b _hb => (D.levelCarrierNormRadius_pos b hφ_compact N).le)
      (Finset.mem_univ a)

/-- Compact full-configuration carrier obtained from the fixed base/time
footprint and the explicit level bump. -/
def levelPieceConfigurationCarrierSet
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ) :
    Set (NPointDomain d (k + 1)) :=
  initialFullConfigurationFromBaseTimeSpatialCLM d k ''
    ((initialBaseTimeFootprint (d := d) φ ∩
        tsupport (D.cutoff a : InitialBaseTimeSpace d k → ℂ)) ×ˢ
      tsupport
        ((initialSpatialFactorBump d k N :
          SchwartzMap (Section43SpatialSpace d k) ℂ) :
            Section43SpatialSpace d k → ℂ))

theorem levelPiece_support_subset_configurationCarrierSet
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    tsupport
        ((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ) ⊆
      D.levelPieceConfigurationCarrierSet a N := by
  intro x hx
  have hcoordinates :=
    D.levelPiece_support_coordinates a N χ x hx
  refine
    ⟨(initialBaseTimeProjectionCLM d k x,
        section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x)),
      hcoordinates, ?_⟩
  exact
    initialFullConfigurationFromBaseTimeSpatialCLM_apply_canonical
      (d := d) (k := k) x

/-- Projection of the compact full carrier to one absolute spacetime
coordinate. -/
def levelPieceOnePointCarrierSet
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ)
    (i : Fin (k + 1)) :
    Set (SpacetimeDim d) :=
  (fun x : NPointDomain d (k + 1) => x i) ''
    D.levelPieceConfigurationCarrierSet a N

theorem levelPieceOnePointCarrierSet_radial_norm_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ D.levelPieceOnePointCarrierSet a N i) :
    ‖y‖ < D.levelCarrierRadialNormRadius a hφ_compact N := by
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨p, hp, rfl⟩
  let L := initialFullConfigurationFromBaseTimeSpatialCLM d k
  let E :=
    (section43SpatialFlatCLE d k).symm.toContinuousLinearMap
  have hp_bound :=
    (D.levelCarrierBaseRadiusData a hφ_compact).bound p.1 hp.1
  have hflat :
      ‖section43SpatialFlatCLE d k p.2‖ ≤
        2 * bumpTruncationRadiusValue N := by
    have hmem :=
      initialSpatialFactorBump_tsupport_flat_subset_closedBall
        (d := d) (k := k) N
        ⟨p.2, hp.2, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hspatial :
      ‖p.2‖ ≤
        2 * ‖E‖ * bumpTruncationRadiusValue N := by
    have hinverse :
        E (section43SpatialFlatCLE d k p.2) = p.2 := by
      exact (section43SpatialFlatCLE d k).symm_apply_apply p.2
    calc
      ‖p.2‖ = ‖E (section43SpatialFlatCLE d k p.2)‖ := by
        rw [hinverse]
      _ ≤ ‖E‖ * ‖section43SpatialFlatCLE d k p.2‖ :=
        ContinuousLinearMap.le_opNorm E _
      _ ≤ ‖E‖ * (2 * bumpTruncationRadiusValue N) := by
        gcongr
      _ = 2 * ‖E‖ * bumpTruncationRadiusValue N := by
        ring
  have hpair :
      ‖p‖ ≤
        (D.levelCarrierBaseRadiusData a hφ_compact).radius +
          2 * ‖E‖ * bumpTruncationRadiusValue N := by
    rw [norm_prod_le_iff]
    constructor
    · exact hp_bound.trans
        (le_add_of_nonneg_right
          (mul_nonneg
            (mul_nonneg (by norm_num) (norm_nonneg E))
            (bumpTruncationRadiusValue_pos N).le))
    · exact hspatial.trans
        (le_add_of_nonneg_left
          (D.levelCarrierBaseRadiusData a hφ_compact).radius_nonneg)
  calc
    ‖L p i‖ ≤ ‖L p‖ :=
      norm_le_pi_norm _ i
    _ ≤ ‖L‖ * ‖p‖ :=
      ContinuousLinearMap.le_opNorm L p
    _ ≤
        ‖L‖ *
          ((D.levelCarrierBaseRadiusData a hφ_compact).radius +
            2 * ‖E‖ * bumpTruncationRadiusValue N) := by
      gcongr
    _ <
        ‖L‖ *
            ((D.levelCarrierBaseRadiusData a hφ_compact).radius +
              2 * ‖E‖ * bumpTruncationRadiusValue N) + 1 := by
      linarith
    _ = D.levelCarrierRadialNormRadius a hφ_compact N := by
      dsimp [levelCarrierRadialNormRadius, levelCarrierInnerNormRadius, L, E]
      ring

theorem levelPieceOnePointCarrierSet_inner_norm_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ D.levelPieceOnePointCarrierSet a N i) :
    ‖y‖ < D.levelCarrierInnerNormRadius a hφ_compact N := by
  exact
    (D.levelPieceOnePointCarrierSet_radial_norm_bound
      a hφ_compact N i hy).trans
      (by
        dsimp [levelCarrierRadialNormRadius]
        linarith)

/-- Quantitative carrier family for one spatial truncation level. -/
structure QuantitativeLevelCover
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) where
  carrier : D.index → OSIIChronologicalCompactFactors d k
  carrier_fix :
    ∀ a χ,
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor (carrier a).factors)
          (D.levelPiece a N χ) =
        D.levelPiece a N χ
  carrier_time_bound :
    ∀ a i y,
      y ∈ tsupport
          (((carrier a).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        |y 0| < D.levelCarrierTimeRadius a hφ_compact
  carrier_norm_bound :
    ∀ a i y,
      y ∈ tsupport
          (((carrier a).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        ‖y‖ < D.levelCarrierNormRadius a hφ_compact N

def QuantitativeLevelCover.toLevelCover
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (C : D.QuantitativeLevelCover hφ_compact N) :
    D.LevelCover N where
  carrier := C.carrier
  carrier_fix := C.carrier_fix

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
