/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

noncomputable def initialSpatialFactorBump
    (d k N : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ :=
  (section43SpatialFlatSchwartzCLE d k).symm
    (unitBallBumpSchwartzPiRadius
      (k * d) (bumpTruncationRadiusValue N)
      (bumpTruncationRadiusValue_pos N))

theorem initialSpatialFactorTruncationCLM_eq_smulLeft
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialSpatialFactorTruncationCLM d k N χ =
      SchwartzMap.smulLeftCLM ℂ
        (initialSpatialFactorBump d k N) χ := by
  ext η
  rw [initialSpatialFactorTruncationCLM_apply,
    bumpTruncationRadius,
    section43SpatialFlatSchwartzCLE_symm_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (unitBallBumpSchwartzPiRadius
        (k * d) (bumpTruncationRadiusValue N)
        (bumpTruncationRadiusValue_pos N)).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (initialSpatialFactorBump d k N).hasTemperateGrowth]
  simp [initialSpatialFactorBump]

theorem initialSpatialFactorTruncation_tsupport_subset_bump
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    tsupport
        ((initialSpatialFactorTruncationCLM d k N χ :
          SchwartzMap (Section43SpatialSpace d k) ℂ) :
            Section43SpatialSpace d k → ℂ) ⊆
      tsupport
        ((initialSpatialFactorBump d k N :
          SchwartzMap (Section43SpatialSpace d k) ℂ) :
            Section43SpatialSpace d k → ℂ) := by
  rw [initialSpatialFactorTruncationCLM_eq_smulLeft]
  intro η hη
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ)
      (g := initialSpatialFactorBump d k N)
      (f := χ) hη).2

theorem initialSpatialFactorBump_hasCompactSupport
    (N : ℕ) :
    HasCompactSupport
      ((initialSpatialFactorBump d k N :
        SchwartzMap (Section43SpatialSpace d k) ℂ) :
          Section43SpatialSpace d k → ℂ) := by
  exact
    (hasCompactSupport_unitBallBumpSchwartzPiRadius
      (k * d) (bumpTruncationRadiusValue N)
      (bumpTruncationRadiusValue_pos N)).comp_homeomorph
        (section43SpatialFlatCLE d k).toHomeomorph

theorem tsupport_section43NPointTimeSpatialTensor_subset_spatial_preimage
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    tsupport
        ((section43NPointTimeSpatialTensor d k φ χ :
          SchwartzNPoint d k) :
            NPointDomain d k → ℂ) ⊆
      (section43QSpatial (d := d) (n := k)) ⁻¹'
        tsupport
          (χ : Section43SpatialSpace d k → ℂ) := by
  intro q hq
  have hfun :
      (((section43NPointTimeSpatialTensor d k φ χ :
          SchwartzNPoint d k) :
            NPointDomain d k → ℂ)) =
        fun q : NPointDomain d k =>
          φ (section43QTime (d := d) (n := k) q) *
            χ (section43QSpatial (d := d) (n := k) q) := by
    funext q
    simp
  have hprod :
      q ∈ tsupport
        (fun q : NPointDomain d k =>
          φ (section43QTime (d := d) (n := k) q) *
            χ (section43QSpatial (d := d) (n := k) q)) := by
    simpa [hfun] using hq
  have hspatial_pullback :
      q ∈ tsupport
        (fun q : NPointDomain d k =>
          χ (section43QSpatial (d := d) (n := k) q)) :=
    tsupport_mul_subset_right hprod
  exact
    (tsupport_comp_subset_preimage
      (χ : Section43SpatialSpace d k → ℂ)
      (f := section43QSpatial (d := d) (n := k))
      (by
        exact
          continuous_snd.comp
            (nPointTimeSpatialCLE (d := d) k).continuous))
      hspatial_pullback

/-- Every support point of a factorwise compact source lies over the fixed
compact basepoint cutoff. The route-local name avoids coupling this module to
the concurrently developed base/time-footprint API. -/
theorem initialSpatialFactor_basepoint_mem_tsupport_of_mem_fullSource
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    x 0 ∈
      tsupport
        (((BHW.normalizedCutoffOfBump d).toSchwartz :
          SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
  have hfun :
      (((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) =
        fun y =>
          (BHW.normalizedCutoffOfBump d).toSchwartz (y 0) *
            (φ (reducedTimeProjectionCLM d k y) *
              χ (section43QSpatial (d := d) (n := k)
                (BHW.reducedDiffMapReal (k + 1) d y))) := by
    funext y
    exact initialReducedSpatialFullSourceCLM_apply_point φ χ y
  have hprod :
      x ∈ tsupport
        (fun y =>
          (BHW.normalizedCutoffOfBump d).toSchwartz (y 0) *
            (φ (reducedTimeProjectionCLM d k y) *
              χ (section43QSpatial (d := d) (n := k)
                (BHW.reducedDiffMapReal (k + 1) d y)))) := by
    rw [← hfun]
    exact hx
  have hbase_pullback :
      x ∈ tsupport
        (fun y : NPointDomain d (k + 1) =>
          (BHW.normalizedCutoffOfBump d).toSchwartz (y 0)) :=
    tsupport_mul_subset_left hprod
  exact
    (tsupport_comp_subset_preimage
      (((BHW.normalizedCutoffOfBump d).toSchwartz :
        SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)
      (f := fun y : NPointDomain d (k + 1) => y 0)
      (continuous_apply 0)) hbase_pullback

theorem exists_initialReducedSpatialFactorCompactSource_commonCarrier
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ∃ K : Set (NPointDomain d (k + 1)),
      IsCompact K ∧
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          tsupport
              ((initialReducedSpatialFactorCompactSourceCLM
                  (d := d) φ N χ :
                SchwartzNPoint d (k + 1)) :
                  NPointDomain d (k + 1) → ℂ) ⊆
            K := by
  let Kspatial : Set (Section43SpatialSpace d k) :=
    tsupport
      ((initialSpatialFactorBump d k N :
        SchwartzMap (Section43SpatialSpace d k) ℂ) :
          Section43SpatialSpace d k → ℂ)
  let Kreduced : Set (NPointDomain d k) :=
    (nPointTimeSpatialCLE (d := d) k).symm ''
      (tsupport (φ : (Fin k → ℝ) → ℂ) ×ˢ Kspatial)
  let assemble :
      SpacetimeDim d × NPointDomain d k →
        NPointDomain d (k + 1) :=
    fun p =>
      (BHW.realDiffCoordCLE (k + 1) d).symm
        (Fin.cons p.1 p.2)
  let K : Set (NPointDomain d (k + 1)) :=
    assemble ''
      (tsupport
        (((BHW.normalizedCutoffOfBump d).toSchwartz :
          SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ×ˢ Kreduced)
  have hKspatial : IsCompact Kspatial :=
    initialSpatialFactorBump_hasCompactSupport
      (d := d) (k := k) N |>.isCompact
  have hKreduced : IsCompact Kreduced := by
    exact
      (hφ_compact.isCompact.prod hKspatial).image
        (nPointTimeSpatialCLE (d := d) k).symm.continuous
  have hK : IsCompact K := by
    have hcons :
        Continuous
          (fun p : SpacetimeDim d × NPointDomain d k =>
            (Fin.cons p.1 p.2 : NPointDomain d (k + 1))) := by
      exact
        (Fin.consEquivL ℝ
          (fun _ : Fin (k + 1) => SpacetimeDim d)).continuous
    exact
      ((BHW.normalizedCutoffOfBump_hasCompactSupport d).isCompact.prod
        hKreduced).image
          ((BHW.realDiffCoordCLE (k + 1) d).symm.continuous.comp
            hcons)
  refine ⟨K, hK, ?_⟩
  intro χ x hx
  have hbase :
      x 0 ∈
        tsupport
          (((BHW.normalizedCutoffOfBump d).toSchwartz :
            SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) :=
    initialSpatialFactor_basepoint_mem_tsupport_of_mem_fullSource
      φ (initialSpatialFactorTruncationCLM d k N χ) x
      (by
        simpa [initialReducedSpatialFactorCompactSourceCLM_apply] using hx)
  have hdiff :
      BHW.reducedDiffMapRealCLM (k + 1) d x ∈
        tsupport
          ((section43NPointTimeSpatialTensor d k φ
              (initialSpatialFactorTruncationCLM d k N χ) :
            SchwartzNPoint d k) :
              NPointDomain d k → ℂ) :=
    reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (BHW.normalizedCutoffOfBump d).toSchwartz
      (section43NPointTimeSpatialTensor d k φ
        (initialSpatialFactorTruncationCLM d k N χ))
      (by
        simpa [initialReducedSpatialFactorCompactSourceCLM_apply,
          initialReducedSpatialFullSourceCLM_apply] using hx)
  have htime :
      section43QTime (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        tsupport (φ : (Fin k → ℝ) → ℂ) :=
    tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
      d k φ (initialSpatialFactorTruncationCLM d k N χ) hdiff
  have hspatial_truncated :
      section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        tsupport
          ((initialSpatialFactorTruncationCLM d k N χ :
            SchwartzMap (Section43SpatialSpace d k) ℂ) :
              Section43SpatialSpace d k → ℂ) :=
    tsupport_section43NPointTimeSpatialTensor_subset_spatial_preimage
      φ (initialSpatialFactorTruncationCLM d k N χ) hdiff
  have hspatial :
      section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        Kspatial :=
    initialSpatialFactorTruncation_tsupport_subset_bump
      (d := d) (k := k) N χ hspatial_truncated
  have hreduced :
      BHW.reducedDiffMapRealCLM (k + 1) d x ∈ Kreduced := by
    refine
      ⟨(section43QTime (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x),
        section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x)),
        ⟨htime, hspatial⟩, ?_⟩
    exact
      (nPointTimeSpatialCLE (d := d) k).symm_apply_apply
        (BHW.reducedDiffMapRealCLM (k + 1) d x)
  refine
    ⟨(x 0, BHW.reducedDiffMapRealCLM (k + 1) d x),
      ⟨hbase, hreduced⟩, ?_⟩
  have hcoord :
      Fin.cons (x 0) (BHW.reducedDiffMapRealCLM (k + 1) d x) =
        BHW.realDiffCoordCLE (k + 1) d x := by
    ext i μ
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [BHW.realDiffCoordCLE_apply]
    · change
        BHW.reducedDiffMapReal (k + 1) d x j μ =
          x j.succ μ - x j.castSucc μ
      exact BHW.reducedDiffMapReal_apply (k + 1) d x j μ
  simp only [assemble, hcoord]
  exact
    (BHW.realDiffCoordCLE (k + 1) d).symm_apply_apply x

theorem
    nonempty_initialReducedSpatialFactorCompactSource_spatialChronologicalCompactCoverData
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    Nonempty
      (SpatialChronologicalCompactCoverData
        (initialReducedSpatialFactorCompactSourceCLM
          (d := d) φ N)) := by
  obtain ⟨K₀, hK₀_compact, hK₀_support⟩ :=
    exists_initialReducedSpatialFactorCompactSource_commonCarrier
      (d := d) (k := k) φ hφ_compact N
  let K : Set (NPointDomain d (k + 1)) :=
    K₀ ∩
      (reducedTimeProjectionCLM d k) ⁻¹'
        tsupport (φ : (Fin k → ℝ) → ℂ)
  have hK_compact : IsCompact K := by
    exact hK₀_compact.inter_right
      ((isClosed_tsupport _).preimage
        (reducedTimeProjectionCLM d k).continuous)
  have hsource :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        tsupport
            ((initialReducedSpatialFactorCompactSourceCLM
                (d := d) φ N χ :
              SchwartzNPoint d (k + 1)) :
                NPointDomain d (k + 1) → ℂ) ⊆
          K := by
    intro χ x hx
    refine ⟨hK₀_support χ hx, ?_⟩
    exact
      reducedTimeProjection_mem_tsupport_of_mem_initialReducedSpatialFullSource
        φ (initialSpatialFactorTruncationCLM d k N χ) x
        (by
          simpa [initialReducedSpatialFactorCompactSourceCLM_apply] using hx)
  apply
    nonempty_spatialChronologicalCompactCoverData
      (initialReducedSpatialFactorCompactSourceCLM
        (d := d) φ N)
      K hK_compact hsource
  intro x hx
  have htime :
      reducedTimeProjectionCLM d k x ∈
        section43TimeStrictPositiveRegion k :=
    hφ_positive hx.2
  have hmono :
      StrictMono (fun i : Fin (k + 1) => x i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi := htime ⟨i.val, by omega⟩
    change 0 < x i.succ 0 - x i.castSucc 0 at hi
    exact sub_pos.mp hi
  intro i j hij
  exact hmono hij

end OSIIChapterV
end OSReconstruction
