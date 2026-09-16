/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimeLevelCover




















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The model unit-ball bump vanishes outside its radius-`2` support ball. -/
theorem initial_unitBallBumpSchwartzPi_zero_of_two_le_norm
    {m : ℕ} {x : Fin m → ℝ} (hx : 2 ≤ ‖x‖) :
    unitBallBumpSchwartzPi m x = 0 := by
  let b : ContDiffBump (0 : Fin m → ℝ) :=
    ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBallBumpSchwartzPi m x = f x := by
    change (HasCompactSupport.toSchwartzMap hf_compact hf_smooth) x = f x
    rfl
  rw [happly]
  change ((b x : ℝ) : ℂ) = 0
  refine congrArg (fun r : ℝ => (r : ℂ)) ?_
  have hdist : 2 ≤ dist x 0 := by
    simpa [dist_eq_norm] using hx
  exact b.zero_of_le_dist hdist

/-- The flattened support of the standard level bump lies in the radius
`2 * bumpTruncationRadiusValue N` closed ball. -/
theorem initialSpatialFactorBump_tsupport_flat_subset_closedBall
    (N : ℕ) :
    (section43SpatialFlatCLE d k) ''
        tsupport
          ((initialSpatialFactorBump d k N :
            SchwartzMap (Section43SpatialSpace d k) ℂ) :
              Section43SpatialSpace d k → ℂ) ⊆
      Metric.closedBall
        (0 : Fin (k * d) → ℝ)
        (2 * bumpTruncationRadiusValue N) := by
  let R : ℝ := bumpTruncationRadiusValue N
  have hR : 0 < R := bumpTruncationRadiusValue_pos N
  have hsupp :
      Function.support
          (unitBallBumpSchwartzPiRadius (k * d) R hR :
            (Fin (k * d) → ℝ) → ℂ) ⊆
        Metric.closedBall
          (0 : Fin (k * d) → ℝ) (2 * R) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hnorm
    have htwoR : 2 * R < ‖x‖ := lt_of_not_ge hnorm
    have htwo : 2 < ‖R⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      rw [lt_inv_mul_iff₀ hR]
      simpa [mul_comm, mul_left_comm, mul_assoc] using htwoR
    apply hx
    rw [unitBallBumpSchwartzPiRadius_apply]
    exact
      initial_unitBallBumpSchwartzPi_zero_of_two_le_norm
        htwo.le
  have htsupport :
      tsupport
          (unitBallBumpSchwartzPiRadius (k * d) R hR :
            (Fin (k * d) → ℝ) → ℂ) ⊆
        Metric.closedBall
          (0 : Fin (k * d) → ℝ) (2 * R) :=
    closure_minimal hsupp Metric.isClosed_closedBall
  intro x hx
  rcases hx with ⟨η, hη, rfl⟩
  have hη' :
      section43SpatialFlatCLE d k η ∈
        tsupport
          (unitBallBumpSchwartzPiRadius (k * d) R hR :
            (Fin (k * d) → ℝ) → ℂ) := by
    change η ∈ tsupport
      ((unitBallBumpSchwartzPiRadius (k * d) R hR :
        (Fin (k * d) → ℝ) → ℂ) ∘ section43SpatialFlatCLE d k) at hη
    apply
      tsupport_comp_subset_preimage
        (unitBallBumpSchwartzPiRadius (k * d) R hR :
          (Fin (k * d) → ℝ) → ℂ)
        (section43SpatialFlatCLE d k).continuous
    exact hη
  simpa [R] using htsupport hη'

/-- Reconstruct the full absolute configuration from the compact base/time
coordinates and the reduced spatial block. -/
noncomputable def initialFullConfigurationFromBaseTimeSpatialCLM
    (d k : ℕ) :
    (InitialBaseTimeSpace d k × Section43SpatialSpace d k) →L[ℝ]
      NPointDomain d (k + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        (BHW.realDiffCoordCLE (k + 1) d).symm
          (Fin.cons p.1.1
            ((nPointTimeSpatialCLE (d := d) k).symm
              (p.1.2, p.2)))
      map_add' := by
        intro p q
        rw [← (BHW.realDiffCoordCLE (k + 1) d).symm.map_add]
        congr 1
        have hreduced :=
          (nPointTimeSpatialCLE (d := d) k).symm.map_add
            (p.1.2, p.2) (q.1.2, q.2)
        ext i μ
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · simpa using congrArg (fun z => z j μ) hreduced
      map_smul' := by
        intro c p
        rw [← (BHW.realDiffCoordCLE (k + 1) d).symm.map_smul]
        congr 1
        have hreduced :=
          (nPointTimeSpatialCLE (d := d) k).symm.map_smul
            c (p.1.2, p.2)
        ext i μ
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · simpa using congrArg (fun z => z j μ) hreduced }

/-- The reconstruction map recovers every absolute configuration from its
canonical base/time projection and reduced spatial coordinate. -/
@[simp] theorem initialFullConfigurationFromBaseTimeSpatialCLM_apply_canonical
    (x : NPointDomain d (k + 1)) :
    initialFullConfigurationFromBaseTimeSpatialCLM d k
        (initialBaseTimeProjectionCLM d k x,
          section43QSpatial (d := d) (n := k)
            (BHW.reducedDiffMapRealCLM (k + 1) d x)) =
      x := by
  let q : NPointDomain d k :=
    BHW.reducedDiffMapRealCLM (k + 1) d x
  have htime :
      reducedTimeProjectionCLM d k x =
        section43QTime (d := d) (n := k) q := by
    rfl
  have hreduced :
      (nPointTimeSpatialCLE (d := d) k).symm
          (reducedTimeProjectionCLM d k x,
            section43QSpatial (d := d) (n := k) q) =
        q := by
    rw [htime]
    exact
      (nPointTimeSpatialCLE (d := d) k).symm_apply_apply q
  have hcoord :
      Fin.cons (x 0) q =
        BHW.realDiffCoordCLE (k + 1) d x := by
    ext i μ
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [BHW.realDiffCoordCLE_apply]
    · change
        BHW.reducedDiffMapReal (k + 1) d x j μ =
          x j.succ μ - x j.castSucc μ
      exact BHW.reducedDiffMapReal_apply (k + 1) d x j μ
  change
    (BHW.realDiffCoordCLE (k + 1) d).symm
        (Fin.cons (x 0)
          ((nPointTimeSpatialCLE (d := d) k).symm
            (reducedTimeProjectionCLM d k x,
              section43QSpatial (d := d) (n := k) q))) =
      x
  rw [hreduced, hcoord]
  exact (BHW.realDiffCoordCLE (k + 1) d).symm_apply_apply x

/-- The explicit reconstruction has the prescribed absolute Euclidean time
coordinates; the reduced spatial input changes only spatial components. -/
@[simp] theorem initialFullConfigurationFromBaseTimeSpatialCLM_time
    (p : InitialBaseTimeSpace d k)
    (η : Section43SpatialSpace d k)
    (i : Fin (k + 1)) :
    initialFullConfigurationFromBaseTimeSpatialCLM d k (p, η) i 0 =
      initialBaseTimeConfigurationCLM d k p i 0 := by
  let ξ : NPointDomain d k :=
    (nPointTimeSpatialCLE (d := d) k).symm (p.2, η)
  let τ : NPointDomain d k :=
    initialBaseTimeGapConfigurationCLM d k p.2
  have hξτ : ∀ j : Fin k, ξ j 0 = τ j 0 := by
    intro j
    simp [ξ, τ, initialBaseTimeGapConfigurationCLM,
      nPointTimeSpatialCLE]
  have hdiff :
      diffVarSection d k ξ i 0 =
        diffVarSection d k τ i 0 := by
    change
      (∑ j : Fin i.val, ξ ⟨j.val, by omega⟩ 0) =
        ∑ j : Fin i.val, τ ⟨j.val, by omega⟩ 0
    apply Finset.sum_congr rfl
    intro j _hj
    exact hξτ ⟨j.val, by omega⟩
  have hprepend :
      Fin.cons p.1 ξ = BHW.prependBasepointReal d k p.1 ξ := by
    ext j μ
    refine Fin.cases ?_ (fun r => ?_) j <;>
      simp [BHW.prependBasepointReal]
  have hfull :=
    realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
      (d := d) k p.1 ξ
  have hi := congrFun (congrFun hfull i) 0
  change
    (BHW.realDiffCoordCLE (k + 1) d).symm
        (Fin.cons p.1
          ((nPointTimeSpatialCLE (d := d) k).symm (p.2, η))) i 0 =
      initialBaseTimeConfigurationCLM d k p i 0
  calc
    (BHW.realDiffCoordCLE (k + 1) d).symm
          (Fin.cons p.1
            ((nPointTimeSpatialCLE (d := d) k).symm (p.2, η))) i 0 =
        p.1 0 + diffVarSection d k ξ i 0 := by
      change
        (BHW.realDiffCoordCLE (k + 1) d).symm
            (Fin.cons p.1 ξ) i 0 =
          p.1 0 + diffVarSection d k ξ i 0
      rw [hprepend]
      exact hi
    _ = p.1 0 + diffVarSection d k τ i 0 := by
      rw [hdiff]
    _ = initialBaseTimeConfigurationCLM d k p i 0 := by
      rfl

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- A support point of a fixed time piece has fixed compact base/time
coordinates and reduced spatial coordinate in the explicit level bump. -/
theorem levelPiece_support_coordinates
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ)) :
    initialBaseTimeProjectionCLM d k x ∈
        initialBaseTimeFootprint (d := d) φ ∩
          tsupport
            (D.cutoff a : InitialBaseTimeSpace d k → ℂ) ∧
      section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        tsupport
          ((initialSpatialFactorBump d k N :
            SchwartzMap (Section43SpatialSpace d k) ℂ) :
              Section43SpatialSpace d k → ℂ) := by
  have hxpair :=
    SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ)
      (g := D.weight a)
      (f := initialReducedSpatialFullSourceCLM (d := d) φ
        (initialSpatialFactorTruncationCLM d k N χ))
      (by simpa [levelPiece, piece] using hx)
  have hbaseTime :
      initialBaseTimeProjectionCLM d k x ∈
        initialBaseTimeFootprint (d := d) φ :=
    initialBaseTimeProjection_mem_footprint_of_mem_source
      φ (initialSpatialFactorTruncationCLM d k N χ) x hxpair.1
  have hcutoff :
      initialBaseTimeProjectionCLM d k x ∈
        tsupport
          (D.cutoff a : InitialBaseTimeSpace d k → ℂ) :=
    tsupport_comp_subset_preimage
      (D.cutoff a : InitialBaseTimeSpace d k → ℂ)
      (initialBaseTimeProjectionCLM d k).continuous
      (by
        change x ∈ tsupport
          ((D.cutoff a : InitialBaseTimeSpace d k → ℂ) ∘
            initialBaseTimeProjectionCLM d k)
        exact hxpair.2)
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
      hxpair.1
  have hspatialTruncated :
      section43QSpatial (d := d) (n := k)
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        tsupport
          ((initialSpatialFactorTruncationCLM d k N χ :
            SchwartzMap (Section43SpatialSpace d k) ℂ) :
              Section43SpatialSpace d k → ℂ) :=
    tsupport_section43NPointTimeSpatialTensor_subset_spatial_preimage
      φ (initialSpatialFactorTruncationCLM d k N χ) hdiff
  exact
    ⟨⟨hbaseTime, hcutoff⟩,
      initialSpatialFactorTruncation_tsupport_subset_bump
        (d := d) (k := k) N χ hspatialTruncated⟩

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
