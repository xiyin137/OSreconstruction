/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalTubeIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIICollisionControlledOrder









noncomputable section

open Complex Set

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d} {lgc : OSLinearGrowthCondition d OS}
variable {stage : OSIITimeContinuationStage d k}

theorem osiiEquation66OSBuiltGlobalPhysicalDensity_mixedSpatialRealPoint
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (tau : Fin k -> Real) (htau : tau ∈ section43TimeStrictPositiveRegion k)
    (x : Fin (k * d) -> Real) :
    osiiEquation66OSBuiltGlobalPhysicalDensity lgc stage
        (osiiStep4MixedSpatialRealPoint d k tau x) =
      osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau htau x := by
  obtain ⟨D⟩ := Hstage {tau} isCompact_singleton (by simpa)
  have htauD := D.compactCarrier_subset (Set.mem_singleton tau)
  rw [osiiEquation66OSBuiltGlobalPhysicalDensity_eq_canonicalPhysicalDensity_of_mem D
    (by simpa [osiiEquation66FlatTime, osiiStep4MixedSpatialRealPoint] using htauD)]
  exact osiiEquation66OSBuiltCanonicalPhysicalDensity_mixedSpatialRealPoint lgc D tau htauD x

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}

include lgc in
theorem exists_flatWick_polynomial_bound
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    ∃ (C : Real) (N M : Nat), 0 < C ∧
      ∀ q : NPointDomain d k,
        section43QTime (d := d) (n := k) q ∈ section43TimeStrictPositiveRegion k ->
        ‖H.kernel (fun j => wickRotatePoint (q j))‖ ≤
          C * (1 + ‖q‖) ^ N *
            (1 + (osiiTimeBoundaryDistance k
              (osiiPositiveRealTimeEmbed (section43QTime (d := d) (n := k) q)))⁻¹) ^ M := by
  let G := osiiStep4MultiGapCenteredWindowScaleBoundData d k OS lgc
  let C := OSIIStep4FullSchwartzAngularContinuationData.equation66E0PolynomialConstant G *
    16 ^ (2 * G.scaleDegree)
  have hC : 0 ≤ C := mul_nonneg
    (OSIIStep4FullSchwartzAngularContinuationData.equation66E0PolynomialConstant_nonneg G)
    (by positivity)
  refine ⟨C + 1, 2 * (G.scaleDegree + G.growthDegree), 2 * G.scaleDegree,
    by positivity, ?_⟩
  intro q hq
  let tau := section43QTime (d := d) (n := k) q
  let x : Fin (k * d) -> Real := fun i =>
    q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2.succ
  have hflat : flattenCLEquivReal k (d + 1) q =
      osiiStep4MixedSpatialRealPoint d k tau x := by
    ext i
    obtain ⟨⟨j, mu⟩, rfl⟩ := finProdFinEquiv.surjective i
    cases mu using Fin.cases with
    | zero =>
        simp [osiiStep4MixedSpatialRealPoint, flattenCLEquivReal_apply,
          tau, section43QTime, nPointTimeSpatialCLE]
    | succ mu =>
        simp only [osiiStep4MixedSpatialRealPoint, flattenCLEquivReal_apply,
          Equiv.symm_apply_apply, Fin.cases_succ]
        exact (congrArg (fun p : Fin k × Fin d => q p.1 p.2.succ)
          (finProdFinEquiv.symm_apply_apply (j, mu))).symm
  have htime : ‖osiiPositiveRealTimeEmbed tau‖ ≤ ‖q‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).2
    intro j
    simpa [osiiPositiveRealTimeEmbed, tau, section43QTime, nPointTimeSpatialCLE] using
      (norm_le_pi_norm (q j) 0).trans (norm_le_pi_norm q j)
  have hspace : ‖x‖ ≤ ‖q‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).2
    intro i
    exact (norm_le_pi_norm (q (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2.succ).trans (norm_le_pi_norm q _)
  have hraw := osiiEquation66OSBuiltMixedSpatialDensity_norm_le d OS lgc G tau hq x
  rw [H.flatWick_eq_globalPhysicalDensity (lgc := lgc) Hstage R q hq,
    hflat, osiiEquation66OSBuiltGlobalPhysicalDensity_mixedSpatialRealPoint Hstage tau hq x]
  let P := G.scaleDegree + G.growthDegree
  let B := (1 + (osiiTimeBoundaryDistance k (osiiPositiveRealTimeEmbed tau))⁻¹) ^
    (2 * G.scaleDegree)
  have hB : 0 ≤ B := by
    dsimp [B, osiiTimeBoundaryDistance]
    exact pow_nonneg (add_nonneg zero_le_one
      (inv_nonneg.mpr Metric.infDist_nonneg)) _
  calc
    ‖osiiEquation66OSBuiltMixedSpatialDensity d OS lgc tau hq x‖ ≤
        C * (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ P * B * (1 + ‖x‖) ^ P := hraw
    _ ≤ (C + 1) * (1 + ‖q‖) ^ P * B * (1 + ‖q‖) ^ P := by
      gcongr
      linarith
    _ = (C + 1) * (1 + ‖q‖) ^ (2 * P) * B := by
      rw [two_mul, pow_add]
      ring

include lgc in
/-- The collision weight controls a chronological chart at every distinct
Euclidean configuration. Identifying different orderings remains a separate
source-covariance obligation. -/
theorem exists_collisionWeighted_flatWick_bound
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    ∃ (C : Real) (N M : Nat), 0 < C ∧ ∀ x : NPointDomain d (k + 1),
      x ∉ CoincidenceLocus d (k + 1) ->
      ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
        (sigma : Equiv.Perm (Fin (k + 1))),
        R.transpose * R = 1 ∧ R.det = 1 ∧
        let q := BHW.reducedDiffMapReal (k + 1) d (fun j => R.mulVec (x (sigma j)))
        section43QTime (d := d) (n := k) q ∈ section43TimeStrictPositiveRegion k ∧
        ‖H.kernel (fun j => wickRotatePoint (q j))‖ *
            Metric.infDist x (CoincidenceLocus d (k + 1)) ^ (M + 1) ≤
          C * (1 + ‖x‖) ^ N := by
  obtain ⟨C, N, M, hC, hgrowth⟩ := H.exists_flatWick_polynomial_bound (lgc := lgc) Hstage Rstage
  obtain ⟨c, hc, horder⟩ := exists_osiiCollisionControlledOrder d k
  let A : Real := 2 * (d + 1)
  let B : Real := 2 + c⁻¹
  have hA : 1 ≤ A := by
    dsimp [A]
    have hd : (0 : Real) ≤ d := by positivity
    linarith
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C * A ^ N * B ^ M * 2, N + M + 1, M, by positivity, ?_⟩
  intro x hx
  obtain ⟨R, sigma, hR, hdet, hpositive, hnorm, hwall⟩ := horder x hx
  let q : NPointDomain d k :=
    BHW.reducedDiffMapReal (k + 1) d (fun j => R.mulVec (x (sigma j)))
  let delta := Metric.infDist x (CoincidenceLocus d (k + 1))
  let b := osiiTimeBoundaryDistance k
    (osiiPositiveRealTimeEmbed (section43QTime (d := d) (n := k) q))
  have h01 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have hval := congrArg Fin.val h
    exact NeZero.ne k (by simpa using hval.symm)
  have hcoin : (CoincidenceLocus d (k + 1)).Nonempty :=
    ⟨0, 0, Fin.last k, h01, rfl⟩
  have hdelta : 0 < delta := (isClosed_CoincidenceLocus.notMem_iff_infDist_pos hcoin).1 hx
  have hdelta_upper : delta ≤ 2 * ‖x‖ :=
    (infDist_CoincidenceLocus_le_pairDifference x 0 (Fin.last k) h01).trans
      ((norm_sub_le _ _).trans (by
        nlinarith [norm_le_pi_norm x 0, norm_le_pi_norm x (Fin.last k)]))
  have hb : 0 < b := (mul_pos hc hdelta).trans_le hwall
  have hdiv : delta / b ≤ c⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hb hc]
    simpa only [mul_one, one_mul, mul_comm] using hwall
  have hscaled : delta * (1 + b⁻¹) ≤ B * (1 + ‖x‖) := by
    have hid : delta * (1 + b⁻¹) = delta + delta / b := by
      rw [div_eq_mul_inv]
      ring
    rw [hid]
    dsimp [B]
    nlinarith [mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg x)]
  have hqnorm : 1 + ‖q‖ ≤ A * (1 + ‖x‖) := by
    change ‖q‖ ≤ A * ‖x‖ at hnorm
    nlinarith
  have hkernel := hgrowth q hpositive
  change ‖H.kernel (fun j => wickRotatePoint (q j))‖ ≤
    C * (1 + ‖q‖) ^ N * (1 + b⁻¹) ^ M at hkernel
  refine ⟨R, sigma, hR, hdet, hpositive, ?_⟩
  change ‖H.kernel (fun j => wickRotatePoint (q j))‖ * delta ^ (M + 1) ≤ _
  calc
    ‖H.kernel (fun j => wickRotatePoint (q j))‖ * delta ^ (M + 1) ≤
        (C * (1 + ‖q‖) ^ N * (1 + b⁻¹) ^ M) * delta ^ (M + 1) :=
      mul_le_mul_of_nonneg_right hkernel (pow_nonneg hdelta.le _)
    _ = C * (1 + ‖q‖) ^ N * (delta * (1 + b⁻¹)) ^ M * delta := by
      rw [mul_pow, pow_succ]
      ring
    _ ≤ C * (A * (1 + ‖x‖)) ^ N * (B * (1 + ‖x‖)) ^ M * (2 * (1 + ‖x‖)) := by
      gcongr
      linarith
    _ = (C * A ^ N * B ^ M * 2) * (1 + ‖x‖) ^ (N + M + 1) := by
      simp only [mul_pow, pow_add, pow_one]
      ring

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
