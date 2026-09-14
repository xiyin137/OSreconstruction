/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformHilbertDegree
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedMZ












noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

namespace OSIIStep4MultiGapSelectedCommonSlopeData

/-- At one selected gap, the spectator package has the common total-arity
degrees supplied by the E0' radial data. -/
theorem exists_spectatorPackage_coordinateChart_uniformDegree_bound_at_gap
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc))
    (i : Fin k) :
    ∃ C : Real, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center y y' : Fin (k * (d + 1)) -> Real),
          ∀ hcenter : ∀ j : Fin k,
            rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
            (y, y') ∈
                osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho ->
              ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                    d k hrho center y y' hcenter)
                (x : Fin k -> osiiAxisPairIndex d -> Real)
                (a : osiiAxisPairIndex d),
                (D.spectatorPackage x i
                  ).flatTubeBranchCoordinateChartBound OS a <=
                    C * (16 / rho) ^ (k * D0.hilbertScaleRate) *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) i
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x i center))) ^
                        (k * D0.hilbertGrowthRate) := by
  obtain ⟨C, hC, hbound⟩ :=
    D0.exists_selectedBlockAxisPairCoordinateChart_bound
      lgc i.val (osiiStep4MultiGapAfterCount i)
  refine ⟨C, hC, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D x a
  let spectator := osiiStep4MultiGapSpectatorCenter d D.T x i center
  let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i spectator
  let splitY := osiiStep4MultiGapSplitCoordinates (d + 1) i y
  let splitY' := osiiStep4MultiGapSplitCoordinates (d + 1) i y'
  let hsplit := osiiStep4MultiGapSplitCoordinates_time_lower d k i spectator
    (osiiStep4MultiGapSpectatorCenter_time_lower
      d k D.T D.hT x i center hcenter)
  have hpSplit :
      (splitY, splitY') ∈
        osiiStep4PartialConvolutionClosedImaginaryBox (d + 1)
          (i.val + 1 + osiiStep4MultiGapAfterCount i) rho := by
    simpa [splitY, splitY'] using
      osiiStep4MultiGapSplitCoordinates_pair_mem_closedImaginaryBox
        (d + 1) i hp
  simpa [spectator, splitCenter, splitY, splitY', hsplit,
    osiiStep4MultiGap_split_count i] using
      hbound hrho hrho_le splitCenter hsplit
        (splitY, splitY') hpSplit (D.spectatorPackage x i) a

/-- The actual coherent packet branch inherits the same selected-gap bound. -/
theorem exists_packetFamily_logBranch_uniformDegree_bound_at_gap
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc))
    (i : Fin k) :
    ∃ C : Real, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center y y' : Fin (k * (d + 1)) -> Real),
          ∀ hcenter : ∀ j : Fin k,
            rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
            (y, y') ∈
                osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho ->
              ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                    d k hrho center y y' hcenter)
                (x : Fin k -> osiiAxisPairIndex d -> Real)
                (a : osiiAxisPairIndex d) (w : Complex),
                |w.im| < Real.pi / 2 ->
                  norm ((D.packetFamily OS lgc).logBranch x (i, a)
                    (osiiAxisPairMultiGapUpdate
                      (osiiAxisPairSimultaneousLogRealEmbed x) (i, a) w)) <=
                    C * (16 / rho) ^ (k * D0.hilbertScaleRate) *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) i
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x i center))) ^
                        (k * D0.hilbertGrowthRate) := by
  obtain ⟨C, hC, hpackage⟩ :=
    exists_spectatorPackage_coordinateChart_uniformDegree_bound_at_gap
      d k OS lgc D0 i
  refine ⟨C, hC, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D x a w hw
  have hlocal :=
    (D.spectatorPackage x i).norm_flatTubeBranch_coordinateChart_le
      OS lgc a (x i) w hw
  rw [((D.spectatorPackage x i).toSemigroupPacketFamily OS lgc
    ).toDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
      (x i) a hw] at hlocal
  have hbranch :
      norm ((D.packetFamily OS lgc).logBranch x (i, a)
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) (i, a) w)) <=
        (D.spectatorPackage x i).flatTubeBranchCoordinateChartBound OS a := by
    simpa [OSIIAxisPairMultiGapSemigroupPacketFamily.logBranch,
      OSIIAxisPairSemigroupPacketFamily.toDirectionalBranchFamily,
      OSIIAxisPairSemigroupPacketFamily.logBranch,
      osiiAxisPairMultiGapUpdate] using hlocal
  exact hbranch.trans
    (hpackage hrho hrho_le center y y' hcenter hp D x a)

/-- All chronological gaps share the same two degrees.  A finite sum is
needed only for the numerical constants. -/
theorem exists_packetFamily_logBranch_uniformDegree_bound
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) :
    ∃ C : Real, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center y y' : Fin (k * (d + 1)) -> Real),
          ∀ hcenter : ∀ j : Fin k,
            rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
            (y, y') ∈
                osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho ->
              ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                    d k hrho center y y' hcenter)
                (x : Fin k -> osiiAxisPairIndex d -> Real)
                (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
                |w.im| < Real.pi / 2 ->
                  norm ((D.packetFamily OS lgc).logBranch x q
                    (osiiAxisPairMultiGapUpdate
                      (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
                    C * (16 / rho) ^ (k * D0.hilbertScaleRate) *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x q.1 center))) ^
                        (k * D0.hilbertGrowthRate) := by
  let hexists (i : Fin k) :=
    exists_packetFamily_logBranch_uniformDegree_bound_at_gap
      d k OS lgc D0 i
  choose C hC hbound using hexists
  let Cstar : Real := ∑ i : Fin k, C i
  have hCstar : 0 <= Cstar :=
    Finset.sum_nonneg fun i _hi => hC i
  refine ⟨Cstar, hCstar, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D x q w hw
  let A : Real := 16 / rho
  let B : Real := 1 + norm
    (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
      (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center))
  have hC_le : C q.1 <= Cstar :=
    Finset.single_le_sum
      (fun i _hi => hC i) (Finset.mem_univ q.1)
  calc
    norm ((D.packetFamily OS lgc).logBranch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
      C q.1 * A ^ (k * D0.hilbertScaleRate) *
        B ^ (k * D0.hilbertGrowthRate) := by
      simpa [A, B] using
        hbound q.1 hrho hrho_le center y y' hcenter hp
          D x q.2 w hw
    _ <= Cstar * A ^ (k * D0.hilbertScaleRate) *
        B ^ (k * D0.hilbertGrowthRate) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC_le
          (pow_nonneg (by positivity) _))
        (pow_nonneg (by positivity) _)
    _ = Cstar * (16 / rho) ^ (k * D0.hilbertScaleRate) *
        (1 + norm
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter
              d D.T x q.1 center))) ^
            (k * D0.hilbertGrowthRate) := rfl

/-- Gap-independent form measured by the common chronological translation
majorant. -/
theorem exists_packetFamily_logBranch_uniformDegree_bound_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) :
    ∃ C : Real, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center y y' : Fin (k * (d + 1)) -> Real),
          ∀ hcenter : ∀ j : Fin k,
            rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
            (y, y') ∈
                osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho ->
              ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                    d k hrho center y y' hcenter)
                (x : Fin k -> osiiAxisPairIndex d -> Real)
                (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
                |w.im| < Real.pi / 2 ->
                  norm ((D.packetFamily OS lgc).logBranch x q
                    (osiiAxisPairMultiGapUpdate
                      (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
                    C * (16 / rho) ^ (k * D0.hilbertScaleRate) *
                      (1 + norm center +
                        osiiAxisPairChronologicalTranslationMajorant
                          D.T x) ^ (k * D0.hilbertGrowthRate) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_packetFamily_logBranch_uniformDegree_bound d k OS lgc D0
  refine ⟨C, hC, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D x q w hw
  have hraw := hbound hrho hrho_le center y y' hcenter hp D x q w hw
  have hspectator :
      norm (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
        (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center)) <=
        norm center +
          osiiAxisPairChronologicalTranslationMajorant D.T x :=
    (norm_osiiStep4MultiGapSplitCoordinates_le (d + 1) q.1 _).trans
      (norm_osiiStep4MultiGapSpectatorCenter_le_majorant
        d k D.T x q.1 center)
  have hbase :
      1 + norm (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
          (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center)) <=
        1 + norm center +
          osiiAxisPairChronologicalTranslationMajorant D.T x := by
    linarith
  exact hraw.trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbase
        (k * D0.hilbertGrowthRate))
      (mul_nonneg hC (pow_nonneg (by positivity) _)))

/-- The centered logarithmic compact window preserves the same two
rates-times-arity degrees. -/
theorem exists_packetFamily_logBranch_uniformDegree_bound_on_centered_log_window
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) :
    ∃ C : Real, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center y y' : Fin (k * (d + 1)) -> Real),
          ∀ hcenter : ∀ j : Fin k,
            rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1)))),
            (y, y') ∈
                osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) k rho ->
              ∀ (D : OSIIStep4MultiGapSelectedCommonSlopeData
                    d k hrho center y y' hcenter)
                (u x : Fin k -> osiiAxisPairIndex d -> Real)
                (R : Real),
                (∀ i a,
                  osiiNarrowTimeCenteredRealLogCoordinate D.T x i a <=
                    u i a + R) ->
                  ∀ (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
                  |w.im| < Real.pi / 2 ->
                    norm ((D.packetFamily OS lgc).logBranch x q
                      (osiiAxisPairMultiGapUpdate
                        (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
                      C * (16 / rho) ^ (k * D0.hilbertScaleRate) *
                        (1 + norm center + Real.exp R *
                          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
                            Real.exp (u i a))) ^
                          (k * D0.hilbertGrowthRate) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_packetFamily_logBranch_uniformDegree_bound_majorant
      d k OS lgc D0
  refine ⟨C, hC, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D u x R hx q w hw
  have hraw := hbound hrho hrho_le center y y' hcenter hp D x q w hw
  have hmajorant :=
    osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_mul
      d k D.T D.hT R u x hx
  have hbase :
      1 + norm center +
          osiiAxisPairChronologicalTranslationMajorant D.T x <=
        1 + norm center + Real.exp R *
          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp (u i a)) := by
    linarith
  have hbase_nonneg :
      0 <= 1 + norm center +
        osiiAxisPairChronologicalTranslationMajorant D.T x :=
    add_nonneg (by positivity)
      (osiiAxisPairChronologicalTranslationMajorant_nonneg D.T x)
  exact hraw.trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase_nonneg hbase
        (k * D0.hilbertGrowthRate))
      (mul_nonneg hC (pow_nonneg (by positivity) _)))

end OSIIStep4MultiGapSelectedCommonSlopeData

/-- Existing centered-window growth data together with its exact
linear-in-arity degree identities. -/
structure OSIIUniformMultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) where
  toScaleBoundData :
    OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc
  scaleDegree_eq :
    toScaleBoundData.scaleDegree = k * D0.hilbertScaleRate
  growthDegree_eq :
    toScaleBoundData.growthDegree = k * D0.hilbertGrowthRate

/-- The E0' radial data produces centered-window packet data with exact
rates-times-arity degrees. -/
theorem nonempty_uniformMultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) :
    Nonempty (OSIIUniformMultiGapCenteredWindowScaleBoundData
      d k OS lgc D0) := by
  obtain ⟨C, hC, hbound⟩ :=
    OSIIStep4MultiGapSelectedCommonSlopeData.exists_packetFamily_logBranch_uniformDegree_bound_on_centered_log_window
      d k OS lgc D0
  exact ⟨{
    toScaleBoundData := {
      constant := C
      scaleDegree := k * D0.hilbertScaleRate
      growthDegree := k * D0.hilbertGrowthRate
      constant_nonneg := hC
      bound := hbound }
    scaleDegree_eq := rfl
    growthDegree_eq := rfl }⟩

/-- A fixed witness retaining the exact arity-linear packet degrees. -/
noncomputable def osiiUniformMultiGapCenteredWindowScaleBoundData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D0 : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc)) :
    OSIIUniformMultiGapCenteredWindowScaleBoundData d k OS lgc D0 :=
  Classical.choice
    (nonempty_uniformMultiGapCenteredWindowScaleBoundData
      d k OS lgc D0)

/-- One coefficient and three rates, chosen before arity, for the actual
centered-window packet bounds. This is the input needed by the quantitative
VI.1 density construction. -/
structure OSIIUniformMultiGapGrowthData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  coefficient : Real
  arityRate : Nat
  scaleRate : Nat
  growthRate : Nat
  coefficient_nonneg : 0 <= coefficient
  toScaleBoundData : ∀ (k : Nat) [NeZero k],
    OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc
  constant_le : ∀ (k : Nat) [NeZero k],
    (toScaleBoundData k).constant <=
      coefficient * (k : Real) ^ (k * arityRate)
  scaleDegree_eq : ∀ (k : Nat) [NeZero k],
    (toScaleBoundData k).scaleDegree = k * scaleRate
  growthDegree_eq : ∀ (k : Nat) [NeZero k],
    (toScaleBoundData k).growthDegree = k * growthRate

/-- Corrected arity-linear E0' supplies the all-arity packet data. The
reflected point arities remain visible in the source theorem; the split
identity then gives the same coefficient and rates at every gap. -/
theorem nonempty_arityLinearUniformMultiGapGrowthData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    Nonempty (OSIIUniformMultiGapGrowthData d OS lgc) := by
  obtain ⟨A, hA, beta, hchart⟩ :=
    exists_selectedBlockAxisPairCoordinateChartBound_fixedArityMajorant
      d OS lgc
  let Q := 2 * (3 * (d + 1) + 4 * lgc.sobolev_index)
  let R := 8 * lgc.sobolev_index
  have hdata : ∀ (k : Nat) [NeZero k],
      ∃ G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc,
        G.constant = A * (k : Real) ^ (k * beta) ∧
        G.scaleDegree = k * Q ∧ G.growthDegree = k * R := by
    intro k inst
    let C := A * (k : Real) ^ (k * beta)
    have hC : 0 <= C := mul_nonneg hA (by positivity)
    refine ⟨{
      constant := C
      scaleDegree := k * Q
      growthDegree := k * R
      constant_nonneg := hC
      bound := ?_ }, rfl, rfl, rfl⟩
    intro rho hrho hrho_le center y y' hcenter hp D u x windowRadius hx q w hw
    let i := q.1
    let spectator := osiiStep4MultiGapSpectatorCenter d D.T x i center
    let splitCenter := osiiStep4MultiGapSplitCoordinates (d + 1) i spectator
    let splitY := osiiStep4MultiGapSplitCoordinates (d + 1) i y
    let splitY' := osiiStep4MultiGapSplitCoordinates (d + 1) i y'
    let hsplit := osiiStep4MultiGapSplitCoordinates_time_lower d k i spectator
      (osiiStep4MultiGapSpectatorCenter_time_lower
        d k D.T D.hT x i center hcenter)
    have hlocal := (D.spectatorPackage x i).norm_flatTubeBranch_coordinateChart_le
      OS lgc q.2 (x i) w hw
    rw [((D.spectatorPackage x i).toSemigroupPacketFamily OS lgc
      ).toDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
        (x i) q.2 hw] at hlocal
    have hbranch :
        norm ((D.packetFamily OS lgc).logBranch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
          (D.spectatorPackage x i).flatTubeBranchCoordinateChartBound OS q.2 := by
      simpa [i, OSIIAxisPairMultiGapSemigroupPacketFamily.logBranch,
        OSIIAxisPairSemigroupPacketFamily.toDirectionalBranchFamily,
        OSIIAxisPairSemigroupPacketFamily.logBranch,
        osiiAxisPairMultiGapUpdate] using hlocal
    have hsource :
        (D.spectatorPackage x i).flatTubeBranchCoordinateChartBound OS q.2 <=
          C * (16 / rho) ^ (k * Q) * (1 + norm splitCenter) ^ (k * R) := by
      simpa [C, Q, R, i, spectator, splitCenter, splitY, splitY', hsplit,
        osiiStep4MultiGap_split_count, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using
        hchart i.val (osiiStep4MultiGapAfterCount i) hrho hrho_le
          splitCenter splitY splitY' hsplit (D.spectatorPackage x i) q.2
    have hcenterNorm : norm splitCenter <= norm center +
        osiiAxisPairChronologicalTranslationMajorant D.T x :=
      (norm_osiiStep4MultiGapSplitCoordinates_le (d + 1) i spectator).trans
        (norm_osiiStep4MultiGapSpectatorCenter_le_majorant
          d k D.T x i center)
    have hmajorant :=
      osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_mul
        d k D.T D.hT windowRadius u x hx
    have hbase : 1 + norm splitCenter <=
        1 + norm center + Real.exp windowRadius *
          (∑ j : Fin k, ∑ a : osiiAxisPairIndex d, Real.exp (u j a)) := by
      linarith
    exact (hbranch.trans hsource).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase (k * R))
        (mul_nonneg hC (pow_nonneg (by positivity) _)))
  choose G hG using hdata
  exact ⟨{
    coefficient := A
    arityRate := beta
    scaleRate := Q
    growthRate := R
    coefficient_nonneg := hA
    toScaleBoundData := G
    constant_le := fun k => (hG k).1.le
    scaleDegree_eq := fun k => (hG k).2.1
    growthDegree_eq := fun k => (hG k).2.2 }⟩

/-- A single chosen all-arity packet bound from the genuine public input. -/
noncomputable def osiiArityLinearUniformMultiGapGrowthData
    (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIUniformMultiGapGrowthData d OS lgc :=
  Classical.choice (nonempty_arityLinearUniformMultiGapGrowthData d OS lgc)

end OSReconstruction
