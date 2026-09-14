/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockMZUniform
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketCenteredGrowth










noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

/-- Reindexing a flattened block tuple along a selected chronological split
does not increase its sup norm. -/
theorem norm_osiiStep4MultiGapSplitCoordinates_le
    (q : Nat) {k : Nat} (i : Fin k)
    (x : Fin (k * q) -> Real) :
    norm (osiiStep4MultiGapSplitCoordinates q i x) <= norm x := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro a
  simpa [osiiStep4MultiGapSplitCoordinates] using
    (norm_le_pi_norm x (osiiStep4MultiGapSplitCoordinateEquiv q i a))

/-- The canonical radial imaginary box is preserved by every selected-gap
reindexing. -/
theorem osiiStep4MultiGapSplitCoordinates_pair_mem_closedImaginaryBox
    (q : Nat) {k : Nat} (i : Fin k) {rho : Real}
    {y y' : Fin (k * q) -> Real}
    (hp : (y, y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox q k rho) :
    (osiiStep4MultiGapSplitCoordinates q i y,
        osiiStep4MultiGapSplitCoordinates q i y') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox q
        (i.val + 1 + osiiStep4MultiGapAfterCount i) rho := by
  rcases hp with ⟨hy, hy'⟩
  constructor
  · rw [mem_closedBall, dist_zero_right] at hy ⊢
    exact (norm_osiiStep4MultiGapSplitCoordinates_le q i y).trans hy
  · rw [mem_closedBall, dist_zero_right] at hy' ⊢
    exact (norm_osiiStep4MultiGapSplitCoordinates_le q i y').trans hy'

/-- The spectator center is controlled by the original center and the common
chronological translation majorant, independently of the selected gap. -/
theorem norm_osiiStep4MultiGapSpectatorCenter_le_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (selected : Fin k)
    (center : Fin (k * (d + 1)) -> Real) :
    norm (osiiStep4MultiGapSpectatorCenter
      d T x selected center) <=
      norm center + osiiAxisPairChronologicalTranslationMajorant T x := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro a
    obtain ⟨⟨j, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
    by_cases hj : j = selected
    · subst j
      rw [osiiStep4MultiGapSpectatorCenter_selected]
      exact (norm_le_pi_norm center
        (finProdFinEquiv (selected, mu))).trans
          (le_add_of_nonneg_right
            (osiiAxisPairChronologicalTranslationMajorant_nonneg T x))
    · rw [osiiStep4MultiGapSpectatorCenter_other d T x selected j hj]
      calc
        norm (center (finProdFinEquiv (j, mu)) +
            osiiAxisPairChronologicalGapTranslation T x j mu) <=
          norm (center (finProdFinEquiv (j, mu))) +
            norm (osiiAxisPairChronologicalGapTranslation T x j mu) :=
              norm_add_le _ _
        _ <= norm center +
            norm (osiiAxisPairChronologicalGapTranslation T x j) := by
          exact add_le_add
            (norm_le_pi_norm center (finProdFinEquiv (j, mu)))
            (norm_le_pi_norm
              (osiiAxisPairChronologicalGapTranslation T x j) mu)
        _ <= norm center +
            osiiAxisPairChronologicalTranslationMajorant T x := by
          exact add_le_add (le_refl (norm center))
            (norm_osiiAxisPairChronologicalGapTranslation_le_majorant
              T x j)
  · exact add_nonneg (norm_nonneg center)
      (osiiAxisPairChronologicalTranslationMajorant_nonneg T x)

/-- In centered logarithmic coordinates the auxiliary slope cancels before
the compact-window estimate is applied. -/
theorem osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_mul
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) (hT : 1 < T) (R : Real)
    (u x : Fin k -> osiiAxisPairIndex d -> Real)
    (hx : forall i a,
      osiiNarrowTimeCenteredRealLogCoordinate T x i a <= u i a + R) :
    osiiAxisPairChronologicalTranslationMajorant T x <=
      Real.exp R *
        (∑ i : Fin k, ∑ a : osiiAxisPairIndex d, Real.exp (u i a)) := by
  refine (osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_sum
    T hT x).trans ?_
  calc
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a)) <=
      ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp R * Real.exp (u i a) := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro a _ha
          calc
            Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a) <=
                Real.exp (u i a + R) := Real.exp_le_exp.mpr (hx i a)
            _ = Real.exp R * Real.exp (u i a) := by
              rw [Real.exp_add]
              ring
    _ = Real.exp R *
        (∑ i : Fin k, ∑ a : osiiAxisPairIndex d, Real.exp (u i a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]

namespace OSIIStep4MultiGapSelectedCommonSlopeData

/-- At a fixed chronological gap, the selected-block radial estimate bounds
the exact compact package used by the coherent multi-gap packet. -/
theorem exists_spectatorPackage_coordinateChart_scale_bound_at_gap
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (i : Fin k) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
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
                    C * (16 / rho) ^ M *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) i
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x i center))) ^ N := by
  obtain ⟨C, M, N, hC, hbound⟩ :=
    exists_selectedBlockAxisPairCoordinateChart_scale_bound
      d i.val (osiiStep4MultiGapAfterCount i) OS
  refine ⟨C, M, N, hC, ?_⟩
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
  simpa [spectator, splitCenter, splitY, splitY', hsplit] using
    hbound hrho hrho_le splitCenter hsplit
      (splitY, splitY') hpSplit (D.spectatorPackage x i) a

/-- The same estimate controls the actual coherent multi-gap logarithmic
branch, uniformly over its active standard strip coordinate. -/
theorem exists_packetFamily_logBranch_scale_bound_at_gap
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (i : Fin k) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
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
                    C * (16 / rho) ^ M *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) i
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x i center))) ^ N := by
  obtain ⟨C, M, N, hC, hpackage⟩ :=
    exists_spectatorPackage_coordinateChart_scale_bound_at_gap
      d k OS i
  refine ⟨C, M, N, hC, ?_⟩
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

/-- One inverse-radius exponent and one spectator-center exponent control all
chronological gaps and signed axis directions of the coherent packet. -/
theorem exists_packetFamily_logBranch_scale_bound
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
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
                    C * (16 / rho) ^ M *
                      (1 + norm
                        (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
                          (osiiStep4MultiGapSpectatorCenter
                            d D.T x q.1 center))) ^ N := by
  let hexists (i : Fin k) :=
    exists_packetFamily_logBranch_scale_bound_at_gap d k OS lgc i
  choose C M N hC hbound using hexists
  let Cstar : Real := ∑ i : Fin k, C i
  let Mstar : Nat := Finset.univ.sup M
  let Nstar : Nat := Finset.univ.sup N
  have hCstar : 0 <= Cstar := by
    exact Finset.sum_nonneg fun i _hi => hC i
  refine ⟨Cstar, Mstar, Nstar, hCstar, ?_⟩
  intro rho hrho hrho_le center y y' hcenter hp D x q w hw
  let A : Real := 16 / rho
  let B : Real := 1 + norm
    (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
      (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center))
  have hA : 1 <= A := by
    dsimp [A]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hB : 1 <= B := by
    dsimp [B]
    linarith [norm_nonneg
      (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
        (osiiStep4MultiGapSpectatorCenter d D.T x q.1 center))]
  have hM : M q.1 <= Mstar := by
    exact Finset.le_sup (f := M) (Finset.mem_univ q.1)
  have hN : N q.1 <= Nstar := by
    exact Finset.le_sup (f := N) (Finset.mem_univ q.1)
  have hC_le : C q.1 <= Cstar := by
    exact Finset.single_le_sum
      (fun i _hi => hC i) (Finset.mem_univ q.1)
  calc
    norm ((D.packetFamily OS lgc).logBranch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
      C q.1 * A ^ (M q.1) * B ^ (N q.1) := by
        simpa [A, B] using
          hbound q.1 hrho hrho_le center y y' hcenter hp
            D x q.2 w hw
    _ <= C q.1 * A ^ Mstar * B ^ (N q.1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hA hM) (hC q.1))
        (pow_nonneg (by positivity) _)
    _ <= C q.1 * A ^ Mstar * B ^ Nstar := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hB hN)
        (mul_nonneg (hC q.1) (pow_nonneg (by positivity) _))
    _ <= Cstar * A ^ Mstar * B ^ Nstar := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC_le
          (pow_nonneg (by positivity) _))
        (pow_nonneg (by positivity) _)
    _ = Cstar * (16 / rho) ^ Mstar *
        (1 + norm
          (osiiStep4MultiGapSplitCoordinates (d + 1) q.1
            (osiiStep4MultiGapSpectatorCenter
              d D.T x q.1 center))) ^ Nstar := rfl

/-- Gap-independent form of the coherent packet bound.  All frozen-base
dependence is now summarized by one translation majorant. -/
theorem exists_packetFamily_logBranch_scale_bound_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
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
                    C * (16 / rho) ^ M *
                      (1 + norm center +
                        osiiAxisPairChronologicalTranslationMajorant
                          D.T x) ^ N := by
  obtain ⟨C, M, N, hC, hbound⟩ :=
    exists_packetFamily_logBranch_scale_bound d k OS lgc
  refine ⟨C, M, N, hC, ?_⟩
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
      (pow_le_pow_left₀ (by positivity) hbase N)
      (mul_nonneg hC (pow_nonneg (by positivity) M)))

/-- Slope-independent compact-window form of the coherent packet estimate.
The real window is expressed in centered logarithmic coordinates, so its
physical size is the finite sum of `exp u` rather than a power of the
auxiliary packet slope. -/
theorem exists_packetFamily_logBranch_scale_bound_on_centered_log_window
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
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
                (forall i a,
                  osiiNarrowTimeCenteredRealLogCoordinate D.T x i a <=
                    u i a + R) ->
                  ∀ (q : osiiAxisPairMultiGapIndex d k) (w : Complex),
                  |w.im| < Real.pi / 2 ->
                    norm ((D.packetFamily OS lgc).logBranch x q
                      (osiiAxisPairMultiGapUpdate
                        (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
                      C * (16 / rho) ^ M *
                        (1 + norm center + Real.exp R *
                          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
                            Real.exp (u i a))) ^ N := by
  obtain ⟨C, M, N, hC, hbound⟩ :=
    exists_packetFamily_logBranch_scale_bound_majorant d k OS lgc
  refine ⟨C, M, N, hC, ?_⟩
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
      (pow_le_pow_left₀ hbase_nonneg hbase N)
      (mul_nonneg hC (pow_nonneg (by positivity) M)))

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
