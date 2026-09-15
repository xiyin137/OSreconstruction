/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapRealShift
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacketReferenceBounds
















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The constant real logarithmic shift removed by the centered narrow-time
coordinate. -/
def osiiNarrowTimeRealLogShift
    (T : ℝ) :
    Fin k → osiiAxisPairIndex d → ℝ :=
  fun _ _ => Real.log (osiiNarrowTimeLogScale (d := d) T)

omit [NeZero k] in
@[simp] theorem osiiNarrowTimeCenteredRealLogCoordinate_sub
    (T : ℝ)
    (y : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiNarrowTimeCenteredRealLogCoordinate T
        (osiiAxisPairMultiGapSub
          (osiiNarrowTimeRealLogShift (d := d) (k := k) T) y) =
      y := by
  funext i a
  simp [osiiAxisPairMultiGapSub, osiiNarrowTimeRealLogShift,
    osiiNarrowTimeCenteredRealLogCoordinate]

omit [NeZero k] in
@[simp] theorem osiiNarrowTimeCenteredLogCoordinate_subReal_shift
    (T : ℝ)
    (ζ : OSIITimeGapSpace k) :
    osiiAxisPairMultiGapSubReal
        (osiiNarrowTimeRealLogShift (d := d) (k := k) T)
        (osiiNarrowTimeCenteredLogCoordinate (d := d) T ζ) =
      osiiNarrowTimeLogCoordinate (d := d) T ζ := by
  funext i a
  simp [osiiAxisPairMultiGapSubReal, osiiNarrowTimeRealLogShift,
    osiiNarrowTimeCenteredLogCoordinate]

omit [NeZero k] in
theorem osiiNarrowTimeCentered_chartRealPart_sub
    (T : ℝ)
    (y : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (w : ℂ) :
    osiiNarrowTimeCenteredRealLogCoordinate T
        (osiiAxisPairMultiGapChartRealPart
          (osiiAxisPairMultiGapSub
            (osiiNarrowTimeRealLogShift (d := d) (k := k) T) y)
          q
          (w -
            (osiiNarrowTimeRealLogShift
              (d := d) (k := k) T q.1 q.2 : ℂ))) =
      osiiAxisPairMultiGapChartRealPart y q w := by
  funext i a
  by_cases hi : i = q.1
  · subst i
    by_cases ha : a = q.2
    · subst a
      simp [osiiAxisPairMultiGapChartRealPart,
        osiiAxisPairMultiGapUpdate,
        osiiAxisPairMultiGapSub,
        osiiNarrowTimeRealLogShift,
        osiiNarrowTimeCenteredRealLogCoordinate]
    · simp [osiiAxisPairMultiGapChartRealPart,
        osiiAxisPairMultiGapUpdate,
        osiiAxisPairMultiGapSub,
        osiiNarrowTimeRealLogShift,
        osiiNarrowTimeCenteredRealLogCoordinate,
        osiiAxisPairSimultaneousLogRealEmbed,
        osiiAxisPairLogRealEmbed, ha]
  · simp [osiiAxisPairMultiGapChartRealPart,
      osiiAxisPairMultiGapUpdate,
      osiiAxisPairMultiGapSub,
      osiiNarrowTimeRealLogShift,
      osiiNarrowTimeCenteredRealLogCoordinate,
      osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed, hi]

namespace OSIIChapterV
namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- All centered logarithmic packet charts, and hence their common real edge,
admit one coefficient uniform in the spatial exhaustion level. -/
theorem fixedTimePacketData_exists_multiGapPacketFamily_centered_cosh_bounds_uniform_level
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ C : ℝ, 0 < C ∧
      ∀ level : ℕ,
        let P := D.fixedTimePacketData hφ_compact level
        let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
        let hordered :=
          (P.levelCover.carrier a
            ).sourcewiseLocalizedFactors_axisPairOrdered
              P.slope (P.ordered a) fs
        (∀ x : Fin k → osiiAxisPairIndex d → ℝ,
          ‖(F.multiGapPacketFamily
              OS lgc P.slope P.slope_gt_one hordered).realEdge x‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope x)))) ∧
        (∀ (q : osiiAxisPairMultiGapIndex d k)
          (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
            |w.im| < Real.pi / 2 →
            ‖(F.multiGapPacketFamily
                OS lgc P.slope P.slope_gt_one hordered).logBranch x q
                (osiiAxisPairMultiGapUpdate
                  (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
              C *
                Real.exp
                  (osiiOriginalOSUniformPacketCoshRate OS k *
                    SCV.logCoshGauge
                      (osiiAxisPairMultiGapFlatten
                        (osiiNarrowTimeCenteredRealLogCoordinate
                          P.slope
                          (osiiAxisPairMultiGapChartRealPart x q w))))) := by
  have hexists :
      ∀ q : osiiAxisPairMultiGapIndex d k,
        ∃ C : ℝ, 0 < C ∧
          ∀ (level : ℕ)
            (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
              |w.im| < Real.pi / 2 →
              let P := D.fixedTimePacketData hφ_compact level
              let F :=
                (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
              let hordered :=
                (P.levelCover.carrier a
                  ).sourcewiseLocalizedFactors_axisPairOrdered
                    P.slope (P.ordered a) fs
              ‖(F.multiGapPacketFamily
                  OS lgc P.slope P.slope_gt_one hordered).logBranch x q
                  (osiiAxisPairMultiGapUpdate
                    (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
                C *
                  Real.exp
                    (osiiOriginalOSUniformPacketCoshRate OS k *
                      SCV.logCoshGauge
                        (osiiAxisPairMultiGapFlatten
                          (osiiNarrowTimeCenteredRealLogCoordinate
                            P.slope
                            (osiiAxisPairMultiGapChartRealPart x q w)))) :=
    fun q =>
      D.fixedTimePacketData_exists_multiGapPacketFamily_chart_centered_cosh_bound_uniform_level
        hφ_compact a fs OS lgc q
  choose C hC hchart using hexists
  let Cstar : ℝ :=
    1 + ∑ q : osiiAxisPairMultiGapIndex d k, C q
  have hCstar : 0 < Cstar := by
    have hsum :
        0 ≤ ∑ q : osiiAxisPairMultiGapIndex d k, C q :=
      Finset.sum_nonneg fun q _ => (hC q).le
    dsimp [Cstar]
    linarith
  have hC_le :
      ∀ q : osiiAxisPairMultiGapIndex d k, C q ≤ Cstar := by
    intro q
    have hsingle :
        C q ≤ ∑ p : osiiAxisPairMultiGapIndex d k, C p :=
      Finset.single_le_sum
        (fun p _ => (hC p).le) (Finset.mem_univ q)
    dsimp [Cstar]
    linarith
  refine ⟨Cstar, hCstar, ?_⟩
  intro level
  let P := D.fixedTimePacketData hφ_compact level
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let packet :=
    F.multiGapPacketFamily
      OS lgc P.slope P.slope_gt_one hordered
  have hchartStar :
      ∀ (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          ‖packet.logBranch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
            Cstar *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope
                        (osiiAxisPairMultiGapChartRealPart x q w)))) := by
    intro q x w hw
    have hq := hchart q level x w hw
    change
      ‖packet.logBranch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
        C q *
          Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiNarrowTimeCenteredRealLogCoordinate
                    P.slope
                    (osiiAxisPairMultiGapChartRealPart x q w)))) at hq
    exact hq.trans
      (mul_le_mul_of_nonneg_right
        (hC_le q) (Real.exp_pos _).le)
  let q0 : osiiAxisPairMultiGapIndex d k :=
    ((0 : Fin k), ((0 : Fin d), false))
  have hreal :
      ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
        ‖packet.realEdge x‖ ≤
          Cstar *
            Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiNarrowTimeCenteredRealLogCoordinate
                      P.slope x))) := by
    intro x
    have hstrip :
        |((x q0.1 q0.2 : ℂ)).im| < Real.pi / 2 := by
      simp
      positivity
    have hbound :=
      hchartStar q0 x (x q0.1 q0.2 : ℂ) hstrip
    rw [osiiAxisPairMultiGapUpdate_realEmbed_selected x q0] at hbound
    rw [packet.logBranch_real_edge x q0] at hbound
    rw [osiiAxisPairMultiGapChartRealPart_selected_real x q0] at hbound
    exact hbound
  exact ⟨hreal, hchartStar⟩

/-- The common centered cosh coefficient for one time-partition member and
one source tuple.  It is chosen before the spatial exhaustion level. -/
noncomputable def fixedTimePacketCenteredCoshConstant
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : ℝ :=
  Classical.choose
    (D.fixedTimePacketData_exists_multiGapPacketFamily_centered_cosh_bounds_uniform_level
      hφ_compact a fs OS lgc)

theorem fixedTimePacketCenteredCoshConstant_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    0 < D.fixedTimePacketCenteredCoshConstant
      hφ_compact a fs OS lgc :=
  (Classical.choose_spec
    (D.fixedTimePacketData_exists_multiGapPacketFamily_centered_cosh_bounds_uniform_level
      hφ_compact a fs OS lgc)).1

/-- Recenter one fixed spatial-exhaustion packet in logarithmic time.  The
resulting sourcewise flat cross has the common slope-independent MZ rate and
uses the level-uniform centered coefficient. -/
noncomputable def fixedTimePacketCenteredCoshGrowthData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (level : ℕ)
    (a : D.index)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIAxisPairMultiGapSourcewiseCoshGrowthData d (k + 1) k := by
  let P := D.fixedTimePacketData hφ_compact level
  let base :=
    (P.pieceSourcewisePacketData OS lgc a).toSourcewiseCoshGrowthData
  let shift :=
    osiiNarrowTimeRealLogShift (d := d) (k := k) P.slope
  refine {
    flatCross := base.realShiftFlatCross shift
    realEdge := fun x =>
      base.realEdge (osiiAxisPairMultiGapSub shift x)
    flatCross_realEdge := ?_
    growth := ?_ }
  · intro fs x
    exact base.flatCross_realEdge fs
      (osiiAxisPairMultiGapSub shift x)
  · intro fs
    let hexists :=
      D.fixedTimePacketData_exists_multiGapPacketFamily_centered_cosh_bounds_uniform_level
        hφ_compact a fs OS lgc
    let C : ℝ :=
      D.fixedTimePacketCenteredCoshConstant hφ_compact a fs OS lgc
    have hC : 0 < C := by
      exact D.fixedTimePacketCenteredCoshConstant_pos
        hφ_compact a fs OS lgc
    have hbounds := (Classical.choose_spec hexists).2
    let packet := (P.pieceSourcewisePacketData OS lgc a).packetFamily fs
    let Q : OSIIAxisPairMultiGapFlatCrossData d k :=
      (base.flatCross fs).realShift shift
    have hrealShift :
        ∀ x : Fin k → osiiAxisPairIndex d → ℝ,
          ‖Q.realEdge x‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten x)) := by
      intro x
      have hx := (hbounds level).1
        (osiiAxisPairMultiGapSub shift x)
      change
        ‖packet.realEdge (osiiAxisPairMultiGapSub shift x)‖ ≤
          C *
            Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiNarrowTimeCenteredRealLogCoordinate
                      P.slope
                      (osiiAxisPairMultiGapSub shift x)))) at hx
      simpa [Q, base, shift, packet,
        OSIIChronologicalSourcewisePacketData.toSourcewiseCoshGrowthData,
        OSIIChronologicalSourcewisePacketData.flatCross,
        OSIIChronologicalSourcewisePacketData.packetFamily,
        OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData] using hx
    have hchartShift :
        ∀ (q : osiiAxisPairMultiGapIndex d k)
          (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
            |w.im| < Real.pi / 2 →
            ‖Q.branch x q
                (osiiAxisPairMultiGapUpdate
                  (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
              C *
                Real.exp
                  (osiiOriginalOSUniformPacketCoshRate OS k *
                    SCV.logCoshGauge
                      (osiiAxisPairMultiGapFlatten
                        (osiiAxisPairMultiGapChartRealPart x q w))) := by
      intro q x w hw
      have hwShift :
          |(w - (shift q.1 q.2 : ℂ)).im| < Real.pi / 2 := by
        simpa using hw
      have hx := (hbounds level).2 q
        (osiiAxisPairMultiGapSub shift x)
        (w - (shift q.1 q.2 : ℂ)) hwShift
      change
        ‖packet.logBranch
            (osiiAxisPairMultiGapSub shift x) q
            (osiiAxisPairMultiGapUpdate
              (osiiAxisPairSimultaneousLogRealEmbed
                (osiiAxisPairMultiGapSub shift x))
              q (w - (shift q.1 q.2 : ℂ)))‖ ≤
          C *
            Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiNarrowTimeCenteredRealLogCoordinate
                      P.slope
                      (osiiAxisPairMultiGapChartRealPart
                        (osiiAxisPairMultiGapSub shift x) q
                        (w - (shift q.1 q.2 : ℂ)))))) at hx
      rw [show shift =
          osiiNarrowTimeRealLogShift (d := d) (k := k) P.slope by rfl,
        osiiNarrowTimeCentered_chartRealPart_sub] at hx
      change
        ‖(base.flatCross fs).branch
            (osiiAxisPairMultiGapSub shift x) q
            (osiiAxisPairMultiGapSubReal shift
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w))‖ ≤
          C *
            Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiAxisPairMultiGapChartRealPart x q w)))
      rw [osiiAxisPairMultiGapSubReal_update]
      simpa [base, packet,
        OSIIChronologicalSourcewisePacketData.toSourcewiseCoshGrowthData,
        OSIIChronologicalSourcewisePacketData.flatCross,
        OSIIChronologicalSourcewisePacketData.packetFamily,
        OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData] using hx
    letI : NeZero (k * d) :=
      ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
    let X : OSIIAxisPairFlatCrossData (k * d) :=
      Q.toFlattenedFlatCrossData
    change OSIIAxisPairFlatCrossCoshGrowthData X
    refine {
      rate := osiiOriginalOSUniformPacketCoshRate OS k
      rate_nonneg :=
        osiiOriginalOSUniformPacketCoshRate_nonneg OS k
      realEdgeConstant := C
      realEdgeConstant_nonneg := hC.le
      realEdge_bound := ?_
      chartConstant := C
      chartConstant_pos := hC
      chart_bound := ?_ }
    · intro x
      simpa [X,
        OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData] using
        hrealShift (osiiAxisPairMultiGapUnflatten x)
    · intro q x w hw
      rw [X.family.flatTubeBranch_coordinate_line_eq_branch x q hw]
      simp only [X,
        OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData]
      let uq := osiiAxisPairMultiGapUnflattenIndex q
      rw [show q = osiiAxisPairMultiGapFlattenIndex uq by simp [uq]]
      have hbase :
          osiiAxisPairLogRealEmbed x =
            osiiAxisPairMultiGapFlatten
              (osiiAxisPairSimultaneousLogRealEmbed
                (osiiAxisPairMultiGapUnflatten x)) := by
        rw [osiiAxisPairMultiGapFlatten_realEmbed]
        rw [osiiAxisPairMultiGapFlatten_unflatten]
      rw [hbase]
      rw [osiiAxisPairMultiGapUnflatten_update_flatten]
      have hbound :=
        hchartShift uq (osiiAxisPairMultiGapUnflatten x) w hw
      rw [osiiAxisPairMultiGapFlatten_chartRealPart_unflatten
        x uq w] at hbound
      have hflatbase :
          osiiAxisPairMultiGapFlatten
              (osiiAxisPairSimultaneousLogRealEmbed
                (osiiAxisPairMultiGapUnflatten x)) =
            fun c => (x c : ℂ) := by
        rw [osiiAxisPairMultiGapFlatten_realEmbed]
        rw [osiiAxisPairMultiGapFlatten_unflatten]
        rfl
      rw [hflatbase]
      simpa [osiiAxisPairLogRealEmbed] using hbound

@[simp]
theorem fixedTimePacketCenteredCoshGrowthData_rate
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (level : ℕ)
    (a : D.index)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((D.fixedTimePacketCenteredCoshGrowthData
        hφ_compact level a OS lgc).growth fs).rate =
      osiiOriginalOSUniformPacketCoshRate OS k :=
  rfl

@[simp]
theorem fixedTimePacketCenteredCoshGrowthData_chartConstant
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (level : ℕ)
    (a : D.index)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((D.fixedTimePacketCenteredCoshGrowthData
        hφ_compact level a OS lgc).growth fs).chartConstant =
      D.fixedTimePacketCenteredCoshConstant hφ_compact a fs OS lgc :=
  rfl

end InitialBaseTimePartitionData
end OSIIChapterV
end OSReconstruction
