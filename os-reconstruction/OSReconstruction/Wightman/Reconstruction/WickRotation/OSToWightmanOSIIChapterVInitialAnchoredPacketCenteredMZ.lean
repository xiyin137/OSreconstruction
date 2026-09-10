/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketReferenceBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacketCenteredMZ
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketCenteredUniformBounds















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Ordinary E0 gives one centered compensated-branch coefficient for every
shrinking-time scale and spatial exhaustion level. -/
theorem
    exists_compensatedMovingPacket_branchOfOS_centered_cosh_bound_uniform_indices
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ)
        (z : ℂ), 0 < z.re →
          let P := A.commonPacketAt timeScale spatialLevel
          let F :=
            (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
          let hordered :=
            (P.levelCover.carrier a
              ).sourcewiseLocalizedFactors_axisPairOrdered
                P.slope (P.ordered a) fs
          ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
              P.slope P.slope_gt_one
              (osiiAxisPairPositiveCoefficients (x q.1))
              (fun b =>
                le_of_lt
                  (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
              q.2
              (F.packetLeftSource P.slope hordered x q)
              (F.packetLeftSource_support
                P.slope P.slope_gt_one hordered x q)
              (F.packetRightSource P.slope hordered x q)
              (F.packetRightSource_support
                P.slope P.slope_gt_one hordered x q)).branchOfOS
                OS z‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope x))) := by
  obtain ⟨CL, CR, hCL, hCR, hbounds⟩ :=
    A.exists_uniformPhysicalPacketVectorBounds_ofOS OS a fs q
  let B :=
    2 *
        ((A.partitionAt 0).commonLevelCarrierTimeRadius
          (A.timeTest_compact 0) + 1) +
      1
  have htime :
      0 ≤
        (A.partitionAt 0).commonLevelCarrierTimeRadius
          (A.timeTest_compact 0) :=
    ((A.partitionAt 0).commonLevelCarrierTimeRadius_pos
      a (A.timeTest_compact 0)).le
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith
  let m :=
    osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
      osiiOriginalOSBoundedStateSourceOrder OS (k + 1)
  let centeredConstant :=
    OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
      (d := d) (k := k) B
  let C : ℝ :=
    1 + CL * centeredConstant ^ m + CR * centeredConstant ^ m
  have hcenteredConstant : 0 < centeredConstant := by
    dsimp [centeredConstant,
      OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant]
    have hK :=
      osiiAxisPairCenteredTranslationCoshConstant_nonneg
        (d := d) (k := k)
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have hpow : 0 ≤ centeredConstant ^ m :=
      pow_nonneg hcenteredConstant.le _
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro timeScale spatialLevel x z hz
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a
      ).sourcewiseLocalizedFactors_axisPairOrdered
        P.slope (P.ordered a) fs
  have hcenter :
      ‖F.packetCenterOffsetVector P.slope hordered q‖ ≤ B := by
    simpa [P, F, hordered, B] using
      A.commonPacketAt_sourcewiseLocalized_norm_packetCenterOffsetVector_le
        timeScale spatialLevel a fs q
  have hphysical := hbounds timeScale spatialLevel x
  simpa [C, centeredConstant, m, P, F, hordered,
    osiiOriginalOSUniformPacketCoshRate] using
    F.norm_compensatedMovingPacket_branchOfOS_centered_cosh_le_of_vector_bounds
      OS m q B hB CL CR hCL hCR
      P.slope P.slope_gt_one hordered hcenter x z hz
      hphysical.1 hphysical.2

/-- Every original-OS logarithmic chart has one centered coefficient
independent of both anchored packet indices. -/
theorem
    exists_multiGapFlatCrossOfOS_chart_centered_cosh_bound_uniform_indices
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          let P := A.commonPacketAt timeScale spatialLevel
          let F :=
            (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
          let hordered :=
            (P.levelCover.carrier a
              ).sourcewiseLocalizedFactors_axisPairOrdered
                P.slope (P.ordered a) fs
          ‖(F.multiGapFlatCrossOfOS
              OS P.slope P.slope_gt_one hordered).branch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope
                        (osiiAxisPairMultiGapChartRealPart x q w)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    A.exists_compensatedMovingPacket_branchOfOS_centered_cosh_bound_uniform_indices
      OS a fs q
  refine ⟨C, hC, ?_⟩
  intro timeScale spatialLevel x w hw
  dsimp only
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a
      ).sourcewiseLocalizedFactors_axisPairOrdered
        P.slope (P.ordered a) fs
  let y := osiiAxisPairMultiGapChartRealPart x q w
  let packet :=
    F.multiGapFlatCrossOfOS
      OS P.slope P.slope_gt_one hordered
  have hxy :
      ∀ p : osiiAxisPairMultiGapIndex d k, p ≠ q →
        x p.1 p.2 = y p.1 p.2 := by
    intro p hp
    exact
      (osiiAxisPairMultiGapChartRealPart_eq_of_ne
        x q p w hp).symm
  have hbranch :
      packet.branch x q = packet.branch y q :=
    packet.branch_congr_of_eq_off_selected q hxy
  have hexpRe : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  have hphysical :=
    hbound timeScale spatialLevel y (Complex.exp w) hexpRe
  rw [congrFun hbranch
    (osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w)]
  simpa [P, F, hordered, packet, y,
    OSIIChronologicalCompactFactors.multiGapFlatCrossOfOS,
    OSIIAxisPairMultiGapFlatCrossData.ofCompensatedFrozenDependentOfOS,
    osiiAxisPairMultiGapUpdate] using hphysical

/-- All original-OS logarithmic charts and their common real edge share one
centered coefficient before either packet index is chosen. -/
theorem
    exists_multiGapFlatCrossOfOS_centered_cosh_bounds_uniform_indices
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ),
        let P := A.commonPacketAt timeScale spatialLevel
        let F :=
          (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
        let hordered :=
          (P.levelCover.carrier a
            ).sourcewiseLocalizedFactors_axisPairOrdered
              P.slope (P.ordered a) fs
        (∀ x : Fin k → osiiAxisPairIndex d → ℝ,
          ‖(F.multiGapFlatCrossOfOS
              OS P.slope P.slope_gt_one hordered).realEdge x‖ ≤
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
            ‖(F.multiGapFlatCrossOfOS
                OS P.slope P.slope_gt_one hordered).branch x q
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
  choose C hC hchart using
    fun q : osiiAxisPairMultiGapIndex d k =>
      A.exists_multiGapFlatCrossOfOS_chart_centered_cosh_bound_uniform_indices
        OS a fs q
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
  intro timeScale spatialLevel
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a
      ).sourcewiseLocalizedFactors_axisPairOrdered
        P.slope (P.ordered a) fs
  let packet :=
    F.multiGapFlatCrossOfOS
      OS P.slope P.slope_gt_one hordered
  have hchartStar :
      ∀ (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          ‖packet.branch x q
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
    have hq := hchart q timeScale spatialLevel x w hw
    change
      ‖packet.branch x q
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
    rw [osiiAxisPairMultiGapUpdate_realEmbed_selected x q0,
      packet.branch_real_edge x q0,
      osiiAxisPairMultiGapChartRealPart_selected_real x q0] at hbound
    exact hbound
  exact ⟨hreal, hchartStar⟩

/-- Uniform physical-vector bounds imply one centered compensated-branch
estimate shared by every shrinking time scale and spatial packet level. -/
theorem
    exists_compensatedMovingPacket_centered_cosh_bound_of_uniformPhysicalVectorBounds
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ)
        (z : ℂ), 0 < z.re →
          let P := A.commonPacketAt timeScale spatialLevel
          let F :=
            (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
          let hordered :=
            (P.levelCover.carrier a
              ).sourcewiseLocalizedFactors_axisPairOrdered
                P.slope (P.ordered a) fs
          ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
              P.slope P.slope_gt_one
              (osiiAxisPairPositiveCoefficients (x q.1))
              (fun b =>
                le_of_lt
                  (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
              q.2
              (F.packetLeftSource P.slope hordered x q)
              (F.packetLeftSource_support
                P.slope P.slope_gt_one hordered x q)
              (F.packetRightSource P.slope hordered x q)
              (F.packetRightSource_support
                P.slope P.slope_gt_one hordered x q)).branch
                OS lgc z‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope x))) := by
  obtain ⟨C, hC, hbound⟩ :=
    A.exists_compensatedMovingPacket_branchOfOS_centered_cosh_bound_uniform_indices
      OS a fs q
  refine ⟨C, hC, ?_⟩
  intro timeScale spatialLevel x z hz
  dsimp only
  rw [OSIIAxisPairRotatedSourcePacket.branch_eq_branchOfOS _ OS lgc z hz]
  exact hbound timeScale spatialLevel x z hz

/-- Transport the uniform physical centered estimate to one logarithmic
packet chart. -/
theorem
    exists_multiGapPacketFamily_chart_centered_cosh_bound_of_uniformPhysicalVectorBounds
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          let P := A.commonPacketAt timeScale spatialLevel
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
                        (osiiAxisPairMultiGapChartRealPart x q w)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    A.exists_compensatedMovingPacket_centered_cosh_bound_of_uniformPhysicalVectorBounds
      OS lgc hvector a fs q
  refine ⟨C, hC, ?_⟩
  intro timeScale spatialLevel x w hw
  dsimp only
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a
      ).sourcewiseLocalizedFactors_axisPairOrdered
        P.slope (P.ordered a) fs
  let y := osiiAxisPairMultiGapChartRealPart x q w
  let packet :=
    F.multiGapPacketFamily
      OS lgc P.slope P.slope_gt_one hordered
  have hxy :
      ∀ p : osiiAxisPairMultiGapIndex d k, p ≠ q →
        x p.1 p.2 = y p.1 p.2 := by
    intro p hp
    exact
      (osiiAxisPairMultiGapChartRealPart_eq_of_ne
        x q p w hp).symm
  have hbranch :
      packet.logBranch x q = packet.logBranch y q :=
    packet.logBranch_congr_of_eq_off_selected q hxy
  have hexpRe : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  have hphysical :=
    hbound timeScale spatialLevel y (Complex.exp w) hexpRe
  let z :=
    osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w
  calc
    ‖packet.logBranch x q z‖ =
        ‖packet.logBranch y q z‖ := by
      rw [congrFun hbranch z]
    _ ≤
        C *
          Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiNarrowTimeCenteredRealLogCoordinate P.slope y))) := by
      simpa [P, F, hordered, packet, y, z,
        OSIIChronologicalCompactFactors.multiGapPacketFamily,
        OSIIAxisPairMultiGapSemigroupPacketFamily.logBranch,
        OSIIAxisPairMultiGapSemigroupPacketFamily.ofCompensatedFrozenDependent,
        OSIIAxisPairGapRotatedSourcePacket.branch,
        osiiAxisPairMultiGapUpdate] using hphysical

/-- All logarithmic packet charts, and hence their common real edge, admit
one centered-cosh coefficient uniform in both anchored packet indices. -/
theorem
    exists_multiGapPacketFamily_centered_cosh_bounds_of_uniformPhysicalVectorBounds
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (timeScale spatialLevel : ℕ),
        let P := A.commonPacketAt timeScale spatialLevel
        let F :=
          (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
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
          ∀ (timeScale spatialLevel : ℕ)
            (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
              |w.im| < Real.pi / 2 →
              let P := A.commonPacketAt timeScale spatialLevel
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
      A.exists_multiGapPacketFamily_chart_centered_cosh_bound_of_uniformPhysicalVectorBounds
        OS lgc hvector a fs q
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
  intro timeScale spatialLevel
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a
      ).sourcewiseLocalizedFactors_axisPairOrdered
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
    have hq := hchart q timeScale spatialLevel x w hw
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

/-- The common centered-cosh coefficient supplied by the physical-vector
contract for one partition member and one product source. -/
noncomputable def anchoredPacketCenteredCoshConstant
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) : ℝ :=
  Classical.choose
    (A.exists_multiGapPacketFamily_centered_cosh_bounds_of_uniformPhysicalVectorBounds
      OS lgc hvector a fs)

theorem anchoredPacketCenteredCoshConstant_pos
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    0 < A.anchoredPacketCenteredCoshConstant
      OS lgc hvector a fs :=
  (Classical.choose_spec
    (A.exists_multiGapPacketFamily_centered_cosh_bounds_of_uniformPhysicalVectorBounds
      OS lgc hvector a fs)).1

/-- Recenter one anchored packet in logarithmic time.  Its growth constants
are independent of both the shrinking time scale and the spatial exhaustion
level. -/
noncomputable def anchoredPacketCenteredCoshGrowthData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index) :
    OSIIAxisPairMultiGapSourcewiseCoshGrowthData d (k + 1) k := by
  let P := A.commonPacketAt timeScale spatialLevel
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
      A.exists_multiGapPacketFamily_centered_cosh_bounds_of_uniformPhysicalVectorBounds
        OS lgc hvector a fs
    let C : ℝ :=
      A.anchoredPacketCenteredCoshConstant OS lgc hvector a fs
    have hC : 0 < C := by
      exact A.anchoredPacketCenteredCoshConstant_pos
        OS lgc hvector a fs
    have hbounds := (Classical.choose_spec hexists).2
    let packet :=
      (P.pieceSourcewisePacketData OS lgc a).packetFamily fs
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
      have hx := (hbounds timeScale spatialLevel).1
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
      have hx := (hbounds timeScale spatialLevel).2 q
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
theorem anchoredPacketCenteredCoshGrowthData_rate
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((A.anchoredPacketCenteredCoshGrowthData
        OS lgc hvector timeScale spatialLevel a).growth fs).rate =
      osiiOriginalOSUniformPacketCoshRate OS k :=
  rfl

@[simp]
theorem anchoredPacketCenteredCoshGrowthData_chartConstant
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hvector : A.HasUniformPhysicalPacketVectorBounds OS lgc)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((A.anchoredPacketCenteredCoshGrowthData
        OS lgc hvector timeScale spatialLevel a).growth fs).chartConstant =
      A.anchoredPacketCenteredCoshConstant OS lgc hvector a fs :=
  rfl

/-- The original-OS centered coefficient is selected before either anchored
packet index and depends only on the fixed source. -/
noncomputable def anchoredPacketCenteredCoshConstantOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) : ℝ :=
  Classical.choose
    (A.exists_multiGapFlatCrossOfOS_centered_cosh_bounds_uniform_indices
      OS a fs)

theorem anchoredPacketCenteredCoshConstantOfOS_pos
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    0 < A.anchoredPacketCenteredCoshConstantOfOS OS a fs :=
  (Classical.choose_spec
    (A.exists_multiGapFlatCrossOfOS_centered_cosh_bounds_uniform_indices
      OS a fs)).1

/-- Recenter the genuine original-OS sourcewise continuation while retaining
one growth coefficient for every shrinking scale and spatial level. -/
noncomputable def anchoredPacketCenteredCoshGrowthDataOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index) :
    OSIIAxisPairMultiGapSourcewiseCoshGrowthData d (k + 1) k := by
  let P := A.commonPacketAt timeScale spatialLevel
  let base :=
    (P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)
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
      A.exists_multiGapFlatCrossOfOS_centered_cosh_bounds_uniform_indices
        OS a fs
    let C : ℝ :=
      A.anchoredPacketCenteredCoshConstantOfOS OS a fs
    have hC : 0 < C :=
      A.anchoredPacketCenteredCoshConstantOfOS_pos OS a fs
    have hbounds := (Classical.choose_spec hexists).2
    let packet := base.flatCross fs
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
      have hx := (hbounds timeScale spatialLevel).1
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
        OSIIChronologicalCompactFactors.toSourcewiseCoshGrowthDataAtSlopeOfOS]
        using hx
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
      have hx := (hbounds timeScale spatialLevel).2 q
        (osiiAxisPairMultiGapSub shift x)
        (w - (shift q.1 q.2 : ℂ)) hwShift
      change
        ‖packet.branch
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
      simpa [packet] using hx
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
theorem anchoredPacketCenteredCoshGrowthDataOfOS_rate
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((A.anchoredPacketCenteredCoshGrowthDataOfOS
        OS timeScale spatialLevel a).growth fs).rate =
      osiiOriginalOSUniformPacketCoshRate OS k :=
  rfl

@[simp]
theorem anchoredPacketCenteredCoshGrowthDataOfOS_chartConstant
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((A.anchoredPacketCenteredCoshGrowthDataOfOS
        OS timeScale spatialLevel a).growth fs).chartConstant =
      A.anchoredPacketCenteredCoshConstantOfOS OS a fs :=
  rfl

/-- Centering the original-OS sourcewise continuation changes only its real
logarithmic coordinates. -/
theorem anchoredPacketCenteredOfOS_toMZFamily_eq
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (timeScale spatialLevel : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    (A.anchoredPacketCenteredCoshGrowthDataOfOS
        OS timeScale spatialLevel a).toMZFamily.toFun fs z =
      let P := A.commonPacketAt timeScale spatialLevel
      ((P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).toMZFamily.toFun fs
          (osiiAxisPairMultiGapSubReal
            (osiiNarrowTimeRealLogShift
              (d := d) (k := k) P.slope) z) := by
  let P := A.commonPacketAt timeScale spatialLevel
  let base :=
    (P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)
  let shift :=
    osiiNarrowTimeRealLogShift (d := d) (k := k) P.slope
  apply base.toMZFamily_realShift_eq shift
    (A.anchoredPacketCenteredCoshGrowthDataOfOS
      OS timeScale spatialLevel a)
  · rfl
  · intro x
    rfl
  · exact hz

/-- The genuine original-OS sourcewise continuation has one centered damped
bound for every shrinking-time scale and spatial exhaustion level. -/
theorem norm_anchoredPacketOfOS_toMZFamily_mul_centeredDamping_le
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (timeScale spatialLevel : ℕ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η) :
    let P := A.commonPacketAt timeScale spatialLevel
    ‖((P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
        OS P.slope P.slope_gt_one (P.ordered a)).toMZFamily.toFun fs
          (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ) *
      SCV.logCoshDamping
        (osiiOriginalOSUniformPacketCoshRate OS k)
        (osiiAxisPairMultiGapFlatten
          (osiiNarrowTimeCenteredLogCoordinate
            (d := d) P.slope ζ))‖ ≤
      A.anchoredPacketCenteredCoshConstantOfOS OS a fs := by
  let P := A.commonPacketAt timeScale spatialLevel
  let Q :=
    A.anchoredPacketCenteredCoshGrowthDataOfOS
      OS timeScale spatialLevel a
  let shift :=
    osiiNarrowTimeRealLogShift (d := d) (k := k) P.slope
  let z :=
    osiiNarrowTimeCenteredLogCoordinate (d := d) P.slope ζ
  have hraw :
      osiiNarrowTimeLogCoordinate (d := d) P.slope ζ ∈
        osiiAxisPairMultiGapLogDomain d k :=
    osiiNarrowTimeLogCoordinate_mapsTo
      P.slope (lt_trans zero_lt_one P.slope_gt_one)
      η hηsum hζ
  have hz :
      z ∈ osiiAxisPairMultiGapLogDomain d k := by
    apply
      (osiiAxisPairMultiGapSubReal_mem_logDomain_iff shift z).1
    simpa [z, shift] using hraw
  have hbound :=
    Q.norm_toMZFamily_mul_logCoshDamping_le_chartConstant
      z hz fs
  have heq :=
    A.anchoredPacketCenteredOfOS_toMZFamily_eq
      OS timeScale spatialLevel a fs z hz
  rw [heq] at hbound
  simpa [P, Q, z, shift] using hbound

/-- On each compact narrow-time set, original OS axioms give a genuine
sourcewise MZ bound uniform in both anchored packet indices. -/
theorem commonPacket_toSourcewiseMZFamilyAtSlopeOfOS_compact_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η) :
    ∃ C : ℝ, ∀ timeScale spatialLevel ζ, ζ ∈ K →
      let P := A.commonPacketAt timeScale spatialLevel
      ‖((P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
          OS P.slope P.slope_gt_one (P.ordered a)).toMZFamily.toFun fs
            (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)‖ ≤ C := by
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let rate :=
    osiiOriginalOSUniformPacketCoshRate OS k
  let T₀ : ℝ := 2
  let image :=
    osiiNarrowTimeCenteredLogCoordinate (d := d) T₀ '' K
  have hT₀ : 0 < T₀ := by
    norm_num [T₀]
  have himage : IsCompact image := by
    exact isCompact_osiiNarrowTimeCenteredLogCoordinate_image
      T₀ hT₀ η K hK_compact hK_subset
  let weightInv :
      (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
    fun z =>
      (SCV.logCoshDamping rate
        (osiiAxisPairMultiGapFlatten z))⁻¹
  have hweight :
      Continuous
        (fun z : Fin k → osiiAxisPairIndex d → ℂ =>
          SCV.logCoshDamping rate
            (osiiAxisPairMultiGapFlatten z)) :=
    (SCV.differentiable_logCoshDamping rate).continuous.comp
      (osiiAxisPairMultiGapFlattenCLE
        (d := d) (k := k)).continuous
  have hweightInv : Continuous weightInv := by
    exact hweight.inv₀ fun z =>
      SCV.logCoshDamping_ne_zero rate
        (osiiAxisPairMultiGapFlatten z)
  obtain ⟨M, hM⟩ :=
    himage.exists_bound_of_continuousOn hweightInv.continuousOn
  let M₀ : ℝ := max M 0
  let C₀ :=
    A.anchoredPacketCenteredCoshConstantOfOS OS a fs
  refine ⟨C₀ * M₀, ?_⟩
  intro timeScale spatialLevel ζ hζK
  let P := A.commonPacketAt timeScale spatialLevel
  let F :=
    ((P.levelCover.carrier a).toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS P.slope P.slope_gt_one (P.ordered a)).toMZFamily.toFun fs
        (osiiNarrowTimeLogCoordinate (d := d) P.slope ζ)
  let w :=
    SCV.logCoshDamping rate
      (osiiAxisPairMultiGapFlatten
        (osiiNarrowTimeCenteredLogCoordinate
          (d := d) P.slope ζ))
  have hζ := hK_subset hζK
  have hdamped : ‖F * w‖ ≤ C₀ :=
    A.norm_anchoredPacketOfOS_toMZFamily_mul_centeredDamping_le
      OS a fs η hηsum timeScale spatialLevel ζ hζ
  have hcenter :
      osiiNarrowTimeCenteredLogCoordinate (d := d) P.slope ζ =
        osiiNarrowTimeCenteredLogCoordinate (d := d) T₀ ζ :=
    osiiNarrowTimeCenteredLogCoordinate_eq_of_pos
      P.slope T₀
      (lt_trans zero_lt_one P.slope_gt_one) hT₀
      η ζ hζ
  have hzin :
      osiiNarrowTimeCenteredLogCoordinate
        (d := d) P.slope ζ ∈ image := by
    rw [hcenter]
    exact ⟨ζ, hζK, rfl⟩
  have hinv : ‖w⁻¹‖ ≤ M₀ :=
    (hM _ hzin).trans (le_max_left _ _)
  have hw : w ≠ 0 :=
    SCV.logCoshDamping_ne_zero rate
      (osiiAxisPairMultiGapFlatten
        (osiiNarrowTimeCenteredLogCoordinate
          (d := d) P.slope ζ))
  calc
    ‖F‖ = ‖(F * w) * w⁻¹‖ := by
      rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]
    _ ≤ ‖F * w‖ * ‖w⁻¹‖ := norm_mul_le _ _
    _ ≤ C₀ * M₀ :=
      mul_le_mul hdamped hinv (norm_nonneg _)
        (A.anchoredPacketCenteredCoshConstantOfOS_pos OS a fs).le

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
