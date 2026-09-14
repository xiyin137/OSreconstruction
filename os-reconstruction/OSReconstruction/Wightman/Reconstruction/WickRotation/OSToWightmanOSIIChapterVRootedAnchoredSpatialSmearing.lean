/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialAgreement
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedHolomorphicSmearing
















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- Apply the genuine original-OS middle-root contraction to every right
block without changing any open generator domain. -/
noncomputable def rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k) :
    GeneratorOpenHilbertFieldScaleFamilyData OS k where
  leftDomain := E.leftDomain
  rightDomain := E.rightDomain
  leftDomain_open := E.leftDomain_open
  rightDomain_open := E.rightDomain_open
  leftField := E.leftField
  rightField := fun i scale mode z =>
    D.semigroupBridgeRootOperatorOfOS i scale
      (E.rightField i scale mode z)
  leftField_holomorphic := E.leftField_holomorphic
  rightField_holomorphic := by
    intro i scale mode
    exact
      (D.semigroupBridgeRootOperatorOfOS i scale
        ).differentiable.differentiableOn.comp
          (E.rightField_holomorphic i scale mode)
          (fun _ _ => Set.mem_univ _)
  leftField_polyBounded_on_compact :=
    E.leftField_polyBounded_on_compact
  rightField_polyBounded_on_compact := by
    intro i K hK_compact hK_domain
    obtain ⟨C, hC, p, hbound⟩ :=
      E.rightField_polyBounded_on_compact
        i K hK_compact hK_domain
    refine ⟨C, hC, p, ?_⟩
    intro scale z hz mode
    calc
      ‖D.semigroupBridgeRootOperatorOfOS i scale
          (E.rightField i scale mode z)‖
          ≤ ‖D.semigroupBridgeRootOperatorOfOS i scale‖ *
              ‖E.rightField i scale mode z‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (C * (1 + (mode : ℝ)) ^ p) := by
        gcongr
        · exact
            D.semigroupBridgeRootOperatorOfOS_norm_le_one
              i scale
        · exact hbound scale z hz mode
      _ = C * (1 + (mode : ℝ)) ^ p := one_mul _

/-- Compatibility presentation of genuine original-OS open-field root
smearing. -/
noncomputable def rootSmearedGeneratorOpenHilbertFieldScaleFamilyData
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k) :
    GeneratorOpenHilbertFieldScaleFamilyData OS k :=
  rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D E

/-- Original-OS root smearing contracts every right Hilbert field vector. -/
theorem
    norm_rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS_rightField_le
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (z : Fin (i.m - 1) -> Complex) :
    ‖(rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D E
        ).rightField i scale mode z‖ ≤
      ‖E.rightField i scale mode z‖ := by
  change
    ‖D.semigroupBridgeRootOperatorOfOS i scale
        (E.rightField i scale mode z)‖ ≤
      ‖E.rightField i scale mode z‖
  calc
    _ ≤ ‖D.semigroupBridgeRootOperatorOfOS i scale‖ *
          ‖E.rightField i scale mode z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖E.rightField i scale mode z‖ := by
      gcongr
      exact D.semigroupBridgeRootOperatorOfOS_norm_le_one i scale
    _ = _ := one_mul _

/-- Compatibility wrapper for growth-free open-field root contraction. -/
theorem norm_rootSmearedGeneratorOpenHilbertFieldScaleFamilyData_rightField_le
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (z : Fin (i.m - 1) -> Complex) :
    ‖(rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc E
        ).rightField i scale mode z‖ ≤
      ‖E.rightField i scale mode z‖ :=
  norm_rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS_rightField_le
    D E i scale mode z

/-- On a positive bridge the genuine original-OS rooted generator is the
middle-root integral of its unsmeared original-OS modes. -/
theorem
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS_mode_positiveReal_eq_integral
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        D E).modeOfOS timeScale i mode
        (osiiPositiveRealTimeEmbed τ) =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          E.modeOfOS timeScale i mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) := by
  let u : OSHilbertSpace OS :=
    E.leftField i timeScale mode
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed τ
            (i.leftGlobalIndex a)))
  let v : OSHilbertSpace OS :=
    E.rightField i timeScale mode
      (fun b =>
        osiiPositiveRealTimeEmbed τ
          (i.rightGlobalIndex b))
  have hvector :
      Integrable
        (fun t : ℝ =>
          D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS
              (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v) := by
    exact
      D.integrable_semigroupBridgeRootWeight_smul_originalTimeShift_add
        i timeScale (τ i.bridgeGlobalIndex) hbridge v
  rw [GeneratorOpenHilbertFieldScaleFamilyData.modeOfOS,
    generatorSpatialHermiteModeOfOS]
  change
    @inner ℂ (OSHilbertSpace OS) _ u
        (osiiOriginalOSHilbertComplex OS
          ((τ i.bridgeGlobalIndex : ℝ) : ℂ)
          (D.semigroupBridgeRootOperatorOfOS i timeScale v)) =
      _
  rw [D.osiiOriginalOSHilbertComplex_semigroupBridgeRootOperatorOfOS
    i timeScale (τ i.bridgeGlobalIndex) hbridge v]
  calc
    @inner ℂ (OSHilbertSpace OS) _ u
        (∫ t : ℝ,
          D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS
              (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v)
        =
      ∫ t : ℝ,
        @inner ℂ (OSHilbertSpace OS) _ u
          (D.semigroupBridgeRootWeight i timeScale t •
            osiiOriginalOSHilbertComplex OS
              (((τ i.bridgeGlobalIndex + t : ℝ)) : ℂ) v) := by
            exact (integral_inner hvector u).symm
    _ =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          E.modeOfOS timeScale i mode
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i τ
                (τ i.bridgeGlobalIndex + t))) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by
              simp only [inner_smul_right]
              congr 1
              rw [GeneratorOpenHilbertFieldScaleFamilyData.modeOfOS,
                generatorSpatialHermiteModeOfOS]
              change _ =
                @inner ℂ (OSHilbertSpace OS) _
                  (E.leftField i timeScale mode
                    (fun a =>
                      -star
                        (osiiPositiveRealTimeEmbed
                          (generatorBridgeVariation i τ
                            (τ i.bridgeGlobalIndex + t))
                          (i.leftGlobalIndex a))))
                  (osiiOriginalOSHilbertComplex OS
                    (osiiPositiveRealTimeEmbed
                      (generatorBridgeVariation i τ
                        (τ i.bridgeGlobalIndex + t))
                      i.bridgeGlobalIndex)
                    (E.rightField i timeScale mode
                      (fun b =>
                        osiiPositiveRealTimeEmbed
                          (generatorBridgeVariation i τ
                            (τ i.bridgeGlobalIndex + t))
                          (i.rightGlobalIndex b))))
              simp only [osiiPositiveRealTimeEmbed,
                generatorBridgeVariation_left,
                generatorBridgeVariation_bridge,
                generatorBridgeVariation_right,
                u, v]

/-- Original-OS source equality for one split needs only its four genuine
block real-edge conditions. -/
theorem sourceAgreeingGeneratorModeOfOS_eq_of_blockRealEdges
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hEleft : i.leftRealCoordinates τ ∈ E.leftRealRegion i)
    (hEright : i.rightRealCoordinates τ ∈ E.rightRealRegion i)
    (hFleft : i.leftRealCoordinates τ ∈ F.leftRealRegion i)
    (hFright : i.rightRealCoordinates τ ∈ F.rightRealRegion i) :
    E.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) =
      F.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) := by
  calc
    E.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) =
        OS.S (i.n + i.m)
          (ZeroDiagonalSchwartz.ofClassical
            (((E.leftSource i scale mode
                (i.leftRealCoordinates τ)).1).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (τ i.bridgeGlobalIndex)
                (E.rightSource i scale mode
                  (i.rightRealCoordinates τ)).1))) := by
      exact
        generatorSemigroupPairing_positiveReal_eq_schwinger
          OS i
          (E.leftField i scale mode)
          (E.rightField i scale mode)
          (E.leftSource i scale mode)
          (E.rightSource i scale mode)
          (E.leftField_realEdge i scale mode)
          (E.rightField_realEdge i scale mode)
          τ hbridge hEleft hEright
    _ =
        OS.S (i.n + i.m)
          (ZeroDiagonalSchwartz.ofClassical
            (((F.leftSource i scale mode
                (i.leftRealCoordinates τ)).1).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (τ i.bridgeGlobalIndex)
                (F.rightSource i scale mode
                  (i.rightRealCoordinates τ)).1))) := by
      rw [P.leftSource_eq, P.rightSource_eq]
    _ =
        F.modeOfOS scale i mode
          (osiiPositiveRealTimeEmbed τ) := by
      symm
      exact
        generatorSemigroupPairing_positiveReal_eq_schwinger
          OS i
          (F.leftField i scale mode)
          (F.rightField i scale mode)
          (F.leftSource i scale mode)
          (F.rightSource i scale mode)
          (F.leftField_realEdge i scale mode)
          (F.rightField_realEdge i scale mode)
          τ hbridge hFleft hFright

/-- Original-OS root smearing preserves source agreement at every common
admissible real generator point. -/
theorem rootSmearedGeneratorModeOfOS_eq_of_commonRealAutomatic
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hautomatic : τ ∈ P.commonRealAutomaticSet) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        E.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode
        (osiiPositiveRealTimeEmbed τ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        F.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode
        (osiiPositiveRealTimeEmbed τ) := by
  obtain ⟨J, _hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  rw [
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS_mode_positiveReal_eq_integral
      D E.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale mode τ hbridge,
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS_mode_positiveReal_eq_integral
      D F.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale mode τ hbridge]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases hweight :
        D.semigroupBridgeRootWeight i timeScale t = 0
    · simp [hweight]
    · have htJ : t ∈ J := by
        apply hsupport timeScale
        exact subset_tsupport _
          (by simpa [Function.mem_support] using hweight)
      apply congrArg
        (fun z : ℂ =>
          D.semigroupBridgeRootWeight i timeScale t * z)
      apply sourceAgreeingGeneratorModeOfOS_eq_of_blockRealEdges
        P i timeScale mode
      · rw [generatorBridgeVariation_bridge]
        exact
          add_pos
            hbridge
            (hJ_positive htJ)
      · simpa using (hautomatic.1 i).1
      · simpa using (hautomatic.1 i).2
      · simpa using (hautomatic.2 i).1
      · simpa using (hautomatic.2 i).2

/-- Original-OS root smearing preserves the canonical common positive-real
source germ at every split and packet scale. -/
theorem rootSmearedGeneratorModeOfOS_eq_on_commonPositiveReal
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k → ℝ)
    (hτ :
      τ ∈
        P.toCommonPositiveRealModeAgreementDataOfOS.realRegion) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        E.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode
        (osiiPositiveRealTimeEmbed τ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        F.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode
        (osiiPositiveRealTimeEmbed τ) := by
  let hV := mem_nhds_iff.mp P.commonRealAutomaticSet_mem_nhds
  let V : Set (Fin k → ℝ) := Classical.choose hV
  have hVspec := Classical.choose_spec hV
  have hVsub : V ⊆ P.commonRealAutomaticSet :=
    hVspec.1
  change τ ∈ V ∩ section43TimeStrictPositiveRegion k at hτ
  exact
    rootSmearedGeneratorModeOfOS_eq_of_commonRealAutomatic
      P D i timeScale mode τ
      (hτ.2 i.bridgeGlobalIndex) (hVsub hτ.1)

/-- Compatibility wrapper for the original-OS common positive-real rooted
source germ. -/
theorem rootSmearedGeneratorMode_eq_on_commonPositiveReal
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (τ : Fin k -> ℝ)
    (hτ :
      τ ∈
        (P.toCommonPositiveRealModeAgreementData lgc).realRegion) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
        E.toGeneratorOpenHilbertFieldScaleFamilyData).mode
        lgc timeScale i mode
        (osiiPositiveRealTimeEmbed τ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
        F.toGeneratorOpenHilbertFieldScaleFamilyData).mode
        lgc timeScale i mode
        (osiiPositiveRealTimeEmbed τ) :=
  rootSmearedGeneratorModeOfOS_eq_on_commonPositiveReal
    P D i timeScale mode τ hτ

/-- Rooted source-agreeing original-OS generator modes coincide throughout
their genuine connected complex source germ. -/
theorem rootSmearedGeneratorModeOfOS_eq_on_commonComplex
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermDataOfOS
        P.toCommonPositiveRealModeAgreementDataOfOS)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ C.domain i) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        E.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode z =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
        F.toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode z := by
  let RE :=
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
      E.toGeneratorOpenHilbertFieldScaleFamilyData
  let RF :=
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS D
      F.toGeneratorOpenHilbertFieldScaleFamilyData
  let U : Set (OSIITimeGapSpace k) := C.domain i
  let h : OSIITimeGapSpace k -> ℂ :=
    fun w =>
      RE.modeOfOS timeScale i mode w -
        RF.modeOfOS timeScale i mode w
  have hU_open : IsOpen U :=
    C.domain_open i
  have hU_connected : IsConnected U :=
    (C.domain_convex i).isConnected
      ⟨osiiPositiveRealTimeEmbed C.center,
        C.center_mem_domain i⟩
  have hh : DifferentiableOn ℂ h U :=
    (RE.modeOfOS_holomorphic timeScale i mode).mono
        (fun w hw => C.ball_subset_first i hw) |>.sub
      ((RF.modeOfOS_holomorphic timeScale i mode).mono
        (fun w hw => C.ball_subset_second i hw))
  let V : Set (Fin k -> ℝ) :=
    P.toCommonPositiveRealModeAgreementDataOfOS.realRegion ∩
      SCV.realToComplex ⁻¹' U
  have hrealToComplex :
      Continuous (SCV.realToComplex (m := k)) :=
    continuous_pi fun j =>
      Complex.continuous_ofReal.comp (continuous_apply j)
  have hV_open : IsOpen V :=
    P.toCommonPositiveRealModeAgreementDataOfOS.realRegion_open.inter
      (hrealToComplex.isOpen_preimage U hU_open)
  have hV_nonempty : V.Nonempty := by
    refine ⟨C.center, C.center_mem, ?_⟩
    change SCV.realToComplex C.center ∈ U
    rw [show SCV.realToComplex C.center =
        osiiPositiveRealTimeEmbed C.center by rfl]
    exact C.center_mem_domain i
  have hV_sub :
      ∀ x ∈ V, SCV.realToComplex x ∈ U :=
    fun x hx => hx.2
  have hh_zero :
      ∀ x ∈ V, h (SCV.realToComplex x) = 0 := by
    intro x hx
    simp only [h]
    rw [show SCV.realToComplex x =
        osiiPositiveRealTimeEmbed x by rfl,
      rootSmearedGeneratorModeOfOS_eq_on_commonPositiveReal
        P D i timeScale mode x hx.1,
      sub_self]
  exact
    sub_eq_zero.mp
      (SCV.identity_theorem_totally_real
        hU_open hU_connected hh
        hV_open hV_nonempty hV_sub hh_zero z hz)

/-- Root-smeared modes agree throughout every common complex mode germ. -/
theorem rootSmearedGeneratorMode_eq_on_commonComplex
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (C :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermData
        (P.toCommonPositiveRealModeAgreementData lgc))
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ C.domain i) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
        E.toGeneratorOpenHilbertFieldScaleFamilyData).mode
        lgc timeScale i mode z =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
        F.toGeneratorOpenHilbertFieldScaleFamilyData).mode
        lgc timeScale i mode z := by
  let RE :=
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
      E.toGeneratorOpenHilbertFieldScaleFamilyData
  let RF :=
    rootSmearedGeneratorOpenHilbertFieldScaleFamilyData D lgc
      F.toGeneratorOpenHilbertFieldScaleFamilyData
  let U : Set (OSIITimeGapSpace k) := C.domain i
  let h : OSIITimeGapSpace k → ℂ :=
    fun w =>
      RE.mode lgc timeScale i mode w -
        RF.mode lgc timeScale i mode w
  have hU_open : IsOpen U :=
    C.domain_open i
  have hU_connected : IsConnected U :=
    (C.domain_convex i).isConnected
      ⟨osiiPositiveRealTimeEmbed C.center,
        C.center_mem_domain i⟩
  have hh : DifferentiableOn ℂ h U :=
    (RE.mode_holomorphic lgc timeScale i mode).mono
        (fun w hw => C.ball_subset_first i hw) |>.sub
      ((RF.mode_holomorphic lgc timeScale i mode).mono
        (fun w hw => C.ball_subset_second i hw))
  let V : Set (Fin k → ℝ) :=
    (P.toCommonPositiveRealModeAgreementData lgc).realRegion ∩
      SCV.realToComplex ⁻¹' U
  have hrealToComplex :
      Continuous (SCV.realToComplex (m := k)) :=
    continuous_pi fun j =>
      Complex.continuous_ofReal.comp (continuous_apply j)
  have hV_open : IsOpen V :=
    (P.toCommonPositiveRealModeAgreementData lgc).realRegion_open.inter
      (hrealToComplex.isOpen_preimage U hU_open)
  have hV_nonempty : V.Nonempty := by
    refine ⟨C.center, C.center_mem, ?_⟩
    change SCV.realToComplex C.center ∈ U
    rw [show SCV.realToComplex C.center =
        osiiPositiveRealTimeEmbed C.center by rfl]
    exact C.center_mem_domain i
  have hV_sub :
      ∀ x ∈ V, SCV.realToComplex x ∈ U :=
    fun x hx => hx.2
  have hh_zero :
      ∀ x ∈ V, h (SCV.realToComplex x) = 0 := by
    intro x hx
    simp only [h]
    rw [show SCV.realToComplex x =
        osiiPositiveRealTimeEmbed x by rfl,
      rootSmearedGeneratorMode_eq_on_commonPositiveReal
        P D lgc i timeScale mode x hx.1,
      sub_self]
  exact
    sub_eq_zero.mp
      (SCV.identity_theorem_totally_real
        hU_open hU_connected hh
        hV_open hV_nonempty hV_sub hh_zero z hz)

/-- The genuine original-OS local root-smearing transformation is exactly
the original synchronized rooted Hermite generator. -/
theorem rootSmearedLocalGeneratorOpenField_modeOfOS_eq
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale mode : ℕ)
    (z : OSIITimeGapSpace k) :
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        H.toContinuousTranslationData
        (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          A R H).toGeneratorOpenHilbertFieldScaleFamilyData).modeOfOS
        timeScale i mode z =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorModeOfOS
        i timeScale mode z := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases n with
  | zero => omega
  | succ q =>
    cases m with
    | zero => omega
    | succ r =>
      rfl

/-- The split-adapted spatial lift used by the rooted generator family:
first insert the fixed spatial basepoint, then pass to split-global
coordinates. -/
noncomputable def rootedGeneratorSplitSpatialLiftCLM
    (i : GeneratorIndex k) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
  (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
    (d := d) i).comp
      (section43SpatialBasepointLiftCLM d k
        (normalizedSpatialBasepointCutoff d).toSchwartz)

/-- The full split-adapted spatial Hermite series formed from a genuine
original-OS root-smeared open-field family. -/
noncomputable def rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  ∑' mode : ℕ,
    (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        D E).modeOfOS timeScale i mode z *
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F

/-- Compatibility presentation of the original-OS split-adapted spatial
Hermite series. -/
noncomputable def rootSmearedGeneratorOpenFieldSpatialHermiteSum
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
    D E i timeScale z F

/-- For any continuous spatial lift, the genuine original-OS rooted sum is
the generic original-OS open-field Hermite series for the split lift. -/
theorem
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_spatialHermiteScalarSumOfOS_of_lift
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        D E i timeScale z (lift χ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        D E).spatialHermiteScalarSumOfOS
          ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i).comp lift)
          i timeScale z χ := by
  rfl

/-- The split-adapted rooted sum for an arbitrary continuous spatial lift is
the generic open-field spatial Hermite series for the induced split lift. -/
theorem
    rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_spatialHermiteScalarSum_of_lift
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        D lgc E i timeScale z (lift χ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData
        D lgc E).spatialHermiteScalarSum lgc
          ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i).comp lift)
          i timeScale z χ := by
  rfl

/-- The canonical original-OS basepoint lift presents the rooted sum as its
generic split-global open-field Hermite series. -/
theorem
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_spatialHermiteScalarSumOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        D E i timeScale z
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyDataOfOS
        D E).spatialHermiteScalarSumOfOS
          (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale z χ := by
  rfl

/-- With the canonical basepoint lift, the split-adapted rooted sum is the
generic open-field spatial Hermite series for the split-global lift. -/
theorem
    rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_spatialHermiteScalarSum
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (E : GeneratorOpenHilbertFieldScaleFamilyData OS k)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        D lgc E i timeScale z
        (section43SpatialBasepointLiftCLM d k
          (normalizedSpatialBasepointCutoff d).toSchwartz χ) =
      (rootSmearedGeneratorOpenHilbertFieldScaleFamilyData
        D lgc E).spatialHermiteScalarSum
          lgc (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale z χ := by
  rfl

/-- Source-agreeing original-OS open-field families have the same full
root-smeared Hermite series on their actual common complex source germ. -/
theorem rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS_eq_on_commonComplex
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermDataOfOS
        P.toCommonPositiveRealModeAgreementDataOfOS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ C.domain i)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        D E.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z χ =
      rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        D F.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z χ := by
  apply tsum_congr
  intro mode
  rw [rootSmearedGeneratorModeOfOS_eq_on_commonComplex
    P D C i timeScale mode z hz]

/-- Source-agreeing open-field families have the same full root-smeared
split-adapted Hermite series on their common complex germ. -/
theorem rootSmearedGeneratorOpenFieldSpatialHermiteSum_eq_on_commonComplex
    {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
    (P :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
        E F)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (C :
      GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermData
        (P.toCommonPositiveRealModeAgreementData lgc))
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ C.domain i)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        D lgc E.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z χ =
      rootSmearedGeneratorOpenFieldSpatialHermiteSum
        D lgc F.toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z χ := by
  apply tsum_congr
  intro mode
  exact
    congrArg
      (fun value : ℂ =>
        value *
          GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
            (d := d) i mode χ)
      (rootSmearedGeneratorMode_eq_on_commonComplex
        P D lgc C i timeScale mode z hz)

/-- The genuine original-OS split-adapted series for the local rooted family
is exactly its original synchronized rooted Hermite sum. -/
theorem rootSmearedLocalGeneratorOpenFieldSpatialHermiteSumOfOS_eq
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSumOfOS
        H.toContinuousTranslationData
        (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          A R H).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
        i timeScale z F := by
  apply tsum_congr
  intro mode
  rw [rootSmearedLocalGeneratorOpenField_modeOfOS_eq]

/-- The generic split-adapted series for the local rooted family is exactly
the original rooted Hermite sum. -/
theorem rootSmearedLocalGeneratorOpenFieldSpatialHermiteSum_eq
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (z : OSIITimeGapSpace k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    rootSmearedGeneratorOpenFieldSpatialHermiteSum
        H.toContinuousTranslationData lgc
        (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          A R H).toGeneratorOpenHilbertFieldScaleFamilyData
        i timeScale z F =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z F :=
  rootSmearedLocalGeneratorOpenFieldSpatialHermiteSumOfOS_eq
    H i timeScale z F

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
