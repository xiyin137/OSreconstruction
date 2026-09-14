/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIConfigurationTranslation
import OSReconstruction.Wightman.Reconstruction.DenseCLM
















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

omit [NeZero d] [NeZero k] in
private theorem productTensor_cutoff_productTensor
    (χs fs : Fin n → SchwartzSpacetime d) :
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs)
        (SchwartzMap.productTensor fs) =
      SchwartzMap.productTensor
        (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) := by
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((SchwartzMap.productTensor χs : SchwartzNPoint d n) :
      NPointDomain d n → ℂ))
    (SchwartzMap.productTensor χs).hasTemperateGrowth
    (SchwartzMap.productTensor fs) y]
  rw [SchwartzMap.productTensor_apply]
  have hfactor :
      ∀ i : Fin n,
        (SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) (y i) =
          (χs i) (y i) * (fs i) (y i) := by
    intro i
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
      (χs i).hasTemperateGrowth (fs i) (y i)]
    simp [smul_eq_mul]
  simp [SchwartzMap.productTensor_apply, hfactor, smul_eq_mul,
    Finset.prod_mul_distrib]

omit [NeZero d] in
private theorem vanishes_smulLeft_of_hasTemperateGrowth
    {ψ : NPointDomain d n → ℂ} {f : SchwartzNPoint d n}
    (hψ : ψ.HasTemperateGrowth)
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro m y hy
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun z : NPointDomain d n => ψ z * f z := by
    funext z
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply hψ f z)
  have hle :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℂ)
      hψ.1 (f.smooth ⊤) y
      (n := m) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
          ‖iteratedFDeriv ℝ (m - i)
            (f : NPointDomain d n → ℂ) y‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (m - i)
            (f : NPointDomain d n → ℂ) y = 0 :=
      hf (m - i) y hy
    simp [hfi]
  have hzero_norm :
      ‖iteratedFDeriv ℝ m
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) y‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      exact hle.trans_eq hsum_zero
    · exact norm_nonneg _
  exact norm_eq_zero.mp hzero_norm

namespace OSIIChronologicalCompactFactors

/-- The fixed chronological carrier after all independent point
translations. -/
noncomputable def chronologicalTranslatedCarrier
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d (k + 1) :=
  SchwartzMap.productTensor
    (osiiAxisPairChronologicalTranslatedFactors T x F.factors)

/-- Localize one arbitrary full Schwartz source by the translated
chronological carrier. -/
noncomputable def sourcewiseLocalizedTranslatedFullCLM
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d (k + 1) →L[ℂ] SchwartzNPoint d (k + 1) :=
  (SchwartzMap.smulLeftCLM ℂ
    (F.chronologicalTranslatedCarrier T x)).comp
      (translateSchwartzConfigurationCLM
        (fun i => -osiiAxisPairChronologicalPointTranslation T x i))

@[simp] theorem sourcewiseLocalizedTranslatedFullCLM_productTensor
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    F.sourcewiseLocalizedTranslatedFullCLM T x
        (SchwartzMap.productTensor fs) =
      F.sourcewiseLocalizedTranslatedProductCMM T x fs := by
  rw [sourcewiseLocalizedTranslatedFullCLM,
    ContinuousLinearMap.comp_apply,
    translateSchwartzConfigurationCLM_apply,
    translateSchwartzConfiguration_productTensor]
  unfold chronologicalTranslatedCarrier
  rw [productTensor_cutoff_productTensor]
  rw [F.sourcewiseLocalizedTranslatedProductCMM_apply]
  apply congrArg SchwartzMap.productTensor
  funext i
  ext y
  simp only [osiiAxisPairChronologicalTranslatedFactors,
    sourcewiseLocalizedFactors, SCV.translateSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SCV.translateSchwartz
      (-osiiAxisPairChronologicalPointTranslation T x i)
      (F.factors i)).hasTemperateGrowth]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (F.factors i).hasTemperateGrowth]
  simp [smul_eq_mul, SCV.translateSchwartz_apply, mul_comm]

/-- Localization by the translated chronological carrier sends every full
Schwartz source to the zero-diagonal OS test space. -/
theorem sourcewiseLocalizedTranslatedFullCLM_vanishes
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (f : SchwartzNPoint d (k + 1)) :
    VanishesToInfiniteOrderOnCoincidence
      (F.sourcewiseLocalizedTranslatedFullCLM T x f) := by
  let carrier := F.chronologicalTranslatedCarrier T x
  let moved :=
    translateSchwartzConfigurationCLM
      (fun i => -osiiAxisPairChronologicalPointTranslation T x i) f
  have hcarrier : VanishesToInfiniteOrderOnCoincidence carrier :=
    F.chronologicalTranslated_productTensor_vanishes T hT hordered x
  have hswap :
      F.sourcewiseLocalizedTranslatedFullCLM T x f =
        SchwartzMap.smulLeftCLM ℂ moved carrier := by
    rw [sourcewiseLocalizedTranslatedFullCLM,
      ContinuousLinearMap.comp_apply]
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply carrier.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply moved.hasTemperateGrowth]
    exact mul_comm _ _
  rw [hswap]
  exact vanishes_smulLeft_of_hasTemperateGrowth
    moved.hasTemperateGrowth hcarrier

/-- The explicit full-source localization as a continuous map into the
zero-diagonal OS test space. -/
noncomputable def sourcewiseLocalizedTranslatedFullZeroCLM
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    SchwartzNPoint d (k + 1) →L[ℂ]
      ZeroDiagonalSchwartz d (k + 1) :=
  (F.sourcewiseLocalizedTranslatedFullCLM T x).codRestrict
    (zeroDiagonalSubmodule d (k + 1))
    (F.sourcewiseLocalizedTranslatedFullCLM_vanishes
      T hT hordered x)

/-- The original-OS nuclear real edge is the explicit localized Schwinger
functional on every full Schwartz source; no growth hypothesis is needed. -/
theorem
    toSourcewiseCoshGrowthDataAtSlopeOfOS_realEdgeDistribution_eq_fullSchwinger
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS T hT hordered).toMZFamily.realEdgeDistribution x =
      (OsterwalderSchraderAxioms.schwingerCLM
        (d := d) OS (k + 1)).comp
        (F.sourcewiseLocalizedTranslatedFullZeroCLM
          T hT hordered x) := by
  apply clm_eq_of_eq_on_productTensor d (k + 1)
  intro fs
  rw [OSIIAxisPairMultiGapSourcewiseMZFamily.realEdgeDistribution_productTensor]
  change
    F.sourcewiseLocalizedRealEdge OS T hT hordered x fs =
      OS.S (k + 1)
        (F.sourcewiseLocalizedTranslatedFullZeroCLM
          T hT hordered x (SchwartzMap.productTensor fs))
  rw [F.sourcewiseLocalizedRealEdge_apply]
  apply congrArg (OS.S (k + 1))
  apply Subtype.ext
  let hvanish :=
    (F.sourcewiseLocalizedFactors fs
      ).chronologicalTranslated_productTensor_vanishes
        T hT
        (F.sourcewiseLocalizedFactors_axisPairOrdered T hordered fs) x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hvanish]
  exact (F.sourcewiseLocalizedTranslatedFullCLM_productTensor
    T x fs).symm

/-- The nuclear real-edge distribution is the explicit full-source localized
Schwinger functional. The legacy growth argument is retained only for the
older packet-family interface. -/
theorem toSourcewisePacketDataAtSlope_realEdgeDistribution_eq_fullSchwinger
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    (F.toSourcewisePacketDataAtSlope OS lgc T hT hordered
      ).toSourcewiseCoshGrowthData.toMZFamily.realEdgeDistribution x =
      (OsterwalderSchraderAxioms.schwingerCLM
        (d := d) OS (k + 1)).comp
        (F.sourcewiseLocalizedTranslatedFullZeroCLM
          T hT hordered x) := by
  calc
    _ = (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
          OS T hT hordered).toMZFamily.realEdgeDistribution x := by
      apply clm_eq_of_eq_on_productTensor d (k + 1)
      intro fs
      rw [OSIIAxisPairMultiGapSourcewiseMZFamily.realEdgeDistribution_productTensor,
        OSIIAxisPairMultiGapSourcewiseMZFamily.realEdgeDistribution_productTensor]
      rfl
    _ = _ :=
      F.toSourcewiseCoshGrowthDataAtSlopeOfOS_realEdgeDistribution_eq_fullSchwinger
        OS T hT hordered x

end OSIIChronologicalCompactFactors

end OSReconstruction
