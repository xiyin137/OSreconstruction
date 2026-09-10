/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds


















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

/-- Exact physical input needed to promote ordered moving packets from a
fixed compact product source to a sourcewise multi-gap MZ family.

The common slope and rotated-order field are deliberately outside the source
tuple.  This prevents source-dependent chart domains from being hidden in the
sourcewise continuation. -/
structure OSIIChronologicalSourcewisePacketData
    (d n k : ℕ) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  T : ℝ
  hT : 1 < T
  factors :
    (Fin n → SchwartzSpacetime d) →
      OSIIChronologicalCompactFactors d k
  axisPairOrdered :
    ∀ (fs : Fin n → SchwartzSpacetime d)
      (a : osiiAxisPairIndex d)
      (i j : Fin (k + 1)), i < j →
        ∀ y ∈ tsupport
            (((factors fs).factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              (((factors fs).factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T a).matrix.mulVec z) 0
  realEdge :
    (Fin k → osiiAxisPairIndex d → ℝ) →
      ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ
  packetRealEdge_eq :
    ∀ (fs : Fin n → SchwartzSpacetime d)
      (x : Fin k → osiiAxisPairIndex d → ℝ),
      ((factors fs).multiGapPacketFamily
        OS lgc T hT (axisPairOrdered fs)).realEdge x =
          realEdge x fs

namespace OSIIChronologicalCompactFactors

/-- Localize each source slot by one fixed compact chronological carrier. -/
noncomputable def sourcewiseLocalizedFactors
    (F : OSIIChronologicalCompactFactors d k)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    OSIIChronologicalCompactFactors d k where
  factors := fun i =>
    SchwartzMap.smulLeftCLM ℂ (F.factors i) (fs i)
  factor_compact := by
    intro i
    refine (F.factor_compact i).mono' ?_
    intro y hy
    have hyts :
        y ∈ tsupport
          ((SchwartzMap.smulLeftCLM ℂ (F.factors i) (fs i) :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
      subset_closure hy
    exact
      (SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((F.factors i : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        (f := fs i) hyts).2
  ordered_support := by
    intro i j hij y hy z hz
    exact F.ordered_support i j hij y
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((F.factors i : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        (f := fs i) hy).2)
      z
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((F.factors j : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        (f := fs j) hz).2)

/-- A slope valid on the fixed carrier remains valid after arbitrary
sourcewise cutoff localization. -/
theorem sourcewiseLocalizedFactors_axisPairOrdered
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
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
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ∀ a : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            (((F.sourcewiseLocalizedFactors fs).factors i :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              (((F.sourcewiseLocalizedFactors fs).factors j :
                SchwartzSpacetime d) : SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T a).matrix.mulVec z) 0 := by
  intro a i j hij y hy z hz
  exact hordered a i j hij y
    ((SchwartzMap.tsupport_smulLeftCLM_subset
      (g := ((F.factors i : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ))
      (f := fs i) hy).2)
    z
    ((SchwartzMap.tsupport_smulLeftCLM_subset
      (g := ((F.factors j : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ))
      (f := fs j) hz).2)

/-- Fixed-slot localization followed by its full chronological translation. -/
noncomputable def sourcewiseLocalizedTranslatedFactorCLM
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin (k + 1)) :
    SchwartzSpacetime d →L[ℂ] SchwartzSpacetime d :=
  (SCV.translateSchwartzCLM
      (-osiiAxisPairChronologicalPointTranslation T x i)).comp
    (SchwartzMap.smulLeftCLM ℂ (F.factors i))

/-- The localized, fully translated product tensor as a continuous
multilinear Schwartz-valued map. -/
noncomputable def sourcewiseLocalizedTranslatedProductCMM
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (k + 1) => SchwartzSpacetime d)
      (SchwartzNPoint d (k + 1)) :=
  (SchwartzMap.productTensorMLM (E := SpacetimeDim d) (k + 1)
    ).compContinuousLinearMap
      (F.sourcewiseLocalizedTranslatedFactorCLM T x)

@[simp]
theorem sourcewiseLocalizedTranslatedProductCMM_apply
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    F.sourcewiseLocalizedTranslatedProductCMM T x fs =
      SchwartzMap.productTensor
        (osiiAxisPairChronologicalTranslatedFactors T x
          (F.sourcewiseLocalizedFactors fs).factors) := by
  rfl

/-- The localized translated product tensor, with its genuine
zero-diagonal proof retained in a continuous multilinear map. -/
noncomputable def sourcewiseLocalizedTranslatedZeroCMM
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
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (k + 1) => SchwartzSpacetime d)
      (ZeroDiagonalSchwartz d (k + 1)) :=
  let M := F.sourcewiseLocalizedTranslatedProductCMM T x
  { toMultilinearMap :=
      { toFun := fun fs =>
          ⟨M fs,
            (F.sourcewiseLocalizedFactors fs
              ).chronologicalTranslated_productTensor_vanishes
                T hT
                (F.sourcewiseLocalizedFactors_axisPairOrdered
                  T hordered fs) x⟩
        map_update_add' := by
          intro hdec fs i f g
          letI := hdec
          apply Subtype.ext
          exact M.map_update_add fs i f g
        map_update_smul' := by
          intro hdec fs i c f
          letI := hdec
          apply Subtype.ext
          exact M.map_update_smul fs i c f }
    cont := M.cont.subtype_mk _ }

/-- Continuous multilinear Schwinger real edge for one fixed chronological
cutoff carrier and slope. -/
noncomputable def sourcewiseLocalizedRealEdge
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
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (k + 1) => SchwartzSpacetime d) ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (k + 1)
    ).compContinuousMultilinearMap
      (F.sourcewiseLocalizedTranslatedZeroCMM T hT hordered x)

@[simp]
theorem sourcewiseLocalizedRealEdge_apply
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
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    F.sourcewiseLocalizedRealEdge OS T hT hordered x fs =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x
            (F.sourcewiseLocalizedFactors fs).factors))) := by
  let hvanish :=
    (F.sourcewiseLocalizedFactors fs
      ).chronologicalTranslated_productTensor_vanishes
        T hT
        (F.sourcewiseLocalizedFactors_axisPairOrdered T hordered fs) x
  rw [sourcewiseLocalizedRealEdge]
  change
    OS.S (k + 1)
      (⟨SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x
            (F.sourcewiseLocalizedFactors fs).factors),
        hvanish⟩ : ZeroDiagonalSchwartz d (k + 1)) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x
            (F.sourcewiseLocalizedFactors fs).factors)))
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes _ hvanish]

/-- A fixed compact chronological carrier supplies the existing sourcewise
multi-gap MZ package under the original OS axioms alone. Its real edge is a
genuine continuous multilinear zero-diagonal Schwinger functional. -/
noncomputable def toSourcewiseCoshGrowthDataAtSlopeOfOS
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
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIAxisPairMultiGapSourcewiseCoshGrowthData d (k + 1) k where
  flatCross := fun fs =>
    (F.sourcewiseLocalizedFactors fs).multiGapFlatCrossOfOS
      OS T hT (F.sourcewiseLocalizedFactors_axisPairOrdered T hordered fs)
  realEdge := F.sourcewiseLocalizedRealEdge OS T hT hordered
  flatCross_realEdge := by
    intro fs x
    simpa [OSIIChronologicalCompactFactors.multiGapFlatCrossOfOS,
      OSIIAxisPairMultiGapFlatCrossData.ofCompensatedFrozenDependentOfOS] using
      (F.sourcewiseLocalizedRealEdge_apply
        OS T hT hordered x fs).symm
  growth := fun fs =>
    (F.sourcewiseLocalizedFactors fs
      ).multiGapFlatCrossOfOS_coshGrowthDataAtUniformSlopeRate
        OS T hT
        (F.sourcewiseLocalizedFactors_axisPairOrdered T hordered fs)

/-- Every localized Schwartz source has the same fixed-arity cosh rate,
independent of both the source tuple and the auxiliary packet slope. -/
theorem toSourcewiseCoshGrowthDataAtSlopeOfOS_rate
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
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    ((F.toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS T hT hordered).growth fs).rate =
        osiiOriginalOSUniformPacketCoshRate OS k := by
  rfl

/-- The genuine original-OS sourcewise continuation has the exact common-rate
record consumed by the existing source-parametric MZ machinery. -/
noncomputable def toSourcewiseCoshGrowthDataAtSlopeOfOS_commonRate
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
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
      OS T hT hordered).CommonRate where
  rate := osiiOriginalOSUniformPacketCoshRate OS k
  growth_rate :=
    F.toSourcewiseCoshGrowthDataAtSlopeOfOS_rate OS T hT hordered

/-- Every genuine original-OS sourcewise logarithmic point determines one
unique continuous distribution on the complete Schwartz source space. -/
theorem existsUnique_schwartzDistributionAtOfOS
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ w ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec w) 0)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    ∃! W : SchwartzNPoint d (k + 1) →L[ℂ] ℂ,
      ∀ fs : Fin (k + 1) → SchwartzSpacetime d,
        W (SchwartzMap.productTensor fs) =
          (F.toSourcewiseCoshGrowthDataAtSlopeOfOS
            OS T hT hordered).toMZFamily.toFun fs z :=
  (F.toSourcewiseCoshGrowthDataAtSlopeOfOS_commonRate
    OS T hT hordered).existsUnique_schwartzDistributionAt z hz

/-- A fixed chronological cutoff carrier and a common valid slope supply the
complete sourcewise packet handoff. -/
noncomputable def toSourcewisePacketDataAtSlope
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
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIChronologicalSourcewisePacketData d (k + 1) k OS lgc where
  T := T
  hT := hT
  factors := F.sourcewiseLocalizedFactors
  axisPairOrdered :=
    F.sourcewiseLocalizedFactors_axisPairOrdered T hordered
  realEdge := F.sourcewiseLocalizedRealEdge OS T hT hordered
  packetRealEdge_eq := by
    intro fs x
    exact (F.sourcewiseLocalizedRealEdge_apply
      OS T hT hordered x fs).symm

end OSIIChronologicalCompactFactors

namespace OSIIChronologicalSourcewisePacketData

/-- Physical dependent packet family associated to one source tuple. -/
noncomputable def packetFamily
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc)
    (fs : Fin n → SchwartzSpacetime d) :
    OSIIAxisPairMultiGapSemigroupPacketFamily d k D.T OS lgc :=
  (D.factors fs).multiGapPacketFamily
    OS lgc D.T D.hT (D.axisPairOrdered fs)

/-- Interleaved flat cross obtained from the physical packet family. -/
noncomputable def flatCross
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc)
    (fs : Fin n → SchwartzSpacetime d) :
    OSIIAxisPairMultiGapFlatCrossData d k :=
  (D.packetFamily fs).toFlatCrossData
    ((D.factors fs).continuousOn_multiGapPacketFamily_branch
      OS lgc D.T D.hT (D.axisPairOrdered fs))

/-- Sourcewise physical packet data automatically supplies the cosh-growth
flat-cross package consumed by multi-gap MZ. -/
noncomputable def toSourcewiseCoshGrowthData
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc) :
    OSIIAxisPairMultiGapSourcewiseCoshGrowthData d n k where
  flatCross := D.flatCross
  realEdge := D.realEdge
  flatCross_realEdge := by
    intro fs x
    simpa [flatCross, packetFamily,
      OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData] using
      D.packetRealEdge_eq fs x
  growth := fun fs =>
    (D.factors fs).multiGapPacketFamily_coshGrowthDataAtOriginalOSUniformSlopeRate
      OS lgc D.T D.hT (D.axisPairOrdered fs)

/-- The damping rate used by the sourcewise family is definitionally common
to every source tuple. -/
@[simp]
theorem toSourcewiseCoshGrowthData_rate
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc)
    (fs : Fin n → SchwartzSpacetime d) :
    (D.toSourcewiseCoshGrowthData.growth fs).rate =
      osiiOriginalOSUniformPacketCoshRate OS k :=
  rfl

/-- The chronological packet package carries the common damping-rate datum
needed to make all canonical Gaussian approximants jointly continuous in the
Schwartz sources. -/
noncomputable def commonRate
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc) :
    D.toSourcewiseCoshGrowthData.CommonRate where
  rate := osiiOriginalOSUniformPacketCoshRate OS k
  growth_rate := D.toSourcewiseCoshGrowthData_rate

/-- Every fixed compact chronological carrier now yields the unique full
Schwartz distribution at every point of the first global Chapter V.1
multi-gap carrier. -/
theorem existsUnique_schwartzDistributionAt
    (D : OSIIChronologicalSourcewisePacketData d n k OS lgc)
    (z : Fin k → osiiAxisPairIndex d → ℂ)
    (hz : z ∈ osiiAxisPairMultiGapLogDomain d k) :
    ∃! W : SchwartzNPoint d n →L[ℂ] ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d,
        W (SchwartzMap.productTensor fs) =
          D.toSourcewiseCoshGrowthData.toMZFamily.toFun fs z :=
  D.commonRate.existsUnique_schwartzDistributionAt z hz

end OSIIChronologicalSourcewisePacketData

end OSReconstruction
