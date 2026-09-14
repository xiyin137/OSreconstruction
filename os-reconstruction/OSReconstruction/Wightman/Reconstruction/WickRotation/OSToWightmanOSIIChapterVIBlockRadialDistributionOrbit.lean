/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialChronologicalCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapRealEdge



















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]

/-- A finite chronological localization together with one common axis-pair
slope for all of its product carriers. -/
structure OSIIChronologicalCompactLocalizationContinuationData
    (d k : Nat) [NeZero d] [NeZero k]
    (K : Set (NPointDomain d (k + 1))) where
  localization : OSIIChronologicalCompactLocalizationData d k K
  T : Real
  hT : 1 < T
  axisPairOrdered :
    forall a : localization.index,
      forall b : osiiAxisPairIndex d,
        forall i j : Fin (k + 1), i < j ->
          ∀ y ∈ tsupport
              (((localization.carrier a).factors i : SchwartzSpacetime d) :
                SpacetimeDim d -> Complex),
            ∀ z ∈ tsupport
                (((localization.carrier a).factors j : SchwartzSpacetime d) :
                  SpacetimeDim d -> Complex),
              ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T b).matrix.mulVec z) 0

namespace OSIIChronologicalCompactLocalizationData

end OSIIChronologicalCompactLocalizationData

namespace OSIIChronologicalCompactLocalizationContinuationData

variable {K : Set (NPointDomain d (k + 1))}

/-- The sourcewise packet datum attached to one localization piece. -/
noncomputable def sourcewisePacketData
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (a : C.localization.index) :
    OSIIChronologicalSourcewisePacketData d (k + 1) k OS lgc :=
  (C.localization.carrier a).toSourcewisePacketDataAtSlope
    OS lgc C.T C.hT (C.axisPairOrdered a)

/-- Sum the canonical full-Schwartz distribution pairings of all finite
localization pieces. -/
noncomputable def pairing
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d (k + 1))
    (z : Fin k -> osiiAxisPairIndex d -> Complex) : Complex :=
  (@Finset.univ C.localization.index C.localization.indexFintype).sum fun a =>
    (C.sourcewisePacketData OS lgc a).schwartzDistributionFamily.pairing
      (C.localization.piece a f) z

/-- The coherent finite sum as a full-Schwartz distribution at each
multi-gap point, totalized by zero outside the honest first carrier. -/
noncomputable def distribution
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin k -> osiiAxisPairIndex d -> Complex) :
    SchwartzNPoint d (k + 1) →L[ℂ] ℂ :=
  letI : Fintype C.localization.index := C.localization.indexFintype
  if hz : z ∈ osiiAxisPairMultiGapLogDomain d k then
    ∑ a : C.localization.index,
      (((C.sourcewisePacketData OS lgc a).schwartzDistributionFamily
        ).distribution ⟨z, hz⟩).comp (C.localization.piece a)
  else
    0

/-- Applying the summed distribution is exactly the coherent scalar
pairing. -/
@[simp] theorem distribution_apply
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin k -> osiiAxisPairIndex d -> Complex)
    (f : SchwartzNPoint d (k + 1)) :
    C.distribution OS lgc z f = C.pairing OS lgc f z := by
  letI : Fintype C.localization.index := C.localization.indexFintype
  by_cases hz : z ∈ osiiAxisPairMultiGapLogDomain d k
  · simp [distribution, pairing,
      OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.pairing,
      hz]
  · simp [distribution, pairing,
      OSIIAxisPairMultiGapSourcewiseMZFamily.SchwartzDistributionFamily.pairing,
      hz]

/-- The finite sum of the localized zero-diagonal sources at a real
logarithmic point. -/
noncomputable def localizedTranslatedZeroSum
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1)) :
    ZeroDiagonalSchwartz d (k + 1) :=
  letI : Fintype C.localization.index := C.localization.indexFintype
  ∑ a : C.localization.index,
    (C.localization.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
      C.T C.hT (C.axisPairOrdered a) x (C.localization.piece a f)

/-- The coherent finite sum is weakly holomorphic against every full
Schwartz source. -/
theorem pairing_differentiableOn
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d (k + 1)) :
    DifferentiableOn Complex (C.pairing OS lgc f)
      (osiiAxisPairMultiGapLogDomain d k) := by
  apply DifferentiableOn.fun_sum
  intro a _ha
  exact
    (C.sourcewisePacketData OS lgc a
      ).schwartzDistributionFamily_differentiableOn_pairing
        (Nat.succ_pos k) (C.localization.piece a f)

/-- On a compact subset of the honest multi-gap carrier, the summed
distribution pairing is jointly continuous in the carrier point and in any
continuous full-Schwartz source family. -/
theorem continuous_pairing_joint_apply_on_compact
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Z : Set (Fin k -> osiiAxisPairIndex d -> Complex))
    (hZ_compact : IsCompact Z)
    (hZ_domain : Z ⊆ osiiAxisPairMultiGapLogDomain d k)
    {X : Type*} [TopologicalSpace X]
    (f : X -> SchwartzNPoint d (k + 1))
    (hf : Continuous f) :
    Continuous
      (fun p : Z × X => C.pairing OS lgc (f p.2) p.1.1) := by
  unfold pairing
  apply continuous_finset_sum
  intro a _ha
  let A := (C.sourcewisePacketData OS lgc a).schwartzDistributionFamily
  have hsource : Continuous
      (fun x : X => C.localization.piece a (f x)) :=
    (C.localization.piece a).continuous.comp hf
  have hdist :=
    A.continuous_distribution_joint_apply_on_compact_of_pos
      (Nat.succ_pos k) Z hZ_compact hZ_domain
      (fun x : X => C.localization.piece a (f x)) hsource
  apply hdist.congr
  intro p
  exact
    (A.pairing_of_mem (C.localization.piece a (f p.2))
      p.1.1 (hZ_domain p.1.2)).symm

/-- The compact-subtype formulation of joint continuity descends to the
ambient compact set. -/
theorem continuousOn_pairing_joint_on_compact
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Z : Set (Fin k -> osiiAxisPairIndex d -> Complex))
    (hZ_compact : IsCompact Z)
    (hZ_domain : Z ⊆ osiiAxisPairMultiGapLogDomain d k) :
    ContinuousOn
      (fun p :
          (Fin k -> osiiAxisPairIndex d -> Complex) ×
            SchwartzNPoint d (k + 1) =>
        C.pairing OS lgc p.2 p.1)
      (Z ×ˢ Set.univ) := by
  have hsubtype := C.continuous_pairing_joint_apply_on_compact
    OS lgc Z hZ_compact hZ_domain
    (fun f : SchwartzNPoint d (k + 1) => f) continuous_id
  exact continuousOn_joint_of_subtype
    (fun z : Z => fun f : SchwartzNPoint d (k + 1) =>
      C.pairing OS lgc f z.1)
    (fun z => fun f => C.pairing OS lgc f z)
    hsubtype.continuousOn (fun _ _ _ => rfl)

/-- The underlying full Schwartz source of the localized finite sum is the
chronological translate of the original compactly supported source. -/
theorem localizedTranslatedZeroSum_coe
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1))
    (hsupport : tsupport (f : NPointDomain d (k + 1) -> Complex) ⊆ K) :
    (C.localizedTranslatedZeroSum x f).1 =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f := by
  letI : Fintype C.localization.index := C.localization.indexFintype
  rw [localizedTranslatedZeroSum]
  change
    (∑ a : C.localization.index,
      (C.localization.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
        C.T C.hT (C.axisPairOrdered a) x
          (C.localization.piece a f)).1 =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f
  have hcoe :
      (∑ a : C.localization.index,
        (C.localization.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
          C.T C.hT (C.axisPairOrdered a) x
            (C.localization.piece a f)).1 =
        ∑ a : C.localization.index,
          ((C.localization.carrier a
            ).sourcewiseLocalizedTranslatedFullZeroCLM
              C.T C.hT (C.axisPairOrdered a) x
                (C.localization.piece a f)).1 := by
    delta ZeroDiagonalSchwartz
    exact
      Submodule.coe_sum
        (zeroDiagonalSubmodule d (k + 1))
        (fun a : C.localization.index =>
          (C.localization.carrier a
            ).sourcewiseLocalizedTranslatedFullZeroCLM
              C.T C.hT (C.axisPairOrdered a) x
                (C.localization.piece a f))
        Finset.univ
  rw [hcoe]
  change
    (∑ a : C.localization.index,
      (C.localization.carrier a).sourcewiseLocalizedTranslatedFullCLM
        C.T x (C.localization.piece a f)) =
      translateSchwartzConfiguration
        (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f
  calc
    (∑ a : C.localization.index,
        (C.localization.carrier a).sourcewiseLocalizedTranslatedFullCLM
          C.T x (C.localization.piece a f)) =
        ∑ a : C.localization.index,
          translateSchwartzConfigurationCLM
            (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i)
            (C.localization.piece a f) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact
        OSIIChapterV.sourcewiseLocalizedTranslatedFullCLM_eq_translate_of_fixed
          (C.localization.carrier a) C.T x (C.localization.piece a f)
          (C.localization.carrier_fix a f)
    _ = translateSchwartzConfigurationCLM
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i)
          (∑ a : C.localization.index, C.localization.piece a f) := by
      rw [map_sum
        (g := translateSchwartzConfigurationCLM
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i))
        (f := fun a : C.localization.index => C.localization.piece a f)
        (s := Finset.univ)]
    _ = translateSchwartzConfigurationCLM
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f := by
      exact congrArg
        (translateSchwartzConfigurationCLM
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i))
        (C.localization.sum_eq f hsupport).symm
    _ = translateSchwartzConfiguration
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f := rfl

/-- At every real logarithmic point, the coherent finite continuation is the
Schwinger functional of its named chronologically translated source sum. -/
theorem pairing_realEdge
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1)) :
    C.pairing OS lgc f
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      OS.S (k + 1) (C.localizedTranslatedZeroSum x f) := by
  letI : Fintype C.localization.index := C.localization.indexFintype
  let S := OsterwalderSchraderAxioms.schwingerCLM
    (d := d) OS (k + 1)
  have hterm : forall a : C.localization.index,
      (C.sourcewisePacketData OS lgc a
        ).schwartzDistributionFamily.pairing
          (C.localization.piece a f)
          (osiiAxisPairSimultaneousLogRealEmbed x) =
        S
          ((C.localization.carrier a
            ).sourcewiseLocalizedTranslatedFullZeroCLM
              C.T C.hT (C.axisPairOrdered a) x
              (C.localization.piece a f)) := by
    intro a
    let P := C.sourcewisePacketData OS lgc a
    let A := P.schwartzDistributionFamily
    rw [A.pairing_realEdge]
    have hdistribution := congrArg
      (fun L : SchwartzNPoint d (k + 1) →L[Complex] Complex =>
        L (C.localization.piece a f))
      ((C.localization.carrier a
        ).toSourcewisePacketDataAtSlope_realEdgeDistribution_eq_fullSchwinger
          OS lgc C.T C.hT (C.axisPairOrdered a) x)
    simpa [P, A, sourcewisePacketData, S] using hdistribution
  unfold pairing
  rw [Finset.sum_congr rfl (fun a _ha => hterm a)]
  rw [localizedTranslatedZeroSum]
  exact (map_sum S
    (fun a : C.localization.index =>
      (C.localization.carrier a).sourcewiseLocalizedTranslatedFullZeroCLM
        C.T C.hT (C.axisPairOrdered a) x (C.localization.piece a f))
    Finset.univ).symm

/-- On sources supported in the localization carrier, the finite localized
sum disappears from the real-edge formula: the coherent continuation is the
Schwinger functional of the single chronologically translated full source.
This is the support-local form used to compare independently chosen cutoff
extensions. -/
theorem pairing_realEdge_eq_schwinger_translate_of_support
    (C : OSIIChronologicalCompactLocalizationContinuationData d k K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (f : SchwartzNPoint d (k + 1))
    (hsupport : tsupport (f : NPointDomain d (k + 1) -> Complex) ⊆ K) :
    C.pairing OS lgc f
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (translateSchwartzConfiguration
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i)
          f)) := by
  rw [C.pairing_realEdge]
  let g := translateSchwartzConfiguration
    (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i) f
  have hcoe : (C.localizedTranslatedZeroSum x f).1 = g := by
    simpa only [g] using C.localizedTranslatedZeroSum_coe x f hsupport
  have hg : VanishesToInfiniteOrderOnCoincidence g := by
    rw [← hcoe]
    exact (C.localizedTranslatedZeroSum x f).2
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes g hg]
  exact congrArg (OS.S (k + 1)) (Subtype.ext hcoe)

/-- Support-local real edge for an arbitrary observed reduced Schwartz test.
This is the route-facing version of `pairing_realEdge_eq_schwinger_translate_of_support`:
its hypothesis is exactly the flat support condition used by equation `(6.6)`,
while the positive-basepoint lift and compact absolute carrier remain hidden
inside the proof. -/
theorem pairing_realEdge_reducedTestLift_eq_schwinger_translate_of_flatSupport
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (C : OSIIChronologicalCompactLocalizationContinuationData d k
      (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center))
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (phi : SchwartzNPoint d k)
    (hsupport :
      Function.support (flattenSchwartzNPoint (d := d) phi) ⊆
        Metric.closedBall center (rho / 4)) :
    C.pairing OS lgc
        (BHW.reducedTestLift k d
          (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi)
        (osiiAxisPairSimultaneousLogRealEmbed x) =
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (translateSchwartzConfiguration
          (fun i => -osiiAxisPairChronologicalPointTranslation C.T x i)
          (BHW.reducedTestLift k d
            (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi))) := by
  exact C.pairing_realEdge_eq_schwinger_translate_of_support
    OS lgc x _
      (osiiStep4PositiveReducedTestLift_tsupport_subset_commonCarrier
        d k rho center phi hsupport)

end OSIIChronologicalCompactLocalizationContinuationData

/-- Independent chronological prefix translations shift exactly the reduced
center of the positive-basepoint radial source. -/
theorem
    translateConfiguration_positiveLiftedCenteredPartialKernel_axisPairGaps
    (d k : Nat) [NeZero d] [NeZero k]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    translateSchwartzConfiguration
        (fun j => -osiiAxisPairChronologicalPointTranslation T x j)
        (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho center y y') =
      osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho
          (center + osiiStep4AxisPairGapTranslationFlat d T x) y y' := by
  ext u
  rw [translateSchwartzConfiguration_apply]
  simp only [
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource,
    BHW.reducedTestLift_apply]
  have hzero :
      osiiAxisPairChronologicalPointTranslation T x
          (0 : Fin (k + 1)) = 0 :=
    osiiAxisPairChronologicalPointTranslation_zero T x
  have hred :=
    reducedDiffMapReal_sub_axisPairChronologicalPointTranslation d k T x u
  have hu :
      u + (fun j => -osiiAxisPairChronologicalPointTranslation T x j) =
        fun j => u j - osiiAxisPairChronologicalPointTranslation T x j := by
    ext j mu
    simp [sub_eq_add_neg]
  rw [hu, hred]
  simp only [hzero, sub_zero]
  congr 1
  rw [
    osiiStep4CenteredPartialConvolutionKernelFullSource_apply,
    osiiStep4CenteredPartialConvolutionKernelFullSource_apply]
  congr 2
  funext a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  have hi : (finProdFinEquiv (i, mu)).divNat = i :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, mu))
  have hmu : (finProdFinEquiv (i, mu)).modNat = mu :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, mu))
  apply Complex.ext
  · simp only [osiiStep4ComplexOfRealImag_re, Pi.sub_apply, Pi.add_apply]
    rw [finProdFinEquiv.symm_apply_apply]
    simp [osiiStep4AxisPairGapTranslationFlat]
    ring
  · simp

end OSReconstruction
