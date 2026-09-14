import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapContinuity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapGrowthMZ

/-!
# OS II Chapter VI: Multi-gap radial packet growth

The frozen radial packet family has polynomial growth in its spectator
configuration translations. A common chronological translation majorant turns
those polynomial estimates into one source-independent cosh-growth rate across
all gaps and signed directions. The resulting growth record supplies the
global multi-gap Malgrange-Zerner continuation of the fixed-radius BVT.
-/

noncomputable section

open Matrix Set
open scoped BigOperators Classical

namespace OSReconstruction

theorem norm_axisPairChronologicalPointTranslation_le_card_mul
    {d r : Nat} [NeZero d]
    (T : Real)
    (x : Fin r -> osiiAxisPairIndex d -> Real)
    (M : Real) (hM : 0 <= M)
    (hgap : forall i : Fin r,
      norm (osiiAxisPairChronologicalGapTranslation T x i) <= M)
    (j : Fin (r + 1)) :
    norm (osiiAxisPairChronologicalPointTranslation T x j) <=
      (r : Real) * M := by
  rw [osiiAxisPairChronologicalPointTranslation]
  calc
    norm (∑ i : Fin r,
        if i.val < j.val then
          osiiAxisPairChronologicalGapTranslation T x i
        else 0) <=
      ∑ i : Fin r,
        norm (if i.val < j.val then
          osiiAxisPairChronologicalGapTranslation T x i
        else 0) := norm_sum_le _ _
    _ <= ∑ _i : Fin r, M := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hij : i.val < j.val
      · simpa [hij] using hgap i
      · simp [hij, hM]
    _ = (r : Real) * M := by simp

theorem norm_multiGapLeftSpectatorGap_le_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (j : Fin i.val) :
    norm (osiiAxisPairChronologicalGapTranslation T
        (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) <=
      osiiAxisPairChronologicalTranslationMajorant T x := by
  let b := osiiStep4MultiGapSplitBlockEquiv i
    (osiiStep4ReversedBeforeBlockIndex
      i.val (osiiStep4MultiGapAfterCount i) j)
  have hparity :
      (osiiStep4EuclideanParityMatrix d).mulVec
          (osiiAxisPairChronologicalGapTranslation T
            (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) =
        osiiAxisPairChronologicalGapTranslation T x b := by
    rw [euclideanParity_mulVec_axisPairGapTranslation]
    unfold osiiAxisPairChronologicalGapTranslation
    apply Finset.sum_congr rfl
    intro a _ha
    simp [osiiStep4MultiGapLeftSpectatorLogCoordinates, b,
      osiiAxisPairPositiveCoefficients,
      osiiAxisPairOpposite_opposite]
  calc
    norm (osiiAxisPairChronologicalGapTranslation T
        (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) =
      norm ((osiiStep4EuclideanParityMatrix d).mulVec
        (osiiAxisPairChronologicalGapTranslation T
          (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j)) :=
        (norm_parity_eq d _).symm
    _ = norm (osiiAxisPairChronologicalGapTranslation T x b) :=
      congrArg norm hparity
    _ <= osiiAxisPairChronologicalTranslationMajorant T x :=
      norm_osiiAxisPairChronologicalGapTranslation_le_majorant T x b

theorem norm_multiGapRightSpectatorGap_le_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) (j : Fin (osiiStep4MultiGapAfterCount i)) :
    norm (osiiAxisPairChronologicalGapTranslation T
        (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) <=
      osiiAxisPairChronologicalTranslationMajorant T x := by
  let b := osiiStep4MultiGapSplitBlockEquiv i
    (osiiStep4AfterBlockIndex
      i.val (osiiStep4MultiGapAfterCount i) j)
  have hgap :
      osiiAxisPairChronologicalGapTranslation T
          (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j =
        osiiAxisPairChronologicalGapTranslation T x b := by
    unfold osiiAxisPairChronologicalGapTranslation
    apply Finset.sum_congr rfl
    intro a _ha
    rfl
  rw [hgap]
  exact norm_osiiAxisPairChronologicalGapTranslation_le_majorant T x b

theorem norm_multiGapLeftSpectatorConfiguration_le_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    norm (fun j => -osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) <=
      (k : Real) * osiiAxisPairChronologicalTranslationMajorant T x := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  have hM : 0 <= M :=
    osiiAxisPairChronologicalTranslationMajorant_nonneg T x
  have hlocal : forall j : Fin (i.val + 1),
      norm (osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) <=
        (i.val : Real) * M :=
    norm_axisPairChronologicalPointTranslation_le_card_mul T _ M hM
      (norm_multiGapLeftSpectatorGap_le_majorant d k T x i)
  rw [pi_norm_le_iff_of_nonneg]
  · intro j
    rw [norm_neg]
    exact (hlocal j).trans (by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast (Nat.le_of_lt i.isLt))
  · positivity

theorem norm_multiGapRightSpectatorConfiguration_le_majorant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    norm (fun j => -osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) <=
      (k : Real) * osiiAxisPairChronologicalTranslationMajorant T x := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  have hM : 0 <= M :=
    osiiAxisPairChronologicalTranslationMajorant_nonneg T x
  have hlocal : forall j : Fin (osiiStep4MultiGapAfterCount i + 1),
      norm (osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) <=
        (osiiStep4MultiGapAfterCount i : Real) * M :=
    norm_axisPairChronologicalPointTranslation_le_card_mul T _ M hM
      (norm_multiGapRightSpectatorGap_le_majorant d k T x i)
  rw [pi_norm_le_iff_of_nonneg]
  · intro j
    rw [norm_neg]
    exact (hlocal j).trans (by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast (Nat.sub_le k (i.val + 1)))
  · positivity

def osiiStep4MultiGapSpectatorConfigurationCoshConstant
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) : Real :=
  1 + (k : Real) *
    osiiAxisPairChronologicalTranslationMajorantConstant
      (d := d) (k := k) T

theorem osiiStep4MultiGapSpectatorConfigurationCoshConstant_pos
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) :
    0 < osiiStep4MultiGapSpectatorConfigurationCoshConstant d k T := by
  dsimp [osiiStep4MultiGapSpectatorConfigurationCoshConstant]
  have hK := osiiAxisPairChronologicalTranslationMajorantConstant_nonneg
    (d := d) (k := k) T
  have hk : 0 <= (k : Real) := by positivity
  nlinarith [mul_nonneg hk hK]

theorem one_le_multiGapGaugeExp
    {d k : Nat} [NeZero d] [NeZero k]
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    1 <= Real.exp (4 *
      SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  apply Real.one_le_exp
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _i _hi => (Real.cosh_pos _).le)

theorem one_add_norm_multiGapLeftSpectatorConfiguration_le_cosh
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    1 + norm (fun j => -osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) <=
      osiiStep4MultiGapSpectatorConfigurationCoshConstant d k T *
        Real.exp (4 *
          SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K := osiiAxisPairChronologicalTranslationMajorantConstant
    (d := d) (k := k) T
  let E := Real.exp (4 *
    SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x))
  have hconfig :=
    norm_multiGapLeftSpectatorConfiguration_le_majorant d k T x i
  have hM : M <= K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_cosh
        (d := d) (k := k) T x
  have hE : 1 <= E := by
    simpa [E] using one_le_multiGapGaugeExp x
  have hk : 0 <= (k : Real) := by positivity
  change 1 + norm (fun j => -osiiAxisPairChronologicalPointTranslation T
      (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j) <=
    (1 + (k : Real) * K) * E
  dsimp [M, K, E] at hconfig hM hE ⊢
  nlinarith

theorem one_add_norm_multiGapRightSpectatorConfiguration_le_cosh
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    1 + norm (fun j => -osiiAxisPairChronologicalPointTranslation T
        (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) <=
      osiiStep4MultiGapSpectatorConfigurationCoshConstant d k T *
        Real.exp (4 *
          SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K := osiiAxisPairChronologicalTranslationMajorantConstant
    (d := d) (k := k) T
  let E := Real.exp (4 *
    SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x))
  have hconfig :=
    norm_multiGapRightSpectatorConfiguration_le_majorant d k T x i
  have hM : M <= K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_cosh
        (d := d) (k := k) T x
  have hE : 1 <= E := by
    simpa [E] using one_le_multiGapGaugeExp x
  have hk : 0 <= (k : Real) := by positivity
  change 1 + norm (fun j => -osiiAxisPairChronologicalPointTranslation T
      (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j) <=
    (1 + (k : Real) * K) * E
  dsimp [M, K, E] at hconfig hM hE ⊢
  nlinarith

def osiiStep4MultiGapLeftSpectatorConfiguration
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) : NPointDomain d (i.val + 1) :=
  fun j => -osiiAxisPairChronologicalPointTranslation T
    (osiiStep4MultiGapLeftSpectatorLogCoordinates d k x i) j

def osiiStep4MultiGapRightSpectatorConfiguration
    (d k : Nat) [NeZero d]
    (T : Real)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (i : Fin k) :
    NPointDomain d (osiiStep4MultiGapAfterCount i + 1) :=
  fun j => -osiiAxisPairChronologicalPointTranslation T
    (osiiStep4MultiGapRightSpectatorLogCoordinates d k x i) j

noncomputable def osiiStep4MultiGapLeftPositiveCLM
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (q.1.val + 1) →L[Complex]
      SchwartzNPoint d (q.1.val + 1) :=
  schwartzNPointTimeReflectCLM.comp
    ((osiiEuclideanRotateSchwartzCLM
      (osiiAxisPairRotationData T q.2).matrix
      (osiiAxisPairRotationData T q.2).orthogonal).comp
        schwartzNPointTimeReflectCLM)

noncomputable def osiiStep4MultiGapRightPositiveCLM
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (q : osiiAxisPairMultiGapIndex d k) :
    SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1) →L[Complex]
      SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1) :=
  osiiEuclideanRotateSchwartzCLM
    (osiiAxisPairRotationData T q.2).matrix
    (osiiAxisPairRotationData T q.2).orthogonal

@[simp] theorem osiiStep4MultiGapLeftPositiveCLM_apply
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (q.1.val + 1)) :
    osiiStep4MultiGapLeftPositiveCLM T q f =
      (osiiEuclideanRotateSchwartz
        (osiiAxisPairRotationData T q.2).matrix
        (osiiAxisPairRotationData T q.2).orthogonal
        f.timeReflect).timeReflect := by
  simp [osiiStep4MultiGapLeftPositiveCLM]

@[simp] theorem osiiStep4MultiGapRightPositiveCLM_apply
    {d k : Nat} [NeZero d] [NeZero k]
    (T : Real) (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1)) :
    osiiStep4MultiGapRightPositiveCLM T q f =
      osiiEuclideanRotateSchwartz
        (osiiAxisPairRotationData T q.2).matrix
        (osiiAxisPairRotationData T q.2).orthogonal f := by
  simp [osiiStep4MultiGapRightPositiveCLM]

noncomputable def osiiStep4MultiGapLeftVectorGrowthDegree
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) (q : osiiAxisPairMultiGapIndex d k) : Nat :=
  Classical.choose
    (exists_uniformDegree_osiiPositiveTimeSingleVectorCLM_norm_sq_translate_bound
      OS (osiiStep4MultiGapLeftPositiveCLM T q))

theorem osiiStep4MultiGapLeftVectorGrowthDegree_spec
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (q.1.val + 1)) :
    exists C : Real, 0 <= C ∧
      forall a : NPointDomain d (q.1.val + 1),
        forall hpositive :
          tsupport
              (osiiStep4MultiGapLeftPositiveCLM T q
                  (translateSchwartzConfiguration a f) :
                NPointDomain d (q.1.val + 1) -> Complex) <=
            OrderedPositiveTimeRegion d (q.1.val + 1),
        norm (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
          ⟨osiiStep4MultiGapLeftPositiveCLM T q
              (translateSchwartzConfiguration a f), hpositive⟩) ^ 2 <=
          C * (1 + norm a) ^
            osiiStep4MultiGapLeftVectorGrowthDegree OS T q :=
  (Classical.choose_spec
    (exists_uniformDegree_osiiPositiveTimeSingleVectorCLM_norm_sq_translate_bound
      OS (osiiStep4MultiGapLeftPositiveCLM T q))) f

noncomputable def osiiStep4MultiGapRightVectorGrowthDegree
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) (q : osiiAxisPairMultiGapIndex d k) : Nat :=
  Classical.choose
    (exists_uniformDegree_osiiPositiveTimeSingleVectorCLM_norm_sq_translate_bound
      OS (osiiStep4MultiGapRightPositiveCLM T q))

theorem osiiStep4MultiGapRightVectorGrowthDegree_spec
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) (q : osiiAxisPairMultiGapIndex d k)
    (f : SchwartzNPoint d (osiiStep4MultiGapAfterCount q.1 + 1)) :
    exists C : Real, 0 <= C ∧
      forall a : NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1),
        forall hpositive :
          tsupport
              (osiiStep4MultiGapRightPositiveCLM T q
                  (translateSchwartzConfiguration a f) :
                NPointDomain d
                  (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) <=
            OrderedPositiveTimeRegion d
              (osiiStep4MultiGapAfterCount q.1 + 1),
        norm (osiiPositiveTimeSingleVectorCLM OS
          (osiiStep4MultiGapAfterCount q.1 + 1)
          ⟨osiiStep4MultiGapRightPositiveCLM T q
              (translateSchwartzConfiguration a f), hpositive⟩) ^ 2 <=
          C * (1 + norm a) ^
            osiiStep4MultiGapRightVectorGrowthDegree OS T q :=
  (Classical.choose_spec
    (exists_uniformDegree_osiiPositiveTimeSingleVectorCLM_norm_sq_translate_bound
      OS (osiiStep4MultiGapRightPositiveCLM T q))) f

noncomputable def osiiStep4MultiGapPacketCoshRate
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) : Real :=
  4 * (((∑ q : osiiAxisPairMultiGapIndex d k,
    (osiiStep4MultiGapLeftVectorGrowthDegree OS T q +
      osiiStep4MultiGapRightVectorGrowthDegree OS T q)) : Nat) : Real)

theorem osiiStep4MultiGapPacketCoshRate_nonneg
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (T : Real) :
    0 <= osiiStep4MultiGapPacketCoshRate (k := k) OS T := by
  dsimp [osiiStep4MultiGapPacketCoshRate]
  positivity

theorem multiGap_logCoshGauge_nonneg
    {d k : Nat} [NeZero d] [NeZero k]
    (x : Fin k -> osiiAxisPairIndex d -> Real) :
    0 <= SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x) :=
  Finset.sum_nonneg fun _i _hi => (Real.cosh_pos _).le

theorem multiGapGaugeExp_pow
    {d k : Nat} [NeZero d] [NeZero k]
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (N : Nat) :
    (Real.exp (4 *
      SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x))) ^ N =
      Real.exp ((4 * (N : Real)) *
        SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

namespace OSIIStep4MultiGapSelectedCommonSlopeData

theorem leftPositiveCLM_configuration_eq
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiStep4MultiGapLeftPositiveCLM D.T q
        (translateSchwartzConfiguration
          (osiiStep4MultiGapLeftSpectatorConfiguration d k D.T x q.1)
          (osiiStep4MultiGapSelectedLeftPositiveTimeSource
            d k hrho center y y' hcenter q.1).1) =
      (osiiEuclideanRotateSchwartz
        (osiiAxisPairRotationData D.T q.2).matrix
        (osiiAxisPairRotationData D.T q.2).orthogonal
        (D.frozenLeftSource x q.1)).timeReflect := by
  rfl

theorem rightPositiveCLM_configuration_eq
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    osiiStep4MultiGapRightPositiveCLM D.T q
        (translateSchwartzConfiguration
          (osiiStep4MultiGapRightSpectatorConfiguration d k D.T x q.1)
          (osiiStep4MultiGapSelectedRightPositiveTimeSource
            d k hrho center y y' hcenter q.1).1) =
      osiiEuclideanRotateSchwartz
        (osiiAxisPairRotationData D.T q.2).matrix
        (osiiAxisPairRotationData D.T q.2).orthogonal
        (D.frozenRightSource x q.1) := by
  rfl

theorem leftPositiveCLM_configuration_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (osiiStep4MultiGapLeftPositiveCLM D.T q
          (translateSchwartzConfiguration
            (osiiStep4MultiGapLeftSpectatorConfiguration d k D.T x q.1)
            (osiiStep4MultiGapSelectedLeftPositiveTimeSource
              d k hrho center y y' hcenter q.1).1) :
          NPointDomain d (q.1.val + 1) -> Complex) <=
      OrderedPositiveTimeRegion d (q.1.val + 1) := by
  rw [D.leftPositiveCLM_configuration_eq x q]
  apply SchwartzNPoint.timeReflect_tsupport_orderedPositive
  exact osiiEuclideanRotateSchwartz_tsupport_orderedNegative
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal
    (D.frozenLeftSource x q.1) (D.frozenLeftSource_support x q)

theorem rightPositiveCLM_configuration_support
    {d k : Nat} [NeZero d] [NeZero k]
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k) :
    tsupport
        (osiiStep4MultiGapRightPositiveCLM D.T q
          (translateSchwartzConfiguration
            (osiiStep4MultiGapRightSpectatorConfiguration d k D.T x q.1)
            (osiiStep4MultiGapSelectedRightPositiveTimeSource
              d k hrho center y y' hcenter q.1).1) :
          NPointDomain d (osiiStep4MultiGapAfterCount q.1 + 1) -> Complex) <=
      OrderedPositiveTimeRegion d
        (osiiStep4MultiGapAfterCount q.1 + 1) := by
  rw [D.rightPositiveCLM_configuration_eq x q]
  exact osiiEuclideanRotateSchwartz_tsupport_orderedPositive
    (osiiAxisPairRotationData D.T q.2).matrix
    (osiiAxisPairRotationData D.T q.2).orthogonal
    (D.frozenRightSource x q.1) (D.frozenRightSource_support x q)

theorem exists_frozenLeftVector_norm_sq_bound
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    exists C : Real, 0 <= C ∧
      forall x : Fin k -> osiiAxisPairIndex d -> Real,
        norm (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
          ⟨osiiStep4MultiGapLeftPositiveCLM D.T q
              (translateSchwartzConfiguration
                (osiiStep4MultiGapLeftSpectatorConfiguration
                  d k D.T x q.1)
                (osiiStep4MultiGapSelectedLeftPositiveTimeSource
                  d k hrho center y y' hcenter q.1).1),
            D.leftPositiveCLM_configuration_support x q⟩) ^ 2 <=
          C * (1 + norm
            (osiiStep4MultiGapLeftSpectatorConfiguration
              d k D.T x q.1)) ^
                osiiStep4MultiGapLeftVectorGrowthDegree OS D.T q := by
  obtain ⟨C, hC, hbound⟩ :=
    osiiStep4MultiGapLeftVectorGrowthDegree_spec OS D.T q
      (osiiStep4MultiGapSelectedLeftPositiveTimeSource
        d k hrho center y y' hcenter q.1).1
  exact ⟨C, hC, fun x => hbound _
    (D.leftPositiveCLM_configuration_support x q)⟩

theorem exists_frozenRightVector_norm_sq_bound
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    exists C : Real, 0 <= C ∧
      forall x : Fin k -> osiiAxisPairIndex d -> Real,
        norm (osiiPositiveTimeSingleVectorCLM OS
          (osiiStep4MultiGapAfterCount q.1 + 1)
          ⟨osiiStep4MultiGapRightPositiveCLM D.T q
              (translateSchwartzConfiguration
                (osiiStep4MultiGapRightSpectatorConfiguration
                  d k D.T x q.1)
                (osiiStep4MultiGapSelectedRightPositiveTimeSource
                  d k hrho center y y' hcenter q.1).1),
            D.rightPositiveCLM_configuration_support x q⟩) ^ 2 <=
          C * (1 + norm
            (osiiStep4MultiGapRightSpectatorConfiguration
              d k D.T x q.1)) ^
                osiiStep4MultiGapRightVectorGrowthDegree OS D.T q := by
  obtain ⟨C, hC, hbound⟩ :=
    osiiStep4MultiGapRightVectorGrowthDegree_spec OS D.T q
      (osiiStep4MultiGapSelectedRightPositiveTimeSource
        d k hrho center y y' hcenter q.1).1
  exact ⟨C, hC, fun x => hbound _
    (D.rightPositiveCLM_configuration_support x q)⟩

theorem norm_explicitFrozenPacket_branch_le_vectorSquares
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (x : Fin k -> osiiAxisPairIndex d -> Real)
    (q : osiiAxisPairMultiGapIndex d k)
    (z : Complex) (hz : 0 < z.re) :
    norm ((OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (D.frozenLeftSource x q.1)
        (D.frozenLeftSource_support x q)
        (D.frozenRightSource x q.1)
        (D.frozenRightSource_support x q)).branch OS lgc z) <=
      norm (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
        ⟨osiiStep4MultiGapLeftPositiveCLM D.T q
            (translateSchwartzConfiguration
              (osiiStep4MultiGapLeftSpectatorConfiguration
                d k D.T x q.1)
              (osiiStep4MultiGapSelectedLeftPositiveTimeSource
                d k hrho center y y' hcenter q.1).1),
          D.leftPositiveCLM_configuration_support x q⟩) ^ 2 +
      norm (osiiPositiveTimeSingleVectorCLM OS
        (osiiStep4MultiGapAfterCount q.1 + 1)
        ⟨osiiStep4MultiGapRightPositiveCLM D.T q
            (translateSchwartzConfiguration
              (osiiStep4MultiGapRightSpectatorConfiguration
                d k D.T x q.1)
              (osiiStep4MultiGapSelectedRightPositiveTimeSource
                d k hrho center y y' hcenter q.1).1),
          D.rightPositiveCLM_configuration_support x q⟩) ^ 2 := by
  let A : Real := norm (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
    ⟨osiiStep4MultiGapLeftPositiveCLM D.T q
        (translateSchwartzConfiguration
          (osiiStep4MultiGapLeftSpectatorConfiguration d k D.T x q.1)
          (osiiStep4MultiGapSelectedLeftPositiveTimeSource
            d k hrho center y y' hcenter q.1).1),
      D.leftPositiveCLM_configuration_support x q⟩)
  let B : Real := norm (osiiPositiveTimeSingleVectorCLM OS
    (osiiStep4MultiGapAfterCount q.1 + 1)
    ⟨osiiStep4MultiGapRightPositiveCLM D.T q
        (translateSchwartzConfiguration
          (osiiStep4MultiGapRightSpectatorConfiguration d k D.T x q.1)
          (osiiStep4MultiGapSelectedRightPositiveTimeSource
            d k hrho center y y' hcenter q.1).1),
      D.rightPositiveCLM_configuration_support x q⟩)
  have hpacket :=
    OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branch_le
      OS lgc D.T D.hT
      (osiiAxisPairPositiveCoefficients (x q.1))
      (fun b => le_of_lt
        (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
      q.2
      (D.frozenLeftSource x q.1)
      (D.frozenLeftSource_support x q)
      (D.frozenRightSource x q.1)
      (D.frozenRightSource_support x q) z hz
  have hpacket' :
      norm ((OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (D.frozenLeftSource x q.1)
        (D.frozenLeftSource_support x q)
        (D.frozenRightSource x q.1)
        (D.frozenRightSource_support x q)).branch OS lgc z) <=
          2 * A * B := by
    simpa [A, B, D.leftPositiveCLM_configuration_eq x q,
      D.rightPositiveCLM_configuration_eq x q] using hpacket
  calc
    norm ((OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (D.frozenLeftSource x q.1)
        (D.frozenLeftSource_support x q)
        (D.frozenRightSource x q.1)
        (D.frozenRightSource_support x q)).branch OS lgc z)
        <= 2 * A * B := hpacket'
    _ <= A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg (A - B)]

theorem exists_explicitFrozenPacket_cosh_bound
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    exists C : Real, 0 < C ∧
      forall (x : Fin k -> osiiAxisPairIndex d -> Real)
        (z : Complex), 0 < z.re ->
        norm ((OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          D.T D.hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b => le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2
          (D.frozenLeftSource x q.1)
          (D.frozenLeftSource_support x q)
          (D.frozenRightSource x q.1)
          (D.frozenRightSource_support x q)).branch OS lgc z) <=
        C * Real.exp
          (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
            SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
  obtain ⟨CL, hCL, hleft⟩ := D.exists_frozenLeftVector_norm_sq_bound
    OS q
  obtain ⟨CR, hCR, hright⟩ := D.exists_frozenRightVector_norm_sq_bound
    OS q
  let NL := osiiStep4MultiGapLeftVectorGrowthDegree OS D.T q
  let NR := osiiStep4MultiGapRightVectorGrowthDegree OS D.T q
  let N := NL + NR
  let K := osiiStep4MultiGapSpectatorConfigurationCoshConstant d k D.T
  let cL := CL * K ^ NL
  let cR := CR * K ^ NR
  let C := 1 + cL + cR
  have hK : 0 < K := by
    exact osiiStep4MultiGapSpectatorConfigurationCoshConstant_pos d k D.T
  have hcL : 0 <= cL := mul_nonneg hCL (pow_nonneg hK.le _)
  have hcR : 0 <= cR := mul_nonneg hCR (pow_nonneg hK.le _)
  have hC : 0 < C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro x z hz
  let aL := osiiStep4MultiGapLeftSpectatorConfiguration d k D.T x q.1
  let aR := osiiStep4MultiGapRightSpectatorConfiguration d k D.T x q.1
  let G := SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)
  let E := Real.exp (4 * G)
  have hG : 0 <= G := by
    simpa [G] using multiGap_logCoshGauge_nonneg x
  have hE : 1 <= E := by
    simpa [E, G] using one_le_multiGapGaugeExp x
  have hconfigL : 1 + norm aL <= K * E := by
    simpa [aL, K, E, G,
      osiiStep4MultiGapLeftSpectatorConfiguration] using
      one_add_norm_multiGapLeftSpectatorConfiguration_le_cosh
        d k D.T x q.1
  have hconfigR : 1 + norm aR <= K * E := by
    simpa [aR, K, E, G,
      osiiStep4MultiGapRightSpectatorConfiguration] using
      one_add_norm_multiGapRightSpectatorConfiguration_le_cosh
        d k D.T x q.1
  have hpowL : (1 + norm aL) ^ NL <= K ^ NL * E ^ NL := by
    calc
      (1 + norm aL) ^ NL <= (K * E) ^ NL :=
        pow_le_pow_left₀ (by positivity) hconfigL NL
      _ = K ^ NL * E ^ NL := by rw [mul_pow]
  have hpowR : (1 + norm aR) ^ NR <= K ^ NR * E ^ NR := by
    calc
      (1 + norm aR) ^ NR <= (K * E) ^ NR :=
        pow_le_pow_left₀ (by positivity) hconfigR NR
      _ = K ^ NR * E ^ NR := by rw [mul_pow]
  have hNL : NL <= N := by simp [N]
  have hNR : NR <= N := by simp [N]
  have hENL : E ^ NL <= E ^ N := pow_le_pow_right₀ hE hNL
  have hENR : E ^ NR <= E ^ N := pow_le_pow_right₀ hE hNR
  have hsqL :
      norm (osiiPositiveTimeSingleVectorCLM OS (q.1.val + 1)
        ⟨osiiStep4MultiGapLeftPositiveCLM D.T q
            (translateSchwartzConfiguration aL
              (osiiStep4MultiGapSelectedLeftPositiveTimeSource
                d k hrho center y y' hcenter q.1).1),
          D.leftPositiveCLM_configuration_support x q⟩) ^ 2 <=
        cL * E ^ N := by
    calc
      _ <= CL * (1 + norm aL) ^ NL := by
        simpa [aL, NL] using hleft x
      _ <= CL * (K ^ NL * E ^ NL) :=
        mul_le_mul_of_nonneg_left hpowL hCL
      _ = cL * E ^ NL := by simp [cL]; ring
      _ <= cL * E ^ N := mul_le_mul_of_nonneg_left hENL hcL
  have hsqR :
      norm (osiiPositiveTimeSingleVectorCLM OS
        (osiiStep4MultiGapAfterCount q.1 + 1)
        ⟨osiiStep4MultiGapRightPositiveCLM D.T q
            (translateSchwartzConfiguration aR
              (osiiStep4MultiGapSelectedRightPositiveTimeSource
                d k hrho center y y' hcenter q.1).1),
          D.rightPositiveCLM_configuration_support x q⟩) ^ 2 <=
        cR * E ^ N := by
    calc
      _ <= CR * (1 + norm aR) ^ NR := by
        simpa [aR, NR] using hright x
      _ <= CR * (K ^ NR * E ^ NR) :=
        mul_le_mul_of_nonneg_left hpowR hCR
      _ = cR * E ^ NR := by simp [cR]; ring
      _ <= cR * E ^ N := mul_le_mul_of_nonneg_left hENR hcR
  have hNsum : N <= ∑ p : osiiAxisPairMultiGapIndex d k,
      (osiiStep4MultiGapLeftVectorGrowthDegree OS D.T p +
        osiiStep4MultiGapRightVectorGrowthDegree OS D.T p) := by
    exact Finset.single_le_sum
      (fun p _hp => Nat.zero_le
        (osiiStep4MultiGapLeftVectorGrowthDegree OS D.T p +
          osiiStep4MultiGapRightVectorGrowthDegree OS D.T p))
      (Finset.mem_univ q)
  have hpowRate : E ^ N <= Real.exp
      (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T * G) := by
    rw [show E ^ N = Real.exp ((4 * (N : Real)) * G) by
      simpa [E, G] using multiGapGaugeExp_pow x N]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hG
    dsimp [osiiStep4MultiGapPacketCoshRate]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hNsum) (by norm_num)
  calc
    norm ((OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        D.T D.hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b => le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (D.frozenLeftSource x q.1)
        (D.frozenLeftSource_support x q)
        (D.frozenRightSource x q.1)
        (D.frozenRightSource_support x q)).branch OS lgc z) <=
      _ := D.norm_explicitFrozenPacket_branch_le_vectorSquares OS lgc x q z hz
    _ <= cL * E ^ N + cR * E ^ N := add_le_add hsqL hsqR
    _ = (cL + cR) * E ^ N := by ring
    _ <= C * Real.exp
        (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T * G) := by
      apply mul_le_mul
      · dsimp [C]
        linarith
      · exact hpowRate
      · positivity
      · dsimp [C]
        linarith
    _ = C * Real.exp
        (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
          SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := rfl

noncomputable def flatCrossData
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter) :
    OSIIAxisPairMultiGapFlatCrossData d k :=
  (D.packetFamily OS lgc).toFlatCrossData
    (D.continuousOn_packetFamily_branch OS lgc)

theorem exists_packetFamily_logBranch_cosh_bound
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter)
    (q : osiiAxisPairMultiGapIndex d k) :
    exists C : Real, 0 < C ∧
      forall (x : Fin k -> osiiAxisPairIndex d -> Real)
        (w : Complex), |w.im| < Real.pi / 2 ->
        norm ((D.packetFamily OS lgc).logBranch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
          C * Real.exp
            (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiAxisPairMultiGapChartRealPart x q w))) := by
  obtain ⟨C, hC, hbound⟩ :=
    D.exists_explicitFrozenPacket_cosh_bound OS lgc q
  refine ⟨C, hC, ?_⟩
  intro x w hw
  let x' := osiiAxisPairMultiGapChartRealPart x q w
  have hoff : forall p : osiiAxisPairMultiGapIndex d k, p ≠ q ->
      x p.1 p.2 = x' p.1 p.2 := by
    intro p hp
    exact (osiiAxisPairMultiGapChartRealPart_eq_of_ne x q p w hp).symm
  have hcoherent :=
    (D.packetFamily OS lgc).logBranch_congr_of_eq_off_selected q hoff
  have heq := congrFun hcoherent
    (osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w)
  rw [heq]
  simp only [OSIIAxisPairMultiGapSemigroupPacketFamily.logBranch]
  rw [show (osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w) q.1 q.2 = w by
    simp [osiiAxisPairMultiGapUpdate]]
  rw [D.packetFamily_packet_branch_eq_explicit
    OS lgc x' q (Complex.exp w)]
  have hz : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  simpa [x'] using hbound x' (Complex.exp w) hz

theorem exists_packetFamily_cosh_bounds
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter) :
    exists C : Real, 0 < C ∧
      (forall x : Fin k -> osiiAxisPairIndex d -> Real,
        norm ((D.packetFamily OS lgc).realEdge x) <=
          C * Real.exp
            (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
              SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x))) ∧
      forall (q : osiiAxisPairMultiGapIndex d k)
        (x : Fin k -> osiiAxisPairIndex d -> Real) (w : Complex),
        |w.im| < Real.pi / 2 ->
        norm ((D.packetFamily OS lgc).logBranch x q
          (osiiAxisPairMultiGapUpdate
            (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
          C * Real.exp
            (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiAxisPairMultiGapChartRealPart x q w))) := by
  let hexists (q : osiiAxisPairMultiGapIndex d k) :=
    D.exists_packetFamily_logBranch_cosh_bound OS lgc q
  let C : osiiAxisPairMultiGapIndex d k -> Real :=
    fun q => Classical.choose (hexists q)
  have hC : forall q, 0 < C q := by
    intro q
    exact (Classical.choose_spec (hexists q)).1
  have hchart : forall (q : osiiAxisPairMultiGapIndex d k)
      (x : Fin k -> osiiAxisPairIndex d -> Real) (w : Complex),
      |w.im| < Real.pi / 2 ->
      norm ((D.packetFamily OS lgc).logBranch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
        C q * Real.exp
          (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiAxisPairMultiGapChartRealPart x q w))) := by
    intro q
    exact (Classical.choose_spec (hexists q)).2
  let Cstar : Real := 1 + ∑ q : osiiAxisPairMultiGapIndex d k, C q
  have hCstar : 0 < Cstar := by
    have hsum : 0 <= ∑ q : osiiAxisPairMultiGapIndex d k, C q :=
      Finset.sum_nonneg fun q _hq => (hC q).le
    dsimp [Cstar]
    linarith
  have hC_le : forall q : osiiAxisPairMultiGapIndex d k, C q <= Cstar := by
    intro q
    have hsingle : C q <= ∑ p : osiiAxisPairMultiGapIndex d k, C p :=
      Finset.single_le_sum (fun p _hp => (hC p).le) (Finset.mem_univ q)
    dsimp [Cstar]
    linarith
  have hchartStar : forall (q : osiiAxisPairMultiGapIndex d k)
      (x : Fin k -> osiiAxisPairIndex d -> Real) (w : Complex),
      |w.im| < Real.pi / 2 ->
      norm ((D.packetFamily OS lgc).logBranch x q
        (osiiAxisPairMultiGapUpdate
          (osiiAxisPairSimultaneousLogRealEmbed x) q w)) <=
        Cstar * Real.exp
          (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiAxisPairMultiGapChartRealPart x q w))) := by
    intro q x w hw
    exact (hchart q x w hw).trans
      (mul_le_mul_of_nonneg_right (hC_le q) (Real.exp_pos _).le)
  let q0 : osiiAxisPairMultiGapIndex d k :=
    ((0 : Fin k), ((0 : Fin d), false))
  have hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      norm ((D.packetFamily OS lgc).realEdge x) <=
        Cstar * Real.exp
          (osiiStep4MultiGapPacketCoshRate (k := k) OS D.T *
            SCV.logCoshGauge (osiiAxisPairMultiGapFlatten x)) := by
    intro x
    have hstrip : |((x q0.1 q0.2 : Complex)).im| < Real.pi / 2 := by
      simp
      positivity
    have hbound := hchartStar q0 x (x q0.1 q0.2 : Complex) hstrip
    rw [osiiAxisPairMultiGapUpdate_realEmbed_selected x q0] at hbound
    rw [(D.packetFamily OS lgc).logBranch_real_edge x q0] at hbound
    rw [osiiAxisPairMultiGapChartRealPart_selected_real x q0] at hbound
    exact hbound
  exact ⟨Cstar, hCstar, hreal, hchartStar⟩

noncomputable def coshGrowthData
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter) :
    OSIIAxisPairMultiGapFlatCrossCoshGrowthData
      (D.flatCrossData OS lgc) := by
  let hexists := D.exists_packetFamily_cosh_bounds OS lgc
  let C : Real := Classical.choose hexists
  have hC : 0 < C := (Classical.choose_spec hexists).1
  have hreal := (Classical.choose_spec hexists).2.1
  have hchart := (Classical.choose_spec hexists).2.2
  let P : OSIIAxisPairMultiGapFlatCrossData d k := D.flatCrossData OS lgc
  letI : NeZero (k * d) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne d)⟩
  let X : OSIIAxisPairFlatCrossData (k * d) :=
    P.toFlattenedFlatCrossData
  change OSIIAxisPairFlatCrossCoshGrowthData X
  refine {
    rate := osiiStep4MultiGapPacketCoshRate (k := k) OS D.T
    rate_nonneg := osiiStep4MultiGapPacketCoshRate_nonneg
      (k := k) OS D.T
    realEdgeConstant := C
    realEdgeConstant_nonneg := hC.le
    realEdge_bound := ?_
    chartConstant := C
    chartConstant_pos := hC
    chart_bound := ?_ }
  · intro x
    simpa [C, X, P, flatCrossData,
      OSIIAxisPairMultiGapFlatCrossData.toFlattenedFlatCrossData,
      OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData] using
      hreal (osiiAxisPairMultiGapUnflatten x)
  · intro q x w hw
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch x q hw]
    simp only [X, P,
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
    have hbound := hchart uq (osiiAxisPairMultiGapUnflatten x) w hw
    rw [osiiAxisPairMultiGapFlatten_chartRealPart_unflatten x uq w] at hbound
    have hflatbase :
        osiiAxisPairMultiGapFlatten
            (osiiAxisPairSimultaneousLogRealEmbed
              (osiiAxisPairMultiGapUnflatten x)) =
          fun c => (x c : Complex) := by
      rw [osiiAxisPairMultiGapFlatten_realEmbed]
      rw [osiiAxisPairMultiGapFlatten_unflatten]
      rfl
    rw [hflatbase]
    simpa [C, P, flatCrossData,
      OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData,
      osiiAxisPairLogRealEmbed] using hbound

/-- The MZ continuation of the canonical OS centered-kernel edge.  This is
the direct Chapter VI continuation and does not use the reduced-BVT
identification. -/
theorem exists_holomorphic_centeredSchwinger_extension
    {d k : Nat} [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} {hrho : 0 < rho}
    {center y y' : Fin (k * (d + 1)) -> Real}
    {hcenter : forall j : Fin k,
      rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
    (D : OSIIStep4MultiGapSelectedCommonSlopeData
      d k hrho center y y' hcenter) :
    exists Gamma : (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex,
      DifferentiableOn Complex Gamma (osiiAxisPairMultiGapLogDomain d k) ∧
      forall x : Fin k -> osiiAxisPairIndex d -> Real,
        Gamma (osiiAxisPairSimultaneousLogRealEmbed x) =
          osiiStep4FixedRadiusCenteredSchwinger d OS k hrho
            (center + osiiStep4AxisPairGapTranslationFlat d D.T x) y y'
            (osiiStep4MultiGapTranslatedCenter_time_lower
              d k center hcenter D.T D.hT x) := by
  obtain ⟨Gamma, hGamma, hreal⟩ :=
    (D.coshGrowthData OS lgc).exists_holomorphic_realEdge_extension
      (D.flatCrossData OS lgc)
  refine ⟨Gamma, hGamma, ?_⟩
  intro x
  simpa [flatCrossData,
    OSIIAxisPairMultiGapSemigroupPacketFamily.toFlatCrossData,
    packetFamily] using hreal x

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
