/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketCarrierCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketFullBounds









noncomputable section

open Complex Set Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- An enlarged anchored carrier family with quantitative room around the
anchor.  The factor `8` reserves space for the auxiliary positive
translations used to convert one-sided chronological covariance into local
covariance under arbitrary small real translations. -/
structure CommonCarrierRegularityData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor) where
  radius : ℝ
  radius_pos : 0 < radius
  family : AnchoredPacketTimeShellFamilyData (d := d) I anchor
  tailStart_eq :
    family.carrierData.tailStart = A.carrierData.tailStart
  originalCarrier_subset :
    A.carrierData.carrier ⊆ family.carrierData.carrier
  closedBall_subset :
    Metric.closedBall anchor (8 * radius) ⊆
      family.carrierData.carrier

/-- A reduced-time Schwartz test is supported in the radius-`r` ball about
the anchored time point. -/
def AnchoredSupportWithin
    (anchor : Fin k → ℝ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (r : ℝ) : Prop :=
  tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ Metric.closedBall anchor r

/-- Recentring a kernel supported about zero puts its support in the
corresponding ball about the anchor. -/
theorem anchoredSupportWithin_translate_neg_anchor
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (r : ℝ)
    (hψ : SCV.KernelSupportWithin ψ r) :
    AnchoredSupportWithin anchor
      (SCV.translateSchwartz (-anchor) ψ) r := by
  intro x hx
  rw [tsupport_translateSchwartz_eq_preimage] at hx
  have hx_ball := hψ hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx_ball
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa [sub_eq_add_neg] using hx_ball

/-- Translating an anchored-supported test enlarges its support radius by at
most the norm of the translation. -/
theorem AnchoredSupportWithin.translateSchwartz
    {ψ : SchwartzMap (Fin k → ℝ) ℂ}
    {r : ℝ}
    (hψ : AnchoredSupportWithin anchor ψ r)
    (a : Fin k → ℝ) :
    AnchoredSupportWithin anchor
      (SCV.translateSchwartz a ψ) (r + ‖a‖) := by
  intro x hx
  rw [tsupport_translateSchwartz_eq_preimage] at hx
  have hxa := hψ hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hxa ⊢
  change ‖x + a - anchor‖ ≤ r at hxa
  calc
    ‖x - anchor‖ = ‖(x + a - anchor) - a‖ := by
      congr 1
      module
    _ ≤ ‖x + a - anchor‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ r + ‖a‖ := by linarith

/-- Every anchored packet family admits a compact strict-positive carrier
enlargement containing a genuine ball around its anchor. -/
theorem nonempty_commonCarrierRegularityData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor) :
    Nonempty (CommonCarrierRegularityData A) := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp
      (isOpen_section43TimeStrictPositiveRegion k)
      anchor A.anchor_positive
  let radius : ℝ := ε / 16
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hclosed_positive :
      Metric.closedBall anchor (8 * radius) ⊆
        section43TimeStrictPositiveRegion k := by
    intro ξ hξ
    apply hball
    rw [Metric.mem_ball]
    have hdist :
        dist ξ anchor ≤ 8 * radius :=
      Metric.mem_closedBall.mp hξ
    have heigth : 8 * radius < ε := by
      dsimp [radius]
      linarith
    exact hdist.trans_lt heigth
  let carrier : Set (Fin k → ℝ) :=
    A.carrierData.carrier ∪
      Metric.closedBall anchor (8 * radius)
  have hcarrier_compact : IsCompact carrier := by
    dsimp [carrier]
    exact A.carrierData.carrier_compact.union
      (isCompact_closedBall anchor (8 * radius))
  have hcarrier_positive :
      carrier ⊆ section43TimeStrictPositiveRegion k := by
    dsimp [carrier]
    exact union_subset A.carrierData.carrier_positive hclosed_positive
  let C : AnchoredCompactTimeCarrierData I anchor := {
    tailStart := A.carrierData.tailStart
    carrier := carrier
    carrier_compact := hcarrier_compact
    carrier_positive := hcarrier_positive
    translated_support := fun N =>
      (A.carrierData.translated_support N).trans subset_union_left }
  obtain ⟨D⟩ :=
    nonempty_initialBaseTimeCarrierPartitionData
      (d := d) C.carrier C.carrier_compact C.carrier_positive
  let B : AnchoredPacketTimeShellFamilyData (d := d) I anchor := {
    anchor_positive := A.anchor_positive
    carrierData := C
    partition := D }
  refine ⟨{
    radius := radius
    radius_pos := hradius
    family := B
    tailStart_eq := rfl
    originalCarrier_subset := ?_
    closedBall_subset := ?_ }⟩
  · exact subset_union_left
  · exact subset_union_right

/-- Inside the enlarged carrier one can choose a small positive buffer which
remains strictly positive after every sufficiently small arbitrary real
shift.  The buffer itself is chosen smaller than the carrier radius. -/
theorem CommonCarrierRegularityData.exists_positive_buffer
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A) :
    ∃ q : Fin k → ℝ, ∃ ρ : ℝ,
      q ∈ section43TimeStrictPositiveRegion k ∧
      0 < ρ ∧
      ρ < R.radius ∧
      ‖q‖ < R.radius ∧
      ∀ a : Fin k → ℝ, ‖a‖ < ρ →
        q - a ∈ section43TimeStrictPositiveRegion k := by
  let c : ℝ := R.radius / (2 * (‖anchor‖ + 1))
  let q : Fin k → ℝ := c • anchor
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos R.radius_pos
      (mul_pos (by norm_num) (by positivity))
  have hq_positive :
      q ∈ section43TimeStrictPositiveRegion k := by
    intro i
    dsimp [q]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      mul_pos hc (R.family.anchor_positive i)
  have hq_norm : ‖q‖ < R.radius := by
    have hnorm_lt : ‖anchor‖ < ‖anchor‖ + 1 := by linarith
    calc
      ‖q‖ = c * ‖anchor‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      _ < c * (‖anchor‖ + 1) :=
        mul_lt_mul_of_pos_left hnorm_lt hc
      _ = R.radius / 2 := by
        dsimp [c]
        field_simp
      _ < R.radius := by linarith [R.radius_pos]
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp
      (isOpen_section43TimeStrictPositiveRegion k)
      q hq_positive
  let ρ : ℝ := min (ε / 2) (R.radius / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (half_pos hε) (half_pos R.radius_pos)
  have hρ_radius : ρ < R.radius := by
    calc
      ρ ≤ R.radius / 2 := min_le_right _ _
      _ < R.radius := by linarith [R.radius_pos]
  refine ⟨q, ρ, hq_positive, hρ, hρ_radius, hq_norm, ?_⟩
  intro a ha
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : q - a - q = -a := by module
  rw [hsub, norm_neg]
  exact ha.trans
    ((min_le_left (ε / 2) (R.radius / 2)).trans_lt
      (half_lt_self hε))

/-- The chronological positive-shift covariance becomes genuine two-sided
local real-translation covariance after recentering tests at the anchor.
The radius and the covariance identity are uniform in the spatial exhaustion
level. -/
theorem CommonCarrierRegularityData.exists_recentered_localCovarianceOfOS
    {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
    (R : CommonCarrierRegularityData A)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    ∃ ρ > 0, ∀ (a : Fin k → ℝ), ‖a‖ < ρ →
      ∀ (ψ : SchwartzMap (Fin k → ℝ) ℂ),
        SCV.KernelSupportWithin ψ R.radius →
        SCV.KernelSupportWithin (SCV.translateSchwartz a ψ) R.radius →
        ∀ (level : ℕ) (w : OSIITimeGapSpace k),
          w ∈ osiiNarrowTimeCarrier (k := k) η →
          w - osiiPositiveRealTimeEmbed a ∈
            osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            R.family.commonTimeShellDistributionOfOS
                OS η hηsum level w χ
                (SCV.translateSchwartz (-anchor)
                  (SCV.translateSchwartz a ψ)) =
              R.family.commonTimeShellDistributionOfOS
                OS η hηsum level
                (w - osiiPositiveRealTimeEmbed a) χ
                (SCV.translateSchwartz (-anchor) ψ) := by
  obtain ⟨q, ρ, hq_positive, hρ, hρ_radius, hq_norm,
      hq_sub_positive⟩ :=
    R.exists_positive_buffer
  refine ⟨ρ, hρ, ?_⟩
  intro a ha ψ hψ hψa level w hw hw_sub χ
  let φ : SchwartzMap (Fin k → ℝ) ℂ :=
    SCV.translateSchwartz (-anchor) ψ
  let φq : SchwartzMap (Fin k → ℝ) ℂ :=
    SCV.translateSchwartz q φ
  let p : Fin k → ℝ := q - a
  have hp_positive :
      p ∈ section43TimeStrictPositiveRegion k :=
    hq_sub_positive a ha
  have hφ_anchor :
      AnchoredSupportWithin anchor φ R.radius := by
    exact anchoredSupportWithin_translate_neg_anchor ψ R.radius hψ
  have hφ_support :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        R.family.carrierData.carrier := by
    exact hφ_anchor.trans
      ((Metric.closedBall_subset_closedBall (by
          linarith [R.radius_pos])).trans R.closedBall_subset)
  have hφa_anchor :
      AnchoredSupportWithin anchor
        (SCV.translateSchwartz (-anchor)
          (SCV.translateSchwartz a ψ)) R.radius := by
    exact
      anchoredSupportWithin_translate_neg_anchor
        (SCV.translateSchwartz a ψ) R.radius hψa
  have hφa_support :
      tsupport
          (SCV.translateSchwartz (-anchor)
            (SCV.translateSchwartz a ψ) :
            (Fin k → ℝ) → ℂ) ⊆
        R.family.carrierData.carrier := by
    exact hφa_anchor.trans
      ((Metric.closedBall_subset_closedBall (by
          linarith [R.radius_pos])).trans R.closedBall_subset)
  have hφq_anchor :
      AnchoredSupportWithin anchor φq (R.radius + ‖q‖) := by
    exact hφ_anchor.translateSchwartz q
  have hφq_support :
      tsupport (φq : (Fin k → ℝ) → ℂ) ⊆
        R.family.carrierData.carrier := by
    exact hφq_anchor.trans
      ((Metric.closedBall_subset_closedBall (by
          linarith [R.radius_pos, hq_norm])).trans R.closedBall_subset)
  have hleft_p :
      SCV.translateSchwartz (-p) φq =
        SCV.translateSchwartz (-anchor)
          (SCV.translateSchwartz a ψ) := by
    ext x
    change
      ψ (x + -p + q + -anchor) =
        ψ (x + -anchor + a)
    apply congrArg ψ
    dsimp [p]
    module
  have hleft_q :
      SCV.translateSchwartz (-q) φq = φ := by
    ext x
    change ψ (x + -q + q + -anchor) = ψ (x + -anchor)
    apply congrArg ψ
    module
  have hparameter :
      w + osiiPositiveRealTimeEmbed p =
        (w - osiiPositiveRealTimeEmbed a) +
          osiiPositiveRealTimeEmbed q := by
    ext i
    simp [p, osiiPositiveRealTimeEmbed]
    ring
  have hp_cov :=
    R.family.commonTimeShellDistributionOfOS_translate_timeTest
      OS φq hφq_support p hp_positive
      (by simpa [hleft_p] using hφa_support)
      η hη hηsum level w hw χ
  have hq_cov :=
    R.family.commonTimeShellDistributionOfOS_translate_timeTest
      OS φq hφq_support q hq_positive
      (by simpa [hleft_q] using hφ_support)
      η hη hηsum level
      (w - osiiPositiveRealTimeEmbed a) hw_sub χ
  rw [hleft_p] at hp_cov
  rw [hleft_q] at hq_cov
  rw [hparameter] at hp_cov
  exact hp_cov.trans hq_cov.symm

/-- For a fixed reduced-time test, one common packet piece is bounded
uniformly in the spatial exhaustion level on compact complex-time sets. -/
theorem commonPacket_pieceTimeShellDistributionOfOS_fixedTest_compact_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    ∃ C : ℝ, ∀ level ζ, ζ ∈ K →
      ‖(A.commonPacketAt 0 level).pieceTimeShellDistributionOfOS
          OS η hηsum a ζ χ ψ‖ ≤ C := by
  let fN : ℕ → SchwartzNPoint d (k + 1) := fun level =>
    (A.partitionAt 0).timePieceFullSourceCLM a
      (initialSpatialFactorTruncationCLM d k level χ) ψ
  let L : SchwartzNPoint d (k + 1) →L[ℂ]
      SchwartzNPoint d (k + 1) :=
    SchwartzMap.smulLeftCLM ℂ ((A.partitionAt 0).weight a)
  have hfN_tendsto :
      Tendsto fN atTop
        (nhds
          (L (initialReducedSpatialFullSourceCLM (d := d) ψ χ))) := by
    have hsource :=
      initialReducedSpatialFactorCompactSource_tendsto
        (d := d) (k := k) ψ χ
    have hlocalized :=
      (L.continuous.tendsto
        (initialReducedSpatialFullSourceCLM (d := d) ψ χ)).comp hsource
    change Tendsto
      (L ∘ fun N =>
        initialReducedSpatialFactorCompactSourceCLM (d := d) ψ N χ)
      atTop (nhds (L (initialReducedSpatialFullSourceCLM (d := d) ψ χ)))
    exact hlocalized
  have hfN : Bornology.IsVonNBounded ℝ (Set.range fN) := by
    letI : ContinuousSMul ℝ (SchwartzNPoint d (k + 1)) :=
      SchwartzMap.instContinuousSMul
    exact hfN_tendsto.isVonNBounded_range ℝ
  obtain ⟨C, hC⟩ :=
    A.commonPacketOfOS_boundedFullSources_compact_bound
      a OS η hηsum K hK_compact hK_subset fN hfN
  refine ⟨C, ?_⟩
  intro level ζ hζ
  unfold InitialBaseTimePartitionData.FixedTimePacketData.pieceTimeShellDistributionOfOS
  simpa [
    InitialBaseTimePartitionData.FixedTimePacketData.levelTimePieceFullSourceCLM,
    initialSpatialFactorTruncationCLM_apply,
    osiiNarrowTimeStageChart,
    fN] using hC 0 level ζ hζ

/-- The complete common time-shell distribution is pointwise bounded on every
fixed reduced-time Schwartz test, uniformly in the spatial level and on
compact subsets of the narrow carrier. -/
theorem commonTimeShellDistributionOfOS_fixedTest_compact_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ) :
    ∃ C : ℝ, ∀ level ζ, ζ ∈ K →
      ‖A.commonTimeShellDistributionOfOS
          OS η hηsum level ζ χ ψ‖ ≤ C := by
  choose C hC using fun a =>
    A.commonPacket_pieceTimeShellDistributionOfOS_fixedTest_compact_bound
      a OS η hηsum K hK_compact hK_subset χ ψ
  refine ⟨∑ a : A.partition.index, C a, ?_⟩
  intro level ζ hζ
  rw [show
      A.commonTimeShellDistributionOfOS
          OS η hηsum level ζ χ ψ =
        ∑ a : A.partition.index,
          (A.commonPacketAt 0 level).pieceTimeShellDistributionOfOS
            OS η hηsum a ζ χ ψ by
      exact InitialBaseTimePartitionData.FixedTimePacketData.timeShellDistributionOfOS_apply
          (A.commonPacketAt 0 level) OS η hηsum ζ χ ψ]
  calc
    ‖∑ a : A.partition.index,
        (A.commonPacketAt 0 level).pieceTimeShellDistributionOfOS
          OS η hηsum a ζ χ ψ‖
        ≤ ∑ a : A.partition.index,
            ‖(A.commonPacketAt 0 level).pieceTimeShellDistributionOfOS
              OS η hηsum a ζ χ ψ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : A.partition.index, C a :=
      Finset.sum_le_sum fun a _ha => hC a level ζ hζ

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
