/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketApproximation

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Adding a strictly positive real vector preserves the narrow pure-time
carrier. -/
theorem osiiNarrowTimeCarrier_add_positiveReal
    (η : ℝ)
    (hη : 0 < η)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η)
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    ζ + osiiPositiveRealTimeEmbed anchor ∈
      osiiNarrowTimeCarrier (k := k) η := by
  intro i
  have hζi := hζ i
  have hai := hanchor i
  simp only [Pi.add_apply, osiiPositiveRealTimeEmbed,
    Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, add_zero]
  constructor
  · linarith
  · have hηa : 0 < η * anchor i := mul_pos hη hai
    linarith

/-- Every compact subset of the narrow carrier admits a small strictly
positive anchor whose backward shift remains in the carrier. -/
theorem exists_positive_anchor_sub_mem_osiiNarrowTimeCarrier
    (η : ℝ)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiNarrowTimeCarrier (k := k) η) :
    ∃ anchor : Fin k → ℝ,
      anchor ∈ section43TimeStrictPositiveRegion k ∧
        ∀ ζ ∈ K,
          ζ - osiiPositiveRealTimeEmbed anchor ∈
            osiiNarrowTimeCarrier (k := k) η := by
  obtain ⟨r, hr, hthick⟩ :=
    hK_compact.exists_cthickening_subset_open
      (isOpen_osiiNarrowTimeCarrier η) hK_subset
  let δ : ℝ := r / 2
  let anchor : Fin k → ℝ := fun _ => δ
  have hδ : 0 < δ := half_pos hr
  refine ⟨anchor, ?_, ?_⟩
  · intro i
    exact hδ
  · intro ζ hζ
    apply hthick
    apply Metric.mem_cthickening_of_dist_le
      (ζ - osiiPositiveRealTimeEmbed anchor) ζ r K hζ
    rw [dist_eq_norm]
    have hdiff :
        (ζ - osiiPositiveRealTimeEmbed anchor) - ζ =
          -osiiPositiveRealTimeEmbed anchor := by
      module
    rw [hdiff, norm_neg, pi_norm_le_iff_of_nonempty]
    intro i
    simp only [osiiPositiveRealTimeEmbed, anchor, δ,
      norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    linarith

namespace InitialSpatialFactorPacketData

/-- Translating the complete reduced-time test by a positive anchor translates
the packet's complex time parameter by the same anchor.

The equality is first checked on the positive real slice using the exact
packet real edge and composition of Schwartz translations, then extended to
the connected narrow carrier by the totally-real identity theorem. -/
theorem narrowDistributionOfOS_translate_timeTest
    {φ : SchwartzMap (Fin k → ℝ) ℂ}
    {level : ℕ}
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k)
    (P :
      InitialSpatialFactorPacketData
        (d := d) (SCV.translateSchwartz (-anchor) φ) level)
    (Q : InitialSpatialFactorPacketData (d := d) φ level)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Set.EqOn
      (fun ζ => P.narrowDistributionOfOS OS η hηsum ζ χ)
      (fun ζ =>
        Q.narrowDistributionOfOS OS η hηsum
          (ζ + osiiPositiveRealTimeEmbed anchor) χ)
      (osiiNarrowTimeCarrier (k := k) η) := by
  let U := osiiNarrowTimeCarrier (k := k) η
  let shift : OSIITimeGapSpace k → OSIITimeGapSpace k :=
    fun ζ => ζ + osiiPositiveRealTimeEmbed anchor
  let F : OSIITimeGapSpace k → ℂ :=
    fun ζ =>
      P.narrowDistributionOfOS OS η hηsum ζ χ -
        Q.narrowDistributionOfOS OS η hηsum (shift ζ) χ
  have hshift_diff : Differentiable ℂ shift := by
    exact differentiable_id.add_const _
  have hQ_shift :
      DifferentiableOn ℂ
        (fun ζ =>
          Q.narrowDistributionOfOS OS η hηsum (shift ζ) χ) U := by
    exact
      (Q.narrowDistributionOfOS_weaklyHolomorphic
        OS η hηsum χ).comp
        hshift_diff.differentiableOn
        (fun ζ hζ =>
          osiiNarrowTimeCarrier_add_positiveReal
            η hη ζ hζ anchor hanchor)
  have hF : DifferentiableOn ℂ F U :=
    (P.narrowDistributionOfOS_weaklyHolomorphic
      OS η hηsum χ).sub hQ_shift
  have hreal :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        P.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed τ) χ =
          Q.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed (τ + anchor)) χ := by
    intro τ hτ
    have hτanchor :
        τ + anchor ∈ section43TimeStrictPositiveRegion k := by
      intro i
      exact add_pos (hτ i) (hanchor i)
    have htranslate :
        SCV.translateSchwartz (-τ)
            (SCV.translateSchwartz (-anchor) φ) =
          SCV.translateSchwartz (-(τ + anchor)) φ := by
      rw [SCV.translateSchwartz_translateSchwartz]
      congr 1
      funext i
      simp [add_comm]
    rw [P.narrowDistributionOfOS_realEdge
      OS η hη hηsum τ hτ χ]
    rw [Q.narrowDistributionOfOS_realEdge
      OS η hη hηsum (τ + anchor) hτanchor χ]
    apply congrArg (OS.S (k + 1))
    apply SetCoe.ext
    rw [P.cover.localizedTranslatedZeroSum_coe,
      Q.cover.localizedTranslatedZeroSum_coe,
      initialReducedSpatialFactorCompactSourceCLM_apply,
      initialReducedSpatialFactorCompactSourceCLM_apply,
      translate_initialReducedSpatialFullSource_narrow
        P.slope (lt_trans zero_lt_one P.slope_gt_one)
        τ hτ (SCV.translateSchwartz (-anchor) φ)
        (initialSpatialFactorTruncationCLM d k level χ),
      translate_initialReducedSpatialFullSource_narrow
        Q.slope (lt_trans zero_lt_one Q.slope_gt_one)
        (τ + anchor) hτanchor φ
        (initialSpatialFactorTruncationCLM d k level χ),
      htranslate]
  have hpositive_nonempty :
      (section43TimeStrictPositiveRegion k).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    intro i
    simp
  have hpositive_sub :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        SCV.realToComplex τ ∈ U := by
    intro τ hτ
    change osiiPositiveRealTimeEmbed τ ∈ U
    exact osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
      η hη τ hτ
  have hF_zero :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    have h := hreal τ hτ
    change F (osiiPositiveRealTimeEmbed τ) = 0
    simpa [F, shift, osiiPositiveRealTimeEmbed] using
      sub_eq_zero.mpr h
  intro ζ hζ
  have hz :
      F ζ = 0 :=
    SCV.identity_theorem_totally_real
      (isOpen_osiiNarrowTimeCarrier η)
      (isConnected_osiiNarrowTimeCarrier η hη)
      hF
      (isOpen_section43TimeStrictPositiveRegion k)
      hpositive_nonempty
      hpositive_sub
      hF_zero
      ζ hζ
  exact sub_eq_zero.mp hz

end InitialSpatialFactorPacketData

end OSIIChapterV
end OSReconstruction
