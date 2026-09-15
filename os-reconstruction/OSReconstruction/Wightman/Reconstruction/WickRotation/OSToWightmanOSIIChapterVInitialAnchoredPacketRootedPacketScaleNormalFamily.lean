/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedPacketScaleRealEdge
import OSReconstruction.SCV.LocallyUniformDistributionRepresentation









noncomputable section

open Complex Filter MeasureTheory Set
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

namespace RootedA0BlockContinuousTranslationData

/-- The full original-OS rooted Hermite series has one compact bound
independent of the shrinking packet scale. -/
theorem
    exists_rootSmearedSpatialHermiteGeneratorSumOfOS_norm_bound_on_complex_compact
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_domain :
      K ⊆ generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ∃ M > 0,
      ∀ (timeScale : ℕ) (w : OSIITimeGapSpace k), w ∈ K →
        ‖D.rootSmearedSpatialHermiteGeneratorSumOfOS
            i timeScale w F‖ ≤ M := by
  obtain ⟨C, hC, q, hmode⟩ :=
    D.exists_rootSmearedSpatialHermiteGeneratorModeOfOS_norm_polynomial_bound_on_complex_compact
      i K hK_compact hK_domain
  let coefficient : ℕ → ℂ :=
    fun mode =>
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM
        (d := d) i mode F
  let majorant : ℕ → ℝ :=
    fun mode =>
      C * (‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q)
  have hcoefficient :
      Summable fun mode =>
        ‖coefficient mode‖ * (1 + (mode : ℝ)) ^ q := by
    simpa [coefficient,
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCoefficientCLM]
      using
        (summable_norm_coefficient_mul_weight q
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F))
  have hmajorant : Summable majorant := by
    simpa [majorant] using hcoefficient.mul_left C
  have hmajorant_nonneg : 0 ≤ ∑' mode, majorant mode :=
    tsum_nonneg fun mode =>
      mul_nonneg hC.le
        (mul_nonneg (norm_nonneg _)
          (pow_nonneg (by positivity) q))
  refine ⟨(∑' mode, majorant mode) + 1, by positivity, ?_⟩
  intro timeScale w hw
  have hnorm_summable :
      Summable fun mode =>
        ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode w * coefficient mode‖ := by
    exact
      Summable.of_nonneg_of_le
        (fun mode => norm_nonneg _)
        (fun mode => by
          rw [norm_mul]
          exact
            (mul_le_mul_of_nonneg_right
              (hmode timeScale mode w hw)
              (norm_nonneg _)).trans_eq (by
                simp only [majorant]
                ring))
        hmajorant
  rw [rootSmearedSpatialHermiteGeneratorSumOfOS]
  change
    ‖∑' mode,
        D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode w * coefficient mode‖ ≤ _
  calc
    ‖∑' mode,
        D.rootSmearedSpatialHermiteGeneratorModeOfOS
            i timeScale mode w * coefficient mode‖
        ≤ ∑' mode,
            ‖D.rootSmearedSpatialHermiteGeneratorModeOfOS
                i timeScale mode w * coefficient mode‖ :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' mode, majorant mode := by
      apply hnorm_summable.tsum_le_tsum
      · intro mode
        rw [norm_mul]
        exact
          (mul_le_mul_of_nonneg_right
            (hmode timeScale mode w hw)
            (norm_nonneg _)).trans_eq (by
              simp only [majorant]
              ring)
      · exact hmajorant
    _ ≤ (∑' mode, majorant mode) + 1 := by
      linarith

/-- The actual original-OS root-smeared family has its canonical
packet-scale distributional real trace on a nonempty positive-real patch. -/
theorem
    exists_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_mul
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ∃ (L : SchwartzNPoint d k →L[ℂ] ℂ)
        (V : Set (Fin k → ℝ)),
      IsOpen V ∧ V.Nonempty ∧
        (∀ ξ ∈ V,
          osiiPositiveRealTimeEmbed ξ ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ h : SchwartzMap (Fin k → ℝ) ℂ,
          SCV.SupportsInOpen (h : (Fin k → ℝ) → ℂ) V →
            Tendsto
              (fun timeScale =>
                ∫ ξ : Fin k → ℝ,
                  D.rootSmearedSpatialHermiteGeneratorSumOfOS
                      i timeScale
                      (osiiPositiveRealTimeEmbed ξ) F *
                    h ξ)
              atTop
              (𝓝
                (L (section43NPointTimeSpatialTensor d k
                  (generatorChronologicalPullbackTest i anchor h)
                  (section43SpatialHeadMarginal F)))) := by
  exact
    D.exists_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_mul
      i F

end RootedA0BlockContinuousTranslationData

namespace RootedA0BlockHolomorphicTranslationData

/-- Once its genuine distributional real trace is supplied, the original-OS
rooted packet family has a locally uniform holomorphic Vitali limit. -/
theorem
    exists_tendstoLocallyUniformlyOn_rootSmearedSpatialHermiteGeneratorSumOfOS_packetScale_of_distributionalRealEdge
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (V : Set (Fin k → ℝ))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_domain :
      ∀ ξ ∈ V,
        osiiPositiveRealTimeEmbed ξ ∈
          generatorSemigroupDomain i
            (H.toContinuousTranslationData.left i).domain
            (H.toContinuousTranslationData.right i).domain)
    (hreal :
      ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
          Tendsto
            (fun timeScale =>
              ∫ ξ : Fin k → ℝ,
                H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
                    i timeScale
                    (osiiPositiveRealTimeEmbed ξ) F *
                  φ ξ)
            atTop
            (𝓝
              (L (section43NPointTimeSpatialTensor d k
                (generatorChronologicalPullbackTest i anchor φ)
                (section43SpatialHeadMarginal F))))) :
    let D := H.toContinuousTranslationData
    let U :=
      generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain
    ∃ limit : OSIITimeGapSpace k → ℂ,
      TendstoLocallyUniformlyOn
        (fun timeScale z =>
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
            i timeScale z F)
        limit atTop U ∧
      DifferentiableOn ℂ limit U ∧
      ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
        SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
          ∫ ξ : Fin k → ℝ,
              limit (osiiPositiveRealTimeEmbed ξ) * φ ξ =
            L (section43NPointTimeSpatialTensor d k
              (generatorChronologicalPullbackTest i anchor φ)
              (section43SpatialHeadMarginal F)) := by
  let D := H.toContinuousTranslationData
  let U :=
    generatorSemigroupDomain i
      (D.left i).domain (D.right i).domain
  have hU_open : IsOpen U := by
    exact
      isOpen_generatorSemigroupDomain i
        (H.left i).domain_open (H.right i).domain_open
  have hU_convex : Convex ℝ U := by
    apply convex_generatorSemigroupDomain i
    · intro x hx y hy a b ha hb hab
      change star (a • x + b • y) ∈ (H.left i).domain
      simpa using (H.left i).domain_convex hx hy ha hb hab
    · exact (H.right i).domain_convex
  have hU_ne : U.Nonempty := by
    obtain ⟨ξ, hξ⟩ := hV_ne
    exact ⟨osiiPositiveRealTimeEmbed ξ, hV_domain ξ hξ⟩
  have hU_conn : IsConnected U :=
    hU_convex.isConnected hU_ne
  obtain ⟨limit, hlimit, hlimit_hol, hlimit_real⟩ :=
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_bounded_holomorphic_of_distributional_real_limit
      (F := fun timeScale z =>
        D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale z F)
      (U := U)
      (V := V)
      (T := fun φ =>
        L (section43NPointTimeSpatialTensor d k
          (generatorChronologicalPullbackTest i anchor φ)
          (section43SpatialHeadMarginal F)))
      hU_open hU_conn hV_open hV_ne hV_domain
      (fun timeScale =>
        H.differentiableOn_rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale F)
      (fun K hK_compact hK_domain =>
        D.exists_rootSmearedSpatialHermiteGeneratorSumOfOS_norm_bound_on_complex_compact
          i K hK_compact hK_domain F)
      hreal
  exact ⟨limit, hlimit, hlimit_hol, hlimit_real⟩

/-- The genuine original-OS rooted packet family has a locally uniform
holomorphic limit with the exact distributional Schwinger real edge. -/
theorem
    exists_tendstoLocallyUniformlyOn_rootSmearedSpatialHermiteGeneratorSumOfOS_packetScale
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    let D := H.toContinuousTranslationData
    let U :=
      generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain
    ∃ (limit : OSIITimeGapSpace k → ℂ)
        (L : SchwartzNPoint d k →L[ℂ] ℂ)
        (V : Set (Fin k → ℝ)),
      IsOpen V ∧ V.Nonempty ∧
        (∀ ξ ∈ V, osiiPositiveRealTimeEmbed ξ ∈ U) ∧
        TendstoLocallyUniformlyOn
          (fun timeScale z =>
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale z F)
          limit atTop U ∧
        DifferentiableOn ℂ limit U ∧
        ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
          SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
            ∫ ξ : Fin k → ℝ,
                limit (osiiPositiveRealTimeEmbed ξ) * φ ξ =
              L (section43NPointTimeSpatialTensor d k
                (generatorChronologicalPullbackTest i anchor φ)
                (section43SpatialHeadMarginal F)) := by
  let D := H.toContinuousTranslationData
  obtain ⟨L, V, hV_open, hV_ne, hV_domain, hreal⟩ :=
    D.exists_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_mul
      i F
  obtain ⟨limit, hlimit, hlimit_hol, hlimit_real⟩ :=
    H.exists_tendstoLocallyUniformlyOn_rootSmearedSpatialHermiteGeneratorSumOfOS_packetScale_of_distributionalRealEdge
      i F L V hV_open hV_ne hV_domain hreal
  exact
    ⟨limit, L, V, hV_open, hV_ne, hV_domain,
      hlimit, hlimit_hol, hlimit_real⟩

end RootedA0BlockHolomorphicTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
