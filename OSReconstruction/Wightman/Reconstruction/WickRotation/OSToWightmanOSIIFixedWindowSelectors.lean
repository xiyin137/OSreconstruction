import OSReconstruction.SCV.LocalEOWBranchRepresentation
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity

/-!
# OS-II Fixed-Window Branch Representations from Section 4.3 Selectors

This file records the OS II V.1 `(5.7)`--`(5.8)` handoff from concrete
Section 4.3 product-kernel selector data to the fixed-window local EOW branch
representations.

The theorem deliberately keeps the OS-specific hypotheses exposed: the actual
weighted axis-pair/Malgrange-Zerner family must still supply quotient descent,
strict-positive product-kernel selector convergence, pointwise boundedness, and
the side integral identities.
-/

noncomputable section

open Complex Topology MeasureTheory Metric Set Filter
open scoped Classical NNReal BigOperators LineDeriv

namespace OSReconstruction

private instance instTimeSchwartzCompatibleSMul {m : ℕ} :
    LinearMap.CompatibleSMul (SchwartzMap (Fin m → ℝ) ℂ) ℂ ℝ ℂ where
  map_smul := by
    intro f r x
    have hx : r • x = (r : ℂ) • x := by
      ext t
      simp
    rw [hx]
    simpa using f.map_smul (r : ℂ) x

/-- Fixed-window local EOW branch representations from Section 4.3 selector
data.

This is the production form of the dense-boundary/local-EOW assembly.  Once the
raw side CLMs for a concrete branch family have product-kernel selector limits
on the strict positive time region, quotient descent, and pointwise
Banach-Steinhaus bounds, the explicit plus/minus branches represent the common
boundary distribution on the strict side balls. -/
theorem osiiFixedWindow_branchRepresentations_from_section43_selectors
    {m : ℕ} [Nonempty (Fin m)]
    {Cplus Cminus : Set (Fin m → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin m → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin m → ℝ))]
    {rψLarge rψOne ρ r δ σ : ℝ}
    (hm : 0 < m) (hδ : 0 < δ) (hσ : 0 < σ)
    (hδscale : 128 * σ ≤ δ)
    (hσρ : 4 * σ ≤ ρ)
    (hcardσ : (Fintype.card (Fin m) : ℝ) * (4 * σ) < r)
    (Ωplus Ωminus Dplus Dminus : Set (SCV.ComplexChartSpace m))
    (E Kreal : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (hDplus_Ω : Dplus ⊆ Ωplus)
    (hDminus_Ω : Dminus ⊆ Ωminus)
    (Fplus Fminus : SCV.ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ SCV.TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ SCV.TubeDomain Cminus)
    (TplusC TminusC :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hTplus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), Tplus y φ = TplusC y φ)
    (hTminus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), Tminus y φ = TminusC y φ)
    (hTplus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        Tplus y φ = Tplus y ψ)
    (hTminus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        Tminus y φ = Tminus y ψ)
    (hTchart_desc :
      ∀ φ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        (Tchart.restrictScalars ℝ) φ = (Tchart.restrictScalars ℝ) ψ)
    (hplus_kernel :
      ∀ ξ : Fin m → ℝ,
        ξ ∈ section43TimeStrictPositiveRegion m →
        Tendsto
          (fun y : Fin m → ℝ =>
            TplusC y (section43TimeImagAxisProductKernel ξ))
          (𝓝[Cplus] (0 : Fin m → ℝ))
          (nhds (Tchart (section43TimeImagAxisProductKernel ξ))))
    (hminus_kernel :
      ∀ ξ : Fin m → ℝ,
        ξ ∈ section43TimeStrictPositiveRegion m →
        Tendsto
          (fun y : Fin m → ℝ =>
            TminusC y (section43TimeImagAxisProductKernel ξ))
          (𝓝[Cminus] (0 : Fin m → ℝ))
          (nhds (Tchart (section43TimeImagAxisProductKernel ξ))))
    (hplus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(Tplus y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hminus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(Tminus y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, SCV.KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dplus,
          SCV.realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, SCV.KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dminus,
          SCV.realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ E)
    (hKreal_compact : IsCompact Kreal)
    (hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ Kreal)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          SCV.localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          SCV.localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χU : SchwartzMap (SCV.ComplexChartSpace m) ℂ)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : SCV.ComplexChartSpace m) (8 * σ),
        χU z = 1)
    (hχr_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) (2 * σ), χr t = 1)
    (hχr_support :
      tsupport (χr : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 (4 * σ))
    (hχψ_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψOne, χψ t = 1)
    (hχψ_support :
      tsupport (χψ : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rψLarge)
    (hA4_one :
      ‖(SCV.localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne)
    (hrψ_one_large : rψOne ≤ rψLarge) :
    let FplusCoord : SCV.ComplexChartSpace m → ℂ :=
      fun ζ => Fplus (SCV.localEOWChart x0 ys ζ)
    let FminusCoord : SCV.ComplexChartSpace m → ℂ :=
      fun ζ => Fminus (SCV.localEOWChart x0 ys ζ)
    ∃ Hdist : SchwartzMap (SCV.ComplexChartSpace m) ℂ →L[ℂ] ℂ,
      SCV.RepresentsDistributionOnComplexDomain Hdist FplusCoord
        (SCV.StrictPositiveImagBall (m := m) σ) ∧
      SCV.RepresentsDistributionOnComplexDomain Hdist FminusCoord
        (SCV.StrictNegativeImagBall (m := m) σ) := by
  have hTchart_apply :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        (Tchart.restrictScalars ℝ) φ = Tchart φ := by
    intro φ
    rfl
  have hplus_limit :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y φ) (𝓝[Cplus] (0 : Fin m → ℝ))
          (nhds ((Tchart.restrictScalars ℝ) φ)) := by
    let l : Filter (Fin m → ℝ) := 𝓝[Cplus] (0 : Fin m → ℝ)
    have hl_cg : l.IsCountablyGenerated := by infer_instance
    have hl_neBot : NeBot l := by infer_instance
    letI : l.IsCountablyGenerated := hl_cg
    letI : NeBot l := hl_neBot
    exact
      section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
        (n := m) (l := l)
        (TseqC := TplusC) (TC := Tchart)
        (TseqR := Tplus) (TR := Tchart.restrictScalars ℝ)
        hTplus_apply hTchart_apply hTplus_desc hTchart_desc
        (by
          intro ξ hξ
          simpa [l] using hplus_kernel ξ hξ)
        hplus_pointwise_bounded
  have hminus_limit :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y φ) (𝓝[Cminus] (0 : Fin m → ℝ))
          (nhds ((Tchart.restrictScalars ℝ) φ)) := by
    let l : Filter (Fin m → ℝ) := 𝓝[Cminus] (0 : Fin m → ℝ)
    have hl_cg : l.IsCountablyGenerated := by infer_instance
    have hl_neBot : NeBot l := by infer_instance
    letI : l.IsCountablyGenerated := hl_cg
    letI : NeBot l := hl_neBot
    exact
      section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
        (n := m) (l := l)
        (TseqC := TminusC) (TC := Tchart)
        (TseqR := Tminus) (TR := Tchart.restrictScalars ℝ)
        hTminus_apply hTchart_apply hTminus_desc hTchart_desc
        (by
          intro ξ hξ
          simpa [l] using hminus_kernel ξ hξ)
        hminus_pointwise_bounded
  exact
    SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale
      (m := m) (Cplus := Cplus) (Cminus := Cminus)
      (rψLarge := rψLarge) (rψOne := rψOne) (ρ := ρ)
      (r := r) (δ := δ) (σ := σ) hm hδ hσ hδscale hσρ hcardσ
      Ωplus Ωminus Dplus Dminus E Kreal hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open hDplus_Ω hDminus_Ω
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin_closed
      hminus_margin_closed hDplus_sub hDminus_sub Tplus Tminus Tchart
      hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hli hδρ
      hδsum hE_mem hKreal_compact hKreal_mem hplus hminus
      χU χr χψ hχU_one hχr_one hχr_support hχψ_one hχψ_support
      hA4_one hrψ_one_large

/-- Fixed-window slice CLMs from compact branch-integral selector data.

This is the production OS-II `(5.7)`--`(5.8)` bridge below local EOW.  It
keeps the concrete source-current facts exposed: moving and target compact
branch-integral identities, compact convergence and bounds, quotient descent,
pointwise boundedness, and the explicit side-integral representation of the
branch.  These data give the raw compact boundary values needed by
`SCV.localEOWSliceCLMs_from_preparedDomains`. -/
theorem osiiFixedWindow_sliceCLMs_from_branch_integral_compact_representatives
    {m : ℕ} [Nonempty (Fin m)]
    {Cplus Cminus E : Set (Fin m → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin m → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin m → ℝ))]
    {rψ ρ : ℝ}
    (Ωplus Ωminus Dplus Dminus : Set (SCV.ComplexChartSpace m))
    (Fplus Fminus : SCV.ComplexChartSpace m → ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (TplusC TminusC :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (TplusR TminusR :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (KplusSeq KminusSeq : (Fin m → ℝ) → (Fin m → ℝ) → ℂ)
    (Kplus Kminus : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (χcoord : SchwartzMap (Fin m → ℝ) ℂ)
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hχcoord_compact : HasCompactSupport (χcoord : (Fin m → ℝ) → ℂ))
    (hχ_support_E :
      tsupport
        (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
          (Fin m → ℝ) → ℂ) ⊆ E)
    (hχcoord_one :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) (3 * ρ),
        χcoord u = 1)
    (hplus_margin :
      ∀ y ∈ Cplus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωplus)
    (hminus_margin :
      ∀ y ∈ Cminus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ SCV.TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ SCV.TubeDomain Cminus)
    (hDplus_window :
      Dplus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρ))
    (hDminus_window :
      Dminus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρ))
    (hsmall :
      ∀ t : Fin m → ℝ, ‖t‖ ≤ rψ →
        ‖(SCV.localEOWRealLinearCLE ys hli).symm t‖ < ρ)
    (hTplus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), TplusR y φ = TplusC y φ)
    (hTminus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), TminusR y φ = TminusC y φ)
    (hTplus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        TplusR y φ = TplusR y ψ)
    (hTminus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        TminusR y φ = TminusR y ψ)
    (hTchart_desc :
      ∀ φ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        (Tchart.restrictScalars ℝ) φ = (Tchart.restrictScalars ℝ) ψ)
    (hplus_seq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ),
          TplusC y (section43IteratedLaplaceSchwartzRepresentative m g) =
            ∫ τ : Fin m → ℝ, KplusSeq y τ * g.f τ)
    (hminus_seq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ),
          TminusC y (section43IteratedLaplaceSchwartzRepresentative m g) =
            ∫ τ : Fin m → ℝ, KminusSeq y τ * g.f τ)
    (hplus_target_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        Tchart (section43IteratedLaplaceSchwartzRepresentative m g) =
          ∫ τ : Fin m → ℝ, Kplus τ * g.f τ)
    (hminus_target_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        Tchart (section43IteratedLaplaceSchwartzRepresentative m g) =
          ∫ τ : Fin m → ℝ, Kminus τ * g.f τ)
    (hplus_meas :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ),
          AEStronglyMeasurable
            (fun τ : Fin m → ℝ => KplusSeq y τ * g.f τ)
            (volume : Measure (Fin m → ℝ)))
    (hminus_meas :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ),
          AEStronglyMeasurable
            (fun τ : Fin m → ℝ => KminusSeq y τ * g.f τ)
            (volume : Measure (Fin m → ℝ)))
    (hplus_lim :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ τ : Fin m → ℝ,
          τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
            Tendsto (fun y : Fin m → ℝ => KplusSeq y τ)
              (𝓝[Cplus] (0 : Fin m → ℝ)) (nhds (Kplus τ)))
    (hminus_lim :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ τ : Fin m → ℝ,
          τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
            Tendsto (fun y : Fin m → ℝ => KminusSeq y τ)
              (𝓝[Cminus] (0 : Fin m → ℝ)) (nhds (Kminus τ)))
    (hplus_bound :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ), ∀ τ : Fin m → ℝ,
            τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
              ‖KplusSeq y τ‖ ≤ C)
    (hminus_bound :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ), ∀ τ : Fin m → ℝ,
            τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
              ‖KminusSeq y τ‖ ≤ C)
    (hplus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(TplusR y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hminus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(TminusR y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hplus_integral :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ),
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
        TplusR y φ =
          ∫ x : Fin m → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x)
    (hminus_integral :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ),
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
        TminusR y φ =
          ∫ x : Fin m → ℝ,
            Fminus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x) :
    let χ : SchwartzMap (Fin m → ℝ) ℂ :=
      SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord
    let Tcut : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
      Tchart.comp (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ))
    ∃ Tplus Tminus :
        (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      (∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, SCV.KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          SCV.realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ)) ∧
      (∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, SCV.KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          SCV.realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ)) ∧
      (∀ φ, Tendsto (fun y => Tplus y φ) (𝓝[Cplus] (0 : Fin m → ℝ))
        (nhds (((Tcut).restrictScalars ℝ) φ))) ∧
      (∀ φ, Tendsto (fun y => Tminus y φ) (𝓝[Cminus] (0 : Fin m → ℝ))
        (nhds (((Tcut).restrictScalars ℝ) φ))) := by
  have hTchart_apply :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        (Tchart.restrictScalars ℝ) φ = Tchart φ := by
    intro φ
    rfl
  have hplus_bv :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          Tendsto (fun y : Fin m → ℝ =>
            ∫ x : Fin m → ℝ,
              Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
                Complex.I) * φ x)
            (𝓝[Cplus] (0 : Fin m → ℝ))
            (nhds ((Tchart.restrictScalars ℝ) φ)) := by
    exact
      section43_tendsto_localEOW_boundary_integral_of_branch_integral_compact_representatives
        (n := m) (Cplus := Cplus) (E := E) (Fplus := Fplus)
        TplusC Tchart TplusR (Tchart.restrictScalars ℝ)
        KplusSeq Kplus hTplus_apply hTchart_apply hTplus_desc hTchart_desc
        hplus_seq_eval hplus_target_eval hplus_meas hplus_lim hplus_bound
        hplus_pointwise_bounded hplus_integral
  have hminus_bv :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          Tendsto (fun y : Fin m → ℝ =>
            ∫ x : Fin m → ℝ,
              Fminus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
                Complex.I) * φ x)
            (𝓝[Cminus] (0 : Fin m → ℝ))
            (nhds ((Tchart.restrictScalars ℝ) φ)) := by
    exact
      section43_tendsto_localEOW_boundary_integral_of_branch_integral_compact_representatives
        (n := m) (Cplus := Cminus) (E := E) (Fplus := Fminus)
        TminusC Tchart TminusR (Tchart.restrictScalars ℝ)
        KminusSeq Kminus hTminus_apply hTchart_apply hTminus_desc hTchart_desc
        hminus_seq_eval hminus_target_eval hminus_meas hminus_lim hminus_bound
        hminus_pointwise_bounded hminus_integral
  simpa using
    SCV.localEOWSliceCLMs_from_preparedDomains
      (m := m) (Cplus := Cplus) (Cminus := Cminus) (E := E)
      (rψ := rψ) (ρ := ρ) Ωplus Ωminus Dplus Dminus
      Fplus Fminus Tchart x0 ys hli χcoord hΩplus_open hΩminus_open
      hFplus_diff hFminus_diff hχcoord_compact hχ_support_E
      hχcoord_one hplus_margin hminus_margin hDplus_sub hDminus_sub
      hDplus_window hDminus_window hsmall hplus_bv hminus_bv

/-- Fixed-window local EOW branch representations from compact branch-integral
selector data.

This is the assembly form after OS II `(5.7)`--`(5.8)`: compact
branch-integral identities and bounds first produce the prepared side slice
CLMs, and those slice CLMs feed the fixed-window local EOW theorem.  The
remaining OS-specific inputs are exactly the concrete branch-integral facts for
the actual weighted axis-pair/MZ branch family. -/
theorem osiiFixedWindow_branchRepresentations_from_branch_integral_compact_representatives
    {m : ℕ} [Nonempty (Fin m)]
    {Cplus Cminus E : Set (Fin m → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin m → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin m → ℝ))]
    {rψLarge rψOne ρ r δ σ : ℝ}
    (hm : 0 < m) (hδ : 0 < δ) (hσ : 0 < σ)
    (hδscale : 128 * σ ≤ δ)
    (hσρ : 4 * σ ≤ ρ)
    (hcardσ : (Fintype.card (Fin m) : ℝ) * (4 * σ) < r)
    (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (Ωplus Ωminus Dplus Dminus : Set (SCV.ComplexChartSpace m))
    (Kreal : Set (Fin m → ℝ))
    (Fplus Fminus : SCV.ComplexChartSpace m → ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (TplusC TminusC :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (TplusR TminusR :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (KplusSeq KminusSeq : (Fin m → ℝ) → (Fin m → ℝ) → ℂ)
    (Kplus Kminus : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (χcoord : SchwartzMap (Fin m → ℝ) ℂ)
    (χU : SchwartzMap (SCV.ComplexChartSpace m) ℂ)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus)
    (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (hDplus_Ω : Dplus ⊆ Ωplus)
    (hDminus_Ω : Dminus ⊆ Ωminus)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hχcoord_compact : HasCompactSupport (χcoord : (Fin m → ℝ) → ℂ))
    (hχ_support_E :
      tsupport
        (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
          (Fin m → ℝ) → ℂ) ⊆ E)
    (hχcoord_one :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) (3 * ρ),
        χcoord u = 1)
    (hplus_margin :
      ∀ y ∈ Cplus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωplus)
    (hminus_margin :
      ∀ y ∈ Cminus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ SCV.TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ SCV.TubeDomain Cminus)
    (hDplus_window :
      Dplus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρ))
    (hDminus_window :
      Dminus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρ))
    (hsmall :
      ∀ t : Fin m → ℝ, ‖t‖ ≤ rψLarge →
        ‖(SCV.localEOWRealLinearCLE ys hli).symm t‖ < ρ)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωminus)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ E)
    (hKreal_compact : IsCompact Kreal)
    (hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ Kreal)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          SCV.localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          SCV.localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : SCV.ComplexChartSpace m) (8 * σ),
        χU z = 1)
    (hχr_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) (2 * σ), χr t = 1)
    (hχr_support :
      tsupport (χr : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 (4 * σ))
    (hχψ_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψOne, χψ t = 1)
    (hχψ_support :
      tsupport (χψ : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rψLarge)
    (hA4_one :
      ‖(SCV.localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne)
    (hrψ_one_large : rψOne ≤ rψLarge)
    (hTplus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), TplusR y φ = TplusC y φ)
    (hTminus_apply :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ), TminusR y φ = TminusC y φ)
    (hTplus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        TplusR y φ = TplusR y ψ)
    (hTminus_desc :
      ∀ y (φ ψ : SchwartzMap (Fin m → ℝ) ℂ),
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        TminusR y φ = TminusR y ψ)
    (hTchart_desc :
      ∀ φ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        (Tchart.restrictScalars ℝ) φ = (Tchart.restrictScalars ℝ) ψ)
    (hplus_seq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ),
          TplusC y (section43IteratedLaplaceSchwartzRepresentative m g) =
            ∫ τ : Fin m → ℝ, KplusSeq y τ * g.f τ)
    (hminus_seq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ),
          TminusC y (section43IteratedLaplaceSchwartzRepresentative m g) =
            ∫ τ : Fin m → ℝ, KminusSeq y τ * g.f τ)
    (hplus_target_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        Tchart (section43IteratedLaplaceSchwartzRepresentative m g) =
          ∫ τ : Fin m → ℝ, Kplus τ * g.f τ)
    (hminus_target_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        Tchart (section43IteratedLaplaceSchwartzRepresentative m g) =
          ∫ τ : Fin m → ℝ, Kminus τ * g.f τ)
    (hplus_meas :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ),
          AEStronglyMeasurable
            (fun τ : Fin m → ℝ => KplusSeq y τ * g.f τ)
            (volume : Measure (Fin m → ℝ)))
    (hminus_meas :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ),
          AEStronglyMeasurable
            (fun τ : Fin m → ℝ => KminusSeq y τ * g.f τ)
            (volume : Measure (Fin m → ℝ)))
    (hplus_lim :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ τ : Fin m → ℝ,
          τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
            Tendsto (fun y : Fin m → ℝ => KplusSeq y τ)
              (𝓝[Cplus] (0 : Fin m → ℝ)) (nhds (Kplus τ)))
    (hminus_lim :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∀ τ : Fin m → ℝ,
          τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
            Tendsto (fun y : Fin m → ℝ => KminusSeq y τ)
              (𝓝[Cminus] (0 : Fin m → ℝ)) (nhds (Kminus τ)))
    (hplus_bound :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ y in 𝓝[Cplus] (0 : Fin m → ℝ), ∀ τ : Fin m → ℝ,
            τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
              ‖KplusSeq y τ‖ ≤ C)
    (hminus_bound :
      ∀ g : Section43CompactStrictPositiveTimeSource m,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ y in 𝓝[Cminus] (0 : Fin m → ℝ), ∀ τ : Fin m → ℝ,
            τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ) →
              ‖KminusSeq y τ‖ ≤ C)
    (hplus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(TplusR y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hminus_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin m → ℝ, ‖(TminusR y - Tchart.restrictScalars ℝ) φ‖ ≤ C)
    (hplus_integral :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ),
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
        TplusR y φ =
          ∫ x : Fin m → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x)
    (hminus_integral :
      ∀ y (φ : SchwartzMap (Fin m → ℝ) ℂ),
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
        TminusR y φ =
          ∫ x : Fin m → ℝ,
            Fminus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x) :
    let FplusCoord : SCV.ComplexChartSpace m → ℂ :=
      fun ζ => Fplus (SCV.localEOWChart x0 ys ζ)
    let FminusCoord : SCV.ComplexChartSpace m → ℂ :=
      fun ζ => Fminus (SCV.localEOWChart x0 ys ζ)
    ∃ Hdist : SchwartzMap (SCV.ComplexChartSpace m) ℂ →L[ℂ] ℂ,
      SCV.RepresentsDistributionOnComplexDomain Hdist FplusCoord
        (SCV.StrictPositiveImagBall (m := m) σ) ∧
      SCV.RepresentsDistributionOnComplexDomain Hdist FminusCoord
        (SCV.StrictNegativeImagBall (m := m) σ) := by
  classical
  intro FplusCoord FminusCoord
  let χ : SchwartzMap (Fin m → ℝ) ℂ :=
    SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord
  let Tcut : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    Tchart.comp (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ))
  rcases
    osiiFixedWindow_sliceCLMs_from_branch_integral_compact_representatives
      (m := m) (Cplus := Cplus) (Cminus := Cminus) (E := E)
      (rψ := rψLarge) (ρ := ρ)
      Ωplus Ωminus Dplus Dminus Fplus Fminus Tchart TplusC TminusC
      TplusR TminusR KplusSeq KminusSeq Kplus Kminus x0 ys hli χcoord
      hΩplus_open hΩminus_open hFplus_diff hFminus_diff
      hχcoord_compact hχ_support_E hχcoord_one hplus_margin hminus_margin
      hDplus_sub hDminus_sub hDplus_window hDminus_window hsmall
      hTplus_apply hTminus_apply hTplus_desc hTminus_desc hTchart_desc
      hplus_seq_eval hminus_seq_eval hplus_target_eval hminus_target_eval
      hplus_meas hminus_meas hplus_lim hminus_lim hplus_bound hminus_bound
      hplus_pointwise_bounded hminus_pointwise_bounded hplus_integral
      hminus_integral with
    ⟨Tplus, Tminus, hplus_eval, hminus_eval, hplus_limit, hminus_limit⟩
  exact
    SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale
      (m := m) (Cplus := Cplus) (Cminus := Cminus)
      (rψLarge := rψLarge) (rψOne := rψOne) (ρ := ρ)
      (r := r) (δ := δ) (σ := σ) hm hδ hσ hδscale hσρ hcardσ
      Ωplus Ωminus Dplus Dminus E Kreal hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open hDplus_Ω hDminus_Ω
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin_closed
      hminus_margin_closed hDplus_sub hDminus_sub Tplus Tminus Tcut
      hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hli
      hδρ hδsum hE_mem hKreal_compact hKreal_mem hplus hminus
      χU χr χψ hχU_one hχr_one hχr_support hχψ_one hχψ_support
      hA4_one hrψ_one_large

end OSReconstruction
