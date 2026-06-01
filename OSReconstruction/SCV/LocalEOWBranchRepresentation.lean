import OSReconstruction.SCV.LocalEOWChartAssembly
import OSReconstruction.SCV.DistributionalRepresentationGluing

/-!
# Local EOW Branch Representation Extraction

The fixed-window local EOW assembly theorem constructs a recovered chart
representative and proves equality with the explicit plus/minus side branches.
This file extracts the branch-level `RepresentsDistributionOnComplexDomain`
statements used by the OS-II Malgrange-Zerner gluing handoff.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

variable {m : ℕ}

/-- Branch-representation form of the fixed-window local EOW assembly.

This is the precise extraction needed after OS II `(5.7)`--`(5.8)` supplies the
raw side boundary-value limits: the explicit side branches themselves represent
the recovered distribution on the strict side balls. -/
theorem regularizedLocalEOW_branchRepresentations_from_fixedWindowScale
    {Cplus Cminus : Set (Fin m → ℝ)}
    {rψLarge rψOne ρ r δ σ : ℝ}
    (hm : 0 < m) (hδ : 0 < δ) (hσ : 0 < σ)
    (hδscale : 128 * σ ≤ δ)
    (hσρ : 4 * σ ≤ ρ)
    (hcardσ : (Fintype.card (Fin m) : ℝ) * (4 * σ) < r)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E Kreal : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (hDplus_Ω : Dplus ⊆ Ωplus)
    (hDminus_Ω : Dminus ⊆ Ωminus)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hKreal_compact : IsCompact Kreal)
    (hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ Kreal)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χU : SchwartzMap (ComplexChartSpace m) ℂ)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) (8 * σ),
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
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne)
    (hrψ_one_large : rψOne ≤ rψLarge) :
    let FplusCoord : ComplexChartSpace m → ℂ :=
      fun ζ => Fplus (localEOWChart x0 ys ζ)
    let FminusCoord : ComplexChartSpace m → ℂ :=
      fun ζ => Fminus (localEOWChart x0 ys ζ)
    ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
      RepresentsDistributionOnComplexDomain Hdist FplusCoord
        (StrictPositiveImagBall (m := m) σ) ∧
      RepresentsDistributionOnComplexDomain Hdist FminusCoord
        (StrictNegativeImagBall (m := m) σ) := by
  dsimp only
  rcases
    regularizedLocalEOW_chartEnvelope_from_fixedWindowScale
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
      hA4_one hrψ_one_large with
    ⟨_K, H, _hH_diff, Hdist, hHdist, _hK_rep, hplus_eq, hminus_eq⟩
  refine ⟨Hdist, ?_, ?_⟩
  · simpa [RepresentsDistributionOnComplexDomain, RepresentsDistributionOn] using
      representsDistributionOn_congr_on_subset
        (T := Hdist) (H := H) (H' := fun ζ => Fplus (localEOWChart x0 ys ζ))
        (U := Metric.ball (0 : ComplexChartSpace m) (4 * σ))
        (V := StrictPositiveImagBall (m := m) σ)
        (by
          simpa [RepresentsDistributionOnComplexDomain,
            RepresentsDistributionOn] using hHdist)
        hplus_eq
        (by
          intro z hz
          exact Metric.ball_subset_ball (by nlinarith : σ ≤ 4 * σ) hz.1)
  · simpa [RepresentsDistributionOnComplexDomain, RepresentsDistributionOn] using
      representsDistributionOn_congr_on_subset
        (T := Hdist) (H := H) (H' := fun ζ => Fminus (localEOWChart x0 ys ζ))
        (U := Metric.ball (0 : ComplexChartSpace m) (4 * σ))
        (V := StrictNegativeImagBall (m := m) σ)
        (by
          simpa [RepresentsDistributionOnComplexDomain,
            RepresentsDistributionOn] using hHdist)
        hminus_eq
        (by
          intro z hz
          exact Metric.ball_subset_ball (by nlinarith : σ ≤ 4 * σ) hz.1)

end SCV
