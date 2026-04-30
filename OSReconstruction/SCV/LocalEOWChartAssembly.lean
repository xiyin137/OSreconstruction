/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalEOWChartRecovery

/-!
# One-Chart Distributional EOW Assembly Adapters

This file contains the small adapters that assemble the checked fixed-window
local EOW family into the exact chart-kernel inputs expected by the scaled
one-chart recovery theorem.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

variable {m : ℕ}

/-- Fixed-window outputs transported to chart kernels.

The theorem packages the three chart-family fields needed by the one-chart
scaled recovery theorem: holomorphy of `Gchart`, plus and minus side identities
against the pulled-back side functions.  The support of the pushed original
kernel is discharged by the one-chart `4 * σ` support budget. -/
theorem regularizedLocalEOW_chartKernelFamily_outputs_from_fixedWindow
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ rchart σ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
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
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
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
    (hli : LinearIndependent ℝ ys)
    (hrchart_le : rchart ≤ 4 * σ)
    (hA4 :
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψ) :
    let Gchart : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
      fun ψ z =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus
            (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
          (realMollifyLocal Fminus
            (localEOWRealLinearKernelPushforwardCLM ys hli ψ)) z
    let FplusCoord : ComplexChartSpace m → ℂ :=
      fun ζ => Fplus (localEOWChart x0 ys ζ)
    let FminusCoord : ComplexChartSpace m → ℂ :=
      fun ζ => Fminus (localEOWChart x0 ys ζ)
    (∀ ψ, KernelSupportWithin ψ rchart →
      DifferentiableOn ℂ (Gchart ψ)
        (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) ∧
    (∀ ψ, KernelSupportWithin ψ rchart →
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          Gchart ψ w = realMollifyLocal FplusCoord ψ w) ∧
    (∀ ψ, KernelSupportWithin ψ rchart →
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, (w j).im < 0) →
          Gchart ψ w = realMollifyLocal FminusCoord ψ w) := by
  dsimp only
  let P : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    localEOWRealLinearKernelPushforwardCLM ys hli
  let Gorig : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun η z =>
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus η) (realMollifyLocal Fminus η) z
  have hfamily :=
    regularizedLocalEOW_family_from_fixedWindow
      (m := m) (Cplus := Cplus) (Cminus := Cminus) (rψ := rψ)
      (ρ := ρ) (r := r) (δ := δ) hm Ωplus Ωminus Dplus Dminus E
      hΩplus_open hΩminus_open hDplus_open hDminus_open hE_open Fplus Fminus
      hFplus_diff hFminus_diff hplus_margin hminus_margin hDplus_sub
      hDminus_sub Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit
      hminus_limit x0 ys hδ hδρ hδsum hE_mem hplus hminus
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ
    have hPψ : KernelSupportWithin (P ψ) rψ :=
      KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul
        ys hli hψ hrchart_le hA4
    simpa [P, Gorig] using hfamily.1 (P ψ) hPψ
  · intro ψ hψ w hw hwpos
    have hPψ : KernelSupportWithin (P ψ) rψ :=
      KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul
        ys hli hψ hrchart_le hA4
    have hside := (hfamily.2.1 (P ψ) hPψ w hw hwpos).2
    calc
      localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus (P ψ))
          (realMollifyLocal Fminus (P ψ)) w
          = realMollifyLocal Fplus (P ψ) (localEOWChart x0 ys w) := by
              simpa [P, Gorig] using hside
      _ = realMollifyLocal (fun ζ => Fplus (localEOWChart x0 ys ζ)) ψ w := by
              simpa [P] using
                realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback
                  Fplus x0 ys hli ψ w
  · intro ψ hψ w hw hwneg
    have hPψ : KernelSupportWithin (P ψ) rψ :=
      KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul
        ys hli hψ hrchart_le hA4
    have hside := (hfamily.2.2.1 (P ψ) hPψ w hw hwneg).2
    calc
      localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus (P ψ))
          (realMollifyLocal Fminus (P ψ)) w
          = realMollifyLocal Fminus (P ψ) (localEOWChart x0 ys w) := by
              simpa [P, Gorig] using hside
      _ = realMollifyLocal (fun ζ => Fminus (localEOWChart x0 ys ζ)) ψ w := by
              simpa [P] using
                realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback
                  Fminus x0 ys hli ψ w

/-- Continuity of the pulled-back side functions on the strict side balls used
by the scaled one-chart recovery theorem. -/
theorem chartSideFunction_continuousOn_strictBalls_from_fixedWindow
    {ρ r σ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hRρ : 4 * σ ≤ ρ)
    (hcardR : (Fintype.card (Fin m) : ℝ) * (4 * σ) < r)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
    ContinuousOn (fun ζ => Fplus (localEOWChart x0 ys ζ))
      (StrictPositiveImagBall (m := m) (4 * σ)) ∧
    ContinuousOn (fun ζ => Fminus (localEOWChart x0 ys ζ))
      (StrictNegativeImagBall (m := m) (4 * σ)) := by
  constructor
  · have hmem : ∀ w ∈ StrictPositiveImagBall (m := m) (4 * σ),
        localEOWChart x0 ys w ∈ Ωplus := by
      intro w hw
      exact localEOWChart_mem_fixedWindow_of_strictPositiveImagBall
        (m := m) hm Ωplus x0 ys hRρ hcardR hplus hw
    exact (chartHolomorphy_from_originalHolomorphy Ωplus x0 ys Fplus
      (StrictPositiveImagBall (m := m) (4 * σ)) hmem hFplus_diff).continuousOn
  · have hmem : ∀ w ∈ StrictNegativeImagBall (m := m) (4 * σ),
        localEOWChart x0 ys w ∈ Ωminus := by
      intro w hw
      exact localEOWChart_mem_fixedWindow_of_strictNegativeImagBall
        (m := m) hm Ωminus x0 ys hRρ hcardR hminus hw
    exact (chartHolomorphy_from_originalHolomorphy Ωminus x0 ys Fminus
      (StrictNegativeImagBall (m := m) (4 * σ)) hmem hFminus_diff).continuousOn

end SCV
