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

/-- The explicit prepared side domains used by the one-chart distributional
EOW assembly.

The two domains are the intersections of the original holomorphy domains, the
bounded local side tubes, and the inverse-affine real window.  The theorem
packages their openness, projection facts, and the fixed-window polywedge
membership hypotheses needed by the fixed-window family theorem. -/
theorem localEOWPreparedSideDomains_from_fixedWindow
    {ρ rpoly ε rside δside : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε)
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (hrδ : rpoly ≤ δside)
    (hδside :
      ∀ v : Fin m → ℝ, ‖v‖ < δside →
        ‖localEOWRealLinearPart ys v‖ < rside)
    (hplusΩ :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < rpoly →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
    (hminusΩ :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < rpoly →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
    let CplusLoc : Set (Fin m → ℝ) :=
      localEOWSideCone ys ε ∩ Metric.ball 0 rside
    let CminusLoc : Set (Fin m → ℝ) := Neg.neg '' CplusLoc
    let Dplus : Set (ComplexChartSpace m) :=
      Ωplus ∩ TubeDomain CplusLoc ∩
        localEOWAffineRealWindow x0 ys hli (2 * ρ)
    let Dminus : Set (ComplexChartSpace m) :=
      Ωminus ∩ TubeDomain CminusLoc ∩
        localEOWAffineRealWindow x0 ys hli (2 * ρ)
    IsOpen Dplus ∧ IsOpen Dminus ∧
    Dplus ⊆ Ωplus ∧ Dminus ⊆ Ωminus ∧
    Dplus ⊆ TubeDomain CplusLoc ∧ Dminus ⊆ TubeDomain CminusLoc ∧
    Dplus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) ∧
    Dminus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) ∧
    (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
      (∀ j, 0 ≤ v j) →
      0 < ∑ j, v j →
      (∑ j, v j) < rpoly →
        localEOWChart x0 ys
          (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus) ∧
    (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
      (∀ j, v j ≤ 0) →
      0 < ∑ j, -v j →
      (∑ j, -v j) < rpoly →
        localEOWChart x0 ys
          (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) := by
  dsimp only
  let CplusLoc : Set (Fin m → ℝ) :=
    localEOWSideCone ys ε ∩ Metric.ball 0 rside
  let CminusLoc : Set (Fin m → ℝ) := Neg.neg '' CplusLoc
  let Dplus : Set (ComplexChartSpace m) :=
    Ωplus ∩ TubeDomain CplusLoc ∩
      localEOWAffineRealWindow x0 ys hli (2 * ρ)
  let Dminus : Set (ComplexChartSpace m) :=
    Ωminus ∩ TubeDomain CminusLoc ∩
      localEOWAffineRealWindow x0 ys hli (2 * ρ)
  have hCplusLoc_open : IsOpen CplusLoc := by
    dsimp [CplusLoc]
    exact (isOpen_localEOWSideCone ys ε).inter isOpen_ball
  have hCminusLoc_open : IsOpen CminusLoc := by
    dsimp [CminusLoc]
    exact isOpen_neg_image CplusLoc hCplusLoc_open
  have hDplus_open : IsOpen Dplus := by
    dsimp [Dplus]
    exact (hΩplus_open.inter (tubeDomain_isOpen hCplusLoc_open)).inter
      (isOpen_localEOWAffineRealWindow x0 ys hli (2 * ρ))
  have hDminus_open : IsOpen Dminus := by
    dsimp [Dminus]
    exact (hΩminus_open.inter (tubeDomain_isOpen hCminusLoc_open)).inter
      (isOpen_localEOWAffineRealWindow x0 ys hli (2 * ρ))
  have hDplus_Ω : Dplus ⊆ Ωplus := by
    intro z hz
    exact hz.1.1
  have hDminus_Ω : Dminus ⊆ Ωminus := by
    intro z hz
    exact hz.1.1
  have hDplus_tube : Dplus ⊆ TubeDomain CplusLoc := by
    intro z hz
    exact hz.1.2
  have hDminus_tube : Dminus ⊆ TubeDomain CminusLoc := by
    intro z hz
    exact hz.1.2
  have hDplus_window :
      Dplus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) := by
    intro z hz
    exact hz.2
  have hDminus_window :
      Dminus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) := by
    intro z hz
    exact hz.2
  have hnonneg_norm_lt :
      ∀ v : Fin m → ℝ, (∀ j, 0 ≤ v j) →
        (∑ j, v j) < rpoly → ‖v‖ < δside := by
    intro v hv_nonneg hv_sum_lt
    have hsum_nonneg : 0 ≤ ∑ j, v j :=
      Finset.sum_nonneg fun j _ => hv_nonneg j
    have hv_norm_le : ‖v‖ ≤ ∑ j, v j := by
      rw [pi_norm_le_iff_of_nonneg hsum_nonneg]
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hv_nonneg j)]
      exact Finset.single_le_sum (fun i _ => hv_nonneg i) (Finset.mem_univ j)
    exact lt_of_le_of_lt hv_norm_le (lt_of_lt_of_le hv_sum_lt hrδ)
  have hnonpos_norm_lt :
      ∀ v : Fin m → ℝ, (∀ j, v j ≤ 0) →
        (∑ j, -v j) < rpoly → ‖v‖ < δside := by
    intro v hv_nonpos hv_sum_lt
    let vneg : Fin m → ℝ := fun j => -v j
    have hvneg_nonneg : ∀ j, 0 ≤ vneg j := by
      intro j
      exact neg_nonneg.mpr (hv_nonpos j)
    have hvneg_norm_lt : ‖vneg‖ < δside :=
      hnonneg_norm_lt vneg hvneg_nonneg (by simpa [vneg] using hv_sum_lt)
    have hvnorm : ‖v‖ = ‖vneg‖ := by
      dsimp [vneg]
      rw [show (fun j : Fin m => -v j) = -v by
        ext j
        rfl]
      exact (norm_neg v).symm
    rwa [hvnorm]
  have hplus_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < rpoly →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus := by
    intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    let w : ComplexChartSpace m :=
      fun j => (u j : ℂ) + (v j : ℂ) * Complex.I
    have hΩ : localEOWChart x0 ys w ∈ Ωplus := by
      exact hplusΩ u hu v hv_nonneg hv_sum_pos hv_sum_lt
    have htube : localEOWChart x0 ys w ∈ TubeDomain CplusLoc := by
      change (fun i => (localEOWChart x0 ys w i).im) ∈ CplusLoc
      rw [localEOWChart_im_eq_realLinearPart_im]
      have hv_norm_lt : ‖v‖ < δside :=
        hnonneg_norm_lt v hv_nonneg hv_sum_lt
      have him_eq : (fun j : Fin m => (w j).im) = v := by
        ext j
        simp [w]
      rw [him_eq]
      constructor
      · exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
          hv_nonneg hv_sum_pos
      · rw [Metric.mem_ball, dist_zero_right]
        exact hδside v hv_norm_lt
    have hwindow :
        localEOWChart x0 ys w ∈
          localEOWAffineRealWindow x0 ys hli (2 * ρ) := by
      have hu_norm : ‖u‖ ≤ ρ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hu
      have hw_re : ‖(fun j : Fin m => (w j).re)‖ < 2 * ρ := by
        have hrew : (fun j : Fin m => (w j).re) = u := by
          ext j
          simp [w]
        rw [hrew]
        nlinarith [hu_norm, hρ]
      exact localEOWChart_mem_affineRealWindow_of_re_norm_lt
        x0 ys hli hw_re
    exact ⟨⟨hΩ, htube⟩, hwindow⟩
  have hminus_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < rpoly →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus := by
    intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    let w : ComplexChartSpace m :=
      fun j => (u j : ℂ) + (v j : ℂ) * Complex.I
    let vneg : Fin m → ℝ := fun j => -v j
    have hvneg_nonneg : ∀ j, 0 ≤ vneg j := by
      intro j
      exact neg_nonneg.mpr (hv_nonpos j)
    have hvneg_sum_pos : 0 < ∑ j, vneg j := by
      simpa [vneg] using hv_sum_pos
    have hvneg_sum_lt : (∑ j, vneg j) < rpoly := by
      simpa [vneg] using hv_sum_lt
    have hΩ : localEOWChart x0 ys w ∈ Ωminus := by
      exact hminusΩ u hu v hv_nonpos hv_sum_pos hv_sum_lt
    have htube : localEOWChart x0 ys w ∈ TubeDomain CminusLoc := by
      change (fun i => (localEOWChart x0 ys w i).im) ∈ CminusLoc
      rw [localEOWChart_im_eq_realLinearPart_im]
      have hvneg_norm_lt : ‖vneg‖ < δside :=
        hnonneg_norm_lt vneg hvneg_nonneg hvneg_sum_lt
      have him_eq : (fun j : Fin m => (w j).im) = v := by
        ext j
        simp [w]
      rw [him_eq]
      refine ⟨localEOWRealLinearPart ys vneg, ?_, ?_⟩
      · constructor
        · exact localEOWRealLinearPart_mem_localEOWSideCone ys hε
            hvneg_nonneg hvneg_sum_pos
        · rw [Metric.mem_ball, dist_zero_right]
          exact hδside vneg hvneg_norm_lt
      · have hv_eq : v = -vneg := by
          ext j
          simp [vneg]
        rw [hv_eq, localEOWRealLinearPart_neg]
    have hwindow :
        localEOWChart x0 ys w ∈
          localEOWAffineRealWindow x0 ys hli (2 * ρ) := by
      have hu_norm : ‖u‖ ≤ ρ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hu
      have hw_re : ‖(fun j : Fin m => (w j).re)‖ < 2 * ρ := by
        have hrew : (fun j : Fin m => (w j).re) = u := by
          ext j
          simp [w]
        rw [hrew]
        nlinarith [hu_norm, hρ]
      exact localEOWChart_mem_affineRealWindow_of_re_norm_lt
        x0 ys hli hw_re
    exact ⟨⟨hΩ, htube⟩, hwindow⟩
  change
    IsOpen Dplus ∧ IsOpen Dminus ∧
    Dplus ⊆ Ωplus ∧ Dminus ⊆ Ωminus ∧
    Dplus ⊆ TubeDomain CplusLoc ∧ Dminus ⊆ TubeDomain CminusLoc ∧
    Dplus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) ∧
    Dminus ⊆ localEOWAffineRealWindow x0 ys hli (2 * ρ) ∧
    (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
      (∀ j, 0 ≤ v j) →
      0 < ∑ j, v j →
      (∑ j, v j) < rpoly →
        localEOWChart x0 ys
          (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus) ∧
    (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
      (∀ j, v j ≤ 0) →
      0 < ∑ j, -v j →
      (∑ j, -v j) < rpoly →
        localEOWChart x0 ys
          (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
  exact ⟨hDplus_open, hDminus_open, hDplus_Ω, hDminus_Ω,
    hDplus_tube, hDminus_tube, hDplus_window, hDminus_window, hplus_mem,
    hminus_mem⟩

/-- Evaluating an affine pushed chart-coordinate test at the real part of an
original complex chart point evaluates the original test at the real part of
the inverse affine chart coordinate. -/
theorem localEOWAffineTestPushforwardCLM_apply_re
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (z : ComplexChartSpace m) :
    localEOWAffineTestPushforwardCLM x0 ys hli φ
        (fun j : Fin m => (z j).re) =
      φ (fun j : Fin m =>
        (((localEOWComplexAffineEquiv x0 ys hli).symm z) j).re) := by
  let A := localEOWComplexAffineEquiv x0 ys hli
  let q : ComplexChartSpace m := A.symm z
  have hchart : localEOWChart x0 ys q = z := by
    rw [← localEOWComplexAffineEquiv_apply x0 ys hli q]
    exact A.apply_symm_apply z
  have hq_decomp :
      (fun j : Fin m => ((q j).re : ℂ) + ((q j).im : ℂ) * Complex.I) = q := by
    ext j
    simp [Complex.re_add_im]
  have hreal_chart :
      localEOWRealChart x0 ys (fun j : Fin m => (q j).re) =
        (fun j : Fin m => (z j).re) := by
    have hdecomp :=
      localEOWChart_real_add_imag x0 ys
        (fun j : Fin m => (q j).re) (fun j : Fin m => (q j).im)
    rw [hq_decomp] at hdecomp
    have hreal := congrArg
      (fun f : ComplexChartSpace m => fun j : Fin m => (f j).re)
      (hdecomp.symm.trans hchart)
    ext j
    simpa using congrFun hreal j
  calc
    localEOWAffineTestPushforwardCLM x0 ys hli φ
        (fun j : Fin m => (z j).re) =
      localEOWAffineTestPushforwardCLM x0 ys hli φ
        (localEOWRealChart x0 ys (fun j : Fin m => (q j).re)) := by
        rw [hreal_chart]
    _ = φ (fun j : Fin m => (q j).re) := by
        simpa using
          localEOWAffineTestPushforwardCLM_apply_realChart
            x0 ys hli φ (fun j : Fin m => (q j).re)
    _ = φ (fun j : Fin m => ((A.symm z) j).re) := rfl

/-- A chart-coordinate cutoff equal to one on `closedBall 0 (3 * ρ)` remains
one after affine pushforward at `Re z + t`, provided `z` lies in the
`2 * ρ` affine real window and the inverse-chart displacement of `t` is
smaller than `ρ`. -/
theorem localEOWAffineCutoff_one_of_affineRealWindow_add
    {ρ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (χcoord : SchwartzMap (Fin m → ℝ) ℂ)
    (hχcoord_one :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) (3 * ρ),
        χcoord u = 1)
    {z : ComplexChartSpace m}
    (hz : z ∈ localEOWAffineRealWindow x0 ys hli (2 * ρ))
    {t : Fin m → ℝ}
    (ht : ‖(localEOWRealLinearCLE ys hli).symm t‖ < ρ) :
    localEOWAffineTestPushforwardCLM x0 ys hli χcoord
        (fun j : Fin m => (z j).re + t j) = 1 := by
  let zt : ComplexChartSpace m := z + realEmbed t
  have hzt_window :
      zt ∈ localEOWAffineRealWindow x0 ys hli (3 * ρ) := by
    simpa [zt] using
      localEOWAffineRealWindow_add_realEmbed x0 ys hli hz ht
  have hx_eq :
      (fun j : Fin m => (z j).re + t j) =
        (fun j : Fin m => (zt j).re) := by
    ext j
    simp [zt, realEmbed]
  rw [hx_eq]
  rw [localEOWAffineTestPushforwardCLM_apply_re]
  apply hχcoord_one
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (by
    simpa [localEOWAffineRealWindow, zt] using hzt_window)

/-- The affine pushed cutoff is one on the translated smoothing-kernel support
used by the slice-family theorem. -/
theorem localEOWAffineCutoff_one_on_translatedKernel
    {ρ rψ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (χcoord : SchwartzMap (Fin m → ℝ) ℂ)
    (hχcoord_one :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) (3 * ρ),
        χcoord u = 1)
    {z : ComplexChartSpace m}
    (hz : z ∈ localEOWAffineRealWindow x0 ys hli (2 * ρ))
    (hsmall :
      ∀ t : Fin m → ℝ, ‖t‖ ≤ rψ →
        ‖(localEOWRealLinearCLE ys hli).symm t‖ < ρ)
    {ψ : SchwartzMap (Fin m → ℝ) ℂ}
    (hψ : KernelSupportWithin ψ rψ)
    {x : Fin m → ℝ}
    (hx : x ∈ tsupport
      (translateSchwartz (fun j : Fin m => - (z j).re) ψ :
        (Fin m → ℝ) → ℂ)) :
    localEOWAffineTestPushforwardCLM x0 ys hli χcoord x = 1 := by
  let a : Fin m → ℝ := fun j => - (z j).re
  let t : Fin m → ℝ := x + a
  have hsub :
      tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘
          fun y : Fin m → ℝ => y + a) ⊆
        (fun y : Fin m → ℝ => y + a) ⁻¹'
          tsupport (ψ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage (ψ : (Fin m → ℝ) → ℂ)
      (continuous_id.add continuous_const)
  have hx' : x ∈ tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘
      fun y : Fin m → ℝ => y + a) := by
    simpa [a, translateSchwartz_apply] using hx
  have ht_support : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) := by
    simpa [t] using hsub hx'
  have ht_ball := hψ ht_support
  have ht_norm : ‖t‖ ≤ rψ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using ht_ball
  have hx_eq : x = fun j : Fin m => (z j).re + t j := by
    ext j
    simp [t, a]
  rw [hx_eq]
  exact localEOWAffineCutoff_one_of_affineRealWindow_add
    x0 ys hli χcoord hχcoord_one hz (hsmall t ht_norm)

/-- Assemble prepared fixed-window local EOW data into the scaled one-chart
recovery theorem.

This is the keystone below `chartDistributionalEOW_local_envelope`: the side
domains, slice CLMs, cutoffs, and scale inequalities are already prepared, but
the mixed pairing CLM, local covariance, descent kernel, and shrinking
approximate identity are constructed here. -/
theorem regularizedLocalEOW_chartEnvelope_from_fixedWindowScale
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
    ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ,
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H
          (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) ∧
        (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          SupportsInOpen (φ : ComplexChartSpace m → ℂ)
            (Metric.ball (0 : ComplexChartSpace m) (4 * σ)) →
          KernelSupportWithin ψ σ →
            K (schwartzTensorProduct₂ φ ψ) =
              Hdist (realConvolutionTest φ ψ)) ∧
        (∀ z ∈ StrictPositiveImagBall (m := m) σ, H z = FplusCoord z) ∧
        (∀ z ∈ StrictNegativeImagBall (m := m) σ, H z = FminusCoord z) := by
  dsimp only
  let D := Fin m → ℝ
  let X := ComplexChartSpace m
  let P : SchwartzMap D ℂ →L[ℂ] SchwartzMap D ℂ :=
    localEOWRealLinearKernelPushforwardCLM ys hli
  let Gorig : SchwartzMap D ℂ → X → ℂ := fun η z =>
    localRudinEnvelope δ x0 ys
      (realMollifyLocal Fplus η) (realMollifyLocal Fminus η) z
  let Gchart : SchwartzMap D ℂ → X → ℂ := fun ψ z => Gorig (P ψ) z
  let FplusCoord : X → ℂ := fun ζ => Fplus (localEOWChart x0 ys ζ)
  let FminusCoord : X → ℂ := fun ζ => Fminus (localEOWChart x0 ys ζ)
  have hplus_margin :
      ∀ ψ : SchwartzMap D ℂ, KernelSupportWithin ψ rψLarge →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : D → ℂ),
          z + realEmbed t ∈ Ωplus := by
    intro ψ hψ z hz t ht
    exact hplus_margin_closed z hz t (hψ ht)
  have hminus_margin :
      ∀ ψ : SchwartzMap D ℂ, KernelSupportWithin ψ rψLarge →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : D → ℂ),
          z + realEmbed t ∈ Ωminus := by
    intro ψ hψ z hz t ht
    exact hminus_margin_closed z hz t (hψ ht)
  have hA4_large :
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψLarge :=
    hA4_one.trans hrψ_one_large
  have hRcut_window :
      Metric.closedBall (0 : X) (16 * σ) ⊆
        Metric.ball (0 : X) (δ / 2) := by
    simpa [X] using
      oneChartRecoveryScale_cut_closedBall_subset_half
        (m := m) hσ hδscale
  obtain ⟨Lorig, hLorig_value0, hLorig_bound⟩ :=
    regularizedLocalEOW_originalFamily_compactValueCLM
      (m := m) (Cplus := Cplus) (Cminus := Cminus)
      (rLarge := rψLarge) (ρ := ρ) (r := r) (δ := δ)
      (Rcut := 16 * σ) hm Ωplus Ωminus Dplus Dminus E
      hΩplus_open hΩminus_open hDplus_open hDminus_open hE_open
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin_closed
      hminus_margin_closed hDplus_sub hDminus_sub Tplus Tminus Tchart
      hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hδ hδρ
      hδsum hE_mem hplus hminus χψ hχψ_support hRcut_window
  have hLorig_value :
      ∀ z ∈ Metric.closedBall (0 : X) (16 * σ),
        ∀ η : SchwartzMap D ℂ,
          Lorig z η =
            Gorig (SchwartzMap.smulLeftCLM ℂ (χψ : D → ℂ) η) z := by
    intro z hz η
    simpa [Gorig, X, D] using hLorig_value0 z hz η
  obtain ⟨Lchart, hLchart_apply, hLchart_value, hLchart_bound⟩ :=
    regularizedLocalEOW_chartKernelFamily_valueCLM
      (m := m) ys hli (Rcut := 16 * σ) (r := 2 * σ)
      (rcut := 4 * σ) (rψ := rψOne) χr χψ Gorig Lorig
      hχr_one hχr_support hA4_one hχψ_one hLorig_value hLorig_bound
  have hmix_le_four : 2 * σ ≤ 4 * σ := by nlinarith [hσ]
  have hcore_le_four : σ ≤ 4 * σ := by nlinarith [hσ]
  have houtputs_mix :=
    regularizedLocalEOW_chartKernelFamily_outputs_from_fixedWindow
      (m := m) (Cplus := Cplus) (Cminus := Cminus)
      (rψ := rψLarge) (ρ := ρ) (r := r) (δ := δ)
      (rchart := 2 * σ) (σ := σ) hm Ωplus Ωminus Dplus Dminus E
      hΩplus_open hΩminus_open hDplus_open hDminus_open hE_open
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin hminus_margin
      hDplus_sub hDminus_sub Tplus Tminus Tchart hplus_eval hminus_eval
      hplus_limit hminus_limit x0 ys hδ hδρ hδsum hE_mem hplus
      hminus hli hmix_le_four hA4_large
  have houtputs_core :=
    regularizedLocalEOW_chartKernelFamily_outputs_from_fixedWindow
      (m := m) (Cplus := Cplus) (Cminus := Cminus)
      (rψ := rψLarge) (ρ := ρ) (r := r) (δ := δ)
      (rchart := σ) (σ := σ) hm Ωplus Ωminus Dplus Dminus E
      hΩplus_open hΩminus_open hDplus_open hDminus_open hE_open
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin hminus_margin
      hDplus_sub hDminus_sub Tplus Tminus Tchart hplus_eval hminus_eval
      hplus_limit hminus_limit x0 ys hδ hδρ hδsum hE_mem hplus
      hminus hli hcore_le_four hA4_large
  have hcont_integrand :
      ∀ F : SchwartzMap (X × D) ℂ,
        ContinuousOn
          (fun z : X =>
            χU z *
              Gorig
                (SchwartzMap.smulLeftCLM ℂ (χψ : D → ℂ)
                  (P (SchwartzMap.smulLeftCLM ℂ (χr : D → ℂ)
                    (schwartzPartialEval₁CLM z F)))) z)
          (Metric.closedBall (0 : X) (16 * σ)) := by
    intro F
    have hcont :=
      continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand
        (m := m) (Cplus := Cplus) (Cminus := Cminus)
        (δ := δ) (ρ := ρ) (r := r) (Rcut := 16 * σ)
        (rψLarge := rψLarge) hm Ωplus Ωminus Dplus Dminus Kreal
        hΩplus_open hΩminus_open hDplus_open hDminus_open
        Fplus Fminus hFplus_diff hFminus_diff hplus_margin_closed
        hminus_margin_closed hDplus_sub hDminus_sub Tplus Tminus Tchart
        hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hli hδ
        hδρ hδsum hRcut_window hKreal_compact hKreal_mem hplus hminus
        χU χr χψ hχψ_support F
    simpa [Gorig, P, X, D] using hcont
  have hLchart_cutoff :
      ∀ z ∈ Metric.closedBall (0 : X) (16 * σ),
      ∀ ψ : SchwartzMap D ℂ,
        Lchart z ψ =
          Gorig
            (SchwartzMap.smulLeftCLM ℂ (χψ : D → ℂ)
              (P (SchwartzMap.smulLeftCLM ℂ (χr : D → ℂ) ψ))) z := by
    intro z hz ψ
    calc
      Lchart z ψ =
          Lorig z
            (P (SchwartzMap.smulLeftCLM ℂ (χr : D → ℂ) ψ)) := by
          simpa [P, D] using hLchart_apply z ψ
      _ =
          Gorig
            (SchwartzMap.smulLeftCLM ℂ (χψ : D → ℂ)
              (P (SchwartzMap.smulLeftCLM ℂ (χr : D → ℂ) ψ))) z :=
          hLorig_value z hz _
  obtain ⟨K, hG_holo_mix, hK_rep_mix⟩ :=
    regularizedLocalEOW_pairingCLM_of_fixedWindow
      (m := m) ys hli δ (8 * σ) (16 * σ) (2 * σ)
      (by nlinarith [hσ]) (by nlinarith [hσ]) hRcut_window χU χr χψ
      hχU_one Gorig Lchart hLchart_cutoff hLchart_value hLchart_bound
      hcont_integrand houtputs_mix.1
  have hRcov_small : 2 * (8 * σ) < δ / 4 := by
    nlinarith [hσ, hδscale]
  have hG_cont :
      ∀ ψ, KernelSupportWithin ψ (2 * σ) →
        ContinuousOn
          (fun z : X =>
            localRudinEnvelope δ x0 ys
              (realMollifyLocal Fplus (P ψ))
              (realMollifyLocal Fminus (P ψ)) z)
          (Metric.ball (0 : X) (8 * σ)) := by
    intro ψ hψ
    have hholo := houtputs_mix.1 ψ hψ
    have hsub :
        Metric.ball (0 : X) (8 * σ) ⊆
          Metric.ball (0 : X) (δ / 2) := by
      simpa [X] using
        oneChartRecoveryScale_cov_ball_subset_half
          (m := m) hσ hδscale
    simpa [Gorig, P, X, D] using hholo.continuousOn.mono hsub
  have hcov :
      ProductKernelRealTranslationCovariantLocal K
        (Metric.ball (0 : X) (8 * σ)) (σ + σ) := by
    simpa [X, two_mul] using
      regularizedLocalEOW_pairingCLM_localCovariant_from_fixedWindow
        (m := m) (Cplus := Cplus) (Cminus := Cminus)
        (rψ := rψLarge) (ρ := ρ) (r := r) (δ := δ)
        (Rcov := 8 * σ) (Rmix := 2 * σ) (σ := σ) hm hδ
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff hplus_margin hminus_margin hDplus_sub hDminus_sub
        Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit
        hminus_limit x0 ys hδρ hδsum hE_mem hplus hminus hli K
        hRcov_small (by nlinarith [hσ]) hA4_large
        (by
          intro φ ψ hφ hψ
          simpa [Gorig, P, X, D] using hK_rep_mix φ ψ hφ
            hψ)
        hG_cont
  have hplusΩ :
      ∀ u ∈ Metric.closedBall (0 : D) ρ, ∀ v : D,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus := by
    intro u hu v hv hsum_pos hsum_lt
    exact hDplus_Ω (hplus u hu v hv hsum_pos hsum_lt)
  have hminusΩ :
      ∀ u ∈ Metric.closedBall (0 : D) ρ, ∀ v : D,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus := by
    intro u hu v hv hsum_pos hsum_lt
    exact hDminus_Ω (hminus u hu v hv hsum_pos hsum_lt)
  have hside_cont :=
    chartSideFunction_continuousOn_strictBalls_from_fixedWindow
      (m := m) (ρ := ρ) (r := r) (σ := σ) hm Ωplus Ωminus
      x0 ys Fplus Fminus hFplus_diff hFminus_diff hσρ hcardσ
      hplusΩ hminusΩ
  obtain ⟨η, _hη_nonneg, _hη_real, hη_norm, hη_support⟩ :=
    exists_normalized_schwartz_bump_kernelSupportWithin
      (m := m) σ hσ
  obtain ⟨ψn, hψ_nonneg, hψ_real, hψ_norm, hψ_support_min,
      hψ_support_r⟩ :=
    exists_shrinking_normalized_schwartz_bump_sequence
      (m := m) hσ
  have hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)) := by
    intro n
    exact KernelSupportWithin.mono (hψ_support_min n) (min_le_right _ _)
  have hψ_approx :
      ∀ θ : SchwartzMap X ℂ,
        Tendsto
          (fun n => realConvolutionTest θ (ψn n))
          atTop
          (nhds θ) := by
    intro θ
    simpa [X, D] using
      tendsto_realConvolutionTest_of_shrinking_normalized_support
        (m := m) θ ψn hψ_nonneg hψ_real hψ_norm hψ_support_shrink
  have hK_rep_core :
      ∀ (φ : SchwartzMap X ℂ) (ψ : SchwartzMap D ℂ),
        SupportsInOpen (φ : X → ℂ) (Metric.ball (0 : X) (8 * σ)) →
        KernelSupportWithin ψ σ →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : X, Gchart ψ z * φ z := by
    intro φ ψ hφ hψ
    have hψ_mix : KernelSupportWithin ψ (2 * σ) :=
      KernelSupportWithin.mono hψ (by nlinarith [hσ])
    simpa [Gchart, Gorig, P, X, D] using hK_rep_mix φ ψ hφ hψ_mix
  have hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈
        Metric.ball (0 : X) σ ∩ StrictPositiveImagBall (m := m) σ,
        Gchart (ψn n) z = realMollifyLocal FplusCoord (ψn n) z := by
    refine Filter.Eventually.of_forall ?_
    intro n z hz
    have hz_big : z ∈ Metric.ball (0 : X) (δ / 2) := by
      have hsmall : σ < δ / 2 := by nlinarith [hσ, hδscale]
      exact Metric.ball_subset_ball (le_of_lt hsmall) hz.1
    simpa [Gchart, FplusCoord, P, X, D] using
      houtputs_core.2.1 (ψn n) (hψ_support_r n) z hz_big hz.2.2
  have hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈
        Metric.ball (0 : X) σ ∩ StrictNegativeImagBall (m := m) σ,
        Gchart (ψn n) z = realMollifyLocal FminusCoord (ψn n) z := by
    refine Filter.Eventually.of_forall ?_
    intro n z hz
    have hz_big : z ∈ Metric.ball (0 : X) (δ / 2) := by
      have hsmall : σ < δ / 2 := by nlinarith [hσ, hδscale]
      exact Metric.ball_subset_ball (le_of_lt hsmall) hz.1
    simpa [Gchart, FminusCoord, P, X, D] using
      houtputs_core.2.2 (ψn n) (hψ_support_r n) z hz_big hz.2.2
  obtain ⟨H, hH_diff, Hdist, hHdist, hHdist_rep, hH_plus, hH_minus⟩ :=
    regularizedEnvelope_chartEnvelope_from_oneChartScale
      (m := m) hm hσ hδscale K Gchart FplusCoord FminusCoord ψn η
      hη_norm hη_support hcov
      (by
        intro ψ hψ
        simpa [Gchart, X, D] using houtputs_core.1 ψ hψ)
      hK_rep_core hψ_nonneg hψ_real hψ_norm hψ_support_shrink
      hψ_support_r hψ_approx hG_plus hG_minus hside_cont.1 hside_cont.2
  refine ⟨K, H, hH_diff, Hdist, hHdist, hHdist_rep, ?_, ?_⟩
  · intro z hz
    exact hH_plus z ⟨hz.1, hz⟩
  · intro z hz
    exact hH_minus z ⟨hz.1, hz⟩

end SCV
