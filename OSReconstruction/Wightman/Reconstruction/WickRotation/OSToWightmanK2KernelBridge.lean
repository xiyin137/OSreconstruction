/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent
import OSReconstruction.Wightman.Reconstruction.SliceIntegral

/-!
# `k = 2` Front Kernel Bridge

This file isolates the front density/kernel seam in the `k = 2` OS route:

- density of admissible difference shells in `ZeroDiagonalSchwartz d 2`,
- reduced zero-origin pairing by a scalar difference kernel,
- promotion to an off-diagonal two-point kernel representation.

Keeping this seam separate makes iteration much faster than recompiling the full
Bochner/convergence assembly every time the front blocker changes.
-/

noncomputable section

open MeasureTheory Complex Topology
open OSReconstruction
open scoped Pointwise SchwartzMap LineDeriv

variable {d : ℕ} [NeZero d]

private theorem unrestricted_differenceShell_span_dense_zeroDiagonal :
    Dense (((Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d),
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
        Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2)) := by
  sorry

/-- First local step in the cutoff half of the density seam: if a difference
lift lies in `ZeroDiagonalSchwartz`, then the difference factor vanishes at the
origin. -/
private theorem differenceLift_in_ZDS_implies_h_zero_at_zero
    (χ h : SchwartzSpacetime d)
    (hf : VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h))
    (hχ_nonzero : ∃ x, χ x ≠ 0) :
    (h : SpacetimeDim d → ℂ) 0 = 0 := by
  rcases hχ_nonzero with ⟨x₀, hx₀⟩
  let xdiag : NPointDomain d 2 := fun _ => x₀
  have hxdiag : xdiag ∈ CoincidenceLocus d 2 := by
    refine ⟨0, 1, by decide, ?_⟩
    simp [xdiag]
  have hdiag0 : ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) xdiag) = 0 := by
    have hdiag :
        iteratedFDeriv ℝ 0
          (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ)) xdiag = 0 := hf 0 xdiag hxdiag
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using hdiag
  have hmul : χ x₀ * h 0 = 0 := by
    simpa [xdiag, twoPointDifferenceLift_apply] using hdiag0
  exact (mul_eq_zero.mp hmul).resolve_left hx₀

/-- Stronger local step for the cutoff argument: if a difference lift lies in
`ZeroDiagonalSchwartz`, then the difference factor vanishes to infinite order at
the origin. -/
private theorem differenceLift_in_ZDS_implies_h_vanishes_at_zero
    (χ h : SchwartzSpacetime d)
    (hf : VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h))
    (hχ_nonzero : ∃ x, χ x ≠ 0) :
    ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0 := by
  rcases hχ_nonzero with ⟨x₀, hx₀⟩
  let z0 : NPointDomain d 2 := Fin.cons x₀ (fun _ => (0 : SpacetimeDim d))
  let xdiag : NPointDomain d 2 := fun _ => x₀
  have hxdiag : xdiag ∈ CoincidenceLocus d 2 := by
    refine ⟨0, 1, by decide, ?_⟩
    simp [xdiag]
  let Fcd : SchwartzNPoint d 2 :=
    twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)
  have hcd_zero : ∀ k : ℕ,
      iteratedFDeriv ℝ k (Fcd : NPointDomain d 2 → ℂ) z0 = 0 := by
    intro k
    have hcomp :
        iteratedFDeriv ℝ k (Fcd : NPointDomain d 2 → ℂ) z0 =
          (iteratedFDeriv ℝ k
            (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
              NPointDomain d 2 → ℂ)) ((twoPointCenterDiffCLE d) z0)).compContinuousLinearMap
            (fun _ => (twoPointCenterDiffCLE d).toContinuousLinearMap) := by
      dsimp [Fcd, twoPointCenterDiffSchwartzCLM]
      simpa using
        (twoPointCenterDiffCLE d).toContinuousLinearMap.iteratedFDeriv_comp_right
          (f := (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ)))
          ((twoPointDifferenceLift χ h : SchwartzNPoint d 2).smooth k)
          (x := z0) (i := k) le_rfl
    have hbase :
        iteratedFDeriv ℝ k
          (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ)) ((twoPointCenterDiffCLE d) z0) = 0 := by
      apply hf k
      simpa [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, z0, xdiag] using hxdiag
    rw [hcomp, hbase]
    ext u
    simp
  intro k
  ext u
  let insDiff : SpacetimeDim d → NPointDomain d 2 := fun v =>
    fun j => Fin.cases (0 : SpacetimeDim d) (fun _ : Fin 1 => v) j
  let du : Fin k → NPointDomain d 2 := fun i =>
    insDiff (u i)
  have hline_zero :
      (LineDeriv.iteratedLineDerivOp du Fcd) z0 = 0 := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    change (iteratedFDeriv ℝ k (Fcd : NPointDomain d 2 → ℂ) z0) du = 0
    have hz :
        (iteratedFDeriv ℝ k (Fcd : NPointDomain d 2 → ℂ) z0) du =
          (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => NPointDomain d 2) ℂ) du := by
      exact congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => NPointDomain d 2) ℂ => T du)
        (hcd_zero k)
    simpa using hz
  have hline_id_generic :
      ∀ {k : ℕ} (u : Fin k → SpacetimeDim d),
        LineDeriv.iteratedLineDerivOp
            (fun i => insDiff (u i))
            (χ.prependField (onePointToFin1CLM d h)) =
          χ.prependField (onePointToFin1CLM d (LineDeriv.iteratedLineDerivOp u h)) := by
    intro k u
    induction k with
    | zero =>
        ext x
        simp
    | succ k ih =>
        ext x
        have htail := ih (u := Fin.tail u)
        change
          (∂_{insDiff (u 0)}
            (∂^{fun i => insDiff (Fin.tail u i)}
              (SchwartzMap.prependField χ ((onePointToFin1CLM d) h)))) x =
            (SchwartzMap.prependField χ ((onePointToFin1CLM d) (∂^{u} h))) x
        rw [htail]
        have hχfd :
            HasFDerivAt
              (fun y : NPointDomain d 2 => χ (y 0))
              ((fderiv ℝ (fun z : SpacetimeDim d => χ z) (x 0)).comp
                (ContinuousLinearMap.proj (R := ℝ) (i := (0 : Fin 2)))) x := by
          simpa using
            (SchwartzMap.hasFDerivAt (f := χ) (x := x 0)).comp x
              (hasFDerivAt_apply (0 : Fin 2) x)
        have hhfd :
            HasFDerivAt
              (fun y : NPointDomain d 2 => (∂^{Fin.tail u} h) (y 1))
              ((fderiv ℝ (fun z : SpacetimeDim d => (∂^{Fin.tail u} h) z) (x 1)).comp
                (ContinuousLinearMap.proj (R := ℝ) (i := (1 : Fin 2)))) x := by
          simpa using
            (SchwartzMap.hasFDerivAt (f := (∂^{Fin.tail u} h)) (x := x 1)).comp x
              (hasFDerivAt_apply (1 : Fin 2) x)
        have happly :=
          congrArg (fun L : NPointDomain d 2 →L[ℝ] ℂ => L (insDiff (u 0)))
            (hχfd.mul hhfd).fderiv
        simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv,
          SchwartzMap.prependField_apply, onePointToFin1CLM_apply,
          LineDeriv.iteratedLineDerivOp_succ_left, insDiff,
          ContinuousLinearMap.comp_apply, mul_add, add_mul] using happly
  have hline_id :
      LineDeriv.iteratedLineDerivOp du Fcd =
        χ.prependField (onePointToFin1CLM d (LineDeriv.iteratedLineDerivOp u h)) := by
    simpa [Fcd, du, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
      (hline_id_generic (u := u))
  have hmul : χ x₀ * (LineDeriv.iteratedLineDerivOp u h) 0 = 0 := by
    simpa [hline_id, du, z0, SchwartzMap.prependField_apply, onePointToFin1CLM_apply]
      using hline_zero
  have hu_zero : (LineDeriv.iteratedLineDerivOp u h) 0 = 0 := (mul_eq_zero.mp hmul).resolve_left hx₀
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv] using hu_zero

/-- The standard compact radial bump on spacetime, rescaled to radius `R`. -/
private abbrev spacetimeUnitBallBumpRadius (R : ℝ) (hR : 0 < R) : SchwartzSpacetime d :=
  unitBallBumpSchwartzPiRadius (d + 1) R hR

/-- The annular cutoff `ρ_R - ρ_ε` vanishes on a neighborhood of the origin. -/
private theorem zero_not_mem_tsupport_annulusCutoff
    (ε R : ℝ) (hε : 0 < ε) (hR : ε < R) :
    (0 : SpacetimeDim d) ∉ tsupport
      (fun x : SpacetimeDim d =>
        spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
          spacetimeUnitBallBumpRadius (d := d) ε hε x) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : SpacetimeDim d) hε) ?_
  intro x hx
  have hxR : x ∈ Metric.closedBall (0 : SpacetimeDim d) R := by
    rw [Metric.mem_closedBall]
    have hx' : dist x 0 < ε := by simpa [Metric.mem_ball] using hx
    linarith
  have hxε : x ∈ Metric.closedBall (0 : SpacetimeDim d) ε := by
    rw [Metric.mem_closedBall]
    have hx' : dist x 0 < ε := by simpa [Metric.mem_ball] using hx
    linarith
  have hR_one :
      unitBallBumpSchwartzPi (d + 1) (R⁻¹ • x) = 1 := by
    simpa [spacetimeUnitBallBumpRadius, unitBallBumpSchwartzPiRadius_apply] using
      (unitBallBumpSchwartzPiRadius_one_of_mem_closedBall (m := d + 1)
        (hR := lt_trans hε hR) hxR)
  have hε_one :
      unitBallBumpSchwartzPi (d + 1) (ε⁻¹ • x) = 1 := by
    simpa [spacetimeUnitBallBumpRadius, unitBallBumpSchwartzPiRadius_apply] using
      (unitBallBumpSchwartzPiRadius_one_of_mem_closedBall (m := d + 1)
        (hR := hε) hxε)
  simp [spacetimeUnitBallBumpRadius, unitBallBumpSchwartzPiRadius_apply, hR_one, hε_one]

/-- Multiplying by the annular cutoff produces an origin-avoiding compactly
supported Schwartz function. -/
private theorem hasCompactSupport_annulusCutoff_mul
    (h : SchwartzSpacetime d)
    (ε R : ℝ) (hε : 0 < ε) (hR : ε < R) :
    HasCompactSupport
      ((SchwartzMap.smulLeftCLM ℂ
          (fun x : SpacetimeDim d =>
            spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
              spacetimeUnitBallBumpRadius (d := d) ε hε x) h : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  have hRcs :
      HasCompactSupport
        (((SchwartzMap.smulLeftCLM ℂ
            (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
    simpa [spacetimeUnitBallBumpRadius] using
      hasCompactSupport_cutoff_mul_radius (m := d + 1) R (lt_trans hε hR) h
  have hεcs :
      HasCompactSupport
        (((SchwartzMap.smulLeftCLM ℂ
            (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
    simpa [spacetimeUnitBallBumpRadius] using
      hasCompactSupport_cutoff_mul_radius (m := d + 1) ε hε h
  have hdiffTG :
      (fun x : SpacetimeDim d =>
        spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
          spacetimeUnitBallBumpRadius (d := d) ε hε x).HasTemperateGrowth := by
    simpa using
      (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)).hasTemperateGrowth.sub
        (spacetimeUnitBallBumpRadius (d := d) ε hε).hasTemperateGrowth
  have hEq :
      (((SchwartzMap.smulLeftCLM ℂ
          (fun x : SpacetimeDim d =>
            spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
              spacetimeUnitBallBumpRadius (d := d) ε hε x) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) =
        ((((SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
                SchwartzSpacetime d) -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
                SchwartzSpacetime d)) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
    ext x
    calc
      (((SchwartzMap.smulLeftCLM ℂ
          (fun x : SpacetimeDim d =>
            spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
              spacetimeUnitBallBumpRadius (d := d) ε hε x) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) x)
          =
        (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
            spacetimeUnitBallBumpRadius (d := d) ε hε x) • h x := by
              rw [SchwartzMap.smulLeftCLM_apply_apply hdiffTG]
      _ =
        (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x -
            spacetimeUnitBallBumpRadius (d := d) ε hε x) * h x := by
            simp [smul_eq_mul]
      _ =
        (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR) x) * h x -
          (spacetimeUnitBallBumpRadius (d := d) ε hε x) * h x := by
            ring
      _ =
        ((((SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
                SchwartzSpacetime d) -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
                SchwartzSpacetime d)) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) x := by
            rw [show
                ((((SchwartzMap.smulLeftCLM ℂ
                      (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
                        SchwartzSpacetime d) -
                    (SchwartzMap.smulLeftCLM ℂ
                      (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
                        SchwartzSpacetime d)) : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ) x =
                  (((SchwartzMap.smulLeftCLM ℂ
                        (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
                          SchwartzSpacetime d) : SpacetimeDim d → ℂ) x -
                    (((SchwartzMap.smulLeftCLM ℂ
                        (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
                          SchwartzSpacetime d) : SpacetimeDim d → ℂ) x)) by
                  rfl]
            rw [SchwartzMap.smulLeftCLM_apply_apply
                  ((spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)).hasTemperateGrowth),
                SchwartzMap.smulLeftCLM_apply_apply
                  ((spacetimeUnitBallBumpRadius (d := d) ε hε).hasTemperateGrowth)]
            simp [spacetimeUnitBallBumpRadius, smul_eq_mul]
  have hsub :
      HasCompactSupport
        ((((SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hε hR)) h :
                SchwartzSpacetime d) -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) ε hε) h :
                SchwartzSpacetime d)) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
    simpa using hRcs.sub hεcs
  exact hEq.symm ▸ hsub

set_option maxHeartbeats 800000 in
private theorem exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : SpacetimeDim d),
        ‖iteratedFDeriv ℝ n
            ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖ ≤
          C * (δ⁻¹) ^ n := by
  let ψ : SchwartzSpacetime d := unitBallBumpSchwartzPi (d + 1)
  obtain ⟨C, hC, hCbound⟩ := (ψ : SchwartzSpacetime d).decay 0 n
  refine ⟨C, le_of_lt hC, ?_⟩
  intro δ hδ x
  let e : SpacetimeDim d →L[ℝ] SpacetimeDim d :=
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
      (Units.mk0 δ hδ.ne')).symm) : SpacetimeDim d ≃L[ℝ] SpacetimeDim d).toContinuousLinearMap
  have he_apply (y : SpacetimeDim d) : e y = δ⁻¹ • y := by
    change
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) = δ⁻¹ • y
    rw [show
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) =
          ((↑((Units.mk0 δ hδ.ne')⁻¹) : ℝ) • y) by rfl]
    simp [Units.val_inv_eq_inv_val]
  have he_norm : ‖e‖ ≤ δ⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound e (inv_nonneg.mpr hδ.le) ?_
    intro y
    calc
      ‖e y‖ = ‖δ⁻¹ • y‖ := by rw [he_apply]
      _ = ‖δ⁻¹‖ * ‖y‖ := norm_smul _ _
      _ = δ⁻¹ * ‖y‖ := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
      _ ≤ δ⁻¹ * ‖y‖ := by rfl
  have hcomp :
      iteratedFDeriv ℝ n
          (((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ)) x =
        (((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e)) := by
    dsimp [spacetimeUnitBallBumpRadius, ψ]
    simpa using
      e.iteratedFDeriv_comp_right
        (f := ((unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) x‖
        =
      ‖(((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e))‖ := by
            rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x)‖ *
          ∏ _ : Fin n, ‖e‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _ : Fin n, ‖e‖ := by
            gcongr
            simpa using hCbound (e x)
    _ = C * ‖e‖ ^ n := by
            simp
    _ ≤ C * (δ⁻¹) ^ n := by
            gcongr

/-- Schwartz functions vanishing to infinite order at the origin can be
be cut off near the origin with arbitrarily small Schwartz seminorm error. -/
private theorem schwartz_small_origin_cutoff_seminorm_small
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (N M : ℕ) (ε : ℝ) (hε : 0 < ε),
      ∃ (δ : ℝ) (hδ : 0 < δ),
        SchwartzMap.seminorm ℝ N M
          ((SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                SchwartzSpacetime d)) < ε := by
  sorry

/-- Schwartz functions can be cut off at large radius with arbitrarily small
Schwartz seminorm error. -/
private theorem schwartz_large_radius_cutoff_seminorm_small
    (h : SchwartzSpacetime d) :
    ∀ (N M : ℕ) (ε Rmin : ℝ) (hε : 0 < ε) (hRmin : 0 < Rmin),
      ∃ (R : ℝ) (hR : Rmin < R),
        SchwartzMap.seminorm ℝ N M
          (h -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) R
                (lt_trans hRmin hR)) h : SchwartzSpacetime d)) < ε := by
  intro N M ε Rmin hε hRmin
  obtain ⟨n₀, hn₀⟩ :=
    Metric.tendsto_atTop.mp (SchwartzMap.tendsto_bump_truncation h N M) ε hε
  let n : ℕ := max n₀ ⌈Rmin⌉₊
  refine ⟨bumpTruncationRadiusValue n, ?_, ?_⟩
  · have hceil : Rmin ≤ ⌈Rmin⌉₊ := Nat.le_ceil Rmin
    have hn_ge : (⌈Rmin⌉₊ : ℝ) ≤ n := by
      exact_mod_cast le_max_right n₀ ⌈Rmin⌉₊
    have : Rmin < bumpTruncationRadiusValue n := by
      dsimp [bumpTruncationRadiusValue]
      linarith
    exact this
  · have hn : n₀ ≤ n := le_max_left _ _
    have hnonneg :
        0 ≤ SchwartzMap.seminorm ℝ N M
          (h -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) (bumpTruncationRadiusValue n)
                (bumpTruncationRadiusValue_pos n)) h : SchwartzSpacetime d)) := by
      positivity
    have hEq :
        h -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) (bumpTruncationRadiusValue n)
                (bumpTruncationRadiusValue_pos n)) h : SchwartzSpacetime d) =
          h - bumpTruncationRadius h n := by
      simp [bumpTruncationRadius, bumpTruncationRadiusValue, spacetimeUnitBallBumpRadius,
        add_assoc]
    have hnonneg' :
        0 ≤ SchwartzMap.seminorm ℝ N M (h - bumpTruncationRadius h n) := by
      positivity
    have hdist :
        dist
            (SchwartzMap.seminorm ℝ N M
              (h -
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) (bumpTruncationRadiusValue n)
                    (bumpTruncationRadiusValue_pos n)) h : SchwartzSpacetime d)))
            0 < ε := by
      simpa [hEq] using hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hdist
    exact hdist

/-- Schwartz functions vanishing to infinite order at the origin can be
approximated in Schwartz seminorms by origin-avoiding compactly supported
Schwartz functions. This is the analytic engine behind Step B. -/
private theorem schwartz_origin_avoidance_approximation
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (N M : ℕ) (ε : ℝ), 0 < ε →
      ∃ (h' : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h' : SpacetimeDim d → ℂ) ∧
        HasCompactSupport (h' : SpacetimeDim d → ℂ) ∧
        SchwartzMap.seminorm ℝ N M (h - h') < ε := by
  sorry

/-- Cutoff half of the density seam in its honest form: if a two-point
difference shell already lies in `ZeroDiagonalSchwartz`, then it belongs to the
closure of the origin-avoiding compactly-supported shell span. -/
private theorem differenceShell_mem_topologicalClosure_zeroOrigin_span_of_vanishes
    (χ h : SchwartzSpacetime d)
    (hvanish : VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h)) :
    ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h) ∈
      (((Submodule.span ℂ
        {f : ZeroDiagonalSchwartz d 2 |
          ∃ (χ h : SchwartzSpacetime d),
            (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
            HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
            f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
          Submodule ℂ (ZeroDiagonalSchwartz d 2)).topologicalClosure :
        Set (ZeroDiagonalSchwartz d 2)) := by
  sorry

/-- General Step B wrapper: for shells not in `ZeroDiagonalSchwartz`, the
classical promotion is already `0`, so the only genuine work is the vanishing
case above. -/
private theorem differenceShell_mem_topologicalClosure_zeroOrigin_span
    (χ h : SchwartzSpacetime d) :
    ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h) ∈
      (((Submodule.span ℂ
        {f : ZeroDiagonalSchwartz d 2 |
          ∃ (χ h : SchwartzSpacetime d),
            (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
            HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
            f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
          Submodule ℂ (ZeroDiagonalSchwartz d 2)).topologicalClosure :
        Set (ZeroDiagonalSchwartz d 2)) := by
  classical
  by_cases hvanish : VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h)
  · exact differenceShell_mem_topologicalClosure_zeroOrigin_span_of_vanishes
      (d := d) χ h hvanish
  · rw [ZeroDiagonalSchwartz.ofClassical_of_not_vanishes
      (f := twoPointDifferenceLift χ h) hvanish]
    exact (Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d),
          (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
          HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}).topologicalClosure.zero_mem

private theorem zeroOrigin_differenceShell_span_dense_zeroDiagonal :
    Dense (((Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d),
          (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
          HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
        Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2)) := by
  let S_all : Set (ZeroDiagonalSchwartz d 2) :=
    {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  let S_zero : Set (ZeroDiagonalSchwartz d 2) :=
    {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  let A : Submodule ℂ (ZeroDiagonalSchwartz d 2) := Submodule.span ℂ S_all
  let B : Submodule ℂ (ZeroDiagonalSchwartz d 2) := Submodule.span ℂ S_zero
  have hA_dense : Dense (A : Set (ZeroDiagonalSchwartz d 2)) := by
    simpa [A, S_all] using unrestricted_differenceShell_span_dense_zeroDiagonal (d := d)
  have hA_closure : A.topologicalClosure = ⊤ := by
    exact (Submodule.dense_iff_topologicalClosure_eq_top).mp hA_dense
  have hA_le : A ≤ B.topologicalClosure := by
    refine Submodule.span_le.mpr ?_
    intro g hg
    rcases hg with ⟨χ, h, rfl⟩
    simpa [B, S_zero] using
      differenceShell_mem_topologicalClosure_zeroOrigin_span (d := d) χ h
  have hAclosure_le : A.topologicalClosure ≤ B.topologicalClosure :=
    Submodule.topologicalClosure_minimal A hA_le B.isClosed_topologicalClosure
  have htop : B.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← hA_closure]
    exact hAclosure_le
  exact (Submodule.dense_iff_topologicalClosure_eq_top).mpr (by simpa [B, S_zero] using htop)

/-- Scalar difference-kernel form of the two-point regularity input. This is the
honest theorem underlying the pair-kernel statement below: a single
polynomial-growth difference kernel, continuous away from the origin, already
reproduces the canonical zero-origin reduced Schwinger pairing. -/
private theorem exists_twoPointDifferenceKernel_zeroOrigin_pairing_offOrigin
    (OS : OsterwalderSchraderAxioms d) :
    ∃ (χ₀ : SchwartzSpacetime d),
      (∫ u : SpacetimeDim d, χ₀ u = 1) ∧
      ∃ (K : SpacetimeDim d → ℂ),
        ContinuousOn K {ξ : SpacetimeDim d | ξ ≠ 0} ∧
        AEStronglyMeasurable (OSReconstruction.twoPointDifferenceKernel (d := d) K) volume ∧
        (∃ (N : ℕ) (C_bd : ℝ), 0 < C_bd ∧
          ∀ᵐ x : NPointDomain d 2 ∂volume,
            ‖OSReconstruction.twoPointDifferenceKernel (d := d) K x‖ ≤
              C_bd * (1 + ‖x‖) ^ N) ∧
        (∀ h : zeroOriginAvoidingSubmodule d,
          HasCompactSupport
            ((((h : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ)) →
            ∫ ξ : SpacetimeDim d, K ξ *
                ((((h : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d)) ξ) =
              (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
                (d := d) OS χ₀) h) := by
  sorry

/-- A zero-origin reduced pairing already reproduces the canonical positive-time
reduced Schwinger pairing on compactly supported tests. This is the direct
bridge from the zero-origin kernel theorem to the positive-time shell formulas
used later in the `k = 2` assembly. -/
private theorem zeroOrigin_pairing_implies_positiveTime_reduced_pairing
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K : SpacetimeDim d → ℂ)
    (hZero : ∀ h : zeroOriginAvoidingSubmodule d,
      HasCompactSupport
        ((((h : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) →
        ∫ ξ : SpacetimeDim d, K ξ *
            ((((h : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d)) ξ) =
          (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
            (d := d) OS χ₀) h) :
    ∀ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        ∫ ξ : SpacetimeDim d, K ξ * h ξ =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
  intro h hh_pos hh_compact
  let hmem : zeroOriginAvoidingSubmodule d :=
    ⟨h, by
      intro h0
      have hpos0 := hh_pos h0
      simpa using hpos0⟩
  calc
    ∫ ξ : SpacetimeDim d, K ξ * h ξ =
        (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
          (d := d) OS χ₀) hmem := by
            simpa [hmem] using hZero hmem hh_compact
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
          rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
            (d := d) (OS := OS) χ₀ hχ₀ χ₀ hmem]
          simp [hχ₀]

theorem schwinger_twoPoint_kernel_repr_offDiagonal
    (OS : OsterwalderSchraderAxioms d) :
    ∃ (K : SpacetimeDim d → SpacetimeDim d → ℂ),
      ContinuousOn (fun p : SpacetimeDim d × SpacetimeDim d => K p.1 p.2)
        {p | p.1 ≠ p.2} ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f =
          ∫ p : SpacetimeDim d × SpacetimeDim d,
            K p.1 p.2 *
              f.1 (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume)) := by
  let S : Set (ZeroDiagonalSchwartz d 2) :=
    {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  rcases exists_twoPointDifferenceKernel_zeroOrigin_pairing_offOrigin OS with
    ⟨χ₀, hχ₀, Kd, hKd_cont, hKd_meas, hKd_bound', hZero⟩
  rcases hKd_bound' with ⟨N, C_bd, hC_bd, hKd_bound⟩
  have hCLM :
      OSReconstruction.twoPointZeroDiagonalKernelCLM
          (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
          hKd_meas C_bd N hC_bd hKd_bound =
        OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 := by
    have hOnSpan :
        ∀ f ∈ ((Submodule.span ℂ S : Submodule ℂ (ZeroDiagonalSchwartz d 2)) :
          Set (ZeroDiagonalSchwartz d 2)),
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
              hKd_meas C_bd N hC_bd hKd_bound f =
            OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 f := by
      intro f hf
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
      · intro g hg
        rcases hg with ⟨χ, h, h0, hh_compact, rfl⟩
        have hvanish :
            VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) :=
          twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0
        let hmem : zeroOriginAvoidingSubmodule d := ⟨h, h0⟩
        rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply
            (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
            hKd_meas C_bd N hC_bd hKd_bound
            (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))]
        rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
            (f := twoPointDifferenceLift χ h) hvanish]
        calc
          ∫ x : NPointDomain d 2,
              OSReconstruction.twoPointDifferenceKernel (d := d) Kd x *
                (twoPointDifferenceLift χ h x)
            = (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, Kd ξ * h ξ := by
                exact
                  OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
                    (d := d) Kd χ h
          _ = (∫ u : SpacetimeDim d, χ u) *
                (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
                  (d := d) OS χ₀) hmem := by
                rw [hZero hmem hh_compact]
          _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
                symm
                rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
                  (d := d) (OS := OS) χ₀ hχ₀ χ hmem]
                ring
      · simp
      · intro f g _ _ hf hg
        rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, hf, hg]
      · intro a f _ hf
        rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, hf]
    apply ContinuousLinearMap.eq_of_eq_on_dense
      (OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
        hKd_meas C_bd N hC_bd hKd_bound)
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2)
      zeroOrigin_differenceShell_span_dense_zeroDiagonal
    intro f hf
    exact hOnSpan f hf
  let K : SpacetimeDim d → SpacetimeDim d → ℂ := fun x₀ x₁ => Kd (x₁ - x₀)
  refine ⟨K, ?_, ?_⟩
  · have hmaps :
        Set.MapsTo (fun p : SpacetimeDim d × SpacetimeDim d => p.2 - p.1)
          {p : SpacetimeDim d × SpacetimeDim d | p.1 ≠ p.2}
          {ξ : SpacetimeDim d | ξ ≠ 0} := by
        intro p hp
        simpa [sub_eq_zero] using hp.symm
    simpa [K] using
      (hKd_cont.comp (((continuous_snd : Continuous fun p : SpacetimeDim d × SpacetimeDim d => p.2).sub
        (continuous_fst : Continuous fun p : SpacetimeDim d × SpacetimeDim d => p.1))).continuousOn
        hmaps)
  · intro f
    have happly :=
      congrArg (fun L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ => L f) hCLM
    change
      OSReconstruction.twoPointZeroDiagonalKernelCLM
          (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
          hKd_meas C_bd N hC_bd hKd_bound f =
        OS.S 2 f at happly
    rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply
        (d := d) (OSReconstruction.twoPointDifferenceKernel (d := d) Kd)
        hKd_meas C_bd N hC_bd hKd_bound] at happly
    rw [← happly]
    let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
      MeasurableEquiv.finTwoArrow
    have heprod :
        MeasureTheory.MeasurePreserving eprod
          MeasureTheory.volume MeasureTheory.volume := by
      simpa [eprod] using
        (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
    calc
      ∫ x : NPointDomain d 2, OSReconstruction.twoPointDifferenceKernel (d := d) Kd x * f.1 x =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          (OSReconstruction.twoPointDifferenceKernel (d := d) Kd) (eprod.symm p) * f.1 (eprod.symm p)
            ∂ (volume.prod volume) := by
            symm
            simpa [eprod] using
              heprod.symm.integral_comp'
                (g := fun x : NPointDomain d 2 =>
                  OSReconstruction.twoPointDifferenceKernel (d := d) Kd x * f.1 x)
      _ =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 *
            f.1 (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with p
            rcases p with ⟨x₀, x₁⟩
            have heq :
                eprod.symm (x₀, x₁) = Fin.cons x₀ (Fin.cons x₁ Fin.elim0) := by
              ext i μ
              fin_cases i <;> rfl
            simp [heq, K, OSReconstruction.twoPointDifferenceKernel, sub_eq_add_neg]
