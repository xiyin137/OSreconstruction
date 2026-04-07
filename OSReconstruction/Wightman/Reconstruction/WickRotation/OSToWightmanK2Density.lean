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
import OSReconstruction.Wightman.Reconstruction.DenseCLM

/-!
# `k = 2` Density Lemmas

This file isolates the route-independent density / cutoff seam used in the
`k = 2` OS route:

- density of admissible difference shells in `ZeroDiagonalSchwartz d 2`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Complex Topology
open OSReconstruction
open scoped Pointwise SchwartzMap LineDeriv

variable {d : ℕ} [NeZero d]

set_option linter.unusedSectionVars false

/-- Multiplying a zero-diagonal Schwartz test by an arbitrary Schwartz cutoff on
the ambient two-point space preserves vanishing to infinite order on the
coincidence locus. -/
private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
    {n : ℕ} {ψ f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply
        (g := ((ψ : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        ψ.hasTemperateGrowth f y)
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (ψ.smooth ⊤) (f.smooth ⊤) x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψ : NPointDomain d n → ℂ) x‖ *
          ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x = 0 := hf (k - i) x hx
    simp [hfi]
  have hnonneg :
      0 ≤ ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ := norm_nonneg _
  have hzero_norm :
      ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      simpa [hsum_zero] using hle
    · exact hnonneg
  exact norm_eq_zero.mp hzero_norm

/-- Multiplying a zero-diagonal Schwartz test by any smooth temperate scalar
factor on the ambient two-point space preserves vanishing to infinite order on
the coincidence locus. -/
private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_of_smooth
    {n : ℕ} {ψ : NPointDomain d n → ℂ}
    (hψ_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ_temp : ψ.HasTemperateGrowth)
    {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply (g := ψ) hψ_temp f y)
  let ffun : NPointDomain d n → ℂ := (f : NPointDomain d n → ℂ)
  have hffun : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ffun := by
    simpa [ffun] using f.smooth'
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hψ_smooth
      hffun x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
          ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x = 0 := hf (k - i) x hx
    simp [hfi]
  have hzero_norm :
      ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      calc
        ‖iteratedFDeriv ℝ k (fun y : NPointDomain d n => ψ y * f y) x‖
            ≤
          ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
              ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ := by
                simpa [ffun] using hle
        _ = 0 := hsum_zero
    · exact norm_nonneg _
  exact norm_eq_zero.mp hzero_norm

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
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply] at hdiag
    exact
      ((continuousMultilinearCurryFin0 ℝ (NPointDomain d 2) ℂ).symm.map_eq_zero_iff).mp hdiag
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
        change
          (fderiv ℝ
              (fun y : NPointDomain d 2 =>
                χ (y 0) * (LineDeriv.iteratedLineDerivOp (Fin.tail u) h) (y 1)) x)
              (insDiff (u 0)) =
            χ (x 0) *
              (fderiv ℝ
                (fun z : SpacetimeDim d =>
                  (LineDeriv.iteratedLineDerivOp (Fin.tail u) h) z) (x 1)) (u 0)
        simpa [insDiff, ContinuousLinearMap.comp_apply, mul_add, add_mul] using happly
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

/-- If a Schwartz function vanishes on a neighborhood of `x`, then every
iterated Fréchet derivative vanishes at `x`. -/
private theorem iteratedFDeriv_eq_zero_of_notMem_tsupport
    (h : SchwartzSpacetime d) {x : SpacetimeDim d}
    (hx : x ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) x = 0 := by
  intro k
  have hev : (h : SpacetimeDim d → ℂ) =ᶠ[𝓝 x] 0 := by
    simpa [notMem_tsupport_iff_eventuallyEq] using hx
  rw [Filter.eventuallyEq_iff_exists_mem] at hev
  obtain ⟨s, hs_mem, hs_eq⟩ := hev
  rw [mem_nhds_iff] at hs_mem
  obtain ⟨t, ht_sub, ht_open, hxt⟩ := hs_mem
  have hEqOn : Set.EqOn (h : SpacetimeDim d → ℂ) 0 t := by
    intro y hy
    exact hs_eq (ht_sub hy)
  have hderivEqWithin :
      iteratedFDerivWithin ℝ k (h : SpacetimeDim d → ℂ) t x =
        iteratedFDerivWithin ℝ k (fun _ : SpacetimeDim d => (0 : ℂ)) t x := by
    simpa using
      (iteratedFDerivWithin_congr
        (f₁ := (h : SpacetimeDim d → ℂ))
        (f := fun _ : SpacetimeDim d => (0 : ℂ))
        (s := t) hEqOn hxt k)
  have hderivEq :
      iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) x =
        iteratedFDeriv ℝ k (fun _ : SpacetimeDim d => (0 : ℂ)) x := by
    rw [← iteratedFDerivWithin_of_isOpen k ht_open hxt,
      hderivEqWithin, iteratedFDerivWithin_of_isOpen k ht_open hxt]
  rw [hderivEq]
  ext u
  simp

/-- The standard compact radial bump on spacetime, rescaled to radius `R`. -/
private abbrev spacetimeUnitBallBumpRadius (R : ℝ) (hR : 0 < R) : SchwartzSpacetime d :=
  unitBallBumpSchwartzPiRadius (d + 1) R hR

/-- The model unit-ball Schwartz bump vanishes outside the radius-`2` ball. -/
private theorem unitBallBumpSchwartzPi_zero_of_two_le_norm {m : ℕ}
    {x : Fin m → ℝ} (hx : 2 ≤ ‖x‖) :
    unitBallBumpSchwartzPi m x = 0 := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBallBumpSchwartzPi m x = f x := by
    change (HasCompactSupport.toSchwartzMap hf_compact hf_smooth : SchwartzMap (Fin m → ℝ) ℂ) x = f x
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [happly]
  rw [show f x = ((b x : ℝ) : ℂ) by rfl]
  refine congrArg (fun r : ℝ => (r : ℂ)) ?_
  have hdist : 2 ≤ dist x 0 := by simpa [dist_eq_norm] using hx
  exact b.zero_of_le_dist hdist

/-- The rescaled spacetime bump vanishes outside the radius-`2R` ball. -/
private theorem spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm
    {R : ℝ} (hR : 0 < R) {x : SpacetimeDim d}
    (hx : 2 * R ≤ ‖x‖) :
    spacetimeUnitBallBumpRadius (d := d) R hR x = 0 := by
  rw [spacetimeUnitBallBumpRadius, unitBallBumpSchwartzPiRadius_apply]
  apply unitBallBumpSchwartzPi_zero_of_two_le_norm
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  rw [le_inv_mul_iff₀ hR]
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hx

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

/-- A single directional derivative costs one derivative-order Schwartz seminorm
and one factor of the direction norm. -/
private theorem seminorm_zero_lineDeriv_le
    (h : SchwartzSpacetime d) (v : SpacetimeDim d) (n : ℕ) :
    SchwartzMap.seminorm ℝ 0 n (LineDeriv.lineDerivOp v h : SchwartzSpacetime d) ≤
      ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) h := by
  refine SchwartzMap.seminorm_le_bound ℝ 0 n
    (LineDeriv.lineDerivOp v h : SchwartzSpacetime d) (by positivity) ?_
  intro x
  calc
    ‖x‖ ^ 0 *
        ‖iteratedFDeriv ℝ n
            (((LineDeriv.lineDerivOp v h : SchwartzSpacetime d) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖
        =
      ‖iteratedFDeriv ℝ n
          (((LineDeriv.lineDerivOp v h : SchwartzSpacetime d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) x‖ := by
            simp
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ)) x v‖ := by
          rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ)) x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (n + 1) (h : SpacetimeDim d → ℂ) x‖ * ‖v‖ := by
          rw [norm_fderiv_iteratedFDeriv]
    _ ≤ (SchwartzMap.seminorm ℝ 0 (n + 1) h) * ‖v‖ := by
          gcongr
          exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h (n + 1) x
    _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) h := by
          ring

/-- Iterated directional derivatives are uniformly controlled by the matching
zero-weight higher Schwartz seminorm, with one factor of `‖u i‖` per
direction. -/
private theorem iteratedLineDeriv_seminorm_zero_le
    (h : SchwartzSpacetime d) (j n : ℕ) :
    ∀ u : Fin j → SpacetimeDim d,
      SchwartzMap.seminorm ℝ 0 n (LineDeriv.iteratedLineDerivOp u h : SchwartzSpacetime d) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) h := by
  induction j generalizing h n with
  | zero =>
      intro u
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      intro u
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      calc
        SchwartzMap.seminorm ℝ 0 n (∂_{u 0} (∂^{Fin.tail u} h) : SchwartzSpacetime d)
            ≤ ‖u 0‖ * SchwartzMap.seminorm ℝ 0 (n + 1) (∂^{Fin.tail u} h : SchwartzSpacetime d) := by
              exact seminorm_zero_lineDeriv_le (h := ∂^{Fin.tail u} h) (v := u 0) (n := n)
        _ ≤ ‖u 0‖ *
              ((∏ i, ‖Fin.tail u i‖) * SchwartzMap.seminorm ℝ 0 (n + 1 + j) h) := by
              gcongr
              exact ih (h := h) (n := n + 1) (u := Fin.tail u)
        _ = (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + (j + 1)) h := by
              rw [Fin.prod_univ_succ, add_assoc]
              have htail : (∏ i : Fin j, ‖Fin.tail u i‖) = ∏ i : Fin j, ‖u i.succ‖ := rfl
              rw [htail]
              ring

/-- Pointwise version of `iteratedLineDeriv_seminorm_zero_le`. -/
private theorem norm_iteratedFDeriv_iteratedLineDeriv_le
    (h : SchwartzSpacetime d) (j n : ℕ) :
    ∀ (u : Fin j → SpacetimeDim d) (x : SpacetimeDim d),
      ‖iteratedFDeriv ℝ n ((LineDeriv.iteratedLineDerivOp u h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) x‖ ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) h := by
  intro u x
  exact le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (∂^{u} h) n x)
    (iteratedLineDeriv_seminorm_zero_le (h := h) (j := j) (n := n) u)

/-- If all iterated derivatives of `h` vanish at the origin, then the same is
true for every iterated directional derivative of `h`. -/
private theorem iteratedLineDeriv_vanish_at_zero
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ n : ℕ, iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ) 0 = 0)
    {j : ℕ} (u : Fin j → SpacetimeDim d) (n : ℕ) :
    iteratedFDeriv ℝ n ((∂^{u} h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) 0 = 0 := by
  induction j generalizing h n with
  | zero =>
      simpa [LineDeriv.iteratedLineDerivOp_fin_zero] using h_vanish n
  | succ j ih =>
      have hu : u = Fin.snoc (Fin.init u) (u (Fin.last j)) := by
        exact (Fin.snoc_init_self u).symm
      rw [hu, LineDeriv.iteratedLineDerivOp_succ_right]
      simp only [Fin.init_snoc, Fin.snoc_last]
      let f : SchwartzSpacetime d := ∂_{u (Fin.last j)} h
      have hf_vanish : ∀ m : ℕ, iteratedFDeriv ℝ m (f : SpacetimeDim d → ℂ) 0 = 0 := by
        intro m
        ext w
        let w' : Fin (m + 1) → SpacetimeDim d := Fin.snoc w (u (Fin.last j))
        have hzero := h_vanish (m + 1)
        have hzero_apply : iteratedFDeriv ℝ (m + 1) (h : SpacetimeDim d → ℂ) 0 w' = 0 := by
          simpa [w'] using congrArg (fun T => T w') hzero
        simpa [f, w', iteratedFDeriv_lineDeriv_eq_snoc] using hzero_apply
      simpa [f] using ih (h := f) (h_vanish := hf_vanish) (u := Fin.init u) (n := n)

/-- Quantitative flatness for iterated directional derivatives on the unit ball. -/
private theorem exists_iteratedLineDeriv_flat_bound
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ n : ℕ, iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ) 0 = 0)
    (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Fin j → SpacetimeDim d) (x : SpacetimeDim d),
        ‖(LineDeriv.iteratedLineDerivOp u h : SchwartzSpacetime d) x‖ ≤
          C * ‖x‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 (j + (m + 1)) h
  refine ⟨A / (((Nat.factorial m : ℕ) : ℝ)), by positivity, ?_⟩
  intro u x
  let F : SchwartzSpacetime d := ∂^{u} h
  let L : ℝ →L[ℝ] SpacetimeDim d :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x
  let g : ℝ → ℂ := (fun z : SpacetimeDim d => (F : SpacetimeDim d → ℂ) z) ∘ L
  have hF_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (F : SpacetimeDim d → ℂ) := fun r => by
    simpa [F] using (F.smooth r)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hF_contDiff r))
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_mem : k ∈ Finset.range (m + 1) := hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
          ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (F : SpacetimeDim d → ℂ) (L 0)).compContinuousLinearMap
              (fun _ : Fin k => L) := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := (F : SpacetimeDim d → ℂ))
            (hF_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k (F : SpacetimeDim d → ℂ) (L 0) = 0 := by
        simpa [F, L, ContinuousLinearMap.smulRight_apply] using
          iteratedLineDeriv_vanish_at_zero (h := h) h_vanish u k
      rw [hcomp, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A * ∏ i, ‖u i‖) * ‖x‖ ^ (m + 1) := by
    intro t ht
    have hL :
        ‖L‖ ≤ ‖x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      calc
        ‖L s‖ = ‖s • x‖ := by rfl
        _ = ‖s‖ * ‖x‖ := norm_smul s x
        _ = ‖x‖ * ‖s‖ := by ring
        _ ≤ ‖x‖ * ‖s‖ := le_rfl
    rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (F : SpacetimeDim d → ℂ) (L t)).compContinuousLinearMap
            (fun _ : Fin (m + 1) => L) := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := (F : SpacetimeDim d → ℂ))
          (hF_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp]
    have hFbound :
        ‖iteratedFDeriv ℝ (m + 1) (F : SpacetimeDim d → ℂ) (L t)‖ ≤
          A * ∏ i, ‖u i‖ := by
      simpa [A, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
        norm_iteratedFDeriv_iteratedLineDeriv_le
          (h := h) (j := j) (n := m + 1) u (L t)
    have hprod_nonneg : 0 ≤ ∏ _ : Fin (m + 1), ‖L‖ := by
      positivity
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (F : SpacetimeDim d → ℂ) (L t)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖
          ≤ ‖iteratedFDeriv ℝ (m + 1) (F : SpacetimeDim d → ℂ) (L t)‖ *
              ∏ _ : Fin (m + 1), ‖L‖ := by
                exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (A * ∏ i, ‖u i‖) * ∏ _ : Fin (m + 1), ‖L‖ := by
            exact mul_le_mul_of_nonneg_right hFbound hprod_nonneg
      _ = (A * ∏ i, ‖u i‖) * ‖L‖ ^ (m + 1) := by
            simp
      _ ≤ (A * ∏ i, ‖u i‖) * ‖x‖ ^ (m + 1) := by
            gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A * ∏ i, ‖u i‖) * ‖x‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hg_one : g 1 = F x := by
    simp [g, L, ContinuousLinearMap.smulRight_apply]
  calc
    ‖(F : SpacetimeDim d → ℂ) x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
          rw [hg_one]
          simp [hTaylor_zero]
    _ ≤ ((A * ∏ i, ‖u i‖) * ‖x‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
          simpa [hTaylor_zero] using hrem
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
          field_simp [Nat.cast_ne_zero]
          ring

/-- Operator-valued flatness near the origin for iterated Fréchet derivatives of
`h`. -/
private theorem exists_iteratedFDeriv_flat_bound
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ n : ℕ, iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ) 0 = 0)
    (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : SpacetimeDim d,
        ‖iteratedFDeriv ℝ j (h : SpacetimeDim d → ℂ) x‖ ≤ C * ‖x‖ ^ (m + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_iteratedLineDeriv_flat_bound (h := h) h_vanish j m
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  have hCx : 0 ≤ C * ‖x‖ ^ (m + 1) := by positivity
  rw [ContinuousMultilinearMap.opNorm_le_iff hCx]
  intro u
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, mul_assoc, mul_left_comm, mul_comm]
    using hC u x

/-- Core power estimate used in the small-origin cutoff proof. -/
private theorem small_origin_power_factor_le
    {N M i : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ_le : δ ≤ 1)
    {x : SpacetimeDim d} (hx : ‖x‖ ≤ 2 * δ) (hi : i ∈ Finset.range (M + 1)) :
    ‖x‖ ^ N * (δ⁻¹) ^ i * ‖x‖ ^ (M + 1) ≤ (2 : ℝ) ^ (N + M + 1) * δ := by
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hi_le : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpowN : ‖x‖ ^ N ≤ (2 * δ) ^ N := by
    gcongr
  have hpowM : ‖x‖ ^ (M + 1) ≤ (2 * δ) ^ (M + 1) := by
    gcongr
  have hdelta_inv_mono :
      (δ⁻¹) ^ i ≤ (δ⁻¹) ^ M := by
    have hδ_inv_ge_one : 1 ≤ δ⁻¹ := by
      rw [one_le_inv₀ hδ]
      exact hδ_le
    exact pow_le_pow_right₀ hδ_inv_ge_one hi_le
  have hcancel : (δ⁻¹) ^ M * δ ^ (M + 1) = δ := by
    calc
      (δ⁻¹) ^ M * δ ^ (M + 1) = ((δ⁻¹) ^ M * δ ^ M) * δ := by
            rw [pow_succ']
            ring
      _ = (((δ ^ M)⁻¹ * δ ^ M) * δ) := by rw [inv_pow]
      _ = δ := by simp [pow_ne_zero M hδ.ne']
  have hδN_le : δ ^ N ≤ 1 := pow_le_one₀ hδ_nonneg hδ_le
  calc
    ‖x‖ ^ N * (δ⁻¹) ^ i * ‖x‖ ^ (M + 1)
        ≤ (2 * δ) ^ N * (δ⁻¹) ^ i * (2 * δ) ^ (M + 1) := by
            gcongr
    _ ≤ (2 * δ) ^ N * (δ⁻¹) ^ M * (2 * δ) ^ (M + 1) := by
          gcongr
    _ = (2 : ℝ) ^ N * (2 : ℝ) ^ (M + 1) * (δ ^ N * ((δ⁻¹) ^ M * δ ^ (M + 1))) := by
          rw [mul_pow, mul_pow]
          ring_nf
    _ = (2 : ℝ) ^ (N + M + 1) * (δ ^ N * ((δ⁻¹) ^ M * δ ^ (M + 1))) := by
          rw [← pow_add]
          ring
    _ = (2 : ℝ) ^ (N + M + 1) * (δ ^ N * δ) := by rw [hcancel]
    _ ≤ (2 : ℝ) ^ (N + M + 1) * δ := by
          have hmult : δ ^ N * δ ≤ (1 : ℝ) * δ := by
            gcongr
          simpa using hmult

/-- Uniform linear small-origin bound for the local cutoff piece. This is the
quantitative core behind the origin-avoidance approximation: once `h` vanishes
to infinite order at the origin, every Schwartz seminorm of `ρ_δ · h` is
bounded by `A * δ` for all sufficiently small `δ`. -/
private theorem schwartz_small_origin_cutoff_seminorm_le_linear
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (N M : ℕ),
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
          SchwartzMap.seminorm ℝ N M
            ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                  SchwartzSpacetime d)) ≤
              A * δ := by
  intro N M
  let B : ℕ → ℝ := fun i =>
    Classical.choose (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)
  let H : ℕ → ℝ := fun i =>
    Classical.choose (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)
  let A : ℝ :=
    ∑ i ∈ Finset.range (M + 1),
      (M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)
  have hB_nonneg : ∀ i : ℕ, 0 ≤ B i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)).1
  have hB_bound :
      ∀ i : ℕ, ∀ (δ : ℝ) (hδ : 0 < δ) (x : SpacetimeDim d),
        ‖iteratedFDeriv ℝ i
            ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖ ≤
          B i * (δ⁻¹) ^ i := by
    intro i δ hδ x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)).2 δ hδ x
  have hH_nonneg : ∀ i : ℕ, 0 ≤ H i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)).1
  have hH_bound :
      ∀ i : ℕ, ∀ x : SpacetimeDim d,
        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
          H i * ‖x‖ ^ (M + 1) := by
    intro i x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)).2 x
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hBi : 0 ≤ B i := hB_nonneg i
    have hHi : 0 ≤ H i := hH_nonneg i
    positivity
  refine ⟨A, hA_nonneg, ?_⟩
  intro δ hδ hδ_le_one
  let ψδ : SchwartzSpacetime d := spacetimeUnitBallBumpRadius (d := d) δ hδ
  let fδ : SchwartzSpacetime d := SchwartzMap.smulLeftCLM ℂ ψδ h
  have hsupp_psi :
      Function.support ((ψδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    by_contra hxball
    rw [Metric.mem_closedBall, dist_eq_norm] at hxball
    have hnorm : 2 * δ ≤ ‖x‖ := by
      have hdist : 2 * δ ≤ dist x 0 := le_of_not_ge hxball
      simpa [dist_eq_norm] using hdist
    have hzero : ψδ x = 0 := by
      exact spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm (d := d) hδ hnorm
    exact hx (by simpa [Function.mem_support] using hzero)
  have htsupport_psi :
      tsupport (((ψδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    exact closure_minimal hsupp_psi Metric.isClosed_closedBall
  have htsupport_fδ :
      tsupport ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    exact htsupport_psi
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((ψδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) (f := h) hx).2)
  have hsupport_deriv :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    exact htsupport_fδ
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) hx)
  have hbound :
      ∀ x : SpacetimeDim d,
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖ ≤
          A * δ := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : SpacetimeDim d) (2 * δ)
    · have hsmul :=
          norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (ψδ.smooth ⊤) (h.smooth ⊤) x
            (n := M) (by exact_mod_cast le_top)
      have hfun :
          (((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) =
            fun y => ψδ y * h y := by
        funext y
        simpa [fδ, smul_eq_mul] using
          (SchwartzMap.smulLeftCLM_apply_apply (g := ((ψδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) ψδ.hasTemperateGrowth h y)
      calc
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖
            = ‖x‖ ^ N * ‖iteratedFDeriv ℝ M (fun y => ψδ y * h y) x‖ := by
                rw [hfun]
        _ ≤ ‖x‖ ^ N *
              ∑ i ∈ Finset.range (M + 1),
                (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ := by
                exact mul_le_mul_of_nonneg_left hsmul (by positivity)
        _ = ∑ i ∈ Finset.range (M + 1),
              ‖x‖ ^ N *
                ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Finset.range (M + 1),
              ((M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)) * δ := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hxnorm : ‖x‖ ≤ 2 * δ := by
                  simpa [Metric.mem_closedBall, dist_eq_norm] using hx
                have hBi := hB_bound i δ hδ x
                have hHi := hH_bound i x
                have hBi_nonneg : 0 ≤ B i := hB_nonneg i
                have hBi_rhs_nonneg : 0 ≤ B i * (δ⁻¹) ^ i := by positivity
                have hchoose_nonneg : 0 ≤ (M.choose i : ℝ) := by positivity
                have hprod :
                    ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
                      (B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1)) := by
                  exact mul_le_mul hBi hHi (norm_nonneg _) hBi_rhs_nonneg
                have hterm_coeff :
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
                      (M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1))) := by
                  calc
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖
                        =
                      (M.choose i : ℝ) * (‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) := by
                          ring
                    _ ≤ (M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1))) := by
                          exact mul_le_mul_of_nonneg_left hprod hchoose_nonneg
                have hterm :
                    ‖x‖ ^ N *
                        ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                          ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) ≤
                      ‖x‖ ^ N *
                        ((M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1)))) := by
                  exact mul_le_mul_of_nonneg_left hterm_coeff (by positivity)
                calc
                  ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖)
                      ≤
                    ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) *
                        (H i * ‖x‖ ^ (M + 1)))) := by
                          exact hterm
                  _ = ((M.choose i : ℝ) * B i * H i) *
                        (‖x‖ ^ N * (δ⁻¹) ^ i * ‖x‖ ^ (M + 1)) := by
                          ring
                  _ ≤ ((M.choose i : ℝ) * B i * H i) *
                        ((2 : ℝ) ^ (N + M + 1) * δ) := by
                          have hcoeff_nonneg : 0 ≤ (M.choose i : ℝ) * B i * H i := by
                            exact mul_nonneg (mul_nonneg hchoose_nonneg hBi_nonneg) (hH_nonneg i)
                          exact mul_le_mul_of_nonneg_left
                            (small_origin_power_factor_le (d := d) hδ hδ_le_one hxnorm hi)
                            hcoeff_nonneg
                  _ = ((M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)) * δ := by
                          ring
        _ = A * δ := by
              simp [A, Finset.sum_mul]
    · have hzero :
          iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x = 0 := by
        by_contra hne
        have hx_support :
            x ∈ Function.support
              (iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
          simpa [Function.mem_support] using hne
        exact hx (hsupport_deriv hx_support)
      have hnonneg : 0 ≤ A * δ := by positivity
      simpa [hzero] using hnonneg
  exact SchwartzMap.seminorm_le_bound ℝ N M fδ (by positivity) hbound

/-- Eventual small-origin version of the local cutoff estimate: below some
radius `δ₀`, every smaller cutoff has Schwartz seminorm error `< ε`. -/
private theorem schwartz_small_origin_cutoff_seminorm_eventually_small
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (N M : ℕ) (ε : ℝ) (_hε : 0 < ε),
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
          SchwartzMap.seminorm ℝ N M
            ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                  SchwartzSpacetime d)) < ε := by
  intro N M ε hε
  obtain ⟨A, hA_nonneg, hA_bound⟩ :=
    schwartz_small_origin_cutoff_seminorm_le_linear (d := d) (h := h) h_vanish N M
  let δ₀ : ℝ := min 1 (ε / (A + 1))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    refine lt_min zero_lt_one ?_
    have hA1_pos : 0 < A + 1 := by positivity
    exact div_pos hε hA1_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδ_le
  have hδ_le_one : δ ≤ 1 := le_trans hδ_le (min_le_left _ _)
  have hsemi_le : SchwartzMap.seminorm ℝ N M
      ((SchwartzMap.smulLeftCLM ℂ
          (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
            SchwartzSpacetime d)) ≤ A * δ := hA_bound δ hδ hδ_le_one
  have hδ_upper : δ ≤ ε / (A + 1) := by
    exact le_trans hδ_le (min_le_right _ _)
  have hA_lt : A * δ < ε := by
    calc
      A * δ ≤ A * (ε / (A + 1)) := by
            gcongr
      _ < ε := by
            have hA1_pos : 0 < A + 1 := by positivity
            have hA1_ne : (A + 1) ≠ 0 := by positivity
            have hrewrite : A * (ε / (A + 1)) = ε - ε / (A + 1) := by
              field_simp [show (A + 1) ≠ 0 by positivity]
              ring
            rw [hrewrite]
            have hsub_pos : 0 < ε / (A + 1) := by positivity
            linarith
  exact lt_of_le_of_lt hsemi_le hA_lt

/-- Schwartz functions vanishing to infinite order at the origin can be
be cut off near the origin with arbitrarily small Schwartz seminorm error. -/
private theorem schwartz_small_origin_cutoff_seminorm_small
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (N M : ℕ) (ε : ℝ) (_hε : 0 < ε),
      ∃ (δ : ℝ) (hδ : 0 < δ),
        SchwartzMap.seminorm ℝ N M
          ((SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                SchwartzSpacetime d)) < ε := by
  intro N M ε hε
  let B : ℕ → ℝ := fun i =>
    Classical.choose (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)
  let H : ℕ → ℝ := fun i =>
    Classical.choose (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)
  let A : ℝ :=
    ∑ i ∈ Finset.range (M + 1),
      (M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)
  have hB_nonneg : ∀ i : ℕ, 0 ≤ B i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)).1
  have hB_bound :
      ∀ i : ℕ, ∀ (δ : ℝ) (hδ : 0 < δ) (x : SpacetimeDim d),
        ‖iteratedFDeriv ℝ i
            ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖ ≤
          B i * (δ⁻¹) ^ i := by
    intro i δ hδ x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) i)).2 δ hδ x
  have hH_nonneg : ∀ i : ℕ, 0 ≤ H i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)).1
  have hH_bound :
      ∀ i : ℕ, ∀ x : SpacetimeDim d,
        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
          H i * ‖x‖ ^ (M + 1) := by
    intro i x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_flat_bound (d := d) (h := h) h_vanish (M - i) M)).2 x
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hBi : 0 ≤ B i := hB_nonneg i
    have hHi : 0 ≤ H i := hH_nonneg i
    positivity
  let δ : ℝ := min 1 (ε / (2 * (A + 1) ^ 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min zero_lt_one ?_
    positivity
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  let ψδ : SchwartzSpacetime d := spacetimeUnitBallBumpRadius (d := d) δ hδ
  let fδ : SchwartzSpacetime d := SchwartzMap.smulLeftCLM ℂ ψδ h
  have hsupp_psi :
      Function.support ((ψδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    by_contra hxball
    rw [Metric.mem_closedBall, dist_eq_norm] at hxball
    have hnorm : 2 * δ ≤ ‖x‖ := by
      have hdist : 2 * δ ≤ dist x 0 := le_of_not_ge hxball
      simpa [dist_eq_norm] using hdist
    have hzero : ψδ x = 0 := by
      exact spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm (d := d) hδ hnorm
    exact hx (by simpa [Function.mem_support] using hzero)
  have htsupport_psi :
      tsupport (((ψδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    exact closure_minimal hsupp_psi Metric.isClosed_closedBall
  have htsupport_fδ :
      tsupport ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    exact htsupport_psi
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ((ψδ : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) (f := h) hx).2)
  have hsupport_deriv :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 * δ) := by
    intro x hx
    exact htsupport_fδ
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) hx)
  have hbound :
      ∀ x : SpacetimeDim d,
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖ ≤
          A * δ := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : SpacetimeDim d) (2 * δ)
    · have hsmul :=
          norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (ψδ.smooth ⊤) (h.smooth ⊤) x
            (n := M) (by exact_mod_cast le_top)
      have hfun :
          (((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) =
            fun y => ψδ y * h y := by
        funext y
        simpa [fδ, smul_eq_mul] using
          (SchwartzMap.smulLeftCLM_apply_apply (g := ((ψδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) ψδ.hasTemperateGrowth h y)
      calc
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖
            = ‖x‖ ^ N * ‖iteratedFDeriv ℝ M (fun y => ψδ y * h y) x‖ := by
                rw [hfun]
        _ ≤ ‖x‖ ^ N *
              ∑ i ∈ Finset.range (M + 1),
                (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ := by
                exact mul_le_mul_of_nonneg_left hsmul (by positivity)
        _ = ∑ i ∈ Finset.range (M + 1),
              ‖x‖ ^ N *
                ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Finset.range (M + 1),
              ((M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)) * δ := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hxnorm : ‖x‖ ≤ 2 * δ := by
                  simpa [Metric.mem_closedBall, dist_eq_norm] using hx
                have hBi := hB_bound i δ hδ x
                have hHi := hH_bound i x
                have hBi_nonneg : 0 ≤ B i := hB_nonneg i
                have hBi_rhs_nonneg : 0 ≤ B i * (δ⁻¹) ^ i := by positivity
                have hchoose_nonneg : 0 ≤ (M.choose i : ℝ) := by positivity
                have hprod :
                    ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
                      (B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1)) := by
                  exact mul_le_mul hBi hHi (norm_nonneg _) hBi_rhs_nonneg
                have hterm_coeff :
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖ ≤
                      (M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1))) := by
                  calc
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖
                        =
                      (M.choose i : ℝ) * (‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) := by
                          ring
                    _ ≤ (M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1))) := by
                          exact mul_le_mul_of_nonneg_left hprod hchoose_nonneg
                have hterm :
                    ‖x‖ ^ N *
                        ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                          ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖) ≤
                      ‖x‖ ^ N *
                        ((M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x‖ ^ (M + 1)))) := by
                  exact mul_le_mul_of_nonneg_left hterm_coeff (by positivity)
                calc
                  ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψδ : SpacetimeDim d → ℂ) x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (h : SpacetimeDim d → ℂ) x‖)
                      ≤
                    ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) *
                        (H i * ‖x‖ ^ (M + 1)))) := by
                          exact hterm
                  _ = ((M.choose i : ℝ) * B i * H i) *
                        (‖x‖ ^ N * (δ⁻¹) ^ i * ‖x‖ ^ (M + 1)) := by
                          ring
                  _ ≤ ((M.choose i : ℝ) * B i * H i) *
                        ((2 : ℝ) ^ (N + M + 1) * δ) := by
                          have hcoeff_nonneg : 0 ≤ (M.choose i : ℝ) * B i * H i := by
                            exact mul_nonneg (mul_nonneg hchoose_nonneg hBi_nonneg) (hH_nonneg i)
                          exact mul_le_mul_of_nonneg_left
                            (small_origin_power_factor_le (d := d) hδ hδ_le_one hxnorm hi)
                            hcoeff_nonneg
                  _ = ((M.choose i : ℝ) * B i * H i * (2 : ℝ) ^ (N + M + 1)) * δ := by
                          ring
        _ = A * δ := by
              simp [A, Finset.sum_mul]
    · have hzero :
          iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x = 0 := by
        by_contra hne
        have hx_support :
            x ∈ Function.support
              (iteratedFDeriv ℝ M ((fδ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
          simpa [Function.mem_support] using hne
        exact hx (hsupport_deriv hx_support)
      have hnonneg : 0 ≤ A * δ := by positivity
      simpa [hzero] using hnonneg
  have hsemi :
      SchwartzMap.seminorm ℝ N M fδ ≤ A * δ := by
    refine SchwartzMap.seminorm_le_bound ℝ N M fδ ?_ ?_
    · positivity
    · exact hbound
  have hAδ_lt : A * δ < ε := by
    have hδ_upper : δ ≤ ε / (2 * (A + 1) ^ 2) := by
      dsimp [δ]
      exact min_le_right _ _
    have hA1_pos : 0 < A + 1 := by positivity
    have hA_le_sq : A ≤ (A + 1) ^ 2 := by
      nlinarith [hA_nonneg]
    calc
      A * δ ≤ A * (ε / (2 * (A + 1) ^ 2)) := by
            gcongr
      _ ≤ (A + 1) ^ 2 * (ε / (2 * (A + 1) ^ 2)) := by
            gcongr
      _ = ε / 2 := by
            field_simp [show (A + 1) ≠ 0 by positivity]
      _ < ε := by linarith
  exact ⟨δ, hδ, lt_of_le_of_lt hsemi hAδ_lt⟩

/-- Schwartz functions can be cut off at large radius with arbitrarily small
Schwartz seminorm error. -/
private theorem schwartz_large_radius_cutoff_seminorm_small
    (h : SchwartzSpacetime d) :
    ∀ (N M : ℕ) (ε Rmin : ℝ) (_hε : 0 < ε) (hRmin : 0 < Rmin),
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
  intro N M ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ :=
    schwartz_small_origin_cutoff_seminorm_small (d := d) (h := h) h_vanish N M (ε / 2) hε2
  obtain ⟨R, hR, hlarge⟩ :=
    schwartz_large_radius_cutoff_seminorm_small (d := d) (h := h) N M (ε / 2) δ hε2 hδ
  let h' : SchwartzSpacetime d :=
    SchwartzMap.smulLeftCLM ℂ
      (fun x : SpacetimeDim d =>
        spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
          spacetimeUnitBallBumpRadius (d := d) δ hδ x) h
  refine ⟨h', ?_, ?_, ?_⟩
  · intro hz
    exact zero_not_mem_tsupport_annulusCutoff (d := d) δ R hδ hR
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (g := (fun x : SpacetimeDim d =>
          spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
            spacetimeUnitBallBumpRadius (d := d) δ hδ x))
        (f := h) hz).2)
  · exact hasCompactSupport_annulusCutoff_mul (d := d) h δ R hδ hR
  · have hdecomp :
        h - h' =
          (h -
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                SchwartzSpacetime d)) +
          (SchwartzMap.smulLeftCLM ℂ
            (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d) := by
        ext x
        have hRtemp :=
          (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)).hasTemperateGrowth
        have hδtemp := (spacetimeUnitBallBumpRadius (d := d) δ hδ).hasTemperateGrowth
        have hdiffTemp :
            (fun x : SpacetimeDim d =>
              spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
                spacetimeUnitBallBumpRadius (d := d) δ hδ x).HasTemperateGrowth := by
          simpa using hRtemp.sub hδtemp
        rw [show (h - h') x = h x - h' x by rfl]
        rw [show
            ((h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d)) +
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d)) x
              =
            (h x -
              ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d) : SpacetimeDim d → ℂ) x) +
              ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                  SchwartzSpacetime d) : SpacetimeDim d → ℂ) x by
            rfl]
        rw [SchwartzMap.smulLeftCLM_apply_apply hdiffTemp,
          SchwartzMap.smulLeftCLM_apply_apply hRtemp,
          SchwartzMap.smulLeftCLM_apply_apply hδtemp]
        simp [smul_eq_mul]
        ring
    calc
      SchwartzMap.seminorm ℝ N M (h - h') =
          SchwartzMap.seminorm ℝ N M
            ((h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d)) +
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d)) := by
                rw [hdecomp]
      _ ≤
          SchwartzMap.seminorm ℝ N M
            (h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d)) +
          SchwartzMap.seminorm ℝ N M
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d) := by
                exact map_add_le_add (SchwartzMap.seminorm ℝ N M)
                  (h -
                    (SchwartzMap.smulLeftCLM ℂ
                      (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                        SchwartzSpacetime d))
                  (SchwartzMap.smulLeftCLM ℂ
                    (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                      SchwartzSpacetime d)
      _ < ε / 2 + ε / 2 := add_lt_add hlarge hsmall
      _ = ε := by ring

/-- Finite-family strengthening of the origin-avoidance approximation: a single
annular cutoff can approximate `h` simultaneously in any finite collection of
Schwartz seminorms. -/
private theorem schwartz_origin_avoidance_approximation_finite
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∀ (s : Finset (ℕ × ℕ)) (ε : ℝ), 0 < ε →
      ∃ (h' : SchwartzSpacetime d),
        (0 : SpacetimeDim d) ∉ tsupport (h' : SpacetimeDim d → ℂ) ∧
        HasCompactSupport (h' : SpacetimeDim d → ℂ) ∧
        ∀ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (h - h') < ε := by
  intro s ε hε
  by_cases hs : s.Nonempty
  · have hε2 : 0 < ε / 2 := by positivity
    let θraw : ℕ × ℕ → ℝ := fun p =>
      Classical.choose
        (schwartz_small_origin_cutoff_seminorm_eventually_small
          (d := d) (h := h) h_vanish p.1 p.2 (ε / 2) hε2)
    have hθraw_pos : ∀ p : ℕ × ℕ, 0 < θraw p := by
      intro p
      exact (Classical.choose_spec
        (schwartz_small_origin_cutoff_seminorm_eventually_small
          (d := d) (h := h) h_vanish p.1 p.2 (ε / 2) hε2)).1
    have hθraw_small :
        ∀ (p : ℕ × ℕ) (δ : ℝ) (hδ : 0 < δ), δ ≤ θraw p →
          SchwartzMap.seminorm ℝ p.1 p.2
            ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                  SchwartzSpacetime d)) < ε / 2 := by
      intro p δ hδ hδ_le
      exact (Classical.choose_spec
        (schwartz_small_origin_cutoff_seminorm_eventually_small
          (d := d) (h := h) h_vanish p.1 p.2 (ε / 2) hε2)).2 δ hδ hδ_le
    let θ : ℕ × ℕ → ℝ := fun p => min 1 (θraw p)
    let δ : ℝ := s.inf' hs θ
    have hδ : 0 < δ := by
      dsimp [δ, θ]
      exact (Finset.lt_inf'_iff hs).2 (fun p hp => by
        exact lt_min zero_lt_one (hθraw_pos p))
    have hsmall :
        ∀ p ∈ s,
          SchwartzMap.seminorm ℝ p.1 p.2
            ((SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                  SchwartzSpacetime d)) < ε / 2 := by
      intro p hp
      have hδ_leθ : δ ≤ θ p := Finset.inf'_le (f := θ) hp
      have hδ_le_raw : δ ≤ θraw p := le_trans hδ_leθ (min_le_right _ _)
      exact hθraw_small p δ hδ hδ_le_raw
    let n₀ : ℕ × ℕ → ℕ := fun p =>
      Classical.choose
        (Metric.tendsto_atTop.mp (SchwartzMap.tendsto_bump_truncation h p.1 p.2) (ε / 2) hε2)
    have hn₀ :
        ∀ (p : ℕ × ℕ) (n : ℕ), n₀ p ≤ n →
          SchwartzMap.seminorm ℝ p.1 p.2 (h - bumpTruncationRadius h n) < ε / 2 := by
      intro p n hn
      have hdist :=
        (Classical.choose_spec
          (Metric.tendsto_atTop.mp (SchwartzMap.tendsto_bump_truncation h p.1 p.2)
            (ε / 2) hε2)) n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (by positivity :
          0 ≤ SchwartzMap.seminorm ℝ p.1 p.2 (h - bumpTruncationRadius h n))] at hdist
      exact hdist
    let n : ℕ := max (s.sup n₀) ⌈δ⌉₊
    let R : ℝ := bumpTruncationRadiusValue n
    have hR : δ < R := by
      have hceil : δ ≤ (⌈δ⌉₊ : ℝ) := Nat.le_ceil δ
      have hsup : (⌈δ⌉₊ : ℝ) ≤ n := by
        exact_mod_cast le_max_right (s.sup n₀) ⌈δ⌉₊
      dsimp [R, bumpTruncationRadiusValue]
      linarith
    have hlarge :
        ∀ p ∈ s,
          SchwartzMap.seminorm ℝ p.1 p.2
            (h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d)) < ε / 2 := by
      intro p hp
      have hnp : n₀ p ≤ n := le_trans (Finset.le_sup hp) (le_max_left _ _)
      have hmain := hn₀ p n hnp
      have hEq :
          h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d) =
            h - bumpTruncationRadius h n := by
        simp [R, n, bumpTruncationRadius, bumpTruncationRadiusValue,
          spacetimeUnitBallBumpRadius, add_assoc]
      simpa [hEq]
        using hmain
    let h' : SchwartzSpacetime d :=
      SchwartzMap.smulLeftCLM ℂ
        (fun x : SpacetimeDim d =>
          spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
            spacetimeUnitBallBumpRadius (d := d) δ hδ x) h
    refine ⟨h', ?_, ?_, ?_⟩
    · intro hz
      exact zero_not_mem_tsupport_annulusCutoff (d := d) δ R hδ hR
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (g := (fun x : SpacetimeDim d =>
            spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
              spacetimeUnitBallBumpRadius (d := d) δ hδ x))
          (f := h) hz).2)
    · exact hasCompactSupport_annulusCutoff_mul (d := d) h δ R hδ hR
    · intro p hp
      have hdecomp :
          h - h' =
            (h -
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                  SchwartzSpacetime d)) +
            (SchwartzMap.smulLeftCLM ℂ
              (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d) := by
          ext x
          have hRtemp :=
            (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)).hasTemperateGrowth
          have hδtemp := (spacetimeUnitBallBumpRadius (d := d) δ hδ).hasTemperateGrowth
          have hdiffTemp :
              (fun x : SpacetimeDim d =>
                spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR) x -
                  spacetimeUnitBallBumpRadius (d := d) δ hδ x).HasTemperateGrowth := by
            simpa using hRtemp.sub hδtemp
          rw [show (h - h') x = h x - h' x by rfl]
          rw [show
              ((h -
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                    SchwartzSpacetime d)) +
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d)) x
                =
              (h x -
                ((SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) x) +
                ((SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) x by
              rfl]
          rw [SchwartzMap.smulLeftCLM_apply_apply hdiffTemp,
            SchwartzMap.smulLeftCLM_apply_apply hRtemp,
            SchwartzMap.smulLeftCLM_apply_apply hδtemp]
          simp [smul_eq_mul]
          ring
      calc
        SchwartzMap.seminorm ℝ p.1 p.2 (h - h') =
            SchwartzMap.seminorm ℝ p.1 p.2
              ((h -
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                    SchwartzSpacetime d)) +
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d)) := by
                  rw [hdecomp]
        _ ≤
            SchwartzMap.seminorm ℝ p.1 p.2
              (h -
                (SchwartzMap.smulLeftCLM ℂ
                  (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                    SchwartzSpacetime d)) +
            SchwartzMap.seminorm ℝ p.1 p.2
              (SchwartzMap.smulLeftCLM ℂ
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) h : SchwartzSpacetime d) := by
                  exact map_add_le_add (SchwartzMap.seminorm ℝ p.1 p.2)
                    (h -
                      (SchwartzMap.smulLeftCLM ℂ
                        (spacetimeUnitBallBumpRadius (d := d) R (lt_trans hδ hR)) h :
                          SchwartzSpacetime d))
                    (SchwartzMap.smulLeftCLM ℂ
                      (spacetimeUnitBallBumpRadius (d := d) δ hδ) h :
                        SchwartzSpacetime d)
        _ < ε / 2 + ε / 2 := add_lt_add (hlarge p hp) (hsmall p hp)
        _ = ε := by ring
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · simpa using (HasCompactSupport.zero :
        HasCompactSupport (((0 : SchwartzSpacetime d) : SpacetimeDim d → ℂ)))
    · intro p hp
      exact False.elim (hs ⟨p, hp⟩)

/-- Sequence version of the origin-avoidance approximation: if `h` vanishes to
infinite order at the origin, then there is a sequence of compactly supported
origin-avoiding Schwartz functions converging to `h` in the full Schwartz
topology. -/
private theorem exists_tendsto_originAvoidingCompact_of_vanishes
    (h : SchwartzSpacetime d)
    (h_vanish : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    ∃ u : ℕ → SchwartzSpacetime d,
      (∀ n, (0 : SpacetimeDim d) ∉ tsupport (u n : SpacetimeDim d → ℂ)) ∧
      (∀ n, HasCompactSupport (u n : SpacetimeDim d → ℂ)) ∧
      Filter.Tendsto u Filter.atTop (nhds h) := by
  let s : ℕ → Finset (ℕ × ℕ) := fun n => Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))
  choose u hu0 hucomp huapprox using
    fun n =>
      schwartz_origin_avoidance_approximation_finite
        (d := d) (h := h) h_vanish (s n) (1 / (n + 1 : ℝ)) (by positivity)
  refine ⟨u, hu0, hucomp, ?_⟩
  rw [(schwartz_withSeminorms ℝ (SpacetimeDim d) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
  refine ⟨max (max p.1 p.2) N, ?_⟩
  intro n hn
  have hp1_le : p.1 ≤ n := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hp2_le : p.2 ≤ n := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hp_mem : p ∈ s n := by
    simp [s, Finset.mem_product, Finset.mem_range, hp1_le, hp2_le]
  have happ := huapprox n p hp_mem
  have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
    have hNle : (N + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (le_trans (le_max_right _ _) hn)
    exact one_div_le_one_div_of_le (by positivity) hNle
  have hneg :
      schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ p (u n - h) =
        SchwartzMap.seminorm ℝ p.1 p.2 (h - u n) := by
    change SchwartzMap.seminorm ℝ p.1 p.2 (u n - h) =
      SchwartzMap.seminorm ℝ p.1 p.2 (h - u n)
    rw [show u n - h = -(h - u n) by
      ext x
      abel_nf]
    exact map_neg_eq_map _ _
  rw [hneg]
  exact lt_trans happ (lt_of_le_of_lt hmono hN)

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
  let B : Submodule ℂ (ZeroDiagonalSchwartz d 2) :=
    Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d),
          (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) ∧
          HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  by_cases hχzero : χ = 0
  · have hzero :
        ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h) = 0 := by
      subst hχzero
      apply Subtype.ext
      rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
        (f := twoPointDifferenceLift (0 : SchwartzSpacetime d) h) hvanish]
      ext x
      simp [twoPointDifferenceLift_apply]
    rw [hzero]
    exact B.topologicalClosure.zero_mem
  · have hχ_nonzero : ∃ x, χ x ≠ 0 := by
      by_contra hno
      apply hχzero
      ext x
      by_contra hx
      exact hno ⟨x, hx⟩
    have h_vanish0 :
        ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0 :=
      differenceLift_in_ZDS_implies_h_vanishes_at_zero
        (d := d) χ h hvanish hχ_nonzero
    obtain ⟨u, hu0, hucomp, hu_tendsto⟩ :=
      exists_tendsto_originAvoidingCompact_of_vanishes
        (d := d) (h := h) h_vanish0
    let z : ℕ → ZeroDiagonalSchwartz d 2 := fun n =>
      twoPointDifferenceLiftFixedCenterZeroDiagCLM χ ⟨u n, hu0 n⟩
    have hz_mem : ∀ n, z n ∈ (B : Set (ZeroDiagonalSchwartz d 2)) := by
      intro n
      refine Submodule.subset_span ?_
      refine ⟨χ, u n, hu0 n, hucomp n, ?_⟩
      dsimp [z]
      exact twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical
        (d := d) χ ⟨u n, hu0 n⟩
    let T : SchwartzSpacetime d →L[ℂ] SchwartzNPoint d 2 :=
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
          ((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
            (onePointToFin1CLM d)))
    have hTu :
        Filter.Tendsto (fun n : ℕ => T (u n)) Filter.atTop (nhds (T h)) := by
      exact (T.continuous.tendsto h).comp hu_tendsto
    have hz_tendsto :
        Filter.Tendsto z Filter.atTop
          (nhds (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))) := by
      rw [tendsto_subtype_rng]
      have hz_eq :
          (fun n => (z n).1) =
            fun n => T (u n) := by
        funext n
        have huv :
            VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ (u n)) :=
          twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ (u n) (hu0 n)
        calc
          (z n).1 = (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ (u n))).1 := by
            dsimp [z]
            exact congrArg Subtype.val
              (twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical
                (d := d) χ ⟨u n, hu0 n⟩)
          _ = twoPointDifferenceLift χ (u n) := by
            rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
              (f := twoPointDifferenceLift χ (u n)) huv]
          _ = T (u n) := by
            rfl
      have htarget_eq :
          (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)).1 = T h := by
        rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
          (f := twoPointDifferenceLift χ h) hvanish]
        rfl
      rw [hz_eq, htarget_eq]
      exact hTu
    have hz_mem_closure :
        ∀ n, z n ∈ (B.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
      intro n
      exact subset_closure (hz_mem n)
    exact B.isClosed_topologicalClosure.mem_of_tendsto hz_tendsto
      (Filter.Eventually.of_forall hz_mem_closure)

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

/-- Public export of the cutoff half of the `k = 2` density seam: every
flat-origin difference shell already lies in the closure of the span generated
by origin-avoiding compactly supported difference shells. This is the exact
closure input needed to upgrade compact support shell agreement to arbitrary
flat-origin shell agreement without reopening the older density proof. -/
theorem differenceShell_mem_topologicalClosure_zeroOriginAvoidingCompact_span
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
  exact differenceShell_mem_topologicalClosure_zeroOrigin_span (d := d) χ h

private theorem twoPointDifferenceLift_vanishes_of_h_vanishes_at_zero
    (χ h : SchwartzSpacetime d)
    (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) :
    VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) := by
  let T : SchwartzSpacetime d →L[ℂ] SchwartzNPoint d 2 :=
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
      ((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
        (onePointToFin1CLM d)))
  have hT_eq : ∀ g : SchwartzSpacetime d, T g = twoPointDifferenceLift χ g := by
    intro g
    ext x
    simp [T, twoPointDifferenceLift_apply, twoPointCenterDiffCLE,
      twoPointCenterDiffLinearEquiv]
  obtain ⟨u, hu0, _, hu_tendsto⟩ :=
    exists_tendsto_originAvoidingCompact_of_vanishes (d := d) (h := h) hzero
  have hTu : Filter.Tendsto (fun n : ℕ => T (u n)) Filter.atTop (nhds (T h)) := by
    exact (T.continuous.tendsto h).comp hu_tendsto
  rw [(schwartz_withSeminorms ℝ (NPointDomain d 2) ℂ).tendsto_nhds_atTop _ _] at hTu
  intro k x hx
  have hu_zero :
      ∀ n : ℕ, iteratedFDeriv ℝ k ((T (u n) : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x = 0 := by
    intro n
    have huv :
        VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ (u n)) :=
      twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ (u n) (hu0 n)
    simpa [hT_eq (u n)] using huv k x hx
  have hsmall :
      ∀ ε : ℝ, 0 < ε →
        ‖iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x‖ < ε := by
    intro ε hε
    rcases hTu (0, k) ε hε with ⟨N, hN⟩
    have hsem :
        SchwartzMap.seminorm ℝ 0 k (T (u N) - T h) < ε := hN N le_rfl
    have hnorm :
        ‖iteratedFDeriv ℝ k
            (((T (u N) - T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x‖ < ε := by
      exact lt_of_le_of_lt
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (T (u N) - T h) k x) hsem
    have hsub :
        iteratedFDeriv ℝ k
            (((T (u N) - T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x =
          -iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x := by
      have hrewrite :
          (((T (u N) - T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) =
            ((T (u N) : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) +
              fun y => -((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) y := by
        ext y
        simp [sub_eq_add_neg]
      have hneg :
          iteratedFDeriv ℝ k
              (fun y : NPointDomain d 2 =>
                -((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) y) x =
            -iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x := by
        simpa using
          (iteratedFDeriv_neg_apply
            (𝕜 := ℝ)
            (i := k)
            (f := ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ))
            (x := x))
      calc
        iteratedFDeriv ℝ k
            (((T (u N) - T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x
            =
          (iteratedFDeriv ℝ k ((T (u N) : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) +
            iteratedFDeriv ℝ k
              (fun y : NPointDomain d 2 =>
                -((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) y)) x := by
              rw [hrewrite, iteratedFDeriv_add
                ((T (u N) : SchwartzNPoint d 2).smooth k)
                (((T h : SchwartzNPoint d 2).smooth k).neg)]
        _ = -iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x := by
              simp [hu_zero N, hneg]
    rw [hsub, norm_neg] at hnorm
    exact hnorm
  have hzero_target :
      iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x = 0 := by
    by_contra hne
    have hpos :
        0 < ‖iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x‖ := by
      exact norm_pos_iff.mpr hne
    exact (lt_irrefl _)
      (hsmall ‖iteratedFDeriv ℝ k ((T h : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x‖ hpos)
  simpa [hT_eq h] using hzero_target

/-- A zero-diagonal two-point Schwartz test stays flat after passing to
center/difference coordinates: every iterated derivative vanishes whenever the
difference variable is `0`. -/
private theorem twoPointCenterDiffSchwartzCLM_vanishes_on_diff_zero
    (F : ZeroDiagonalSchwartz d 2) :
    ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k
        ((twoPointCenterDiffSchwartzCLM (d := d) F.1 : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ) z = 0 := by
  intro k z hz
  have hcomp :
      iteratedFDeriv ℝ k
          (((twoPointCenterDiffSchwartzCLM (d := d) F.1 : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ)) z =
        (iteratedFDeriv ℝ k ((F.1 : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)
          ((twoPointCenterDiffCLE d) z)).compContinuousLinearMap
            (fun _ : Fin k => (twoPointCenterDiffCLE d).toContinuousLinearMap) := by
    simpa [twoPointCenterDiffSchwartzCLM] using
      (twoPointCenterDiffCLE d).toContinuousLinearMap.iteratedFDeriv_comp_right
        (f := ((F.1 : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ))
        ((F.1 : SchwartzNPoint d 2).smooth k) (x := z) (i := k) le_rfl
  have hcoin : (twoPointCenterDiffCLE d z) ∈ CoincidenceLocus d 2 := by
    refine ⟨0, 1, by decide, ?_⟩
    simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, hz]
  have hzero :
      iteratedFDeriv ℝ k ((F.1 : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)
        ((twoPointCenterDiffCLE d) z) = 0 :=
    F.2 k ((twoPointCenterDiffCLE d) z) hcoin
  rw [hcomp, hzero]
  ext u
  simp

private theorem iteratedFDeriv_lineDeriv_eq_snoc_npoint {n : ℕ}
    (f : SchwartzNPoint d 2)
    (v x : NPointDomain d 2)
    (u : Fin n → NPointDomain d 2) :
    iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x u =
      iteratedFDeriv ℝ (n + 1) ((f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x
        (Fin.snoc u v) := by
  have hsucc :
      (∂^{Fin.snoc u v} f : SchwartzNPoint d 2) = ∂^{u} (∂_{v} f) := by
    simpa using (LineDeriv.iteratedLineDerivOp_succ_right (m := Fin.snoc u v) (f := f))
  have hsucc_apply := congrArg (fun g : SchwartzNPoint d 2 => g x) hsucc
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := f) (m := Fin.snoc u v) (x := x),
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := (∂_{v} f : SchwartzNPoint d 2)) (m := u) (x := x)] using hsucc_apply.symm

private theorem lineDerivOp_comm_npoint
    (f : SchwartzNPoint d 2)
    (v w : NPointDomain d 2) :
    ∂_{v} ((∂_{w} f : SchwartzNPoint d 2)) =
      ∂_{w} ((∂_{v} f : SchwartzNPoint d 2)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzNPoint d 2))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d 2 → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d 2 → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzNPoint d 2))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

private theorem lineDerivOp_iterated_comm_npoint {n : ℕ}
    (f : SchwartzNPoint d 2)
    (v : NPointDomain d 2) (u : Fin n → NPointDomain d 2) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact lineDerivOp_comm_npoint f v (u (Fin.last n))

private theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint {n : ℕ}
    (f : SchwartzNPoint d 2)
    (v x : NPointDomain d 2) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d 2 → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d 2 → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : NPointDomain d 2 → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzNPoint d 2 => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [lineDerivOp_iterated_comm_npoint (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzNPoint d 2)) (m := u) (x := x))

/-- Diff-zero flatness is preserved under iterated line derivatives on the
ambient two-point Schwartz space. -/
private theorem iteratedLineDeriv_preserves_diff_zero_flatness
    (f : SchwartzNPoint d 2)
    (hf : ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) z = 0)
    {j : ℕ} (u : Fin j → NPointDomain d 2) :
    ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k ((∂^{u} f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) z = 0 := by
  induction j generalizing f with
  | zero =>
      intro k z hz
      simpa [LineDeriv.iteratedLineDerivOp_fin_zero] using hf k z hz
  | succ j ih =>
      intro k z hz
      have hu : u = Fin.snoc (Fin.init u) (u (Fin.last j)) := by
        exact (Fin.snoc_init_self u).symm
      rw [hu, LineDeriv.iteratedLineDerivOp_succ_right]
      simp only [Fin.init_snoc, Fin.snoc_last]
      let g : SchwartzNPoint d 2 := ∂_{u (Fin.last j)} f
      have hg :
          ∀ m : ℕ, ∀ y : NPointDomain d 2, y 1 = 0 →
            iteratedFDeriv ℝ m (g : NPointDomain d 2 → ℂ) y = 0 := by
        intro m y hy
        ext w
        have hzero := hf (m + 1) y hy
        have hzero_apply :
            iteratedFDeriv ℝ (m + 1) (f : NPointDomain d 2 → ℂ) y
              (Fin.snoc w (u (Fin.last j))) = 0 := by
          simpa using congrArg
            (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => NPointDomain d 2) ℂ =>
              T (Fin.snoc w (u (Fin.last j)))) hzero
        simpa [g] using
          (iteratedFDeriv_lineDeriv_eq_snoc_npoint
            (f := f) (v := u (Fin.last j)) (x := y) (u := w)).trans hzero_apply
      simpa [g] using ih (f := g) (hf := hg) (u := Fin.init u) k z hz

private theorem seminorm_zero_lineDeriv_le_npoint
    (f : SchwartzNPoint d 2) (v : NPointDomain d 2) (n : ℕ) :
    SchwartzMap.seminorm ℝ 0 n (LineDeriv.lineDerivOp v f : SchwartzNPoint d 2) ≤
      ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
  refine SchwartzMap.seminorm_le_bound ℝ 0 n
    (LineDeriv.lineDerivOp v f : SchwartzNPoint d 2) (by positivity) ?_
  intro x
  calc
    ‖x‖ ^ 0 *
        ‖iteratedFDeriv ℝ n
            (((LineDeriv.lineDerivOp v f : SchwartzNPoint d 2) : SchwartzNPoint d 2) :
              NPointDomain d 2 → ℂ) x‖
        =
      ‖iteratedFDeriv ℝ n
          (((LineDeriv.lineDerivOp v f : SchwartzNPoint d 2) : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ) x‖ := by
            simp
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d 2 → ℂ)) x v‖ := by
          rw [← fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d 2 → ℂ)) x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (n + 1) (f : NPointDomain d 2 → ℂ) x‖ * ‖v‖ := by
          rw [norm_fderiv_iteratedFDeriv]
    _ ≤ (SchwartzMap.seminorm ℝ 0 (n + 1) f) * ‖v‖ := by
          gcongr
          exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f (n + 1) x
    _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
          ring

private theorem iteratedLineDeriv_seminorm_zero_le_npoint
    (f : SchwartzNPoint d 2) (j n : ℕ) :
    ∀ u : Fin j → NPointDomain d 2,
      SchwartzMap.seminorm ℝ 0 n (LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d 2) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  induction j generalizing f n with
  | zero =>
      intro u
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      intro u
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      calc
        SchwartzMap.seminorm ℝ 0 n (∂_{u 0} (∂^{Fin.tail u} f) : SchwartzNPoint d 2)
            ≤ ‖u 0‖ * SchwartzMap.seminorm ℝ 0 (n + 1) (∂^{Fin.tail u} f : SchwartzNPoint d 2) := by
              exact seminorm_zero_lineDeriv_le_npoint (f := ∂^{Fin.tail u} f) (v := u 0) (n := n)
        _ ≤ ‖u 0‖ *
              ((∏ i, ‖Fin.tail u i‖) * SchwartzMap.seminorm ℝ 0 (n + 1 + j) f) := by
              gcongr
              exact ih (f := f) (n := n + 1) (u := Fin.tail u)
        _ = (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + (j + 1)) f := by
              rw [Fin.prod_univ_succ, add_assoc]
              have htail : (∏ i : Fin j, ‖Fin.tail u i‖) = ∏ i : Fin j, ‖u i.succ‖ := rfl
              rw [htail]
              ring

private theorem norm_iteratedFDeriv_iteratedLineDeriv_le_npoint
    (f : SchwartzNPoint d 2) (j n : ℕ) :
    ∀ (u : Fin j → NPointDomain d 2) (x : NPointDomain d 2),
      ‖iteratedFDeriv ℝ n ((LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ) x‖ ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  intro u x
  exact le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (∂^{u} f) n x)
    (iteratedLineDeriv_seminorm_zero_le_npoint (f := f) (j := j) (n := n) u)

/- Flatness along the `ξ = 0` subspace propagates to a quantitative power
bound for iterated line derivatives, with constants controlled by Schwartz
seminorms of the original two-point test. -/
set_option maxHeartbeats 400000 in
private theorem exists_iteratedLineDeriv_diff_zero_flat_bound
    (f : SchwartzNPoint d 2)
    (hf : ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) z = 0)
    (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Fin j → NPointDomain d 2) (x : NPointDomain d 2),
        ‖(LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d 2) x‖ ≤
          C * ‖x 1‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 (j + (m + 1)) f
  have hA_nonneg : 0 ≤ A := by
    positivity
  refine ⟨A / (((Nat.factorial m : ℕ) : ℝ)), by positivity, ?_⟩
  intro u x
  let F : SchwartzNPoint d 2 := ∂^{u} f
  let c : NPointDomain d 2 := fun i => if i = 0 then x 0 else 0
  let v : NPointDomain d 2 := x - c
  let L : ℝ →L[ℝ] NPointDomain d 2 :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ := (fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ) (z + c)) ∘ L
  have hF_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (F : NPointDomain d 2 → ℂ) := fun r => by
    simpa [F] using (F.smooth r)
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ) (z + c)) :=
    fun r => by
      simpa using (hF_contDiff r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
          ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ) (z + c))
              (L 0)).compContinuousLinearMap (fun _ : Fin k => L) := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ) (z + c))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hc_zero : c 1 = 0 := by simp [c]
      have hL0c_zero : (L 0 + c) 1 = 0 := by
        simp [L, c, ContinuousLinearMap.smulRight_apply, hc_zero]
      have hzeroF :
          iteratedFDeriv ℝ k (F : NPointDomain d 2 → ℂ) (L 0 + c) = 0 := by
        simpa [F, L, c, ContinuousLinearMap.smulRight_apply] using
          (iteratedLineDeriv_preserves_diff_zero_flatness
            (f := f) (hf := hf) (u := u)) k (L 0 + c) hL0c_zero
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      calc
        ‖L s‖ = ‖s • v‖ := by rfl
        _ = ‖s‖ * ‖v‖ := norm_smul s v
        _ = ‖v‖ * ‖s‖ := by ring
        _ ≤ ‖v‖ * ‖s‖ := le_rfl
    rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ)
            (z + c)) (L t)).compContinuousLinearMap (fun _ : Fin (m + 1) => L) := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d 2 => (F : NPointDomain d 2 → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    have hFbound :
        ‖iteratedFDeriv ℝ (m + 1) (F : NPointDomain d 2 → ℂ) (L t + c)‖ ≤
          A * ∏ i, ‖u i‖ := by
      have hsemi :
          SchwartzMap.seminorm ℝ 0 (m + 1) F ≤ (∏ i, ‖u i‖) * A := by
        simpa [A, F, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
          iteratedLineDeriv_seminorm_zero_le_npoint (f := f) (j := j) (n := m + 1) u
      calc
        ‖iteratedFDeriv ℝ (m + 1) (F : NPointDomain d 2 → ℂ) (L t + c)‖
            ≤ SchwartzMap.seminorm ℝ 0 (m + 1) F := by
                exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ F (m + 1) (L t + c)
        _ ≤ (∏ i, ‖u i‖) * A := hsemi
        _ = A * ∏ i, ‖u i‖ := by ring
    have hprod_nonneg : 0 ≤ ∏ _ : Fin (m + 1), ‖L‖ := by positivity
    have huprod_nonneg : 0 ≤ ∏ i, ‖u i‖ := by
      simpa using Finset.prod_nonneg (fun i _ => norm_nonneg (u i))
    have hcoeff_nonneg : 0 ≤ A * ∏ i, ‖u i‖ := by
      exact mul_nonneg hA_nonneg huprod_nonneg
    have hLpow_all : ∀ n : ℕ, ‖L‖ ^ n ≤ ‖v‖ ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            ‖L‖ ^ (n + 1) = ‖L‖ ^ n * ‖L‖ := by
              ring_nf
            _ ≤ ‖v‖ ^ n * ‖v‖ := by
                  exact mul_le_mul ih hL (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
            _ = ‖v‖ ^ (n + 1) := by
              ring_nf
    have hLpow : ‖L‖ ^ (m + 1) ≤ ‖v‖ ^ (m + 1) := hLpow_all (m + 1)
    let D :=
      iteratedFDeriv ℝ (m + 1) (F : NPointDomain d 2 → ℂ) (L t + c)
    have hDcomp :
        ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖ ≤
          ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := by
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    have hDbound :
        ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ ≤
          (A * ∏ i, ‖u i‖) * ∏ _ : Fin (m + 1), ‖L‖ := by
      exact mul_le_mul_of_nonneg_right hFbound hprod_nonneg
    calc
      ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖
          ≤ ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := hDcomp
      _ ≤ (A * ∏ i, ‖u i‖) * ∏ _ : Fin (m + 1), ‖L‖ := hDbound
      _ = (A * ∏ i, ‖u i‖) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_left hLpow hcoeff_nonneg
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hv : ‖v‖ = ‖x 1‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg (x 1))).2 (by
        intro i
        fin_cases i <;> simp [v, c])
    · simpa [v, c] using (norm_le_pi_norm v (1 : Fin 2))
  have hg_one : g 1 = F x := by
    have hx_eq : L 1 + c = x := by
      ext i
      fin_cases i <;> simp [L, v, c, ContinuousLinearMap.smulRight_apply]
    simp [g, hx_eq]
  calc
    ‖(LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d 2) x‖
        = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
            rw [hg_one]
            simp [F, hTaylor_zero]
    _ ≤ ((A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
            simpa [hTaylor_zero] using hrem
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
            field_simp [Nat.cast_ne_zero]
            ring
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x 1‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
            rw [hv]

/-- Operator-valued diff-zero flatness for iterated Fréchet derivatives on the
ambient two-point Schwartz space. -/
private theorem exists_iteratedFDeriv_diff_zero_flat_bound
    (f : SchwartzNPoint d 2)
    (hf : ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) z = 0)
    (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : NPointDomain d 2,
        ‖iteratedFDeriv ℝ j (f : NPointDomain d 2 → ℂ) x‖ ≤ C * ‖x 1‖ ^ (m + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_iteratedLineDeriv_diff_zero_flat_bound (f := f) (hf := hf) j m
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  have hCx : 0 ≤ C * ‖x 1‖ ^ (m + 1) := by positivity
  rw [ContinuousMultilinearMap.opNorm_le_iff hCx]
  intro u
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, mul_assoc, mul_left_comm, mul_comm]
    using hC u x

private theorem diff_zero_power_factor_le
    {M i : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ_le : δ ≤ 1)
    {x : NPointDomain d 2} (hx : ‖x 1‖ ≤ 2 * δ)
    (hi : i ∈ Finset.range (M + 1)) :
    (δ⁻¹) ^ i * ‖x 1‖ ^ (M + 1) ≤ (2 : ℝ) ^ (M + 1) * δ := by
  have hi_le : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : ‖x 1‖ ^ (M + 1) ≤ (2 * δ) ^ (M + 1) := by
    gcongr
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hδ_inv_ge_one : 1 ≤ δ⁻¹ := by
    rw [one_le_inv₀ hδ]
    exact hδ_le
  have hdelta_inv_mono : (δ⁻¹) ^ i ≤ (δ⁻¹) ^ M := by
    exact pow_le_pow_right₀ hδ_inv_ge_one hi_le
  have hcancel : (δ⁻¹) ^ M * δ ^ (M + 1) = δ := by
    calc
      (δ⁻¹) ^ M * δ ^ (M + 1) = ((δ⁻¹) ^ M * δ ^ M) * δ := by
            rw [pow_succ']
            ring
      _ = (((δ ^ M)⁻¹ * δ ^ M) * δ) := by rw [inv_pow]
      _ = δ := by simp [pow_ne_zero M hδ.ne']
  calc
    (δ⁻¹) ^ i * ‖x 1‖ ^ (M + 1)
        ≤ (δ⁻¹) ^ i * (2 * δ) ^ (M + 1) := by
            gcongr
    _ ≤ (δ⁻¹) ^ M * (2 * δ) ^ (M + 1) := by
          gcongr
    _ = (2 : ℝ) ^ (M + 1) * ((δ⁻¹) ^ M * δ ^ (M + 1)) := by
          rw [mul_pow]
          ring
    _ = (2 : ℝ) ^ (M + 1) * δ := by rw [hcancel]

/-- On compact sets, a two-point Schwartz test whose iterated derivatives all
vanish on the `ξ = 0` subspace vanishes to arbitrarily high finite order in
the difference variable. -/
private theorem norm_le_diff_zero_pow_succ_on_isCompact
    (f : SchwartzNPoint d 2)
    (hf : ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) z = 0)
    {K : Set (NPointDomain d 2)} (hK : IsCompact K)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖f x‖ ≤ C * ‖x 1‖ ^ (m + 1) := by
  let g : SchwartzNPoint d 2 :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm) f
  have hg_vanish : VanishesToInfiniteOrderOnCoincidence g := by
    intro k x hx
    have hcomp :
        iteratedFDeriv ℝ k
            ((g : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x =
          (iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) ((twoPointCenterDiffCLE d).symm x)).compContinuousLinearMap
            (fun _ : Fin k => (twoPointCenterDiffCLE d).symm.toContinuousLinearMap) := by
      simpa [g] using
        (twoPointCenterDiffCLE d).symm.toContinuousLinearMap.iteratedFDeriv_comp_right
          (f := (f : NPointDomain d 2 → ℂ))
          (f.smooth k) (x := x) (i := k) le_rfl
    have hdiff0 : ((twoPointCenterDiffCLE d).symm x) 1 = 0 := by
      rcases hx with ⟨i, j, hij, hijEq⟩
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simpa using sub_eq_zero.mpr hijEq.symm
      · simpa using sub_eq_zero.mpr hijEq
      · exact (hij rfl).elim
    have hzero :
        iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ)
          ((twoPointCenterDiffCLE d).symm x) = 0 := hf k _ hdiff0
    rw [hcomp, hzero]
    ext u
    simp
  let K' : Set (NPointDomain d 2) := (twoPointCenterDiffCLE d) '' K
  have hK' : IsCompact K' := hK.image (twoPointCenterDiffCLE d).continuous
  obtain ⟨C, hC_nonneg, hC⟩ :=
    VanishesToInfiniteOrderOnCoincidence.norm_le_pairDifference_pow_succ_on_isCompact
      (d := d) (n := 2) (f := g) hg_vanish hK' m 1 0 (by decide)
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx
  have hx' : (twoPointCenterDiffCLE d) x ∈ K' := ⟨x, hx, rfl⟩
  calc
    ‖f x‖ = ‖g ((twoPointCenterDiffCLE d) x)‖ := by
      simp [g]
    _ ≤ C * ‖((twoPointCenterDiffCLE d) x) 1 - ((twoPointCenterDiffCLE d) x) 0‖ ^ (m + 1) :=
      hC ((twoPointCenterDiffCLE d) x) hx'
    _ = C * ‖x 1‖ ^ (m + 1) := by
      simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]

/-- Projection onto the difference-variable block in center/difference
coordinates. -/
private abbrev diffProjCLM : NPointDomain d 2 →L[ℝ] SpacetimeDim d :=
  ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => SpacetimeDim d) 1

/-- The difference-variable projection has operator norm at most `1`. -/
private theorem diffProjCLM_opNorm_le_one :
    ‖diffProjCLM (d := d)‖ ≤ (1 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa [diffProjCLM] using (norm_le_pi_norm x (1 : Fin 2))

/-- Uniform derivative bound for the rescaled difference-variable bump pulled
back to center/difference coordinates. -/
private theorem exists_iteratedFDeriv_diffBlockCutoff_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d 2),
        ‖iteratedFDeriv ℝ n
            (fun y : NPointDomain d 2 =>
              (spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (diffProjCLM (d := d) y)) x‖ ≤
          C * (δ⁻¹) ^ n := by
  obtain ⟨C, hC_nonneg, hCbound⟩ :=
    exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) n
  refine ⟨C, hC_nonneg, ?_⟩
  intro δ hδ x
  have hcomp :
      iteratedFDeriv ℝ n
          (fun y : NPointDomain d 2 =>
            (spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
              (diffProjCLM (d := d) y)) x =
        (iteratedFDeriv ℝ n
          ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (diffProjCLM (d := d) x)).compContinuousLinearMap
            (fun _ : Fin n => diffProjCLM (d := d)) := by
    simpa using
      (diffProjCLM (d := d)).iteratedFDeriv_comp_right
        (f := ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (fun y : NPointDomain d 2 =>
          (spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
            (diffProjCLM (d := d) y)) x‖
        =
      ‖(iteratedFDeriv ℝ n
          ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (diffProjCLM (d := d) x)).compContinuousLinearMap
            (fun _ : Fin n => diffProjCLM (d := d))‖ := by
              rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n
          ((spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (diffProjCLM (d := d) x)‖ *
          ∏ _ : Fin n, ‖diffProjCLM (d := d)‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, ‖diffProjCLM (d := d)‖ := by
          gcongr
          exact hCbound δ hδ (diffProjCLM (d := d) x)
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, (1 : ℝ) := by
          gcongr
          exact diffProjCLM_opNorm_le_one (d := d)
    _ = C * (δ⁻¹) ^ n := by simp

/-- Multiply a two-point Schwartz test in center/difference coordinates by a
Schwartz cutoff in the difference variable. -/
private def diffBlockCutoffCLM (ψ : SchwartzSpacetime d) :
    SchwartzNPoint d 2 →L[ℂ] SchwartzNPoint d 2 :=
  SchwartzMap.smulLeftCLM ℂ (fun x : NPointDomain d 2 => ψ (diffProjCLM (d := d) x))

/-- Compactly supported two-point Schwartz tests which are flat along the
`ξ = 0` subspace have uniformly small local diff-cutoff pieces in every
Schwartz seminorm, with linear decay in the cutoff radius. -/
private theorem diffBlockCutoff_small_origin_seminorm_le_linear
    (f : SchwartzNPoint d 2)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ))
    (hf_flat : ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
      iteratedFDeriv ℝ k (f : NPointDomain d 2 → ℂ) z = 0) :
    ∀ (N M : ℕ),
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
          SchwartzMap.seminorm ℝ N M
            (diffBlockCutoffCLM (d := d) (spacetimeUnitBallBumpRadius (d := d) δ hδ) f) ≤
              A * δ := by
  intro N M
  let B : ℕ → ℝ := fun i =>
    Classical.choose (exists_iteratedFDeriv_diffBlockCutoff_bound (d := d) i)
  let H : ℕ → ℝ := fun i =>
    Classical.choose
      (exists_iteratedFDeriv_diff_zero_flat_bound
        (d := d) (f := f) (hf := hf_flat) (j := M - i) (m := M))
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : NPointDomain d 2)).1 hf_compact.isBounded
  let R : ℝ := max R0 1
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have htsupport_f :
      tsupport ((f : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d 2) R := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR0 hx)
  have hB_nonneg : ∀ i : ℕ, 0 ≤ B i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_diffBlockCutoff_bound (d := d) i)).1
  have hB_bound :
      ∀ i : ℕ, ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d 2),
        ‖iteratedFDeriv ℝ i
            (fun y : NPointDomain d 2 =>
              (spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (diffProjCLM (d := d) y)) x‖ ≤
          B i * (δ⁻¹) ^ i := by
    intro i δ hδ x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_diffBlockCutoff_bound (d := d) i)).2 δ hδ x
  have hH_nonneg : ∀ i : ℕ, 0 ≤ H i := by
    intro i
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_diff_zero_flat_bound
        (d := d) (f := f) (hf := hf_flat) (j := M - i) (m := M))).1
  have hH_bound :
      ∀ i : ℕ, ∀ x : NPointDomain d 2,
        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖ ≤
          H i * ‖x 1‖ ^ (M + 1) := by
    intro i x
    exact (Classical.choose_spec
      (exists_iteratedFDeriv_diff_zero_flat_bound
        (d := d) (f := f) (hf := hf_flat) (j := M - i) (m := M))).2 x
  let A : ℝ :=
    ∑ i ∈ Finset.range (M + 1),
      (M.choose i : ℝ) * B i * H i * R ^ N * (2 : ℝ) ^ (M + 1)
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hBi : 0 ≤ B i := hB_nonneg i
    have hHi : 0 ≤ H i := hH_nonneg i
    have hRN : 0 ≤ R ^ N := pow_nonneg hR_nonneg N
    positivity
  refine ⟨A, hA_nonneg, ?_⟩
  intro δ hδ hδ_le_one
  let ψδ : SchwartzSpacetime d := spacetimeUnitBallBumpRadius (d := d) δ hδ
  let fδ : SchwartzNPoint d 2 := diffBlockCutoffCLM (d := d) ψδ f
  let ηδ : NPointDomain d 2 → ℂ := fun x => ψδ (diffProjCLM (d := d) x)
  let ηfun : NPointDomain d 2 → ℂ := ηδ
  have hη_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ηfun := by
    fun_prop
  let ffun : NPointDomain d 2 → ℂ := (f : NPointDomain d 2 → ℂ)
  have hffun : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ffun := by
    simpa [ffun] using f.smooth'
  have hη_temp : ηδ.HasTemperateGrowth := by
    fun_prop
  have hfun :
      ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) = fun x => ηδ x * f x := by
    funext x
    simpa [fδ, diffBlockCutoffCLM, ηδ, smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply (g := ηδ) hη_temp f x)
  have hsupp_eta :
      Function.support ηδ ⊆ {x : NPointDomain d 2 | ‖x 1‖ ≤ 2 * δ} := by
    intro x hx
    by_contra hxball
    have hnorm : 2 * δ ≤ ‖x 1‖ := le_of_not_ge hxball
    have hzero : ηδ x = 0 := by
      simpa [ηδ, diffProjCLM] using
        spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm (d := d) hδ hnorm
    exact hx (by simpa [Function.mem_support] using hzero)
  have hclosed_diff : IsClosed {x : NPointDomain d 2 | ‖x 1‖ ≤ 2 * δ} := by
    exact isClosed_le ((continuous_apply (1 : Fin 2)).norm) continuous_const
  have htsupport_eta :
      tsupport ηδ ⊆ {x : NPointDomain d 2 | ‖x 1‖ ≤ 2 * δ} := by
    exact closure_minimal hsupp_eta hclosed_diff
  have htsupport_fδ_diff :
      tsupport ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ⊆
        {x : NPointDomain d 2 | ‖x 1‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_eta
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := f) hx).2)
  have htsupport_fδ_compact :
      tsupport ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d 2) R := by
    intro x hx
    exact htsupport_f
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := f) hx).1)
  have hsupport_deriv_diff :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ)) ⊆
        {x : NPointDomain d 2 | ‖x 1‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_fδ_diff
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) hx)
  have hsupport_deriv_compact :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ)) ⊆
        Metric.closedBall (0 : NPointDomain d 2) R := by
    intro x hx
    exact htsupport_fδ_compact
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) hx)
  have hbound :
      ∀ x : NPointDomain d 2,
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x‖ ≤
          A * δ := by
    intro x
    by_cases hx :
        x ∈ Function.support
          (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ))
    · have hxdiff : ‖x 1‖ ≤ 2 * δ := hsupport_deriv_diff hx
      have hxR : x ∈ Metric.closedBall (0 : NPointDomain d 2) R :=
        hsupport_deriv_compact hx
      have hRN : ‖x‖ ^ N ≤ R ^ N := by
        gcongr
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
      have hsmul :=
        norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
          hη_smooth
          hffun x
          (n := M) (by exact_mod_cast le_top)
      calc
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x‖
            = ‖x‖ ^ N * ‖iteratedFDeriv ℝ M (fun y => ηδ y * f y) x‖ := by
                rw [hfun]
        _ ≤ ‖x‖ ^ N *
              ∑ i ∈ Finset.range (M + 1),
                (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖ := by
                exact mul_le_mul_of_nonneg_left hsmul (by positivity)
        _ = ∑ i ∈ Finset.range (M + 1),
              ‖x‖ ^ N *
                ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Finset.range (M + 1),
              ((M.choose i : ℝ) * B i * H i * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hBi := hB_bound i δ hδ x
                have hHi := hH_bound i x
                have hBi_nonneg : 0 ≤ B i := hB_nonneg i
                have hHi_nonneg : 0 ≤ H i := hH_nonneg i
                have hBi_rhs_nonneg : 0 ≤ B i * (δ⁻¹) ^ i := by positivity
                have hchoose_nonneg : 0 ≤ (M.choose i : ℝ) := by positivity
                have hprod :
                    ‖iteratedFDeriv ℝ i ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖ ≤
                      (B i * (δ⁻¹) ^ i) * (H i * ‖x 1‖ ^ (M + 1)) := by
                  exact mul_le_mul hBi hHi (norm_nonneg _) hBi_rhs_nonneg
                have hterm_coeff :
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖ ≤
                      (M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) * (H i * ‖x 1‖ ^ (M + 1))) := by
                  calc
                    (M.choose i : ℝ) * ‖iteratedFDeriv ℝ i ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖
                        =
                      (M.choose i : ℝ) * (‖iteratedFDeriv ℝ i ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖) := by
                          ring
                    _ ≤ (M.choose i : ℝ) *
                          ((B i * (δ⁻¹) ^ i) * (H i * ‖x 1‖ ^ (M + 1))) := by
                          exact mul_le_mul_of_nonneg_left hprod hchoose_nonneg
                have hcoeff_nonneg : 0 ≤ (M.choose i : ℝ) * B i * H i := by
                  exact mul_nonneg (mul_nonneg hchoose_nonneg hBi_nonneg) hHi_nonneg
                have hpower :
                    ‖x‖ ^ N * ((δ⁻¹) ^ i * ‖x 1‖ ^ (M + 1)) ≤
                      R ^ N * ((2 : ℝ) ^ (M + 1) * δ) := by
                  exact mul_le_mul hRN
                    (diff_zero_power_factor_le (hδ := hδ) (hδ_le := hδ_le_one) hxdiff hi)
                    (by positivity) (pow_nonneg hR_nonneg _)
                calc
                  ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ‖iteratedFDeriv ℝ i ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - i) (f : NPointDomain d 2 → ℂ) x‖)
                      ≤
                    ‖x‖ ^ N *
                      ((M.choose i : ℝ) * ((B i * (δ⁻¹) ^ i) *
                        (H i * ‖x 1‖ ^ (M + 1)))) := by
                          exact mul_le_mul_of_nonneg_left hterm_coeff (by positivity)
                  _ = ((M.choose i : ℝ) * B i * H i) *
                        (‖x‖ ^ N * ((δ⁻¹) ^ i * ‖x 1‖ ^ (M + 1))) := by
                          ring
                  _ ≤ ((M.choose i : ℝ) * B i * H i) *
                        (R ^ N * ((2 : ℝ) ^ (M + 1) * δ)) := by
                          exact mul_le_mul_of_nonneg_left hpower hcoeff_nonneg
                  _ = ((M.choose i : ℝ) * B i * H i * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                          ring
        _ = A * δ := by
              simp [A, Finset.sum_mul]
    · have hzero :
          iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) x = 0 := by
        by_contra hne
        exact hx (by simpa [Function.mem_support] using hne)
      have hnonneg : 0 ≤ A * δ := by positivity
      simpa [hzero] using hnonneg
  exact SchwartzMap.seminorm_le_bound ℝ N M fδ (by positivity) hbound

/-- On pure product tensors, the difference-block cutoff acts only on the
second factor. -/
private theorem diffBlockCutoff_productTensor
    (ψ χ h : SchwartzSpacetime d) :
    diffBlockCutoffCLM (d := d) ψ (SchwartzMap.productTensor ![χ, h]) =
      SchwartzMap.productTensor ![χ,
        (SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d)] := by
  have htemp :
      (fun x : NPointDomain d 2 => ψ (diffProjCLM (d := d) x)).HasTemperateGrowth := by
    fun_prop
  ext x
  rw [diffBlockCutoffCLM, SchwartzMap.smulLeftCLM_apply_apply htemp]
  simp [diffProjCLM, SchwartzMap.productTensor_apply, smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ψ.hasTemperateGrowth h (x 1)]
  simp [smul_eq_mul]
  ring

/-- A sufficiently large difference-block bump is exactly `1` on the support of
a compactly supported two-point Schwartz test, hence acts by the identity. -/
private theorem exists_large_diffBlockCutoff_eq_self_of_hasCompactSupport
    (F : SchwartzNPoint d 2)
    (hF_compact : HasCompactSupport ((F : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)) :
    ∃ (R : ℝ) (hR : 0 < R),
      diffBlockCutoffCLM (d := d) (spacetimeUnitBallBumpRadius (d := d) R hR) F = F := by
  let S : Set (SpacetimeDim d) :=
    (diffProjCLM (d := d)) '' tsupport ((F : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ)
  have hS_compact : IsCompact S := hF_compact.image (diffProjCLM (d := d)).continuous
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : SpacetimeDim d)).1 hS_compact.isBounded
  let R : ℝ := max R0 1
  have hR : 0 < R := by
    have hR_ge : (1 : ℝ) ≤ R := le_max_right _ _
    linarith
  refine ⟨R, hR, ?_⟩
  ext x
  by_cases hx : F x = 0
  · have htemp :
        (fun y : NPointDomain d 2 =>
          spacetimeUnitBallBumpRadius (d := d) R hR (diffProjCLM (d := d) y)).HasTemperateGrowth := by
      fun_prop
    rw [diffBlockCutoffCLM, SchwartzMap.smulLeftCLM_apply_apply htemp, hx]
    simp
  · have hxt : x ∈ tsupport ((F : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) :=
      subset_tsupport _ (by simpa [Function.mem_support] using hx)
    have hxS : diffProjCLM (d := d) x ∈ S := ⟨x, hxt, rfl⟩
    have hcutoff_one :
        spacetimeUnitBallBumpRadius (d := d) R hR (diffProjCLM (d := d) x) = 1 := by
      have hx_ballR0 : diffProjCLM (d := d) x ∈ Metric.closedBall (0 : SpacetimeDim d) R0 :=
        hR0 hxS
      have hx_ballR : diffProjCLM (d := d) x ∈ Metric.closedBall (0 : SpacetimeDim d) R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx_ballR0 ⊢
        exact le_trans hx_ballR0 (le_max_left _ _)
      simpa [spacetimeUnitBallBumpRadius] using
        (unitBallBumpSchwartzPiRadius_one_of_mem_closedBall (m := d + 1) hR hx_ballR)
    have htemp :
        (fun y : NPointDomain d 2 =>
          spacetimeUnitBallBumpRadius (d := d) R hR (diffProjCLM (d := d) y)).HasTemperateGrowth := by
      fun_prop
    rw [diffBlockCutoffCLM, SchwartzMap.smulLeftCLM_apply_apply htemp, hcutoff_one]
    simp [smul_eq_mul]

/-- Any Schwartz cutoff vanishing on a neighborhood of the origin forces all
derivatives of the product `ψ · h` to vanish at the origin. -/
private theorem vanish_derivs_of_notMem_tsupport
    (ψ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (ψ : SpacetimeDim d → ℂ)) :
    ∀ k : ℕ,
      iteratedFDeriv ℝ k
        ((SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) 0 = 0 := by
  intro k
  have hEq :
      (((SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) =ᶠ[𝓝 (0 : SpacetimeDim d)] 0 := by
    have hψ : (ψ : SpacetimeDim d → ℂ) =ᶠ[𝓝 (0 : SpacetimeDim d)] 0 := by
      simpa [notMem_tsupport_iff_eventuallyEq] using h0
    filter_upwards [hψ] with x hx
    have happly := SchwartzMap.smulLeftCLM_apply_apply
      (g := ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ψ.hasTemperateGrowth h x
    simp [smul_eq_mul, hx] at happly ⊢
    exact happly
  have hderivEqWithin :
      iteratedFDerivWithin ℝ k
          (((SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) Set.univ 0 =
        iteratedFDerivWithin ℝ k (fun _ : SpacetimeDim d => (0 : ℂ)) Set.univ 0 := by
    have hEqWithin :
        (((SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) =ᶠ[𝓝[Set.univ] (0 : SpacetimeDim d)]
          (fun _ : SpacetimeDim d => (0 : ℂ)) := by
      simpa [nhdsWithin_univ] using hEq
    simpa using
      (hEqWithin.iteratedFDerivWithin_eq (by simpa using hEq.eq_of_nhds) k)
  have hderivEq :
      iteratedFDeriv ℝ k
          (((SchwartzMap.smulLeftCLM ℂ ψ h : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) 0 =
        iteratedFDeriv ℝ k (fun _ : SpacetimeDim d => (0 : ℂ)) 0 := by
    simpa [iteratedFDerivWithin_univ] using hderivEqWithin
  rw [hderivEq]
  ext u
  simp

/-- Multiplying in the difference variable by an origin-avoiding cutoff sends
arbitrary two-point Schwartz tests into the closure of the span generated by
product tensors whose second factor is flat at the origin. This is the
operator-level bridge behind the remaining flat-origin density theorem. -/
private theorem diffBlockCutoff_mem_topologicalClosure_flatProductSpan
    (ψ : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (ψ : SpacetimeDim d → ℂ))
    (F : SchwartzNPoint d 2) :
    diffBlockCutoffCLM (d := d) ψ F ∈
      (((Submodule.span ℂ
        {G : SchwartzNPoint d 2 |
          ∃ (χ h : SchwartzSpacetime d),
            (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
            G = SchwartzMap.productTensor ![χ, h]}) :
          Submodule ℂ (SchwartzNPoint d 2)).topologicalClosure :
        Set (SchwartzNPoint d 2)) := by
  let S_all : Set (SchwartzNPoint d 2) :=
    {G : SchwartzNPoint d 2 |
      ∃ fs : Fin 2 → SchwartzSpacetime d, G = SchwartzMap.productTensor fs}
  let S_flat : Set (SchwartzNPoint d 2) :=
    {G : SchwartzNPoint d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
        G = SchwartzMap.productTensor ![χ, h]}
  let M_all : Submodule ℂ (SchwartzNPoint d 2) := Submodule.span ℂ S_all
  let M_flat : Submodule ℂ (SchwartzNPoint d 2) := Submodule.span ℂ S_flat
  let T : SchwartzNPoint d 2 →L[ℂ] SchwartzNPoint d 2 := diffBlockCutoffCLM (d := d) ψ
  have hM_all_dense : Dense (M_all : Set (SchwartzNPoint d 2)) := by
    simpa [M_all, S_all] using productTensor_span_dense d 2
  have hImage : M_all ≤ M_flat.topologicalClosure.comap T.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    intro G hG
    rcases hG with ⟨fs, rfl⟩
    change T (SchwartzMap.productTensor fs) ∈ M_flat.topologicalClosure
    apply subset_closure
    refine Submodule.subset_span ?_
    refine ⟨fs 0, (SchwartzMap.smulLeftCLM ℂ ψ (fs 1) : SchwartzSpacetime d), ?_, ?_⟩
    · exact vanish_derivs_of_notMem_tsupport (d := d) ψ (fs 1) h0
    · simpa [T] using diffBlockCutoff_productTensor (d := d) ψ (fs 0) (fs 1)
  have hclosed :
      IsClosed
        ((M_flat.topologicalClosure.comap T.toLinearMap :
          Submodule ℂ (SchwartzNPoint d 2)) : Set (SchwartzNPoint d 2)) := by
    change IsClosed ((T : SchwartzNPoint d 2 → SchwartzNPoint d 2) ⁻¹'
      (M_flat.topologicalClosure : Set (SchwartzNPoint d 2)))
    exact M_flat.isClosed_topologicalClosure.preimage T.continuous
  have hclosure_le :
      M_all.topologicalClosure ≤ M_flat.topologicalClosure.comap T.toLinearMap :=
    Submodule.topologicalClosure_minimal M_all hImage hclosed
  have htop : (⊤ : Submodule ℂ (SchwartzNPoint d 2)) ≤
      M_flat.topologicalClosure.comap T.toLinearMap := by
    rw [← (Submodule.dense_iff_topologicalClosure_eq_top).mp hM_all_dense]
    exact hclosure_le
  have hmem : F ∈ M_flat.topologicalClosure.comap T.toLinearMap := htop (by simp)
  simpa [T, M_flat, S_flat] using hmem

/-- Inverse center/difference rewrite on two-point Schwartz space. -/
private abbrev twoPointCenterDiffInvSchwartzCLM :
    SchwartzNPoint d 2 →L[ℂ] SchwartzNPoint d 2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm

/-- Pulling a product tensor back through the inverse center/difference map
recovers the corresponding difference shell. -/
private theorem twoPointCenterDiffInvSchwartzCLM_productTensor
    (χ h : SchwartzSpacetime d) :
    twoPointCenterDiffInvSchwartzCLM (d := d) (SchwartzMap.productTensor ![χ, h]) =
      twoPointDifferenceLift χ h := by
  ext x
  simp [twoPointCenterDiffInvSchwartzCLM, twoPointDifferenceLift_apply,
    twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
    SchwartzMap.productTensor_apply]

/-- Pulling the difference-block cutoff back to the original variables amounts
to multiplying by `ψ (x₁ - x₀)`. -/
private theorem twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply
    (ψ : SchwartzSpacetime d) (F : SchwartzNPoint d 2) (x : NPointDomain d 2) :
    twoPointCenterDiffInvSchwartzCLM (d := d)
      (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F)) x =
        ψ (x 1 - x 0) * F x := by
  have htemp :
      (fun x : NPointDomain d 2 => ψ (diffProjCLM (d := d) x)).HasTemperateGrowth := by
    fun_prop
  change
    diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F)
        ((twoPointCenterDiffCLE d).symm x) =
      ψ (x 1 - x 0) * F x
  rw [diffBlockCutoffCLM, SchwartzMap.smulLeftCLM_apply_apply htemp,
    twoPointCenterDiffSchwartzCLM_apply]
  have hcoords : (fun i : Fin 2 => if i = 0 then x 0 else x 1) = x := by
    ext i
    fin_cases i <;> simp
  simp [diffProjCLM, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, smul_eq_mul, hcoords]

/-- If the difference-block cutoff vanishes near `0`, its pullback to the
original variables vanishes to infinite order on the coincidence locus. -/
private theorem twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_vanishes
    (ψ : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (ψ : SpacetimeDim d → ℂ))
    (F : SchwartzNPoint d 2) :
    VanishesToInfiniteOrderOnCoincidence
      (twoPointCenterDiffInvSchwartzCLM (d := d)
        (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F))) := by
  intro k x hx
  have hψ : (ψ : SpacetimeDim d → ℂ) =ᶠ[𝓝 (0 : SpacetimeDim d)] 0 := by
    simpa [notMem_tsupport_iff_eventuallyEq] using h0
  have hdiff : (fun y : NPointDomain d 2 => y 1 - y 0) x = 0 := by
    rcases hx with ⟨i, j, hij, hijEq⟩
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact sub_eq_zero.mpr hijEq.symm
    · exact sub_eq_zero.mpr hijEq
    · exact (hij rfl).elim
  have hEq :
      (((twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d) ψ
            (twoPointCenterDiffSchwartzCLM (d := d) F))) : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) =ᶠ[𝓝 x] 0 := by
    have hcomp : (fun y : NPointDomain d 2 => ψ (y 1 - y 0)) =ᶠ[𝓝 x] 0 := by
      exact hψ.comp_tendsto (by
        simpa [hdiff] using ((continuous_apply 1).sub (continuous_apply 0)).tendsto x)
    filter_upwards [hcomp] with y hy
    simp [twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply, hy]
  have hderivEqWithin :
      iteratedFDerivWithin ℝ k
          ((((twoPointCenterDiffInvSchwartzCLM (d := d)
              (diffBlockCutoffCLM (d := d) ψ
                (twoPointCenterDiffSchwartzCLM (d := d) F))) : SchwartzNPoint d 2) :
            NPointDomain d 2 → ℂ)) Set.univ x =
        iteratedFDerivWithin ℝ k (fun _ : NPointDomain d 2 => (0 : ℂ)) Set.univ x := by
    have hEqWithin :
        ((((twoPointCenterDiffInvSchwartzCLM (d := d)
            (diffBlockCutoffCLM (d := d) ψ
              (twoPointCenterDiffSchwartzCLM (d := d) F))) : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ)) =ᶠ[𝓝[Set.univ] x]
          (fun _ : NPointDomain d 2 => (0 : ℂ)) := by
      simpa [nhdsWithin_univ] using hEq
    simpa using
      (hEqWithin.iteratedFDerivWithin_eq (by simpa using hEq.eq_of_nhds) k)
  simpa [iteratedFDerivWithin_univ] using hderivEqWithin

/-- If the original two-point test is already zero-diagonal, then multiplying
it by an arbitrary difference-variable cutoff keeps it zero-diagonal after
pulling back from center/difference coordinates. -/
private theorem twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_vanishes_of_zeroDiagonal
    (ψ : SchwartzSpacetime d)
    (F : ZeroDiagonalSchwartz d 2) :
    VanishesToInfiniteOrderOnCoincidence
      (twoPointCenterDiffInvSchwartzCLM (d := d)
        (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1))) := by
  let diffMap : NPointDomain d 2 →L[ℝ] SpacetimeDim d :=
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => SpacetimeDim d) 1) -
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => SpacetimeDim d) 0)
  let ψdiff : NPointDomain d 2 → ℂ := fun x => ψ (diffMap x)
  have hψdiff_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψdiff := by
    change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ∘ diffMap)
    exact ψ.smooth'.comp diffMap.contDiff
  have hψdiff_temp : ψdiff.HasTemperateGrowth := by
    simpa [ψdiff] using ψ.hasTemperateGrowth.comp diffMap.hasTemperateGrowth
  have hEq :
      twoPointCenterDiffInvSchwartzCLM (d := d)
        (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1)) =
      SchwartzMap.smulLeftCLM ℂ ψdiff F.1 := by
    ext x
    have hdiff_apply : diffMap x = x 1 - x 0 := by
      simp [diffMap]
    calc
      twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1)) x
          = ψ (x 1 - x 0) * F.1 x := by
              rw [twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply (d := d) ψ F.1 x]
      _ = ψ (diffMap x) * F.1 x := by rw [hdiff_apply]
      _ = (SchwartzMap.smulLeftCLM ℂ ψdiff F.1 : SchwartzNPoint d 2) x := by
            rw [SchwartzMap.smulLeftCLM_apply_apply (g := ψdiff) hψdiff_temp F.1 x]
            simp [ψdiff, smul_eq_mul]
  rw [hEq]
  exact VanishesToInfiniteOrderOnCoincidence.smulLeft_of_smooth
    (d := d) hψdiff_smooth hψdiff_temp F.2

/-- Pulling an origin-avoiding difference-block cutoff back to the original
variables lands in the closure of the flat-at-origin difference-shell span on
the ambient two-point Schwartz space. -/
private theorem twoPointCenterDiffInv_diffBlockCutoff_mem_topologicalClosure_flatDifferenceShellSpan
    (ψ : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (ψ : SpacetimeDim d → ℂ))
    (F : SchwartzNPoint d 2) :
    twoPointCenterDiffInvSchwartzCLM (d := d)
      (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F)) ∈
      (((Submodule.span ℂ
        {G : SchwartzNPoint d 2 |
          ∃ (χ h : SchwartzSpacetime d),
            (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
            G = twoPointDifferenceLift χ h}) :
          Submodule ℂ (SchwartzNPoint d 2)).topologicalClosure :
        Set (SchwartzNPoint d 2)) := by
  let S_flat_prod : Set (SchwartzNPoint d 2) :=
    {G : SchwartzNPoint d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
        G = SchwartzMap.productTensor ![χ, h]}
  let S_flat_shell : Set (SchwartzNPoint d 2) :=
    {G : SchwartzNPoint d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
        G = twoPointDifferenceLift χ h}
  let M_flat_prod : Submodule ℂ (SchwartzNPoint d 2) := Submodule.span ℂ S_flat_prod
  let M_flat_shell : Submodule ℂ (SchwartzNPoint d 2) := Submodule.span ℂ S_flat_shell
  have hImage :
      M_flat_prod ≤
        M_flat_shell.topologicalClosure.comap
          (twoPointCenterDiffInvSchwartzCLM (d := d)).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    intro G hG
    rcases hG with ⟨χ, h, hzero, rfl⟩
    change twoPointCenterDiffInvSchwartzCLM (d := d)
      (SchwartzMap.productTensor ![χ, h]) ∈ M_flat_shell.topologicalClosure
    apply subset_closure
    refine Submodule.subset_span ?_
    exact ⟨χ, h, hzero, twoPointCenterDiffInvSchwartzCLM_productTensor (d := d) χ h⟩
  have hclosed :
      IsClosed
        (((M_flat_shell.topologicalClosure).comap
            (twoPointCenterDiffInvSchwartzCLM (d := d)).toLinearMap :
            Submodule ℂ (SchwartzNPoint d 2)) : Set (SchwartzNPoint d 2)) := by
    change IsClosed
      (((twoPointCenterDiffInvSchwartzCLM (d := d) : SchwartzNPoint d 2 → SchwartzNPoint d 2)) ⁻¹'
        (M_flat_shell.topologicalClosure : Set (SchwartzNPoint d 2)))
    exact M_flat_shell.isClosed_topologicalClosure.preimage
      (twoPointCenterDiffInvSchwartzCLM (d := d)).continuous
  have hclosure_le :
      M_flat_prod.topologicalClosure ≤
        M_flat_shell.topologicalClosure.comap
          (twoPointCenterDiffInvSchwartzCLM (d := d)).toLinearMap :=
    Submodule.topologicalClosure_minimal M_flat_prod hImage hclosed
  have hcutoff :
      diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F) ∈
        (M_flat_prod.topologicalClosure : Set (SchwartzNPoint d 2)) := by
    simpa [M_flat_prod, S_flat_prod] using
      diffBlockCutoff_mem_topologicalClosure_flatProductSpan (d := d) ψ h0
        (twoPointCenterDiffSchwartzCLM (d := d) F)
  have hmem :
      diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F) ∈
        M_flat_shell.topologicalClosure.comap
          (twoPointCenterDiffInvSchwartzCLM (d := d)).toLinearMap :=
    hclosure_le hcutoff
  simpa [M_flat_shell, S_flat_shell] using hmem

/-- The same cutoff bridge, now packaged directly on `ZeroDiagonalSchwartz`. -/
private theorem twoPointCenterDiffInv_diffBlockCutoff_mem_topologicalClosure_flatDifferenceShellSpan_zeroDiag
    (ψ : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (ψ : SpacetimeDim d → ℂ))
    (F : ZeroDiagonalSchwartz d 2) :
    ZeroDiagonalSchwartz.ofClassical
      (twoPointCenterDiffInvSchwartzCLM (d := d)
        (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1))) ∈
      (((Submodule.span ℂ
        {f : ZeroDiagonalSchwartz d 2 |
          ∃ (χ h : SchwartzSpacetime d),
            (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
            f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
          Submodule ℂ (ZeroDiagonalSchwartz d 2)).topologicalClosure :
        Set (ZeroDiagonalSchwartz d 2)) := by
  let x : ZeroDiagonalSchwartz d 2 :=
    ZeroDiagonalSchwartz.ofClassical
      (twoPointCenterDiffInvSchwartzCLM (d := d)
        (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1)))
  let coeZ : ZeroDiagonalSchwartz d 2 → SchwartzNPoint d 2 := fun z => z.1
  let coeL : ZeroDiagonalSchwartz d 2 →ₗ[ℂ] SchwartzNPoint d 2 :=
    { toFun := coeZ
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  let S_sub : Set (ZeroDiagonalSchwartz d 2) :=
    {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  let S_ambient : Set (SchwartzNPoint d 2) :=
    {G : SchwartzNPoint d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        (∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0) ∧
        G = twoPointDifferenceLift χ h}
  let B : Submodule ℂ (ZeroDiagonalSchwartz d 2) := Submodule.span ℂ S_sub
  have hxv :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1))) := by
    exact twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_vanishes
      (d := d) ψ h0 F.1
  have hS :
      coeZ '' S_sub = S_ambient := by
    ext G
    constructor
    · rintro ⟨f, ⟨χ, h, hzero, rfl⟩, rfl⟩
      refine ⟨χ, h, hzero, ?_⟩
      simp [coeZ,
        twoPointDifferenceLift_vanishes_of_h_vanishes_at_zero, hzero]
    · rintro ⟨χ, h, hzero, rfl⟩
      refine ⟨ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h), ?_, ?_⟩
      · exact ⟨χ, h, hzero, rfl⟩
      · simp [coeZ,
          twoPointDifferenceLift_vanishes_of_h_vanishes_at_zero, hzero]
  have hspan :
      (Submodule.span ℂ S_ambient : Submodule ℂ (SchwartzNPoint d 2)) = B.map coeL := by
    calc
      (Submodule.span ℂ S_ambient : Submodule ℂ (SchwartzNPoint d 2))
          = Submodule.span ℂ (coeL '' S_sub) := by
              simp [hS, coeL, coeZ]
      _ = B.map coeL := by
            change Submodule.span ℂ (coeL '' S_sub) = (Submodule.span ℂ S_sub).map coeL
            exact Submodule.span_image (R := ℂ) (R₂ := ℂ) (s := S_sub) coeL
  have hfull :
      x.1 ∈
        closure
          (coeZ ''
            ((B : Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2))) := by
    have hxcoe :
        x.1 =
          twoPointCenterDiffInvSchwartzCLM (d := d)
            (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1)) := by
      change
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointCenterDiffInvSchwartzCLM (d := d)
            (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1)))).1 =
          twoPointCenterDiffInvSchwartzCLM (d := d)
            (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1))
      rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
        (f := twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d) ψ (twoPointCenterDiffSchwartzCLM (d := d) F.1))) hxv]
    rw [hxcoe]
    have hmap :
        (((B.map coeL : Submodule ℂ (SchwartzNPoint d 2)) : Set (SchwartzNPoint d 2))) =
          coeZ '' ((B : Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2)) := by
      exact Submodule.map_coe coeL B
    rw [← hmap, ← hspan]
    simpa [S_ambient] using
      twoPointCenterDiffInv_diffBlockCutoff_mem_topologicalClosure_flatDifferenceShellSpan
        (d := d) ψ h0 F.1
  have hxclosure :
      x ∈
        closure
          ((B : Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2)) := by
    rw [closure_subtype]
    simpa [coeZ] using hfull
  simpa [x] using hxclosure

private theorem unflatten_flattenSchwartzNPoint_local {n : ℕ}
    (f : SchwartzNPoint d n) :
    OSReconstruction.unflattenSchwartzNPoint (d := d)
      (OSReconstruction.flattenSchwartzNPoint (d := d) f) = f := by
  ext x
  simp [OSReconstruction.flattenSchwartzNPoint_apply,
    OSReconstruction.unflattenSchwartzNPoint_apply]

private noncomputable def unitBallBumpSchwartzNPointRadius
    (n d : ℕ) (R : ℝ) (hR : 0 < R) : SchwartzNPoint d n :=
  OSReconstruction.unflattenSchwartzNPoint (d := d)
    (OSReconstruction.unitBallBumpSchwartzPiRadius (n * (d + 1)) R hR)

private noncomputable def bumpTruncationRadiusNPoint {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) : SchwartzNPoint d n :=
  SchwartzMap.smulLeftCLM ℂ
    (unitBallBumpSchwartzNPointRadius n d
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)) f

private theorem bumpTruncationRadiusNPoint_eq_unflatten {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) :
    bumpTruncationRadiusNPoint (d := d) f N =
      OSReconstruction.unflattenSchwartzNPoint (d := d)
        (OSReconstruction.bumpTruncationRadius
          (OSReconstruction.flattenSchwartzNPoint (d := d) f) N) := by
  ext x
  rw [bumpTruncationRadiusNPoint]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((unitBallBumpSchwartzNPointRadius n d
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N) : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (unitBallBumpSchwartzNPointRadius n d
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)).hasTemperateGrowth
    f x]
  rw [unitBallBumpSchwartzNPointRadius, OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [OSReconstruction.flattenSchwartzNPoint_apply, smul_eq_mul]

private theorem dense_hasCompactSupport_zeroDiagonal :
    Dense {F : ZeroDiagonalSchwartz d 2 |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d 2).1 : NPointDomain d 2 → ℂ)} := by
  intro F
  let v : ℕ → SchwartzNPoint d 2 := fun n =>
    bumpTruncationRadiusNPoint (d := d) F.1 n
  have hv_vanish :
      ∀ n, VanishesToInfiniteOrderOnCoincidence (v n) := by
    intro n
    simpa [v, bumpTruncationRadiusNPoint] using
      (VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (d := d) F.2
          (ψ := unitBallBumpSchwartzNPointRadius 2 d
            (OSReconstruction.bumpTruncationRadiusValue n)
            (OSReconstruction.bumpTruncationRadiusValue_pos n)))
  let u : ℕ → ZeroDiagonalSchwartz d 2 := fun n => ⟨v n, hv_vanish n⟩
  have hu_mem :
      ∀ n, u n ∈ {F : ZeroDiagonalSchwartz d 2 |
        HasCompactSupport ((F : ZeroDiagonalSchwartz d 2).1 : NPointDomain d 2 → ℂ)} := by
    intro n
    have hflat_compact :
        HasCompactSupport
          (((bumpTruncationRadius (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n :
            SchwartzMap (Fin (2 * (d + 1)) → ℝ) ℂ)) :
            (Fin (2 * (d + 1)) → ℝ) → ℂ) := by
      simpa [bumpTruncationRadius, bumpTruncationRadiusValue] using
        hasCompactSupport_cutoff_mul_radius
          (m := 2 * (d + 1)) (R := bumpTruncationRadiusValue n)
          (bumpTruncationRadiusValue_pos n)
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)
    have hv_compact :
        HasCompactSupport ((v n : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) := by
      simpa [v] using
        (show HasCompactSupport ((bumpTruncationRadiusNPoint (d := d) F.1 n :
            SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) from by
          rw [bumpTruncationRadiusNPoint_eq_unflatten (d := d)]
          simpa [OSReconstruction.unflattenSchwartzNPoint_apply] using
            hflat_compact.comp_homeomorph (flattenCLEquivReal 2 (d + 1)).toHomeomorph)
    simpa [u] using hv_compact
  have hu_tendsto :
      Filter.Tendsto u Filter.atTop (nhds F) := by
    rw [tendsto_subtype_rng]
    have hv_tendsto :
        Filter.Tendsto v Filter.atTop (nhds F.1) := by
      have hunflat :=
        ((OSReconstruction.unflattenSchwartzNPoint (d := d)).continuous.tendsto
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)).comp
            (SchwartzMap.tendsto_bump_truncation_nhds
              (OSReconstruction.flattenSchwartzNPoint (d := d) F.1))
      have hrew :
          v =
            fun n : ℕ =>
              OSReconstruction.unflattenSchwartzNPoint (d := d)
                (bumpTruncationRadius
                  (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n) := by
        funext n
        simpa [v] using bumpTruncationRadiusNPoint_eq_unflatten (d := d) F.1 n
      rw [hrew]
      simpa [Function.comp, unflatten_flattenSchwartzNPoint_local (d := d) F.1] using
        hunflat
    simpa [u] using hv_tendsto
  exact isClosed_closure.mem_of_tendsto hu_tendsto
    (Filter.Eventually.of_forall fun n => subset_closure (hu_mem n))

theorem flatOrigin_differenceShell_span_dense_zeroDiagonal :
    Dense (((Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d)
          (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
        Submodule ℂ (ZeroDiagonalSchwartz d 2)) : Set (ZeroDiagonalSchwartz d 2)) := by
  let A : Submodule ℂ (ZeroDiagonalSchwartz d 2) :=
    Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d)
          (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  let C : Set (ZeroDiagonalSchwartz d 2) :=
    {F : ZeroDiagonalSchwartz d 2 |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d 2).1 : NPointDomain d 2 → ℂ)}
  intro F
  have hC_dense : Dense C := dense_hasCompactSupport_zeroDiagonal (d := d)
  have hC_subset :
      C ⊆ (A.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
    intro G hG
    let Gcd : SchwartzNPoint d 2 := twoPointCenterDiffSchwartzCLM (d := d) G.1
    have hGcd_compact : HasCompactSupport ((Gcd : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) := by
      change HasCompactSupport
        (((G.1 : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ∘ (twoPointCenterDiffCLE d))
      exact hG.comp_homeomorph (twoPointCenterDiffCLE d).toHomeomorph
    have hGcd_vanish :
        ∀ k : ℕ, ∀ z : NPointDomain d 2, z 1 = 0 →
          iteratedFDeriv ℝ k (Gcd : NPointDomain d 2 → ℂ) z = 0 := by
      simpa [Gcd] using twoPointCenterDiffSchwartzCLM_vanishes_on_diff_zero (d := d) G
    obtain ⟨R, hR, hR_eq⟩ :=
      exists_large_diffBlockCutoff_eq_self_of_hasCompactSupport (d := d) Gcd hGcd_compact
    let ψR : SchwartzSpacetime d := spacetimeUnitBallBumpRadius (d := d) R hR
    have hannulus_mem :
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδR : δ < R),
          ZeroDiagonalSchwartz.ofClassical
            (twoPointCenterDiffInvSchwartzCLM (d := d)
              (diffBlockCutoffCLM (d := d)
                (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)) ∈
            (A.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
      intro δ hδ hδR
      simpa [A, ψR, Gcd] using
        twoPointCenterDiffInv_diffBlockCutoff_mem_topologicalClosure_flatDifferenceShellSpan_zeroDiag
          (d := d) (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ)
          (zero_not_mem_tsupport_annulusCutoff (d := d) δ R hδ hδR)
          G
    have hsmall_vanish :
        ∀ {δ : ℝ} (hδ : 0 < δ),
          VanishesToInfiniteOrderOnCoincidence
            (twoPointCenterDiffInvSchwartzCLM (d := d)
              (diffBlockCutoffCLM (d := d)
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)) := by
      intro δ hδ
      simpa [Gcd] using
        twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_vanishes_of_zeroDiagonal
          (d := d) (spacetimeUnitBallBumpRadius (d := d) δ hδ) G
    have hψR_apply :
        ∀ x : NPointDomain d 2, ψR (x 1 - x 0) * G.1 x = G.1 x := by
      intro x
      have hEq := congrArg
        (fun H : SchwartzNPoint d 2 =>
          twoPointCenterDiffInvSchwartzCLM (d := d) H x) hR_eq
      simpa [Gcd, ψR, twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply,
        twoPointCenterDiffSchwartzCLM_apply, smul_eq_mul] using hEq
    have hsplit :
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδR : δ < R),
          ZeroDiagonalSchwartz.ofClassical
            (twoPointCenterDiffInvSchwartzCLM (d := d)
              (diffBlockCutoffCLM (d := d)
                (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)) +
          ZeroDiagonalSchwartz.ofClassical
            (twoPointCenterDiffInvSchwartzCLM (d := d)
              (diffBlockCutoffCLM (d := d)
                (spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)) = G := by
      intro δ hδ hδR
      let annulus :=
        twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d)
            (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)
      let small :=
        twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d)
            (spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd)
      have hannulus_vanish :
          VanishesToInfiniteOrderOnCoincidence annulus := by
        simpa [annulus] using
          twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_vanishes
            (d := d) (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ)
            (zero_not_mem_tsupport_annulusCutoff (d := d) δ R hδ hδR) G.1
      have hsmall_vanish' :
          VanishesToInfiniteOrderOnCoincidence small := by
        simpa [small] using hsmall_vanish (δ := δ) hδ
      have hsum_apply : ∀ x : NPointDomain d 2, annulus x + small x = G.1 x := by
        intro x
        calc
          annulus x + small x
              =
            ((ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) (x 1 - x 0) * G.1 x) +
              (spacetimeUnitBallBumpRadius (d := d) δ hδ (x 1 - x 0) * G.1 x) := by
                change
                  twoPointCenterDiffInvSchwartzCLM (d := d)
                      (diffBlockCutoffCLM (d := d)
                        (ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd) x +
                    twoPointCenterDiffInvSchwartzCLM (d := d)
                      (diffBlockCutoffCLM (d := d)
                        (spacetimeUnitBallBumpRadius (d := d) δ hδ) Gcd) x =
                  ((ψR - spacetimeUnitBallBumpRadius (d := d) δ hδ) (x 1 - x 0) * G.1 x) +
                    (spacetimeUnitBallBumpRadius (d := d) δ hδ (x 1 - x 0) * G.1 x)
                rw [twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply,
                  twoPointCenterDiffInv_diffBlockCutoff_twoPointCenterDiff_apply]
          _ =
              ((ψR (x 1 - x 0) -
                    spacetimeUnitBallBumpRadius (d := d) δ hδ (x 1 - x 0)) * G.1 x) +
                (spacetimeUnitBallBumpRadius (d := d) δ hδ (x 1 - x 0) * G.1 x) := by
                  rfl
          _ = ψR (x 1 - x 0) * G.1 x := by
                rw [sub_mul, sub_add_cancel]
          _ = G.1 x := hψR_apply x
      calc
          ZeroDiagonalSchwartz.ofClassical annulus +
              ZeroDiagonalSchwartz.ofClassical small
              =
            ZeroDiagonalSchwartz.ofClassical (annulus + small) := by
              symm
              exact ZeroDiagonalSchwartz.ofClassical_add_of_vanishes
                annulus small hannulus_vanish hsmall_vanish'
          _ = ZeroDiagonalSchwartz.ofClassical G.1 := by
              congr 1
              ext x
              exact hsum_apply x
          _ = G := by
              simpa using (ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := G.1) G.2)
    let ρ : ℝ := min 1 (R / 2)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      refine lt_min zero_lt_one ?_
      positivity
    have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
    have hρ_le_one : ρ ≤ 1 := min_le_left _ _
    have hρ_le_halfR : ρ ≤ R / 2 := min_le_right _ _
    have hhalfR_lt_R : R / 2 < R := by
      nlinarith [hR]
    have hρ_lt_R : ρ < R := lt_of_le_of_lt hρ_le_halfR hhalfR_lt_R
    let δSeq : ℕ → ℝ := fun n => ρ / (n + 1 : ℝ)
    have hδSeq_pos : ∀ n : ℕ, 0 < δSeq n := by
      intro n
      dsimp [δSeq]
      positivity
    have hδSeq_le_ρ : ∀ n : ℕ, δSeq n ≤ ρ := by
      intro n
      have hfrac : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
        have hden : (1 : ℝ) ≤ n + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have hone_pos : 0 < (1 : ℝ) := by positivity
        simpa using (one_div_le_one_div_of_le hone_pos hden)
      calc
        δSeq n = ρ * ((n + 1 : ℝ)⁻¹) := by simp [δSeq, div_eq_mul_inv]
        _ ≤ ρ * 1 := by
              simpa using (mul_le_mul_of_nonneg_left hfrac hρ_nonneg)
        _ = ρ := by ring
    have hδSeq_le_one : ∀ n : ℕ, δSeq n ≤ 1 := by
      intro n
      exact le_trans (hδSeq_le_ρ n) hρ_le_one
    have hδSeq_lt_R : ∀ n : ℕ, δSeq n < R := by
      intro n
      exact lt_of_le_of_lt (hδSeq_le_ρ n) hρ_lt_R
    let smallPre : ℕ → SchwartzNPoint d 2 := fun n =>
      diffBlockCutoffCLM (d := d)
        (spacetimeUnitBallBumpRadius (d := d) (δSeq n) (hδSeq_pos n)) Gcd
    have hsmallPre_tendsto :
        Filter.Tendsto smallPre Filter.atTop (nhds (0 : SchwartzNPoint d 2)) := by
      rw [(schwartz_withSeminorms ℝ (NPointDomain d 2) ℂ).tendsto_nhds_atTop _ _]
      intro p ε hε
      obtain ⟨Csemi, hCsemi_nonneg, hCsemi_bound⟩ :=
        diffBlockCutoff_small_origin_seminorm_le_linear
          (d := d) (f := Gcd) hGcd_compact hGcd_vanish p.1 p.2
      let Bnd : ℝ := Csemi * ρ + 1
      have hBnd_pos : 0 < Bnd := by
        dsimp [Bnd]
        positivity
      have hBnd_nonneg : 0 ≤ Bnd := le_of_lt hBnd_pos
      rcases exists_nat_one_div_lt (show 0 < ε / Bnd by positivity) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hsemi_le :
          schwartzSeminormFamily ℝ (NPointDomain d 2) ℂ p (smallPre n - 0) ≤
            Csemi * δSeq n := by
        change SchwartzMap.seminorm ℝ p.1 p.2 (smallPre n - 0) ≤ Csemi * δSeq n
        simpa [smallPre] using hCsemi_bound (δSeq n) (hδSeq_pos n) (hδSeq_le_one n)
      have hCρ_le_Bnd : Csemi * ρ ≤ Bnd := by
        dsimp [Bnd]
        linarith
      have hscale :
          Csemi * δSeq n ≤ Bnd / (n + 1 : ℝ) := by
        have hden_pos : 0 < (n + 1 : ℝ) := by positivity
        have hdiv :
            (Csemi * ρ) / (n + 1 : ℝ) ≤ Bnd / (n + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right hCρ_le_Bnd (le_of_lt hden_pos)
        simpa [δSeq, mul_div_assoc] using hdiv
      have hfrac_mono :
          Bnd / (n + 1 : ℝ) ≤ Bnd / (N + 1 : ℝ) := by
        have hone_div :
            (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
          have hden : (N + 1 : ℝ) ≤ n + 1 := by
            exact_mod_cast Nat.succ_le_succ hn
          have hN_pos : 0 < (N + 1 : ℝ) := by positivity
          simpa using (one_div_le_one_div_of_le hN_pos hden)
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hone_div hBnd_nonneg)
      have hsmall :
          Bnd / (N + 1 : ℝ) < ε := by
        have := mul_lt_mul_of_pos_left hN hBnd_pos
        calc
          Bnd / (N + 1 : ℝ) = Bnd * (1 / (N + 1 : ℝ)) := by
            ring
          _ < Bnd * (ε / Bnd) := this
          _ = ε := by
            field_simp [show Bnd ≠ 0 by positivity]
      exact lt_of_le_of_lt (le_trans hsemi_le (le_trans hscale hfrac_mono)) hsmall
    let rawSmall : ℕ → SchwartzNPoint d 2 := fun n =>
      twoPointCenterDiffInvSchwartzCLM (d := d) (smallPre n)
    have hrawSmall_tendsto :
        Filter.Tendsto rawSmall Filter.atTop (nhds (0 : SchwartzNPoint d 2)) := by
      exact ((twoPointCenterDiffInvSchwartzCLM (d := d)).continuous.tendsto 0).comp
        hsmallPre_tendsto
    let small : ℕ → ZeroDiagonalSchwartz d 2 := fun n =>
      ZeroDiagonalSchwartz.ofClassical (rawSmall n)
    have hsmall_vanish_seq :
        ∀ n : ℕ, VanishesToInfiniteOrderOnCoincidence (rawSmall n) := by
      intro n
      simpa [rawSmall, smallPre] using hsmall_vanish (δ := δSeq n) (hδ := hδSeq_pos n)
    have hsmall_tendsto :
        Filter.Tendsto small Filter.atTop (nhds (0 : ZeroDiagonalSchwartz d 2)) := by
      rw [tendsto_subtype_rng]
      have hsmall_eq : (fun n => (small n).1) = rawSmall := by
        funext n
        rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
          (f := rawSmall n) (hsmall_vanish_seq n)]
      rw [hsmall_eq]
      simpa using hrawSmall_tendsto
    let annulus : ℕ → ZeroDiagonalSchwartz d 2 := fun n =>
      ZeroDiagonalSchwartz.ofClassical
        (twoPointCenterDiffInvSchwartzCLM (d := d)
          (diffBlockCutoffCLM (d := d)
            (ψR - spacetimeUnitBallBumpRadius (d := d) (δSeq n) (hδSeq_pos n)) Gcd))
    have hannulus_mem_seq :
        ∀ n : ℕ, annulus n ∈ (A.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
      intro n
      simpa [annulus] using hannulus_mem (δ := δSeq n) (hδ := hδSeq_pos n) (hδR := hδSeq_lt_R n)
    have hsplit_seq : ∀ n : ℕ, annulus n + small n = G := by
      intro n
      simpa [annulus, small, rawSmall, smallPre] using
        hsplit (δ := δSeq n) (hδ := hδSeq_pos n) (hδR := hδSeq_lt_R n)
    have hannulus_tendsto :
        Filter.Tendsto annulus Filter.atTop (nhds G) := by
      have hsmall_val_tendsto :
          Filter.Tendsto (fun n : ℕ => (small n).1) Filter.atTop
            (nhds (0 : SchwartzNPoint d 2)) := by
        rw [tendsto_subtype_rng] at hsmall_tendsto
        simpa using hsmall_tendsto
      have hval_tendsto :
          Filter.Tendsto (fun n : ℕ => (annulus n).1) Filter.atTop (nhds G.1) := by
        have hseq_eq :
            (fun n : ℕ => (annulus n).1) =
              (fun n : ℕ => G.1 - (small n).1) := by
          funext n
          have hsum_val : (annulus n).1 + (small n).1 = G.1 := by
            have hcoe : ((annulus n + small n : ZeroDiagonalSchwartz d 2)).1 = G.1 := by
              exact congrArg (fun z : ZeroDiagonalSchwartz d 2 => z.1) (hsplit_seq n)
            change (annulus n).1 + (small n).1 = G.1 at hcoe
            exact hcoe
          exact eq_sub_iff_add_eq.mpr hsum_val
        rw [hseq_eq]
        simpa [sub_eq_add_neg] using (tendsto_const_nhds.sub hsmall_val_tendsto)
      rw [tendsto_subtype_rng]
      simpa using hval_tendsto
    exact A.isClosed_topologicalClosure.mem_of_tendsto hannulus_tendsto
      (Filter.Eventually.of_forall fun n => hannulus_mem_seq n)
  have hC_closure_subset :
      closure C ⊆ (A.topologicalClosure : Set (ZeroDiagonalSchwartz d 2)) := by
    exact closure_minimal hC_subset A.isClosed_topologicalClosure
  exact hC_closure_subset (hC_dense F)

end
