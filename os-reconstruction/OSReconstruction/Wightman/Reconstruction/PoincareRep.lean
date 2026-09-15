/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Init
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import OSReconstruction.Wightman.Reconstruction.HeadTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.SchwartzCutoff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.WightmanAxioms



























open scoped Matrix SchwartzMap InnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]



/-- The Poincaré action on n-point domains: act on each spacetime point. -/
def poincareActNPointDomain (g : PoincareGroup d) {n : ℕ}
    (x : NPointDomain d n) : NPointDomain d n :=
  fun i => PoincareGroup.act g (x i)

/-- The n-point domain action is smooth (ContDiff). Each component is affine,
    and the map into the product is smooth by `contDiff_pi`. -/
private theorem affineCompNPoint_smooth (g : PoincareGroup d) {n : ℕ}
    (f : SchwartzNPoint d n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : NPointDomain d n => f (poincareActNPointDomain g x)) := by
  apply f.smooth'.comp
  -- The map x ↦ (fun i => g.act (x i)) is smooth into a pi type
  rw [contDiff_pi]
  intro i
  -- fun x : (Fin n → SpacetimeDim d) => PoincareGroup.act g (x i)
  -- = (PoincareGroup.act g) ∘ (projection at i)
  -- projection at i is a CLM, g.act is affine → both smooth
  exact (ContDiff.add
    ((Matrix.mulVecLin g.lorentz.val).toContinuousLinearMap).contDiff
    contDiff_const).comp
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => SpacetimeDim d) i).contDiff

/-- The n-point Poincaré action has temperate growth. -/
private theorem poincareActNPoint_hasTemperateGrowth (g : PoincareGroup d) (n : ℕ) :
    Function.HasTemperateGrowth
      (poincareActNPointDomain g : NPointDomain d n → NPointDomain d n) := by
  have hL : Function.HasTemperateGrowth
      (ContinuousLinearMap.pi (fun i : Fin n =>
        ((Matrix.mulVecLin g.lorentz.val).toContinuousLinearMap).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => SpacetimeDim d) i)) :
        NPointDomain d n → NPointDomain d n) :=
    ContinuousLinearMap.hasTemperateGrowth _
  have hC : Function.HasTemperateGrowth
      (fun _ : NPointDomain d n => (fun _ : Fin n => g.translation)) :=
    Function.HasTemperateGrowth.const _
  convert hL.add hC using 1 <;>
    ext x i <;> simp [poincareActNPointDomain, PoincareGroup.act_def]

/-- The inverse Lorentz matrix recovers the original vector (n-point version). -/
private theorem lorentz_inv_mulVec' (g : PoincareGroup d) (x : SpacetimeDim d) :
    Matrix.mulVec g.lorentz⁻¹.val (Matrix.mulVec g.lorentz.val x) = x := by
  have : g.lorentz⁻¹.val * g.lorentz.val = 1 := by
    exact_mod_cast congr_arg Subtype.val (inv_mul_cancel (g.lorentz))
  rw [Matrix.mulVec_mulVec, this, Matrix.one_mulVec]

/-- Upper bound for n-point Poincaré action: ‖x‖ ≤ C * (1 + ‖g·x‖)^k. -/
private theorem poincareActNPoint_upperBound (g : PoincareGroup d) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : NPointDomain d n),
      ‖x‖ ≤ C * (1 + ‖poincareActNPointDomain g x‖) ^ k := by
  set Λ_inv := (Matrix.mulVecLin g.lorentz⁻¹.val).toContinuousLinearMap
  refine ⟨1, ‖Λ_inv‖ * (1 + ‖g.translation‖) + 1, fun x => ?_⟩
  simp only [pow_one]
  -- For each component i, bound ‖x i‖
  suffices h : ∀ i : Fin n, ‖x i‖ ≤
      (‖Λ_inv‖ * (1 + ‖g.translation‖) + 1) * (1 + ‖poincareActNPointDomain g x‖) by
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr h
  intro i
  -- Step 1: ‖x i‖ ≤ ‖Λ_inv‖ * ‖Λ * (x i)‖
  have h1 : ‖x i‖ ≤ ‖Λ_inv‖ * ‖g.lorentz.val.mulVec (x i)‖ := by
    calc ‖x i‖ = ‖g.lorentz⁻¹.val.mulVec (g.lorentz.val.mulVec (x i))‖ := by
            rw [lorentz_inv_mulVec']
      _ ≤ ‖Λ_inv‖ * ‖g.lorentz.val.mulVec (x i)‖ := Λ_inv.le_opNorm _
  -- Step 2: ‖Λ * (x i)‖ ≤ ‖act g (x i)‖ + ‖t‖
  have h2 : ‖g.lorentz.val.mulVec (x i)‖ ≤
      ‖PoincareGroup.act g (x i)‖ + ‖g.translation‖ := by
    rw [show g.lorentz.val.mulVec (x i) = PoincareGroup.act g (x i) - g.translation from by
      simp [PoincareGroup.act_def]]
    exact norm_sub_le _ _
  -- Step 3: ‖act g (x i)‖ ≤ ‖poincareActNPointDomain g x‖
  have h3 : ‖PoincareGroup.act g (x i)‖ ≤ ‖poincareActNPointDomain g x‖ :=
    norm_le_pi_norm (poincareActNPointDomain g x) i
  -- Combine
  have h4 : ‖g.lorentz.val.mulVec (x i)‖ ≤
      ‖poincareActNPointDomain g x‖ + ‖g.translation‖ := by linarith
  have h5 : ‖poincareActNPointDomain g x‖ + ‖g.translation‖ ≤
      (1 + ‖g.translation‖) * (1 + ‖poincareActNPointDomain g x‖) := by
    nlinarith [norm_nonneg (poincareActNPointDomain g x), norm_nonneg g.translation]
  calc ‖x i‖ ≤ ‖Λ_inv‖ * ‖g.lorentz.val.mulVec (x i)‖ := h1
    _ ≤ ‖Λ_inv‖ * ((1 + ‖g.translation‖) * (1 + ‖poincareActNPointDomain g x‖)) := by
        exact mul_le_mul_of_nonneg_left (le_trans h4 h5) (norm_nonneg Λ_inv)
    _ = ‖Λ_inv‖ * (1 + ‖g.translation‖) * (1 + ‖poincareActNPointDomain g x‖) := by ring
    _ ≤ (‖Λ_inv‖ * (1 + ‖g.translation‖) + 1) * (1 + ‖poincareActNPointDomain g x‖) := by
        nlinarith [norm_nonneg (poincareActNPointDomain g x)]

/-- Decay for n-point Schwartz functions composed with Poincaré action.
    Generalizes `affineComp_decay` to n-point functions. -/
private theorem affineCompNPoint_decay (g : PoincareGroup d) {n : ℕ}
    (f : SchwartzNPoint d n) (k m : ℕ) :
    ∃ C, ∀ (x : NPointDomain d n),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m
        (fun x => f (poincareActNPointDomain g x)) x‖ ≤ C := by
  exact (SchwartzMap.compCLM ℂ (poincareActNPoint_hasTemperateGrowth g n)
    (poincareActNPoint_upperBound g n) f).decay' k m

/-- The Poincaré action on n-point Schwartz functions:
    (g · f)(x₁,...,xₙ) = f(g⁻¹·x₁,...,g⁻¹·xₙ) -/
def poincareActNPoint (g : PoincareGroup d) {n : ℕ}
    (f : SchwartzNPoint d n) : SchwartzNPoint d n where
  toFun x := f (poincareActNPointDomain g⁻¹ x)
  smooth' := affineCompNPoint_smooth g⁻¹ f
  decay' k m := affineCompNPoint_decay g⁻¹ f k m

@[simp]
theorem poincareActNPoint_apply (g : PoincareGroup d) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (poincareActNPoint g f) x = f (poincareActNPointDomain g⁻¹ x) := rfl







variable (Wfn : WightmanFunctions d)



end
