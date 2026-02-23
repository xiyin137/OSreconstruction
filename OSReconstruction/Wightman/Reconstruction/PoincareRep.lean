/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.PoincareAction
import OSReconstruction.Wightman.Reconstruction.GNSConstruction

/-!
# Poincaré Representation on the GNS Hilbert Space

This file constructs the unitary representation of the Poincaré group on the
GNS Hilbert space, completing a key part of the Wightman reconstruction.

## Construction

1. Define the Poincaré action on n-point Schwartz functions:
   (g · f)(x₁,...,xₙ) = f(g⁻¹·x₁,...,g⁻¹·xₙ)

2. Extend to Borchers sequences componentwise.

3. Show the Wightman inner product is Poincaré-invariant using
   translation_invariant and lorentz_covariant.

4. The action descends to the quotient (PreHilbertSpace) and
   extends to the completion (GNSHilbertSpace).

## Main definitions

- `poincareActNPoint`: Poincaré action on n-point Schwartz functions
- `poincareActBorchers`: Poincaré action on Borchers sequences
- `WightmanInnerProduct_poincare_invariant`: inner product is Poincaré-invariant
-/

open scoped Matrix SchwartzMap InnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Poincaré action on n-point Schwartz functions -/

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
  convert hL.add hC using 1

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
  convert (SchwartzMap.compCLM ℂ (poincareActNPoint_hasTemperateGrowth g n)
    (poincareActNPoint_upperBound g n) f).decay' k m using 2

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

theorem poincareActNPoint_toFun (g : PoincareGroup d) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (poincareActNPoint g f).toFun x =
      f.toFun (fun i => PoincareGroup.act g⁻¹ (x i)) := rfl

/-- The Poincaré action preserves zero. -/
theorem poincareActNPoint_zero (g : PoincareGroup d) (n : ℕ) :
    poincareActNPoint g (0 : SchwartzNPoint d n) = 0 := by
  ext x; rfl

/-! ### Compatibility with conjTensorProduct -/

/-- The Poincaré action commutes with conjTensorProduct at the function level:
    ((g·f).conjTP (g·h))(x) = (f.conjTP h)(g⁻¹·x) -/
theorem poincareActNPoint_conjTensorProduct (g : PoincareGroup d)
    {m k : ℕ} (f : SchwartzNPoint d m) (h : SchwartzNPoint d k)
    (x : NPointDomain d (m + k)) :
    ((poincareActNPoint g f).conjTensorProduct (poincareActNPoint g h)).toFun x =
    (f.conjTensorProduct h).toFun (poincareActNPointDomain g⁻¹ x) := by
  -- Use rfl: both sides reduce to star(f(g⁻¹·args₁)) * h(g⁻¹·args₂) definitionally
  rfl

/-! ### Poincaré action on Borchers sequences -/

/-- The Poincaré action on a Borchers sequence: act on each component. -/
def poincareActBorchers (g : PoincareGroup d) (F : BorchersSequence d) :
    BorchersSequence d where
  funcs n := poincareActNPoint g (F.funcs n)
  bound := F.bound
  bound_spec n hn := by
    rw [F.bound_spec n hn]; exact poincareActNPoint_zero g n

/-! ### Poincaré invariance of Wightman inner product -/

variable (Wfn : WightmanFunctions d)

/-- The Wightman inner product is Poincaré-invariant:
    ⟨g·F, g·G⟩_W = ⟨F, G⟩_W

    This follows from `translation_invariant` and `lorentz_covariant` of the
    Wightman functions. The decomposition is:
    1. First apply Lorentz invariance (pure Lorentz element gL = (0, Λ))
    2. Then apply translation invariance (translation by -a)
    The key identity is that g⁻¹ · y = Λ⁻¹(y - a), which decomposes as:
      first translate by -a: y ↦ y - a
      then Lorentz: y ↦ Λ⁻¹ y -/
theorem WightmanInnerProduct_poincare_invariant
    (g : PoincareGroup d) (F G : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W (poincareActBorchers g F) (poincareActBorchers g G) =
    WightmanInnerProduct d Wfn.W F G := by
  unfold WightmanInnerProduct poincareActBorchers
  simp only
  congr 1; ext n; congr 1; ext m
  -- Decompose g = (a, Λ) into pure Lorentz gL = (0, Λ), then translate by -a
  -- Step 1: W (Fn.conjTP Gm) = W ((gL·Fn).conjTP (gL·Gm)) by Lorentz covariance
  have hL : Wfn.W (n + m) ((F.funcs n).conjTensorProduct (G.funcs m)) =
      Wfn.W (n + m)
        ((poincareActNPoint (PoincareGroup.lorentz' g.lorentz) (F.funcs n)).conjTensorProduct
          (poincareActNPoint (PoincareGroup.lorentz' g.lorentz) (G.funcs m))) :=
    Wfn.lorentz_covariant (n + m) g.lorentz _ _ (fun x => by
      rw [poincareActNPoint_conjTensorProduct]
      congr 1; ext i
      simp only [poincareActNPointDomain, PoincareGroup.act,
        PoincareGroup.inv_lorentz, PoincareGroup.inv_translation,
        PoincareGroup.lorentz'_lorentz, PoincareGroup.lorentz'_translation,
        Matrix.mulVec_zero, neg_zero, add_zero])
  -- Step 2: W ((gL·Fn).conjTP (gL·Gm)) = W ((g·Fn).conjTP (g·Gm)) by translation
  have hT : Wfn.W (n + m)
      ((poincareActNPoint (PoincareGroup.lorentz' g.lorentz) (F.funcs n)).conjTensorProduct
        (poincareActNPoint (PoincareGroup.lorentz' g.lorentz) (G.funcs m))) =
      Wfn.W (n + m)
        ((poincareActNPoint g (F.funcs n)).conjTensorProduct
          (poincareActNPoint g (G.funcs m))) :=
    Wfn.translation_invariant (n + m) (-g.translation) _ _ (fun x => by
      rw [poincareActNPoint_conjTensorProduct g,
        poincareActNPoint_conjTensorProduct (PoincareGroup.lorentz' g.lorentz)]
      congr 1; ext i
      simp only [poincareActNPointDomain, PoincareGroup.act,
        PoincareGroup.inv_lorentz, PoincareGroup.inv_translation,
        PoincareGroup.lorentz'_lorentz, PoincareGroup.lorentz'_translation,
        Matrix.mulVec_zero, neg_zero, add_zero, Matrix.mulVec_add, Matrix.mulVec_neg])
  exact (hL.trans hT).symm

/-- The Poincaré action preserves the borchersSetoid equivalence relation. -/
theorem poincareActBorchers_setoid (g : PoincareGroup d)
    (F G : BorchersSequence d) (h : (borchersSetoid Wfn).r F G) :
    (borchersSetoid Wfn).r (poincareActBorchers g F) (poincareActBorchers g G) := by
  unfold borchersSetoid at h ⊢
  simp only at h ⊢
  rw [WightmanInnerProduct_poincare_invariant Wfn g F F,
      WightmanInnerProduct_poincare_invariant Wfn g G G,
      WightmanInnerProduct_poincare_invariant Wfn g F G,
      WightmanInnerProduct_poincare_invariant Wfn g G F]
  exact h

/-- The Poincaré action on the pre-Hilbert space (quotient). -/
def poincareActPreHilbert (g : PoincareGroup d) :
    PreHilbertSpace Wfn → PreHilbertSpace Wfn :=
  Quotient.lift (fun F => Quotient.mk _ (poincareActBorchers g F)) (by
    intro a b hab
    exact Quotient.sound (poincareActBorchers_setoid Wfn g a b hab))

/-- The Poincaré action on the pre-Hilbert space preserves the inner product. -/
theorem poincareActPreHilbert_inner (g : PoincareGroup d)
    (x y : PreHilbertSpace Wfn) :
    PreHilbertSpace.innerProduct Wfn (poincareActPreHilbert Wfn g x)
      (poincareActPreHilbert Wfn g y) =
    PreHilbertSpace.innerProduct Wfn x y := by
  induction x using Quotient.inductionOn with | _ F =>
  induction y using Quotient.inductionOn with | _ G =>
  exact WightmanInnerProduct_poincare_invariant Wfn g F G

/-! ### Linearity of the Poincaré action (n-point level) -/

/-- The Poincaré action on n-point Schwartz functions is additive. -/
@[simp]
theorem poincareActNPoint_add (g : PoincareGroup d) {n : ℕ}
    (f h : SchwartzNPoint d n) :
    poincareActNPoint g (f + h) = poincareActNPoint g f + poincareActNPoint g h := by
  ext x; rfl

/-- The Poincaré action on n-point Schwartz functions is scalar-linear. -/
@[simp]
theorem poincareActNPoint_smul (g : PoincareGroup d) {n : ℕ}
    (c : ℂ) (f : SchwartzNPoint d n) :
    poincareActNPoint g (c • f) = c • poincareActNPoint g f := by
  ext x; rfl

end
