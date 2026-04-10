/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.UniformSpace.Completion
import OSReconstruction.Wightman.Reconstruction
import OSReconstruction.Wightman.Reconstruction.GNSConstruction
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Reconstruction.PoincareAction
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.Wightman.SpectralEquivalence
import OSReconstruction.vNA.Unbounded.SpectralPowers
import OSReconstruction.SCV.PaleyWiener

/-!
# GNS Hilbert Space Construction

This file completes the GNS construction by equipping `PreHilbertSpace Wfn` with:
1. `AddCommGroup` and `Module ℂ` instances (algebraic structure on the quotient)
2. `InnerProductSpace.Core ℂ` instance (inner product axioms)
3. `NormedAddCommGroup` and `InnerProductSpace ℂ` (derived from the Core)
4. Hilbert space completion via `UniformSpace.Completion`
5. Vacuum vector and field operators on the completion
6. Assembly of `WightmanQFT` proving `wightman_reconstruction`

## Key Steps

The main challenge is lifting algebraic operations from `BorchersSequence` to the
quotient `PreHilbertSpace Wfn = Quotient (borchersSetoid Wfn)`. Two sequences
with the same `funcs` (but different `bound`) are equivalent in the quotient,
which makes the algebraic laws (associativity, commutativity, etc.) hold.

The definiteness axiom `⟨x, x⟩ = 0 → x = 0` follows from the construction of
the quotient: `borchersSetoid` identifies precisely the null vectors, so in the
quotient, the only vector with zero inner product is the zero class.

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter II (GNS)
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Reconstruction
open scoped InnerProductSpace LineDeriv

variable {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)

/-! ## Phase 1: Algebraic Instances on PreHilbertSpace -/

namespace PreHilbertSpace

/-- Two Borchers sequences with the same `funcs` are equivalent in the GNS quotient.
    This is because `⟨F-G, F-G⟩` depends only on `funcs`, and if all funcs agree,
    then `F-G` has zero funcs, making the inner product vanish. -/
theorem borchersSetoid_of_funcs_eq (F G : BorchersSequence d)
    (h : ∀ n, F.funcs n = G.funcs n) :
    borchersSetoid Wfn F G := by
  show (WightmanInnerProduct d Wfn.W F F + WightmanInnerProduct d Wfn.W G G
    - WightmanInnerProduct d Wfn.W F G - WightmanInnerProduct d Wfn.W G F).re = 0
  have h1 := WightmanInnerProduct_congr_left d Wfn.W Wfn.linear F G G h
  have h3 := WightmanInnerProduct_congr_left d Wfn.W Wfn.linear F G F h
  rw [h3, h1]
  have : WightmanInnerProduct d Wfn.W G F + WightmanInnerProduct d Wfn.W G G -
    WightmanInnerProduct d Wfn.W G G - WightmanInnerProduct d Wfn.W G F = 0 := by ring
  rw [this]; simp

/-- Addition respects the GNS equivalence relation. -/
theorem add_respects_equiv (F₁ G₁ F₂ G₂ : BorchersSequence d)
    (h₁ : borchersSetoid Wfn F₁ G₁) (h₂ : borchersSetoid Wfn F₂ G₂) :
    borchersSetoid Wfn (F₁ + F₂) (G₁ + G₂) := by
  -- (F₁+F₂) - (G₁+G₂) has the same funcs as (F₁-G₁) + (F₂-G₂)
  have hlin := Wfn.linear
  -- Extract null hypotheses
  have h1_null : (WightmanInnerProduct d Wfn.W (F₁ - G₁) (F₁ - G₁)).re = 0 := by
    rw [WightmanInnerProduct_expand_diff d Wfn.W hlin]; exact h₁
  have h2_null : (WightmanInnerProduct d Wfn.W (F₂ - G₂) (F₂ - G₂)).re = 0 := by
    rw [WightmanInnerProduct_expand_diff d Wfn.W hlin]; exact h₂
  -- Suffices: ⟨(F₁+F₂)-(G₁+G₂), (F₁+F₂)-(G₁+G₂)⟩.re = 0
  show (WightmanInnerProduct d Wfn.W (F₁ + F₂) (F₁ + F₂) +
    WightmanInnerProduct d Wfn.W (G₁ + G₂) (G₁ + G₂) -
    WightmanInnerProduct d Wfn.W (F₁ + F₂) (G₁ + G₂) -
    WightmanInnerProduct d Wfn.W (G₁ + G₂) (F₁ + F₂)).re = 0
  -- The difference (F₁+F₂)-(G₁+G₂) has same funcs as (F₁-G₁)+(F₂-G₂)
  have hfuncs : ∀ n, ((F₁ + F₂) - (G₁ + G₂)).funcs n = ((F₁ - G₁) + (F₂ - G₂)).funcs n := by
    intro n; simp only [BorchersSequence.add_funcs, BorchersSequence.sub_funcs]; abel
  -- So ⟨diff, diff⟩ equals ⟨(F₁-G₁)+(F₂-G₂), (F₁-G₁)+(F₂-G₂)⟩
  have hexpand := WightmanInnerProduct_expand_diff d Wfn.W hlin (F₁ + F₂) (G₁ + G₂)
  rw [← hexpand]
  have hcongr : WightmanInnerProduct d Wfn.W ((F₁ + F₂) - (G₁ + G₂))
      ((F₁ + F₂) - (G₁ + G₂)) =
    WightmanInnerProduct d Wfn.W ((F₁ - G₁) + (F₂ - G₂))
      ((F₁ - G₁) + (F₂ - G₂)) := by
    exact (WightmanInnerProduct_congr_left d Wfn.W hlin _ _ _ hfuncs).trans
      (WightmanInnerProduct_congr_right d Wfn.W hlin _ _ _ hfuncs)
  rw [hcongr]
  -- Now use: ⟨A+B, A+B⟩ = ⟨A,A⟩ + ⟨A,B⟩ + ⟨B,A⟩ + ⟨B,B⟩
  -- where A = F₁-G₁ (null) and B = F₂-G₂ (null)
  -- null_inner_product_zero: ⟨A,A⟩.re=0 → ⟨A,Y⟩=0
  have hA' : ∀ Y, WightmanInnerProduct d Wfn.W (F₁ - G₁) Y = 0 :=
    fun Y => null_inner_product_zero Wfn (F₁ - G₁) Y h1_null
  have hB' : ∀ Y, WightmanInnerProduct d Wfn.W (F₂ - G₂) Y = 0 :=
    fun Y => null_inner_product_zero Wfn (F₂ - G₂) Y h2_null
  rw [WightmanInnerProduct_add_left d Wfn.W hlin,
    WightmanInnerProduct_add_right d Wfn.W hlin,
    WightmanInnerProduct_add_right d Wfn.W hlin]
  simp only [hA', hB', Complex.zero_re, add_zero]

/-- Negation respects the GNS equivalence relation. -/
theorem neg_respects_equiv (F G : BorchersSequence d)
    (h : borchersSetoid Wfn F G) : borchersSetoid Wfn (-F) (-G) := by
  have hlin := Wfn.linear
  show (WightmanInnerProduct d Wfn.W (-F) (-F) + WightmanInnerProduct d Wfn.W (-G) (-G) -
    WightmanInnerProduct d Wfn.W (-F) (-G) - WightmanInnerProduct d Wfn.W (-G) (-F)).re = 0
  rw [WightmanInnerProduct_neg_left d Wfn.W hlin, WightmanInnerProduct_neg_right d Wfn.W hlin,
    WightmanInnerProduct_neg_left d Wfn.W hlin, WightmanInnerProduct_neg_right d Wfn.W hlin,
    WightmanInnerProduct_neg_left d Wfn.W hlin, WightmanInnerProduct_neg_right d Wfn.W hlin,
    WightmanInnerProduct_neg_left d Wfn.W hlin, WightmanInnerProduct_neg_right d Wfn.W hlin]
  simp only [neg_neg]
  exact h

/-- Scalar multiplication respects the GNS equivalence relation. -/
theorem smul_respects_equiv (c : ℂ) (F G : BorchersSequence d)
    (h : borchersSetoid Wfn F G) : borchersSetoid Wfn (c • F) (c • G) := by
  have hlin := Wfn.linear
  -- ⟨c•F - c•G, c•F - c•G⟩ has same funcs as c•(F-G)
  have h_null : (WightmanInnerProduct d Wfn.W (F - G) (F - G)).re = 0 := by
    rw [WightmanInnerProduct_expand_diff d Wfn.W hlin]; exact h
  show (WightmanInnerProduct d Wfn.W (c • F) (c • F) +
    WightmanInnerProduct d Wfn.W (c • G) (c • G) -
    WightmanInnerProduct d Wfn.W (c • F) (c • G) -
    WightmanInnerProduct d Wfn.W (c • G) (c • F)).re = 0
  rw [WightmanInnerProduct_smul_left d Wfn.W hlin, WightmanInnerProduct_smul_right d Wfn.W hlin,
    WightmanInnerProduct_smul_left d Wfn.W hlin, WightmanInnerProduct_smul_right d Wfn.W hlin,
    WightmanInnerProduct_smul_left d Wfn.W hlin, WightmanInnerProduct_smul_right d Wfn.W hlin,
    WightmanInnerProduct_smul_left d Wfn.W hlin, WightmanInnerProduct_smul_right d Wfn.W hlin]
  -- Factor: conj(c) * c * (⟨F,F⟩ + ⟨G,G⟩ - ⟨F,G⟩ - ⟨G,F⟩) = |c|² * expr
  have : (starRingEnd ℂ c * (c * WightmanInnerProduct d Wfn.W F F) +
    starRingEnd ℂ c * (c * WightmanInnerProduct d Wfn.W G G) -
    starRingEnd ℂ c * (c * WightmanInnerProduct d Wfn.W F G) -
    starRingEnd ℂ c * (c * WightmanInnerProduct d Wfn.W G F)) =
    starRingEnd ℂ c * c * (WightmanInnerProduct d Wfn.W F F +
      WightmanInnerProduct d Wfn.W G G -
      WightmanInnerProduct d Wfn.W F G -
      WightmanInnerProduct d Wfn.W G F) := by ring
  rw [this, Complex.mul_re]
  -- |c|² is real: conj(c)*c = |c|², and im(|c|²) = 0
  have hcc : (starRingEnd ℂ c * c).im = 0 := by
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [h, hcc]; ring

instance instZero : Zero (PreHilbertSpace Wfn) where
  zero := Quotient.mk _ (0 : BorchersSequence d)

instance instAdd : Add (PreHilbertSpace Wfn) where
  add := Quotient.map₂ (· + ·) (fun _ _ h₁ _ _ h₂ => add_respects_equiv Wfn _ _ _ _ h₁ h₂)

instance instNeg : Neg (PreHilbertSpace Wfn) where
  neg := Quotient.map (- ·) (fun _ _ h => neg_respects_equiv Wfn _ _ h)

instance instSMul : SMul ℂ (PreHilbertSpace Wfn) where
  smul c := Quotient.map (c • ·) (fun _ _ h => smul_respects_equiv Wfn c _ _ h)

instance instSub : Sub (PreHilbertSpace Wfn) where
  sub a b := a + (-b)

/-- Key helper: if two BorchersSequences have the same funcs, their quotient
    classes are equal (not just equivalent). -/
theorem mk_eq_of_funcs_eq (F G : BorchersSequence d)
    (h : ∀ n, F.funcs n = G.funcs n) :
    (Quotient.mk (borchersSetoid Wfn) F : PreHilbertSpace Wfn) =
    Quotient.mk (borchersSetoid Wfn) G :=
  Quotient.sound (borchersSetoid_of_funcs_eq Wfn F G h)

instance instAddCommGroup : AddCommGroup (PreHilbertSpace Wfn) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with | h F =>
    induction b using Quotient.inductionOn with | h G =>
    induction c using Quotient.inductionOn with | h H =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp [add_assoc])
  zero_add a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)
  add_zero a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)
  add_comm a b := by
    induction a using Quotient.inductionOn with | h F =>
    induction b using Quotient.inductionOn with | h G =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp [add_comm])
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℂ (PreHilbertSpace Wfn) where
  one_smul a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)
  mul_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp [mul_smul])
  smul_zero c := by
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)
  smul_add c a b := by
    induction a using Quotient.inductionOn with | h F =>
    induction b using Quotient.inductionOn with | h G =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp [smul_add])
  add_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp [add_smul])
  zero_smul a := by
    induction a using Quotient.inductionOn with | h F =>
    exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by simp)

/-! ## Phase 2: Inner Product Space Core -/

/-- The inner product on PreHilbertSpace as an `Inner` instance. -/
instance instInner : Inner ℂ (PreHilbertSpace Wfn) where
  inner := PreHilbertSpace.innerProduct Wfn

theorem inner_eq (F G : BorchersSequence d) :
    @inner ℂ (PreHilbertSpace Wfn) (instInner Wfn) ⟦F⟧ ⟦G⟧ =
    WightmanInnerProduct d Wfn.W F G := rfl

/-- Hermiticity of the inner product on the quotient. -/
theorem inner_conj_symm (x y : PreHilbertSpace Wfn) :
    starRingEnd ℂ (@inner ℂ _ (instInner Wfn) y x) =
    @inner ℂ _ (instInner Wfn) x y := by
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  exact (WightmanInnerProduct_hermitian Wfn F G).symm

/-- Positivity of the inner product on the quotient. -/
theorem inner_re_nonneg (x : PreHilbertSpace Wfn) :
    0 ≤ RCLike.re (@inner ℂ _ (instInner Wfn) x x) := by
  induction x using Quotient.inductionOn with | h F =>
  exact preHilbert_inner_pos Wfn ⟦F⟧

/-- Additivity of the inner product in the first argument. -/
theorem inner_add_left (x y z : PreHilbertSpace Wfn) :
    @inner ℂ _ (instInner Wfn) (x + y) z =
    @inner ℂ _ (instInner Wfn) x z + @inner ℂ _ (instInner Wfn) y z := by
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  induction z using Quotient.inductionOn with | h H =>
  exact WightmanInnerProduct_add_left d Wfn.W Wfn.linear F G H

/-- Scalar multiplication in the first argument (conjugate linear). -/
theorem inner_smul_left (x y : PreHilbertSpace Wfn) (r : ℂ) :
    @inner ℂ _ (instInner Wfn) (r • x) y =
    starRingEnd ℂ r * @inner ℂ _ (instInner Wfn) x y := by
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  exact WightmanInnerProduct_smul_left d Wfn.W Wfn.linear r F G

/-- Definiteness: ⟨x, x⟩ = 0 → x = 0 in the quotient.
    This is the key property that follows from the GNS quotient construction. -/
theorem inner_definite (x : PreHilbertSpace Wfn)
    (h : @inner ℂ _ (instInner Wfn) x x = 0) : x = 0 := by
  induction x using Quotient.inductionOn with | h F =>
  -- h : WightmanInnerProduct d Wfn.W F F = 0
  -- Goal: ⟦F⟧ = ⟦0⟧, i.e., F ≈ 0 in borchersSetoid
  apply Quotient.sound
  show (WightmanInnerProduct d Wfn.W F F + WightmanInnerProduct d Wfn.W 0 0 -
    WightmanInnerProduct d Wfn.W F 0 - WightmanInnerProduct d Wfn.W 0 F).re = 0
  rw [WightmanInnerProduct_zero_right d Wfn.W Wfn.linear F,
    WightmanInnerProduct_zero_left d Wfn.W Wfn.linear F,
    WightmanInnerProduct_zero_right d Wfn.W Wfn.linear (0 : BorchersSequence d)]
  simp only [sub_zero]
  have h' : WightmanInnerProduct d Wfn.W F F = 0 := h
  rw [h']; simp

/-- The `InnerProductSpace.Core` instance on PreHilbertSpace. -/
instance instCore : InnerProductSpace.Core ℂ (PreHilbertSpace Wfn) where
  toCore := {
    toInner := instInner Wfn
    conj_inner_symm := inner_conj_symm Wfn
    re_inner_nonneg := inner_re_nonneg Wfn
    add_left := inner_add_left Wfn
    smul_left := inner_smul_left Wfn
  }
  definite := inner_definite Wfn

/-! ## Phase 3: Normed Space and Inner Product Space

We use the `InnerProductSpace.Core` to derive both `NormedAddCommGroup` and
`InnerProductSpace` instances. The key is that `Core.toNormedAddCommGroup`
provides the norm ‖x‖ = √(Re⟨x,x⟩), and `ofCore` provides the inner product
space structure compatible with that norm.

The `@` annotations are needed to ensure both instances use the same
underlying `SeminormedAddCommGroup`. -/

/-- NormedAddCommGroup on PreHilbertSpace, derived from the Core.
    The norm is ‖x‖ = √(Re⟨x,x⟩). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (PreHilbertSpace Wfn) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (instCore Wfn)

/-- InnerProductSpace on PreHilbertSpace, derived from the Core.
    Uses the same `SeminormedAddCommGroup` as `instNormedAddCommGroup`. -/
noncomputable instance instInnerProductSpace :
    @InnerProductSpace ℂ (PreHilbertSpace Wfn) _
      (instNormedAddCommGroup Wfn).toSeminormedAddCommGroup :=
  @InnerProductSpace.ofCore ℂ _ _ _ _ (instCore Wfn).toCore

/-! ## Phase 4: Hilbert Space Completion -/

/-- The GNS Hilbert space: Cauchy completion of the pre-Hilbert space.
    This is a complete inner product space (Hilbert space). -/
abbrev GNSHilbertSpace := UniformSpace.Completion (PreHilbertSpace Wfn)

/-- The vacuum vector in the Hilbert space (image of vacuum under completion embedding). -/
def gnsVacuum : GNSHilbertSpace Wfn :=
  (vacuumState Wfn : GNSHilbertSpace Wfn)

/-- The vacuum is normalized: ‖Ω‖ = 1 in the pre-Hilbert space.
    The norm is ‖x‖ = √(normSq x) = √(Re⟨x,x⟩), defined by the Core. -/
theorem vacuumState_norm : ‖vacuumState Wfn‖ = 1 := by
  have hvn := vacuum_normalized Wfn
  have hns : @InnerProductSpace.Core.normSq ℂ _ _ _ _ (instCore Wfn).toCore
      (vacuumState Wfn) = 1 := by
    show RCLike.re (PreHilbertSpace.innerProduct Wfn (vacuumState Wfn) (vacuumState Wfn)) = 1
    rw [hvn]; simp
  show Real.sqrt (@InnerProductSpace.Core.normSq ℂ _ _ _ _ (instCore Wfn).toCore
    (vacuumState Wfn)) = 1
  rw [hns, Real.sqrt_one]

end PreHilbertSpace

open PreHilbertSpace

/-! ## Phase 4b: Poincaré Representation on the GNS Hilbert Space -/

/-! ### Linearity and group law on PreHilbertSpace -/

/-- The Poincaré action on the pre-Hilbert space is additive. -/
theorem poincareActPreHilbert_add (g : PoincareGroup d)
    (x y : PreHilbertSpace Wfn) :
    poincareActPreHilbert Wfn g (x + y) =
    poincareActPreHilbert Wfn g x + poincareActPreHilbert Wfn g y := by
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by
    simp [poincareActBorchers, poincareActNPoint_add])

/-- The Poincaré action on the pre-Hilbert space is scalar-linear. -/
theorem poincareActPreHilbert_smul (g : PoincareGroup d)
    (c : ℂ) (x : PreHilbertSpace Wfn) :
    poincareActPreHilbert Wfn g (c • x) =
    c • poincareActPreHilbert Wfn g x := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by
    simp [poincareActBorchers, poincareActNPoint_smul])

/-- The identity acts trivially on the pre-Hilbert space. -/
theorem poincareActPreHilbert_one (x : PreHilbertSpace Wfn) :
    poincareActPreHilbert Wfn 1 x = x := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by
    change poincareActNPoint 1 (F.funcs n) = F.funcs n
    ext z; simp only [poincareActNPoint_apply, inv_one]
    congr 1; funext i; exact PoincareGroup.act_one (z i))

/-- The Poincaré action composes correctly: (g₁*g₂)·x = g₁·(g₂·x). -/
theorem poincareActPreHilbert_mul (g₁ g₂ : PoincareGroup d)
    (x : PreHilbertSpace Wfn) :
    poincareActPreHilbert Wfn (g₁ * g₂) x =
    poincareActPreHilbert Wfn g₁ (poincareActPreHilbert Wfn g₂ x) := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fun n => by
    change poincareActNPoint (g₁ * g₂) (F.funcs n) =
      poincareActNPoint g₁ (poincareActNPoint g₂ (F.funcs n))
    ext z; simp only [poincareActNPoint_apply, mul_inv_rev]
    congr 1; funext i; exact PoincareGroup.act_mul g₂⁻¹ g₁⁻¹ (z i))

/-! ### Continuous linear map on PreHilbertSpace -/

/-- The Poincaré action as a linear map on PreHilbertSpace. -/
noncomputable def poincareActPreHilbertLinearMap (g : PoincareGroup d) :
    PreHilbertSpace Wfn →ₗ[ℂ] PreHilbertSpace Wfn where
  toFun := poincareActPreHilbert Wfn g
  map_add' := poincareActPreHilbert_add Wfn g
  map_smul' := poincareActPreHilbert_smul Wfn g

/-- The Poincaré action preserves the norm on PreHilbertSpace. -/
theorem poincareActPreHilbert_norm (g : PoincareGroup d)
    (x : PreHilbertSpace Wfn) :
    ‖poincareActPreHilbert Wfn g x‖ = ‖x‖ := by
  -- The norm from Core.toNormedAddCommGroup is √(normSq x) where normSq x = Re⟨x,x⟩
  show Real.sqrt (@InnerProductSpace.Core.normSq ℂ _ _ _ _ (instCore Wfn).toCore
    (poincareActPreHilbert Wfn g x)) =
    Real.sqrt (@InnerProductSpace.Core.normSq ℂ _ _ _ _ (instCore Wfn).toCore x)
  congr 1
  -- normSq = Re(inner) and inner is preserved
  exact congr_arg Complex.re (poincareActPreHilbert_inner Wfn g x x)

/-- The Poincaré action as a ContinuousLinearMap on PreHilbertSpace. -/
noncomputable def poincareActPreHilbert_CLM (g : PoincareGroup d) :
    PreHilbertSpace Wfn →L[ℂ] PreHilbertSpace Wfn :=
  (poincareActPreHilbertLinearMap Wfn g).mkContinuous 1 (fun x => by
    rw [one_mul]; exact le_of_eq (poincareActPreHilbert_norm Wfn g x))

@[simp]
theorem poincareActPreHilbert_CLM_apply (g : PoincareGroup d)
    (x : PreHilbertSpace Wfn) :
    poincareActPreHilbert_CLM Wfn g x = poincareActPreHilbert Wfn g x := rfl

/-! ### Extension to the GNS Hilbert space (completion) -/

/-- The Poincaré action on the GNS Hilbert space, obtained by extending the
    pre-Hilbert space action to the completion. -/
noncomputable def poincareActGNS (g : PoincareGroup d) :
    GNSHilbertSpace Wfn →L[ℂ] GNSHilbertSpace Wfn :=
  (UniformSpace.Completion.toComplL.comp (poincareActPreHilbert_CLM Wfn g)).extend
    UniformSpace.Completion.toComplL

/-- The GNS Poincaré action agrees with the pre-Hilbert action on embedded vectors. -/
theorem poincareActGNS_coe (g : PoincareGroup d) (x : PreHilbertSpace Wfn) :
    poincareActGNS Wfn g (x : GNSHilbertSpace Wfn) =
    ((poincareActPreHilbert Wfn g x : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) := by
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _) x

/-- The Poincaré action preserves norms on the completion. -/
theorem poincareActGNS_norm (g : PoincareGroup d) (x : GNSHilbertSpace Wfn) :
    ‖poincareActGNS Wfn g x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (poincareActGNS Wfn g).continuous.norm continuous_norm
  · intro a
    rw [poincareActGNS_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact poincareActPreHilbert_norm Wfn g a

/-! ### Group law on the completion -/

/-- The identity acts trivially on the GNS Hilbert space. -/
theorem poincareActGNS_one :
    poincareActGNS Wfn (1 : PoincareGroup d) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.extend_unique _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _)
    (ContinuousLinearMap.id ℂ _) (by
      ext x
      simp [poincareActPreHilbert_CLM_apply, poincareActPreHilbert_one Wfn])

/-- The Poincaré action composes correctly on the GNS Hilbert space. -/
theorem poincareActGNS_mul (g₁ g₂ : PoincareGroup d) :
    poincareActGNS Wfn (g₁ * g₂) =
    (poincareActGNS Wfn g₁).comp (poincareActGNS Wfn g₂) :=
  ContinuousLinearMap.extend_unique _
    (UniformSpace.Completion.denseRange_coe)
    (UniformSpace.Completion.isUniformInducing_coe _)
    ((poincareActGNS Wfn g₁).comp (poincareActGNS Wfn g₂)) (by
      ext x
      simp only [ContinuousLinearMap.comp_apply, poincareActPreHilbert_CLM_apply]
      show (poincareActGNS Wfn g₁) ((poincareActGNS Wfn g₂) (x : GNSHilbertSpace Wfn)) =
        ((poincareActPreHilbert Wfn (g₁ * g₂) x : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn)
      rw [poincareActGNS_coe Wfn g₂ x, poincareActGNS_coe Wfn g₁,
        ← poincareActPreHilbert_mul Wfn g₁ g₂ x])

/-! ### Unitarity -/

/-- The Poincaré action preserves the inner product on the completion.
    This follows from inner product preservation on the dense pre-Hilbert space. -/
theorem poincareActGNS_inner (g : PoincareGroup d)
    (x y : GNSHilbertSpace Wfn) :
    @inner ℂ _ _ (poincareActGNS Wfn g x) (poincareActGNS Wfn g y) =
    @inner ℂ _ _ x y := by
  -- Density argument: apply induction_on twice
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_inner.comp ((poincareActGNS Wfn g).continuous.prodMk continuous_const))
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  · intro a
    refine UniformSpace.Completion.induction_on y ?_ ?_
    · exact isClosed_eq
        (continuous_inner.comp (continuous_const.prodMk
          (poincareActGNS Wfn g).continuous))
        (continuous_inner.comp (continuous_const.prodMk continuous_id))
    · intro b
      rw [poincareActGNS_coe, poincareActGNS_coe,
        UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
      exact poincareActPreHilbert_inner Wfn g a b

/-- The Poincaré action is unitary: U(g)*.U(g) = id. -/
theorem poincareActGNS_adjoint_comp (g : PoincareGroup d) :
    (poincareActGNS Wfn g).adjoint.comp (poincareActGNS Wfn g) =
    ContinuousLinearMap.id ℂ _ := by
  ext x
  apply @ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.id_apply]
  exact poincareActGNS_inner Wfn g y x

/-- The Poincaré representation on the GNS Hilbert space. -/
noncomputable def gnsPoincareRep :
    PoincareRepresentation d (GNSHilbertSpace Wfn) where
  U := poincareActGNS Wfn
  unitary := poincareActGNS_adjoint_comp Wfn
  mul_map := poincareActGNS_mul Wfn
  one_map := poincareActGNS_one Wfn

/-! ### Vacuum invariance -/

/-- The vacuum is Poincaré-invariant: U(g)Ω = Ω for all g. -/
theorem gnsVacuum_poincare_invariant (g : PoincareGroup d) :
    poincareActGNS Wfn g (gnsVacuum Wfn) = gnsVacuum Wfn := by
  show poincareActGNS Wfn g (vacuumState Wfn : GNSHilbertSpace Wfn) =
    (vacuumState Wfn : GNSHilbertSpace Wfn)
  rw [poincareActGNS_coe]
  congr 1
  -- poincareActPreHilbert Wfn g (vacuumState Wfn) = vacuumState Wfn
  show poincareActPreHilbert Wfn g ⟦vacuumSequence⟧ = ⟦vacuumSequence⟧
  apply Quotient.sound
  -- poincareActBorchers g vacuumSequence ≈ vacuumSequence
  -- They have the same funcs (vacuum has no spacetime arguments to transform)
  exact borchersSetoid_of_funcs_eq Wfn _ _ (fun n => by
    cases n with
    | zero => ext x; rfl
    | succ n =>
      change poincareActNPoint g (0 : SchwartzNPoint d (n + 1)) = 0
      exact poincareActNPoint_zero g (n + 1))

/-! ## Phase 5: Field Operators on Completion and WightmanQFT Assembly -/

/-- The completion embedding is injective (PreHilbertSpace has definite norm). -/
private theorem completion_coe_injective :
    Function.Injective (↑· : PreHilbertSpace Wfn → GNSHilbertSpace Wfn) :=
  UniformSpace.Completion.coe_injective _

/-! ### Field Operator Linearity on PreHilbertSpace -/

/-- fieldOperator is additive in the test function: φ(f+g)x = φ(f)x + φ(g)x. -/
theorem fieldOperator_add_test (f g : SchwartzSpacetime d) (x : PreHilbertSpace Wfn) :
    fieldOperator Wfn (f + g) x = fieldOperator Wfn f x + fieldOperator Wfn g x := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fieldOperatorAction_add_test_funcs f g F)

/-- fieldOperator is scalar-linear in the test function: φ(c·f)x = c·φ(f)x. -/
theorem fieldOperator_smul_test (c : ℂ) (f : SchwartzSpacetime d) (x : PreHilbertSpace Wfn) :
    fieldOperator Wfn (c • f) x = c • fieldOperator Wfn f x := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fieldOperatorAction_smul_test_funcs c f F)

/-- fieldOperator is additive in the vector: φ(f)(x+y) = φ(f)x + φ(f)y. -/
theorem fieldOperator_vector_add (f : SchwartzSpacetime d) (x y : PreHilbertSpace Wfn) :
    fieldOperator Wfn f (x + y) = fieldOperator Wfn f x + fieldOperator Wfn f y := by
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fieldOperatorAction_add_vec_funcs f F G)

/-- fieldOperator is scalar-linear in the vector: φ(f)(c·x) = c·φ(f)x. -/
theorem fieldOperator_vector_smul (f : SchwartzSpacetime d) (c : ℂ) (x : PreHilbertSpace Wfn) :
    fieldOperator Wfn f (c • x) = c • fieldOperator Wfn f x := by
  induction x using Quotient.inductionOn with | h F =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fieldOperatorAction_smul_vec_funcs f c F)

/-! ### Field Operators on Completion -/

/-- Field operator on the GNS Hilbert space (completion).
    For vectors in the image of the pre-Hilbert space, applies `fieldOperator`
    and re-embeds. Outside the dense subspace, maps to 0 (junk value). -/
noncomputable def gnsFieldOp (f : SchwartzSpacetime d) :
    GNSHilbertSpace Wfn → GNSHilbertSpace Wfn :=
  Function.extend
    (↑· : PreHilbertSpace Wfn → GNSHilbertSpace Wfn)
    (fun y => (fieldOperator Wfn f y : GNSHilbertSpace Wfn))
    0

/-- Key lemma: the field operator on the completion agrees with `fieldOperator`
    on embedded pre-Hilbert space vectors. -/
theorem gnsFieldOp_coe (f : SchwartzSpacetime d) (y : PreHilbertSpace Wfn) :
    gnsFieldOp Wfn f (↑y : GNSHilbertSpace Wfn) =
    (fieldOperator Wfn f y : GNSHilbertSpace Wfn) :=
  (completion_coe_injective Wfn).extend_apply _ _ y

/-- The vacuum norm in the completion: ‖Ω‖ = 1. -/
theorem gnsVacuum_norm : ‖gnsVacuum Wfn‖ = 1 := by
  show ‖(vacuumState Wfn : GNSHilbertSpace Wfn)‖ = 1
  rw [UniformSpace.Completion.norm_coe]
  exact vacuumState_norm Wfn

/-! ### Domain: Dense Subspace of Pre-Hilbert Space Vectors -/

/-- The domain for field operators: the image of the pre-Hilbert space under the
    completion embedding. This is a submodule because the embedding is linear. -/
noncomputable def gnsDomainSubmodule :
    Submodule ℂ (GNSHilbertSpace Wfn) where
  carrier := {ψ | ∃ x : PreHilbertSpace Wfn, (x : GNSHilbertSpace Wfn) = ψ}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, UniformSpace.Completion.coe_add x y⟩
  zero_mem' := ⟨0, UniformSpace.Completion.coe_zero⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨c • x, UniformSpace.Completion.coe_smul c x⟩

/-- The domain is dense: the image of the pre-Hilbert space is dense in the completion. -/
theorem gnsDomain_dense : Dense (gnsDomainSubmodule Wfn : Set (GNSHilbertSpace Wfn)) := by
  have : (gnsDomainSubmodule Wfn : Set (GNSHilbertSpace Wfn)) =
      Set.range (↑· : PreHilbertSpace Wfn → GNSHilbertSpace Wfn) := by
    ext ψ; exact Iff.rfl
  rw [this]
  exact UniformSpace.Completion.denseRange_coe

/-- The domain as a DenseSubspace. -/
noncomputable def gnsDomain : DenseSubspace (GNSHilbertSpace Wfn) where
  toSubmodule := gnsDomainSubmodule Wfn
  dense := gnsDomain_dense Wfn

/-- The vacuum is in the domain. -/
theorem gnsVacuum_in_domain : gnsVacuum Wfn ∈ gnsDomain Wfn :=
  ⟨vacuumState Wfn, rfl⟩

/-- Field operators preserve the domain: if ψ ∈ D then φ(f)ψ ∈ D. -/
theorem gnsFieldOp_domain (f : SchwartzSpacetime d) (ψ : GNSHilbertSpace Wfn)
    (hψ : ψ ∈ gnsDomain Wfn) : gnsFieldOp Wfn f ψ ∈ gnsDomain Wfn := by
  obtain ⟨x, hx⟩ := hψ
  rw [← hx, gnsFieldOp_coe]
  exact ⟨fieldOperator Wfn f x, rfl⟩

/-- The matrix element ⟪↑x, φ(f)(↑y)⟫ is continuous in f for pre-Hilbert space vectors.
    This is a finite sum of continuous terms via temperedness + prependField continuity. -/
private theorem matrix_element_continuous_aux (x y : PreHilbertSpace Wfn) :
    Continuous (fun f : SchwartzSpacetime d =>
      @inner ℂ (GNSHilbertSpace Wfn) _
        (x : GNSHilbertSpace Wfn) (gnsFieldOp Wfn f (y : GNSHilbertSpace Wfn))) := by
  -- Lift to Borchers sequence representatives
  induction x using Quotient.inductionOn with | h F =>
  induction y using Quotient.inductionOn with | h G =>
  -- Step 1: Reduce to continuity of WightmanInnerProduct
  suffices h : Continuous (fun f => WightmanInnerProduct d Wfn.W F (fieldOperatorAction f G)) from
    h.congr (fun f => by
      have h1 := gnsFieldOp_coe Wfn f (Quotient.mk (borchersSetoid Wfn) G)
      rw [h1, UniformSpace.Completion.inner_coe]; rfl)
  -- Step 2: The WightmanInnerProduct is a double finite sum; each term is continuous in f
  simp only [WightmanInnerProduct, fieldOperatorAction_bound]
  apply continuous_finset_sum _ (fun n _ => ?_)
  apply continuous_finset_sum _ (fun m _ => ?_)
  -- Case split: m = 0 gives a constant (fieldOperatorAction_funcs_zero), m = k+1 uses prependField
  cases m with
  | zero =>
    simp only [fieldOperatorAction_funcs_zero, SchwartzMap.conjTensorProduct_zero_right,
      (Wfn.linear _).map_zero]
    exact continuous_const
  | succ k =>
    simp only [fieldOperatorAction_funcs_succ]
    exact (Wfn.tempered _).comp
      ((SchwartzMap.conjTensorProduct_continuous_right _).comp
        (SchwartzMap.prependField_continuous_left _))

/-! ### Locality from Local Commutativity -/

/-- Key pointwise identity: swapping the first two coordinates after conjTensorProduct
    corresponds to swapping the roles of f and g in double prependField.
    This is the computational heart of the locality proof. -/
private theorem conjTP_prependField_swap
    (f g : SchwartzSpacetime d) (hk : SchwartzNPoint d k) (n : ℕ)
    (Hn : SchwartzNPoint d n) (x : NPointDomain d (n + (k + 2))) :
    (Hn.conjTensorProduct (SchwartzMap.prependField g (SchwartzMap.prependField f hk))) x =
    (Hn.conjTensorProduct (SchwartzMap.prependField f (SchwartzMap.prependField g hk)))
      (fun l => x (Equiv.swap ⟨n, by omega⟩ ⟨n + 1, by omega⟩ l)) := by
  simp only [SchwartzMap.conjTensorProduct_apply, SchwartzMap.prependField_apply,
    splitFirst, splitLast]
  -- Resolve all swap applications using Fin arithmetic
  have hHn : (fun i => x (Equiv.swap (⟨n, by omega⟩ : Fin (n + (k + 2))) ⟨n + 1, by omega⟩
      (Fin.castAdd (k + 2) (Fin.rev i)))) = (fun i => x (Fin.castAdd (k + 2) (Fin.rev i))) := by
    funext i; congr 1; apply Equiv.swap_apply_of_ne_of_ne
    · intro heq; have := congr_arg Fin.val heq
      simp [Fin.val_castAdd, Fin.val_rev] at this; omega
    · intro heq; have := congr_arg Fin.val heq
      simp [Fin.val_castAdd, Fin.val_rev] at this; omega
  have h0 : x (Equiv.swap (⟨n, by omega⟩ : Fin (n + (k + 2))) ⟨n + 1, by omega⟩
      (Fin.natAdd n 0)) = x (Fin.natAdd n 1) := by
    congr 1
    rw [show Fin.natAdd n (0 : Fin (k + 2)) = ⟨n, by omega⟩ from
      Fin.ext (by simp [Fin.val_natAdd]), Equiv.swap_apply_left]
    exact Fin.ext (by simp [Fin.val_natAdd])
  have h1 : x (Equiv.swap (⟨n, by omega⟩ : Fin (n + (k + 2))) ⟨n + 1, by omega⟩
      (Fin.natAdd n (Fin.succ (0 : Fin (k + 1))))) = x (Fin.natAdd n 0) := by
    congr 1
    rw [show Fin.natAdd n (Fin.succ (0 : Fin (k + 1))) = ⟨n + 1, by omega⟩ from
      Fin.ext (by simp [Fin.val_natAdd]), Equiv.swap_apply_right]
    exact Fin.ext (by simp [Fin.val_natAdd])
  have hss : (fun j : Fin k => x (Equiv.swap (⟨n, by omega⟩ : Fin (n + (k + 2)))
      ⟨n + 1, by omega⟩ (Fin.natAdd n (Fin.succ (Fin.succ j))))) =
      (fun j => x (Fin.natAdd n (Fin.succ (Fin.succ j)))) := by
    funext j; congr 1; apply Equiv.swap_apply_of_ne_of_ne
    · intro heq; have := congr_arg Fin.val heq
      simp [Fin.val_natAdd, Fin.val_succ] at this
    · intro heq; have := congr_arg Fin.val heq
      simp [Fin.val_natAdd, Fin.val_succ] at this
  rw [hHn, h0, h1, hss]
  conv_lhs => arg 2; rw [mul_left_comm]
  rfl

/-- Per-term equality: applying the Wightman function to conjTensorProduct with
    prependField f (prependField g h) equals the same with f, g swapped,
    when f, g have spacelike-separated supports. -/
private theorem locality_term_eq
    (f g : SchwartzSpacetime d) (hfg : AreSpacelikeSeparatedSupports d f g)
    (n k : ℕ) (Hn : SchwartzNPoint d n) (hk : SchwartzNPoint d k) :
    Wfn.W (n + (k + 2))
      (Hn.conjTensorProduct (SchwartzMap.prependField f (SchwartzMap.prependField g hk))) =
    Wfn.W (n + (k + 2))
      (Hn.conjTensorProduct (SchwartzMap.prependField g (SchwartzMap.prependField f hk))) := by
  apply Wfn.locally_commutative (n + (k + 2)) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
  · -- Support condition: when the test function doesn't vanish at x,
    -- coordinates n and n+1 are spacelike separated
    intro x hx
    -- Bridge .toFun to ⇑ so that simp lemmas apply
    change (Hn.conjTensorProduct (SchwartzMap.prependField f (SchwartzMap.prependField g hk))) x ≠ 0 at hx
    simp only [SchwartzMap.conjTensorProduct_apply, SchwartzMap.prependField_apply,
      splitFirst, splitLast] at hx
    -- The product is nonzero, so each factor is nonzero
    have hne := mul_ne_zero_iff.mp hx
    have hfg_ne := mul_ne_zero_iff.mp hne.2
    have hf_ne := hfg_ne.1
    have hg_ne := (mul_ne_zero_iff.mp hfg_ne.2).1
    -- f is evaluated at splitLast x 0 = x(natAdd n 0) = x ⟨n, _⟩
    -- g is evaluated at splitLast x 1 = x(natAdd n 1) = x ⟨n+1, _⟩
    apply hfg
    · exact Function.mem_support.mpr hf_ne
    · exact Function.mem_support.mpr hg_ne
  · -- Swap identity: the swapped function equals the original with f, g exchanged
    intro x
    show (Hn.conjTensorProduct (SchwartzMap.prependField g (SchwartzMap.prependField f hk))) x =
      (Hn.conjTensorProduct (SchwartzMap.prependField f (SchwartzMap.prependField g hk)))
        (fun k => x (Equiv.swap ⟨n, by omega⟩ ⟨n + 1, by omega⟩ k))
    exact conjTP_prependField_swap f g hk n Hn x

/-- The Wightman inner product is the same for φ(f)φ(g)F and φ(g)φ(f)F in the
    second argument, when f, g have spacelike-separated supports. -/
private theorem locality_inner_eq
    (f g : SchwartzSpacetime d) (hfg : AreSpacelikeSeparatedSupports d f g)
    (H F : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W H (fieldOperatorAction f (fieldOperatorAction g F)) =
    WightmanInnerProduct d Wfn.W H (fieldOperatorAction g (fieldOperatorAction f F)) := by
  simp only [WightmanInnerProduct]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  -- For m ≤ 1: both sides give 0 (fieldOperatorAction kills low components)
  -- For m = k + 2: apply locality_term_eq
  match m with
  | 0 => simp
  | 1 => simp [SchwartzMap.prependField_zero_right]
  | k + 2 =>
    simp only [fieldOperatorAction_funcs_succ]
    exact locality_term_eq Wfn f g hfg n k (H.funcs n) (F.funcs k)

/-- φ(f)φ(g)F and φ(g)φ(f)F are equivalent in the Borchers setoid when f, g
    have spacelike-separated supports. -/
private theorem locality_setoid
    (f g : SchwartzSpacetime d) (hfg : AreSpacelikeSeparatedSupports d f g)
    (F : BorchersSequence d) :
    borchersSetoid Wfn (fieldOperatorAction f (fieldOperatorAction g F))
      (fieldOperatorAction g (fieldOperatorAction f F)) := by
  -- The setoid condition is IP(A-B, A-B).re = 0
  -- From locality_inner_eq: IP(H, A) = IP(H, B) for all H
  -- So IP(H, A-B) = 0 for all H, in particular IP(A-B, A-B) = 0
  set A := fieldOperatorAction f (fieldOperatorAction g F)
  set B := fieldOperatorAction g (fieldOperatorAction f F)
  have hAB : ∀ H, WightmanInnerProduct d Wfn.W H A = WightmanInnerProduct d Wfn.W H B :=
    fun H => locality_inner_eq Wfn f g hfg H F
  -- IP(H, A - B) = IP(H, A) - IP(H, B) = 0
  have hNull : ∀ H, WightmanInnerProduct d Wfn.W H (A - B) = 0 := by
    intro H
    rw [WightmanInnerProduct_sub_right d Wfn.W Wfn.linear H A B, hAB H, sub_self]
  -- In particular IP(A-B, A-B) = 0
  have hNullSelf : WightmanInnerProduct d Wfn.W (A - B) (A - B) = 0 := hNull (A - B)
  -- The setoid condition
  show (WightmanInnerProduct d Wfn.W A A + WightmanInnerProduct d Wfn.W B B -
    WightmanInnerProduct d Wfn.W A B - WightmanInnerProduct d Wfn.W B A).re = 0
  rw [← WightmanInnerProduct_expand_diff d Wfn.W Wfn.linear A B, hNullSelf]
  simp

/-- Covariance identity at the SchwartzMap level:
    prependField(f, g·h) = g · prependField(g⁻¹·f, h)
    where g acts by precomposition with g⁻¹. -/
private theorem prependField_poincareAct_comm
    (g : PoincareGroup d) (f : SchwartzSpacetime d) {k : ℕ}
    (h : SchwartzNPoint d k) :
    SchwartzMap.prependField f (poincareActNPoint g h) =
    poincareActNPoint g (SchwartzMap.prependField (poincareActSchwartz g⁻¹ f) h) := by
  ext x
  simp only [SchwartzMap.prependField_apply, poincareActNPoint_apply,
             poincareActNPointDomain, poincareActSchwartz_apply, inv_inv]
  -- Goal: f (x 0) * h (...) = f (act g (act g⁻¹ (x 0))) * h (...)
  -- Second factors match; for first, g · g⁻¹ cancels
  congr 1
  congr 1
  rw [← PoincareGroup.act_mul g g⁻¹, mul_inv_cancel, PoincareGroup.act_one]

/-- Covariance at the Borchers sequence level (funcs-wise):
    (φ(f)(g·Y)).funcs n = (g · φ(g⁻¹·f)(Y)).funcs n -/
private theorem covariance_borchers_funcs (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (Y : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction f (poincareActBorchers g Y)).funcs n =
    (poincareActBorchers g (fieldOperatorAction (poincareActSchwartz g⁻¹ f) Y)).funcs n := by
  cases n with
  | zero =>
    simp only [fieldOperatorAction_funcs_zero, poincareActBorchers]
    exact (poincareActNPoint_zero g 0).symm
  | succ k =>
    simp only [fieldOperatorAction_funcs_succ, poincareActBorchers]
    exact prependField_poincareAct_comm g f (Y.funcs k)

/-- Covariance at the PreHilbertSpace level:
    φ(f)(U(g)y) = U(g)(φ(g⁻¹·f)(y)) -/
private theorem covariance_preHilbert (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (y : PreHilbertSpace Wfn) :
    fieldOperator Wfn f (poincareActPreHilbert Wfn g y) =
    poincareActPreHilbert Wfn g (fieldOperator Wfn (poincareActSchwartz g⁻¹ f) y) := by
  induction y using Quotient.inductionOn with | h Y =>
  exact mk_eq_of_funcs_eq Wfn _ _ (fun n => covariance_borchers_funcs g f Y n)

/-! ### Strong continuity of GNS translation subgroups

We prove that the GNS Poincaré representation has strongly continuous translation
subgroups. The proof proceeds in layers:
1. Translation continuity on Schwartz n-point functions (sorry: standard analysis)
2. Wightman inner product continuity under translation (finite sum of continuous terms)
3. Strong continuity on embedded pre-Hilbert vectors (norm-squared expansion)
4. Extension to the GNS completion (density + isometry argument)
-/

/-- Scalar real-translation orbits are continuous in the Schwartz topology. -/
private theorem continuous_translateSchwartz_smul {m : ℕ}
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    Continuous (fun t : ℝ => SCV.translateSchwartz (t • η) ψ) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let ψ₀ : SchwartzMap (Fin m → ℝ) ℂ := SCV.translateSchwartz (t₀ • η) ψ
  have hzero : ContinuousAt (fun t : ℝ => SCV.translateSchwartz (t • η) ψ₀) 0 := by
    simp only [ContinuousAt]
    rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
    intro p ε hε
    let D : SchwartzMap (Fin m → ℝ) ℂ := ∂_{η} ψ₀
    let pSem : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
      schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p
    have hquot := OSReconstruction.tendsto_diffQuotient_translateSchwartz_zero ψ₀ η
    rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _] at hquot
    specialize hquot p 1 zero_lt_one
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter] at hquot
    obtain ⟨s, hs_nhds, hs_prop⟩ := hquot
    let M : ℝ := pSem D
    have hM_nonneg : 0 ≤ M := apply_nonneg pSem D
    have hM_pos : 0 < M + 1 := by linarith
    let δ : ℝ := ε / (M + 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    refine Filter.mem_of_superset (Filter.inter_mem hs_nhds (Metric.ball_mem_nhds 0 hδ_pos)) ?_
    intro t ht
    rcases ht with ⟨hts, htball⟩
    simp only [Set.mem_setOf_eq]
    have htrans0 : SCV.translateSchwartz (0 : Fin m → ℝ) ψ₀ = ψ₀ := by
      ext x; simp [SCV.translateSchwartz_apply]
    rw [show (0 : ℝ) • η = (0 : Fin m → ℝ) from zero_smul ℝ η, htrans0]
    have ht_abs : |t| < δ := by
      simpa [Real.dist_eq, δ] using htball
    by_cases ht0 : t = 0
    · subst ht0
      simpa [zero_smul, htrans0] using hε
    · have htnz : t ∈ ({0}ᶜ : Set ℝ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
      have hq :
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) < 1 :=
        hs_prop ⟨hts, htnz⟩
      have hsplit :
          t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) =
            (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + D := by
        abel
      have hq' :
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) < 1 + M := by
        calc
          pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀))
              = pSem ((t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + D) := by
                  congr 1
          _ ≤ pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀) - D) + pSem D :=
                map_add_le_add _ _ _
          _ < 1 + M := by
                dsimp [M] at *
                linarith
      have hdecomp :
          SCV.translateSchwartz (t • η) ψ₀ - ψ₀ =
            t • (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) := by
        rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]
      calc
        pSem (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)
            = pSem (t • (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀))) :=
              congr_arg pSem hdecomp
        _ = |t| * pSem (t⁻¹ • (SCV.translateSchwartz (t • η) ψ₀ - ψ₀)) :=
              map_smul_eq_mul _ _ _
        _ < δ * (1 + M) := by
              gcongr
        _ = ε := by
              dsimp [δ]; field_simp [hM_pos.ne']; ring
  have hshift : ContinuousAt (fun t : ℝ => t - t₀) t₀ := by
    simpa using (continuous_id.sub continuous_const).continuousAt
  have hcomp :
      ContinuousAt (fun t : ℝ => SCV.translateSchwartz ((t - t₀) • η) ψ₀) t₀ := by
    simpa [Function.comp] using
      (ContinuousAt.comp_of_eq hzero hshift (by simp))
  have hEqfun :
      (fun t : ℝ => SCV.translateSchwartz (t • η) ψ) =
        (fun t : ℝ => SCV.translateSchwartz ((t - t₀) • η) ψ₀) := by
    funext t
    ext x
    simp only [ψ₀, SCV.translateSchwartz_apply, sub_eq_add_neg]
    congr 1; ext i; simp [Pi.smul_apply, Pi.add_apply]; ring
  rw [hEqfun]
  exact hcomp

-- Local flattening infrastructure (mirrors ForwardTubeDistributions, kept private to avoid import)
private def uncurryLinearEquivLocal (n' dd : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n' → Fin dd → 𝕜) ≃ₗ[𝕜] (Fin n' × Fin dd → 𝕜) :=
  { (Equiv.curry (Fin n') (Fin dd) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private def flattenLinearEquivLocal (n' dd : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n' → Fin dd → 𝕜) ≃ₗ[𝕜] (Fin (n' * dd) → 𝕜) :=
  (uncurryLinearEquivLocal n' dd 𝕜).trans (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

private def flattenCLEquivRealLocal (n' dd : ℕ) :
    (Fin n' → Fin dd → ℝ) ≃L[ℝ] (Fin (n' * dd) → ℝ) :=
  (flattenLinearEquivLocal n' dd ℝ).toContinuousLinearEquiv

@[simp] private theorem flattenCLEquivRealLocal_apply (n' dd : ℕ)
    (f : Fin n' → Fin dd → ℝ) (k : Fin (n' * dd)) :
    flattenCLEquivRealLocal n' dd f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

@[simp] private theorem flattenCLEquivRealLocal_symm_apply (n' dd : ℕ)
    (w : Fin (n' * dd) → ℝ) (i : Fin n') (j : Fin dd) :
    (flattenCLEquivRealLocal n' dd).symm w i j = w (finProdFinEquiv (i, j)) := rfl

/-- Local flattening of Schwartz n-point functions to ordinary real Schwartz space. -/
private abbrev flattenSchwartzNPointLocal {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivRealLocal n (d + 1)).symm

/-- Inverse local flattening of Schwartz n-point functions. -/
private abbrev unflattenSchwartzNPointLocal {n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivRealLocal n (d + 1))

@[simp] private theorem flattenSchwartzNPointLocal_apply {n : ℕ}
    (f : SchwartzNPoint d n) (u : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPointLocal (d := d) f u = f ((flattenCLEquivRealLocal n (d + 1)).symm u) := rfl

@[simp] private theorem unflattenSchwartzNPointLocal_apply {n : ℕ}
    (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (x : NPointDomain d n) :
    unflattenSchwartzNPointLocal (d := d) f x = f (flattenCLEquivRealLocal n (d + 1) x) := rfl

/-- Flattened translation direction corresponding to simultaneous translation of
all n spacetime arguments in the μ-th coordinate. -/
private abbrev flatTranslationDirection (μ : Fin (d + 1)) {n : ℕ} :
    Fin (n * (d + 1)) → ℝ :=
  fun k => if (finProdFinEquiv.symm k).2 = μ then (-1 : ℝ) else 0

/-- Unflattening after adding the flattened translation direction recovers the
expected simultaneous shift of all n spacetime arguments. -/
private theorem unflatten_add_flatTranslationDirection
    (μ : Fin (d + 1)) {n : ℕ} (u : Fin (n * (d + 1)) → ℝ) (t : ℝ) :
    (flattenCLEquivRealLocal n (d + 1)).symm (u + t • flatTranslationDirection (d := d) μ) =
      fun i => ((flattenCLEquivRealLocal n (d + 1)).symm u i) -
        t • PoincareRepresentation.basisVector d μ := by
  ext i ν
  by_cases hν : ν = μ
  · subst hν
    simp [flatTranslationDirection, PoincareRepresentation.basisVector, sub_eq_add_neg]
  · simp [flatTranslationDirection, PoincareRepresentation.basisVector, hν, sub_eq_add_neg]

/-- Translation in the μ-th spacetime direction becomes ordinary real translation
after flattening the n-point Schwartz function. -/
private theorem poincareActNPoint_translationInDirection_eq_unflatten_translate
    (μ : Fin (d + 1)) {n : ℕ} (t : ℝ) (f : SchwartzNPoint d n) :
    poincareActNPoint (PoincareRepresentation.translationInDirection d μ t) f =
      unflattenSchwartzNPointLocal (d := d)
        (SCV.translateSchwartz (t • flatTranslationDirection (d := d) (n := n) μ)
          (flattenSchwartzNPointLocal (d := d) f)) := by
  ext x
  simp only [PoincareRepresentation.translationInDirection, poincareActNPoint_apply,
    SCV.translateSchwartz_apply, unflatten_add_flatTranslationDirection,
    unflattenSchwartzNPointLocal_apply, flattenSchwartzNPointLocal_apply, sub_eq_add_neg]
  congr 1; funext i; ext ν
  simp [poincareActNPointDomain, PoincareGroup.act_def, PoincareGroup.inv_translation,
    PoincareGroup.inv_lorentz, PoincareGroup.translation'_translation,
    PoincareGroup.translation'_lorentz, inv_one, PoincareGroup.one_lorentz_val,
    Matrix.one_mulVec]

/-- Translation in direction μ is continuous in the Schwartz topology on n-point functions.
    This is a standard result: translation is a strongly continuous action on Schwartz space.
    Proof requires adapting the seminorm estimation from
    `SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport` to general Schwartz functions. -/
private theorem continuous_translate_npoint_schwartz
    (μ : Fin (d + 1)) {n : ℕ} (f : SchwartzNPoint d n) :
    Continuous (fun t : ℝ =>
      poincareActNPoint (PoincareRepresentation.translationInDirection d μ t) f) := by
  let ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ := flattenSchwartzNPointLocal (d := d) f
  have hflat :
      Continuous (fun t : ℝ =>
        SCV.translateSchwartz (t • flatTranslationDirection (d := d) (n := n) μ) ψ) :=
    continuous_translateSchwartz_smul
      (η := flatTranslationDirection (d := d) (n := n) μ) ψ
  simpa [ψ, poincareActNPoint_translationInDirection_eq_unflatten_translate] using
    (unflattenSchwartzNPointLocal (d := d) : _ →L[ℂ] SchwartzNPoint d n).continuous.comp hflat

/-- The Wightman inner product ⟨F, T(t·eμ)G⟩ is continuous in t.
    Each summand is a composition of Schwartz translation continuity,
    `conjTensorProduct_continuous_right`, and temperedness of W. -/
private theorem continuous_wip_translate
    (μ : Fin (d + 1)) (F G : BorchersSequence d) :
    Continuous (fun t : ℝ =>
      WightmanInnerProduct d Wfn.W F
        (poincareActBorchers
          (PoincareRepresentation.translationInDirection d μ t) G)) := by
  -- WightmanInnerProduct unfolds to a finite double sum over F.bound and G.bound.
  -- poincareActBorchers preserves the bound and applies poincareActNPoint to each component.
  show Continuous (fun t : ℝ =>
    ∑ n ∈ Finset.range (F.bound + 1),
      ∑ m ∈ Finset.range (G.bound + 1),
        Wfn.W (n + m) ((F.funcs n).conjTensorProduct
          (poincareActNPoint
            (PoincareRepresentation.translationInDirection d μ t) (G.funcs m))))
  apply continuous_finset_sum _ (fun n _ => ?_)
  apply continuous_finset_sum _ (fun m _ => ?_)
  exact (Wfn.tempered (n + m)).comp
    ((SchwartzMap.conjTensorProduct_continuous_right (F.funcs n)).comp
      (continuous_translate_npoint_schwartz μ (G.funcs m)))

/-- Bridge from GNS inner product to WightmanInnerProduct for translated pre-Hilbert vectors.
    Composes `poincareActGNS_coe` with `UniformSpace.Completion.inner_coe`. -/
private theorem inner_translate_eq_wip
    (μ : Fin (d + 1)) (pF pG : PreHilbertSpace Wfn) (t : ℝ) :
    @inner ℂ _ _
      (pF : GNSHilbertSpace Wfn)
      (poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d μ t)
        (pG : GNSHilbertSpace Wfn)) =
    @inner ℂ _ _ pF
      (poincareActPreHilbert Wfn
        (PoincareRepresentation.translationInDirection d μ t) pG) := by
  set g := PoincareRepresentation.translationInDirection d μ t
  rw [show poincareActGNS Wfn g (pG : GNSHilbertSpace Wfn) =
      ((poincareActPreHilbert Wfn g pG : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) from
      poincareActGNS_coe Wfn g pG,
    UniformSpace.Completion.inner_coe]

/-- Strong continuity on pre-Hilbert vectors: t ↦ U(t·eμ)x is continuous.
    Proof: ‖U(t)x - U(t₀)x‖² = 2 Re⟨x,x⟩ - 2 Re⟨x, U(t-t₀)x⟩ → 0 since
    the inner product under translation is continuous (continuous_wip_translate). -/
private theorem gns_stronglyContinuous_preHilbert
    (μ : Fin (d + 1)) (x : PreHilbertSpace Wfn) :
    Continuous (fun t : ℝ =>
      poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d μ t)
        (x : GNSHilbertSpace Wfn)) := by
  induction x using Quotient.inductionOn with | h F =>
  set pF : PreHilbertSpace Wfn := ⟦F⟧
  let trans : ℝ → PoincareGroup d := PoincareRepresentation.translationInDirection d μ
  have hzero : trans 0 = 1 := by
    ext <;> simp [trans, PoincareRepresentation.translationInDirection, PoincareGroup.translation']
  have hadd : ∀ s t : ℝ, trans (s + t) = trans s * trans t := by
    intro s t
    apply PoincareGroup.ext
    · ext ν
      simp [trans, PoincareRepresentation.translationInDirection, PoincareGroup.translation',
        PoincareGroup.mul_translation, PoincareGroup.one_lorentz_val, Matrix.one_mulVec, add_smul]
    · simp [trans, PoincareRepresentation.translationInDirection, PoincareGroup.translation',
        PoincareGroup.mul_lorentz]
  let hfun : ℝ → ℝ := fun s =>
    RCLike.re (@inner ℂ _ _
      (pF : GNSHilbertSpace Wfn)
      (poincareActGNS Wfn (trans s) (pF : GNSHilbertSpace Wfn)))
  have hinner_eq :
      (fun s : ℝ =>
        @inner ℂ _ _
          (pF : GNSHilbertSpace Wfn)
          (poincareActGNS Wfn (trans s) (pF : GNSHilbertSpace Wfn))) =
      (fun s : ℝ =>
        WightmanInnerProduct d Wfn.W F (poincareActBorchers (trans s) F)) := by
    funext s
    rw [inner_translate_eq_wip Wfn μ pF pF s]
    rfl
  have hfun_eq :
      hfun =
      (fun s : ℝ =>
        RCLike.re (WightmanInnerProduct d Wfn.W F (poincareActBorchers (trans s) F))) := by
    funext s
    exact congr_arg RCLike.re (congr_fun hinner_eq s)
  have hfun_cont : Continuous hfun := by
    rw [hfun_eq]
    exact Complex.continuous_re.comp (continuous_wip_translate Wfn μ F F)
  have hfun0 : hfun 0 = ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 := by
    show RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn)
      (poincareActGNS Wfn (trans 0) (pF : GNSHilbertSpace Wfn))) = _
    rw [hzero, show poincareActGNS Wfn 1 = ContinuousLinearMap.id ℂ _ from
      poincareActGNS_one Wfn, ContinuousLinearMap.id_apply]
    exact inner_self_eq_norm_sq _
  rw [continuous_iff_continuousAt]
  intro t₀
  have hshift_cont : ContinuousAt (fun t : ℝ => hfun (t - t₀)) t₀ := by
    exact hfun_cont.continuousAt.comp (continuous_id.sub continuous_const).continuousAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hshift_cont (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  set g_t := trans t
  set g_t₀ := trans t₀
  set g_dt := trans (t - t₀)
  set y : GNSHilbertSpace Wfn := poincareActGNS Wfn g_dt (pF : GNSHilbertSpace Wfn)
  have hclose : |hfun (t - t₀) - ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2| < ε ^ 2 / 2 := by
    have hclose' : dist (hfun (t - t₀)) (hfun 0) < ε ^ 2 / 2 := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hδ ht
    simpa [hfun0, Real.dist_eq] using hclose'
  have hgap :
      ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 -
        RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) y) < ε ^ 2 / 2 := by
    show ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 - hfun (t - t₀) < ε ^ 2 / 2
    linarith [abs_lt.mp hclose]
  have hexpand :
      ‖y - (pF : GNSHilbertSpace Wfn)‖ ^ 2 =
        ‖y‖ ^ 2 - 2 * RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) y) +
          ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 := by
    rw [@norm_sub_sq ℂ (GNSHilbertSpace Wfn) _ _ _]
    have hsym :
        RCLike.re (@inner ℂ _ _ y (pF : GNSHilbertSpace Wfn)) =
          RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) y) := by
      simpa using inner_re_symm (𝕜 := ℂ) y (pF : GNSHilbertSpace Wfn)
    linarith
  have hnsq : ‖y - (pF : GNSHilbertSpace Wfn)‖ ^ 2 < ε ^ 2 := by
    calc
      ‖y - (pF : GNSHilbertSpace Wfn)‖ ^ 2
          = ‖y‖ ^ 2 - 2 * RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) y) +
              ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 := hexpand
      _ ≤ 2 * (‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 -
          RCLike.re (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) y)) := by
          have hy_norm : ‖y‖ = ‖(pF : GNSHilbertSpace Wfn)‖ := by
            show ‖poincareActGNS Wfn g_dt (pF : GNSHilbertSpace Wfn)‖ = _
            exact poincareActGNS_norm Wfn g_dt _
          have hy_sq : ‖y‖ ^ 2 = ‖(pF : GNSHilbertSpace Wfn)‖ ^ 2 := by rw [hy_norm]
          linarith
      _ < 2 * (ε ^ 2 / 2) := by nlinarith
      _ = ε ^ 2 := by ring
  have hdist_eq :
      dist (poincareActGNS Wfn g_t (pF : GNSHilbertSpace Wfn))
        (poincareActGNS Wfn g_t₀ (pF : GNSHilbertSpace Wfn)) =
      ‖y - (pF : GNSHilbertSpace Wfn)‖ := by
    have hg_mul : g_t = g_t₀ * g_dt := by
      dsimp [g_t, g_t₀, g_dt]
      simpa [sub_eq_add_neg] using (hadd t₀ (t - t₀))
    rw [dist_eq_norm, hg_mul, poincareActGNS_mul Wfn g_t₀ g_dt, ContinuousLinearMap.comp_apply]
    rw [← (poincareActGNS Wfn g_t₀).map_sub, poincareActGNS_norm]
  have hroot : ‖y - (pF : GNSHilbertSpace Wfn)‖ < ε :=
    lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using hnsq)
  exact lt_of_eq_of_lt hdist_eq hroot

/-- Extension to GNS completion: strong continuity for all GNS vectors.
    Standard density + isometry argument following the pattern of
    `gns_cluster_completion`. -/
private theorem gns_stronglyContinuous_completion
    (μ : Fin (d + 1)) (x : GNSHilbertSpace Wfn) :
    Continuous (fun t : ℝ =>
      poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d μ t) x) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Approximate x by pre-Hilbert vector φ with ‖x - φ‖ < ε/3
  obtain ⟨φ, hφ⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show (0 : ℝ) < ε / 3 by linarith)
  -- Get δ from pre-Hilbert continuity for φ
  induction φ using Quotient.inductionOn with | h G =>
  set pG : PreHilbertSpace Wfn := ⟦G⟧
  have hcont := (gns_stronglyContinuous_preHilbert Wfn μ pG).continuousAt (x := t₀)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont (ε / 3) (by linarith)
  -- The same δ works for x
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  -- Isometry: poincareActGNS preserves distances (stated for arbitrary g)
  have hiso : ∀ (g : PoincareGroup d) (a b : GNSHilbertSpace Wfn),
      dist (poincareActGNS Wfn g a) (poincareActGNS Wfn g b) = dist a b := fun g a b => by
    rw [dist_eq_norm, ← (poincareActGNS Wfn g).map_sub, poincareActGNS_norm, dist_eq_norm]
  -- Abbreviate the group elements (not the linear maps, to keep rw matching)
  set g_t := PoincareRepresentation.translationInDirection d μ t
  set g_t₀ := PoincareRepresentation.translationInDirection d μ t₀
  calc dist (poincareActGNS Wfn g_t x) (poincareActGNS Wfn g_t₀ x)
      ≤ dist (poincareActGNS Wfn g_t x)
            (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn)) +
        dist (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn))
            (poincareActGNS Wfn g_t₀ (pG : GNSHilbertSpace Wfn)) +
        dist (poincareActGNS Wfn g_t₀ (pG : GNSHilbertSpace Wfn))
            (poincareActGNS Wfn g_t₀ x) := by
        linarith [dist_triangle (poincareActGNS Wfn g_t x)
                    (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn))
                    (poincareActGNS Wfn g_t₀ x),
                  dist_triangle (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn))
                    (poincareActGNS Wfn g_t₀ (pG : GNSHilbertSpace Wfn))
                    (poincareActGNS Wfn g_t₀ x)]
    _ = dist x (pG : GNSHilbertSpace Wfn) +
        dist (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn))
            (poincareActGNS Wfn g_t₀ (pG : GNSHilbertSpace Wfn)) +
        dist (pG : GNSHilbertSpace Wfn) x := by
        rw [hiso, hiso]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist x (pG : GNSHilbertSpace Wfn) < ε / 3 := hφ
        have h2 : dist (poincareActGNS Wfn g_t (pG : GNSHilbertSpace Wfn))
            (poincareActGNS Wfn g_t₀ (pG : GNSHilbertSpace Wfn)) < ε / 3 := hδ ht
        have h3 : dist (pG : GNSHilbertSpace Wfn) x < ε / 3 := by rw [dist_comm]; exact hφ
        linarith
    _ = ε := by ring

/-- Strong continuity of translation subgroups on the GNS Hilbert space. -/
theorem gns_translationStronglyContinuous :
    PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn) :=
  fun μ x => gns_stronglyContinuous_completion Wfn μ x

/-! ### Spectrum condition

The GNS Poincaré representation satisfies the Streater-Wightman spectral condition
(energy non-negativity P₀ ≥ 0 and mass-shell P₀² ≥ Σᵢ Pᵢ²).

**Proof strategy** (bypasses SNAG theorem):

1. Convert `Wfn.spectrum_condition` (forward tube analyticity) to
   `SpectralConditionDistribution` via the backward direction of
   `spectralConditionDistribution_iff_forwardTubeAnalyticity`.

2. `SpectralConditionDistribution` says: the Fourier transform of the reduced
   Wightman distribution (in difference variables) is supported in V̄₊ⁿ.

3. On the GNS Hilbert space, `⟪Ω_F, U(a) Ω_G⟫ = Σ_{n,m} W_{n+m}(f̄_n ⊗ τ_a g_m)`.
   In momentum space (via Fourier transform in the translation variable `a`),
   the momentum operators P_μ act as multiplication by p_μ, and the spectral
   content is supported in V̄₊.

4. Since p₀ ≥ 0 and p₀² ≥ |**p**|² pointwise on V̄₊, integrating against the
   positive spectral density gives `energy_nonneg` and `mass_shell`. -/

/-! ### Helper lemmas for remaining sorry's in gnsQFT

* `gns_spectrum_condition` — spectrum condition (via SpectralConditionDistribution)
* `gns_cyclicity` — Schwartz nuclear theorem (density of product test functions)
* `gns_vacuum_unique_of_poincare_invariant` — PROVED via cluster decomposition
-/

/-- The Wightman functions satisfy the distribution-level spectral condition:
    the Fourier transform of each reduced n-point function (in difference variables)
    is supported in the product forward momentum cone V̄₊ⁿ.

    Derived from `Wfn.spectrum_condition` (forward tube analyticity) via the
    backward direction of `spectralConditionDistribution_iff_forwardTubeAnalyticity`. -/
private lemma wfn_spectralConditionDistribution :
    SpectralConditionDistribution d Wfn.W :=
  (spectralConditionDistribution_iff_forwardTubeAnalyticity d
    Wfn.tempered Wfn.linear Wfn.translation_invariant).mpr
    Wfn.spectrum_condition

/-- **Stone spectral Fourier-Stieltjes representation** (Reed-Simon VIII.5):
    for a strongly continuous one-parameter unitary group `U(t)` with self-adjoint
    generator `A` and spectral measure `P`, the diagonal spectral measure is the
    Fourier-Stieltjes measure of the function `t ↦ ⟪ψ, U(t)ψ⟫`:

    `⟪ψ, U(t)ψ⟫ = ∫ exp(itλ) d(P.diagonalMeasure ψ)(λ)`

    This follows from the spectral theorem `U(t) = ∫ exp(itλ) dP(λ)` (operator integral
    in the strong operator topology), specialized to diagonal matrix elements via
    `operatorIntegral_inner_right`.

    **Ref:** Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem VIII.5-6;
    Hall, "Quantum Theory for Mathematicians", Theorem 10.12. -/
private lemma stone_spectral_representation
    (𝒰 : OneParameterUnitaryGroup (GNSHilbertSpace Wfn))
    (ψ : GNSHilbertSpace Wfn) (t : ℝ) :
    let P := 𝒰.generator.spectralMeasure 𝒰.generator_densely_defined 𝒰.generator_selfadjoint
    @inner ℂ _ _ ψ (𝒰.U t ψ) = ∫ s : ℝ,
      Complex.exp (Complex.I * ↑t * ↑s) ∂(P.diagonalMeasure ψ) := by
  intro P
  -- Prove integrability and boundedness independently (the private lemmas
  -- expI_integrable/expI_norm_le from SpectralPowers aren't accessible here)
  have hf_norm : ∀ (x : ℝ), ‖Complex.exp (Complex.I * ↑t * ↑x)‖ ≤ 1 := fun x => by
    rw [Complex.norm_exp]
    have : (Complex.I * ↑t * ↑x).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [this, Real.exp_zero]
  set f : ℝ → ℂ := fun x => Complex.exp (Complex.I * ↑t * ↑x) with hf_def
  have hf_bdd : ∃ M, (0 : ℝ) ≤ M ∧ ∀ (s : ℝ), ‖f s‖ ≤ M :=
    ⟨1, zero_le_one, hf_norm⟩
  have hf_int : ∀ z : GNSHilbertSpace Wfn,
      MeasureTheory.Integrable f (P.diagonalMeasure z) := by
    intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.aestronglyMeasurable)
      (by filter_upwards with x; simp only [norm_one]; exact hf_norm x)
  -- Stone's theorem + unitaryGroup definition give U(t) = functionalCalculus P exp(it·)
  suffices h : 𝒰.U t = functionalCalculus P f hf_int hf_bdd by
    rw [h]
    exact functionalCalculus_inner_self P f hf_int hf_bdd ψ
  -- unique_from_generator gives U(t) = unitaryGroup(...), which unfolds to
  -- functionalCalculus P f _ _; proof irrelevance closes the gap
  rw [𝒰.unique_from_generator 𝒰.generator
    𝒰.generator_densely_defined 𝒰.generator_selfadjoint rfl t]
  rfl

/-- **Uniqueness of the Fourier-Stieltjes representation** (1-dimensional).

    Two finite positive Borel measures on `ℝ` with the same Fourier-Stieltjes
    transform are equal.  This is the uniqueness half of Bochner's theorem.

    **Ref:** Rudin, *Fourier Analysis on Groups*, Theorem 1.3.6;
    Reed-Simon I, Theorem IX.9; Folland, *A Course in Abstract Harmonic
    Analysis*, Theorem 4.23. -/
theorem bochner_uniqueness (μ₁ μ₂ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ₁] [MeasureTheory.IsFiniteMeasure μ₂]
    (h : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂μ₁ =
                    ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂μ₂) :
    μ₁ = μ₂ := by
  sorry

/-- A function `φ : ℝⁿ → ℂ` is positive-definite if for all finite collections of
    points and complex coefficients, the Hermitian quadratic form is non-negative. -/
def IsPositiveDefiniteFunction {n : ℕ} (φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (x : Fin m → (Fin n → ℝ)),
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, starRingEnd ℂ (c i) * c j * φ (x j - x i)).re

/-- **Bochner's theorem** (multi-dimensional). Every continuous positive-definite
    function on `ℝⁿ` is the Fourier-Stieltjes transform of a unique finite positive
    Borel measure.

    **Ref:** Reed-Simon I, Theorem IX.9; Rudin, *Fourier Analysis on Groups*, §1.4.3. -/
theorem bochner_theorem {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (hcont : Continuous φ)
    (hpd : IsPositiveDefiniteFunction φ) :
    ∃ (μ : MeasureTheory.Measure (Fin n → ℝ)),
      MeasureTheory.IsFiniteMeasure μ ∧
      ∀ x, φ x = ∫ p, Complex.exp (↑(∑ i : Fin n, x i * p i) * Complex.I) ∂μ := by
  sorry

/-! ### Distribution-to-measure bridge lemmas

The following four lemmas bridge between the distributional spectral condition
(`SpectralConditionDistribution`) and the measure-level support condition
`μ((-∞, 0)) = 0` needed for the GNS spectrum condition.

The logical chain is:

1. **`scd_inner_hasOneSidedFourierSupport`** (Steps 1+2):
   SCD + `inner_translate_eq_wip` → the tempered distribution
   `T_F(ψ) = ∫ ⟪F, U₀(t)F⟫ · ψ(t) dt` has one-sided Fourier support in `[0,∞)`.

2. **`bochner_fourier_fubini`** (Theorem A):
   Fubini for the Bochner–Stieltjes representation: if `φ(t) = ∫ exp(its) dμ(s)`,
   the double integral `∫∫ exp(its) · g(t) dt dμ(s)` can be computed in either order.

3. **`oneSidedSupport_implies_schwartz_vanishing`** (combining Theorem A + Fourier inversion):
   If the Fourier–Stieltjes transform of μ has one-sided Fourier support,
   then `∫ ψ dμ = 0` for every Schwartz ψ supported in `(-∞, 0)`.

4. **`measure_Iio_zero_of_schwartz_vanishing`** (Theorem B):
   If `∫ ψ dμ = 0` for all Schwartz ψ with `supp(ψ) ⊆ (-∞, 0)`,
   then `μ((-∞, 0)) = 0`.
-/

/-- **Step 1+2: SCD → one-sided Fourier support of the GNS inner product function.**

    The tempered distribution `T_F(ψ) = ∫ ⟪F, U₀(t)F⟫ · ψ(t) dt` has
    one-sided Fourier support in `[0,∞)`, i.e., `T_F(ℱ[φ]) = 0` for every
    Schwartz φ with `supp(φ) ⊆ (-∞, 0)`.

    **Proof sketch:**
    1. By `inner_translate_eq_wip`, lift to the pre-Hilbert space and choose
       a Borchers representative `B` of `F`. Then
       `⟪F, U₀(t)F⟫ = ∑_{n,m} W_{n+m}(f*_n ⊗ τ_{te₀} f_m)`.
    2. By `SpectralConditionDistribution`, each summand `W_{n+m}` factors through
       the reduced distribution `w` in difference variables, whose Fourier
       transform is supported in `V̄₊^{n+m-1}`.
    3. Time-translation `τ_{te₀}` acts on the last difference variable by
       adding `te₀`, so the 1D Fourier transform in `t` of each summand
       is a marginal of `ŵ` restricted to the energy component `p₀ ≥ 0`.
    4. Summing over `n, m` preserves the support condition.

    **Ref:** Streater-Wightman, §3-1; Reed-Simon II, Theorem X.40. -/
private lemma scd_inner_hasOneSidedFourierSupport
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (F : PreHilbertSpace Wfn) :
    let 𝒰₀ := (gnsPoincareRep Wfn).translationGroup 0 (hsc 0)
    SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ, @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
        (𝒰₀.U t (F : GNSHilbertSpace Wfn)) * (ψ : ℝ → ℂ) t) := by
  sorry

set_option maxHeartbeats 800000 in
/-- **Theorem A (Fubini for Bochner–Stieltjes integrals).**

    For a finite positive Borel measure `μ` on `ℝ` and a Schwartz function `g`,
    the double integral can be computed in either order:

    `∫_t (∫_s exp(its) dμ(s)) · g(t) dt = ∫_s (∫_t exp(its) · g(t) dt) dμ(s)`

    This follows from Fubini's theorem, using the fact that `|exp(its)| = 1`
    and `g` is Schwartz (hence integrable), so the product is integrable
    over the product measure `μ ⊗ Lebesgue`.

    **Ref:** Folland, *Real Analysis*, Theorem 2.37;
    Reed-Simon I, Theorem IX.9 (proof of Bochner's theorem). -/
theorem bochner_fourier_fubini
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (g : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, (∫ s : ℝ, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) * (g : ℝ → ℂ) t =
    ∫ s : ℝ, (∫ t : ℝ, Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t) ∂μ := by
  -- ‖exp(I·t·s)‖ = 1 for all real t, s
  have h_exp_norm : ∀ t s : ℝ,
      ‖Complex.exp (Complex.I * ↑t * ↑s)‖ = 1 := fun t s => by
    rw [show Complex.I * (t : ℂ) * (s : ℂ) = ↑(t * s) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  -- Step 1: Pull g(t) inside the s-integral via integral_mul_const
  have h_pull : ∀ t : ℝ,
      (∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) * (g : ℝ → ℂ) t =
      ∫ s, Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t ∂μ :=
    fun t => (MeasureTheory.integral_mul_const ((g : ℝ → ℂ) t)
      (fun s : ℝ => Complex.exp (Complex.I * ↑t * ↑s))).symm
  simp_rw [h_pull]
  -- Step 2: Apply Fubini's theorem (integral_integral_swap)
  apply MeasureTheory.integral_integral_swap
  -- Step 3: Integrability of (t,s) ↦ exp(I·t·s)·g(t) on volume × μ.
  show MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * ↑p.1 * ↑p.2) * (g : ℝ → ℂ) p.1)
      (MeasureTheory.volume.prod μ)
  have hF_asm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * ↑p.1 * ↑p.2) * (g : ℝ → ℂ) p.1)
      (MeasureTheory.volume.prod μ) :=
    ((Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp continuous_snd))).mul
      (g.continuous.comp continuous_fst)).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hF_asm]
  refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
  · -- For fixed t: s ↦ exp(I·t·s)·g(t) is bounded by ‖g(t)‖ on finite measure μ
    show MeasureTheory.Integrable
      (fun (s : ℝ) => Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t) μ
    exact MeasureTheory.Integrable.of_bound
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
        continuous_const).aestronglyMeasurable
      (‖(g : ℝ → ℂ) t‖)
      (Filter.Eventually.of_forall fun s => by
        rw [norm_mul, h_exp_norm, one_mul])
  · -- The norm integral ∫ ‖F(t,·)‖ ∂μ = μ(ℝ) * ‖g(t)‖ is integrable in t
    have h_inner : (fun t => ∫ s, ‖Complex.exp (Complex.I * ↑t * ↑s) *
        (g : ℝ → ℂ) t‖ ∂μ) = (fun t => (μ Set.univ).toReal * ‖(g : ℝ → ℂ) t‖) := by
      ext t; simp only [norm_mul, h_exp_norm, one_mul, MeasureTheory.integral_const,
        smul_eq_mul]; rfl
    rw [h_inner]; exact g.integrable.norm.const_mul _

/-- **Theorem A + Fourier inversion: one-sided Fourier support of the FS transform
    implies vanishing of Schwartz integrals against the measure.**

    If `μ` is a finite positive Borel measure on `ℝ` whose Fourier-Stieltjes
    transform `φ(t) = ∫ exp(its) dμ(s)` has one-sided Fourier support
    (i.e., the tempered distribution `T(ψ) = ∫ φ(t) ψ(t) dt` satisfies
    `SCV.HasOneSidedFourierSupport T`), then `∫ ψ dμ = 0` for every Schwartz
    `ψ` with `supp(ψ) ⊆ (-∞, 0)`.

    **Proof sketch:**
    1. By `SCV.HasOneSidedFourierSupport`, for any Schwartz `χ` with
       `supp(χ) ⊆ (-∞, 0)`: `∫ φ(t) · ℱ[χ](t) dt = 0`.
    2. By `bochner_fourier_fubini`, `∫ φ(t) · ℱ[χ](t) dt = ∫ G(s) dμ(s)`
       where `G(s) = ∫ exp(its) · ℱ[χ](t) dt`.
    3. By Fourier inversion, `G(s) = c · χ(s/(2π))` (up to normalization).
       Since `supp(χ) ⊆ (-∞, 0)` iff `supp(χ(·/(2π))) ⊆ (-∞, 0)`,
       rescaling shows `∫ ψ dμ = 0` for all Schwartz `ψ` supported in `(-∞, 0)`.

    **Ref:** Rudin, *Fourier Analysis on Groups*, §1.3;
    Hörmander, *Analysis of PDE I*, Theorem 7.1.10. -/
theorem oneSidedSupport_implies_schwartz_vanishing
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (hsupp : SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ, (∫ s : ℝ, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) * (ψ : ℝ → ℂ) t))
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∀ x ∈ Function.support (ψ : ℝ → ℂ), x < 0) :
    ∫ s : ℝ, (ψ : ℝ → ℂ) s ∂μ = 0 := by
  sorry

/-- **Theorem B: Schwartz test vanishing on an open set implies measure vanishing.**

    If `μ` is a finite positive Borel measure on `ℝ` and `∫ ψ dμ = 0` for
    every Schwartz function `ψ` with `supp(ψ) ⊆ (-∞, 0)`, then `μ((-∞, 0)) = 0`.

    **Proof sketch:** By inner regularity, it suffices to show `μ(K) = 0`
    for every compact `K ⊆ (-∞, 0)`. For any such `K`, construct a
    non-negative Schwartz bump `ψ ≥ 0` with `ψ|_K ≥ 1` and
    `supp(ψ) ⊆ (-∞, 0)`. Then `0 ≤ μ(K) ≤ ∫ ψ dμ = 0`.

    The existence of such bumps follows from the density of Schwartz functions
    in `C_c^∞((-∞, 0))` and the existence of compactly supported smooth
    functions dominating indicators of compact sets.

    **Ref:** Rudin, *Real and Complex Analysis*, Theorem 2.18;
    Hörmander, *Analysis of PDE I*, Proposition 1.4.1. -/
theorem measure_Iio_zero_of_schwartz_vanishing
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (h : ∀ (ψ : SchwartzMap ℝ ℂ),
      (∀ x ∈ Function.support (ψ : ℝ → ℂ), x < 0) →
      ∫ s : ℝ, (ψ : ℝ → ℂ) s ∂μ = 0) :
    μ (Set.Iio 0) = 0 := by
  sorry

/-- **SpectralConditionDistribution → diagonal spectral measure of P₀ supported on [0,∞)
    for pre-Hilbert vectors.**

    For `F : PreHilbertSpace Wfn`, `μ_F((-∞, 0)) = 0` where `μ_F` is the
    diagonal spectral measure of the energy operator `P₀` at the embedded vector `↑F`.

    **Proof sketch** (uses `stone_spectral_representation` + distribution theory):
    1. By `inner_translate_eq_wip`, `t ↦ ⟪↑F, U₀(t)(↑F)⟫ = WightmanInnerProduct(F, T(te₀)F)`,
       a finite sum of Wightman evaluations `Σ_{n,m} W_{n+m}(f*_n ⊗ τ_{te₀} f_m)`.
    2. By `SpectralConditionDistribution`, each summand's distributional Fourier transform
       in `t` has support in `{p₀ ≥ 0}` (the energy projection of V̄₊).
    3. By `stone_spectral_representation`, `⟪↑F, U₀(t)(↑F)⟫ = ∫ e^{itλ} dμ_F(λ)`.
    4. By uniqueness of Fourier-Stieltjes representations for finite positive measures
       (Bochner's theorem), combining (2) and (3) gives `μ_F((-∞, 0)) = 0`. -/
private lemma spectralCondition_diagonalMeasure_nonneg_dense
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (F : PreHilbertSpace Wfn) :
    let P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
    let hT := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
    let hsa := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
    (P₀.spectralMeasure hT hsa).diagonalMeasure (F : GNSHilbertSpace Wfn) (Set.Iio 0) = 0 := by
  intro P₀ hT hsa
  set P := P₀.spectralMeasure hT hsa
  set μ_F := P.diagonalMeasure (F : GNSHilbertSpace Wfn)
  -- Step 1: Stone spectral representation.
  -- P₀ = 𝒰₀.generator where 𝒰₀ is the time-translation one-parameter group,
  -- so stone_spectral_representation gives ⟪F, U₀(t)F⟫ = ∫ e^{itλ} dμ_F(λ).
  set 𝒰₀ := (gnsPoincareRep Wfn).translationGroup 0 (hsc 0)
  have h_stone : ∀ t : ℝ, @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
      (𝒰₀.U t (F : GNSHilbertSpace Wfn)) =
      ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂μ_F :=
    fun t => stone_spectral_representation Wfn 𝒰₀ (F : GNSHilbertSpace Wfn) t
  -- Step 2: The distributional spectral condition gives a measure supported on [0,∞).
  -- By `inner_translate_eq_wip`, the function t ↦ ⟪F, U₀(t)F⟫ is a finite sum of
  -- Wightman evaluations Σ_{n,m} W_{n+m}(f*_n ⊗ τ_{te₀} f_m).  By hSCD, each
  -- summand's distributional Fourier transform in t has support in {p₀ ≥ 0}.
  -- Bochner existence then gives a measure ν supported on [0,∞) representing
  -- the same characteristic function.
  have ⟨ν, hν_fin, hν_supp, hν_fs⟩ : ∃ (ν : MeasureTheory.Measure ℝ),
      MeasureTheory.IsFiniteMeasure ν ∧
      ν (Set.Iio 0) = 0 ∧
      ∀ t : ℝ, ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂ν =
               ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂μ_F := by
    -- Lift φ(t) = ⟪F, U₀(t)F⟫ to a function on Fin 1 → ℝ for bochner_theorem.
    let φ₁ : (Fin 1 → ℝ) → ℂ := fun x =>
      @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
        (𝒰₀.U (x 0) (F : GNSHilbertSpace Wfn))
    -- Continuity: ⟪const, U₀(·)F⟫ is continuous by strong continuity of U₀.
    have hcont₁ : Continuous φ₁ :=
      Continuous.inner (𝕜 := ℂ) continuous_const
        ((gns_stronglyContinuous_preHilbert Wfn 0 F).comp (continuous_apply 0))
    -- Positive-definiteness: ∑ c̄ᵢcⱼ⟪F, U₀(xⱼ₀-xᵢ₀)F⟫ = ‖∑ cᵢ U₀(xᵢ₀)F‖² ≥ 0
    have hpd₁ : IsPositiveDefiniteFunction φ₁ := by
      intro m c x
      -- Key: φ₁(xⱼ - xᵢ) = ⟪𝒰₀.U(xᵢ 0) F, 𝒰₀.U(xⱼ 0) F⟫
      -- Uses: U(s-t) = U(-t)∘U(s) = U(t)†∘U(s), then adjoint_inner_right
      have hφ₁_inner : ∀ i j : Fin m,
          φ₁ (x j - x i) = @inner ℂ _ _
            (𝒰₀.U (x i 0) (F : GNSHilbertSpace Wfn))
            (𝒰₀.U (x j 0) (F : GNSHilbertSpace Wfn)) := by
        intro i j
        show @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
            (𝒰₀.U ((x j - x i) 0) (F : GNSHilbertSpace Wfn)) = _
        simp only [Pi.sub_apply]
        rw [show x j 0 - x i 0 = -(x i 0) + x j 0 from by ring, 𝒰₀.add]
        simp only [ContinuousLinearMap.comp_apply]
        rw [𝒰₀.neg, ContinuousLinearMap.adjoint_inner_right]
      set y : Fin m → GNSHilbertSpace Wfn :=
        fun i => 𝒰₀.U (x i 0) (F : GNSHilbertSpace Wfn)
      simp_rw [hφ₁_inner]
      set v := ∑ i : Fin m, c i • y i
      suffices h : (∑ i : Fin m, ∑ j : Fin m,
          starRingEnd ℂ (c i) * c j * @inner ℂ _ _ (y i) (y j)) =
          @inner ℂ _ _ v v by
        rw [h]; exact inner_self_nonneg (𝕜 := ℂ)
      symm; simp only [v]
      rw [sum_inner (𝕜 := ℂ)]
      simp_rw [_root_.inner_smul_left, inner_sum (𝕜 := ℂ), _root_.inner_smul_right]
      congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j; ring
    -- Bochner's theorem gives a representing measure μ₁ on Fin 1 → ℝ.
    obtain ⟨μ₁, hfin₁, hrepr₁⟩ := bochner_theorem φ₁ hcont₁ hpd₁
    haveI : MeasureTheory.IsFiniteMeasure μ₁ := hfin₁
    -- Push forward μ₁ to a measure on ℝ via evaluation at 0.
    refine ⟨μ₁.map (fun f : Fin 1 → ℝ => f 0), ?_, ?_, ?_⟩
    -- IsFiniteMeasure
    · exact ⟨by rw [MeasureTheory.Measure.map_apply (measurable_pi_apply 0)
        MeasurableSet.univ, Set.preimage_univ]; exact MeasureTheory.measure_lt_top μ₁ _⟩
    -- ν(Iio 0) = 0: by SCD + inner_translate_eq_wip, the distributional Fourier
    -- transform of t ↦ ⟪F, U₀(t)F⟫ is supported on [0,∞). The Bochner measure
    -- (= the distributional FT as a positive measure) is supported on [0,∞).
    · -- Step A: Establish ν as a finite measure and compute its FS transform.
      set ν := μ₁.map (fun f : Fin 1 → ℝ => f 0) with hν_def
      haveI : MeasureTheory.IsFiniteMeasure ν :=
        ⟨by rw [hν_def, MeasureTheory.Measure.map_apply (measurable_pi_apply 0)
          MeasurableSet.univ, Set.preimage_univ]; exact MeasureTheory.measure_lt_top μ₁ _⟩
      -- The FS transform of ν equals the inner product function.
      -- From hrepr₁: φ₁(x) = ∫ exp(i⟨x,p⟩) dμ₁(p), specialising to x = (fun _ => t):
      -- φ(t) = ⟪F, U₀(t)F⟫ = ∫ exp(its) dν(s).
      have hν_fs : ∀ t : ℝ, ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂ν =
          @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
            (𝒰₀.U t (F : GNSHilbertSpace Wfn)) := by
        intro t
        rw [hν_def, MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable]
        have hconv : (fun f : Fin 1 → ℝ =>
              Complex.exp (Complex.I * ↑t * ↑(f 0))) =
            (fun f => Complex.exp
              (↑(∑ i : Fin 1, (fun _ : Fin 1 => t) i * f i) * Complex.I)) := by
          ext f; congr 1; simp; ring
        rw [hconv, ← hrepr₁]
      -- Step B: SCD gives one-sided Fourier support for the inner product function.
      have h_ofs := scd_inner_hasOneSidedFourierSupport Wfn hSCD hsc F
      -- Step C: Transfer one-sided Fourier support to the FS transform of ν.
      -- Since ∫ exp(its) dν = ⟪F, U₀(t)F⟫, the distribution
      -- T(ψ) = ∫ (∫ exp(its) dν) · ψ(t) dt has one-sided Fourier support.
      have h_ofs_ν : SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
          ∫ t : ℝ, (∫ s : ℝ, Complex.exp (Complex.I * ↑t * ↑s) ∂ν) *
            (ψ : ℝ → ℂ) t) := by
        intro ψ hψ
        simp_rw [hν_fs]
        exact h_ofs ψ hψ
      -- Step D: By Theorem A + Fourier inversion, Schwartz integrals against ν vanish
      -- on (-∞, 0).  By Theorem B, ν((-∞, 0)) = 0.
      exact measure_Iio_zero_of_schwartz_vanishing ν (fun ψ hψ =>
        oneSidedSupport_implies_schwartz_vanishing ν h_ofs_ν ψ hψ)
    -- ∀ t, ∫ exp(I*t*s) dν = ∫ exp(I*t*s) dμ_F
    · intro t
      rw [MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable]
      -- Convention conversion: exp(I * t * (f 0)) = exp(↑(∑ i : Fin 1, t * f i) * I)
      have hconv : (fun f : Fin 1 → ℝ =>
            Complex.exp (Complex.I * ↑t * ↑(f 0))) =
          (fun f => Complex.exp
            (↑(∑ i : Fin 1, (fun _ : Fin 1 => t) i * f i) * Complex.I)) := by
        ext f; congr 1; simp; ring
      rw [hconv, ← hrepr₁]
      -- φ₁(fun _ => t) = ⟪F, U₀(t)F⟫ = ∫ exp(I*t*s) dμ_F
      exact h_stone t
  -- Step 3: By Bochner uniqueness, ν = μ_F.
  haveI : MeasureTheory.IsFiniteMeasure ν := hν_fin
  haveI : MeasureTheory.IsFiniteMeasure μ_F := P.diagonalMeasure_isFiniteMeasure _
  have h_eq := bochner_uniqueness ν μ_F hν_fs
  -- Step 4: Transfer the support condition.
  rw [← h_eq]; exact hν_supp

/-- The spectral projection onto negative energies is zero on dense GNS vectors.

    For `F : PreHilbertSpace Wfn` (a Borchers sequence modulo null vectors),
    the spectral projection `P((-∞, 0))` kills the embedded vector `↑F`.

    **Proof:** By `spectralCondition_diagonalMeasure_nonneg_dense`,
    `P.diagonalMeasure (↑F) ((-∞, 0)) = 0`. Then `diagonalMeasure_apply_norm_sq`
    gives `‖P.proj ((-∞,0))(↑F)‖² = 0`, hence the projection is zero. -/
private lemma gns_negative_energy_proj_dense_zero
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (F : PreHilbertSpace Wfn) :
    let P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
    let hT := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
    let hsa := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
    (P₀.spectralMeasure hT hsa).proj (Set.Iio 0)
      (F : GNSHilbertSpace Wfn) = 0 := by
  intro P₀ hT hsa
  set P := P₀.spectralMeasure hT hsa
  -- Step 1: Diagonal spectral measure has no mass on (-∞, 0)
  have h_diag : P.diagonalMeasure (F : GNSHilbertSpace Wfn) (Set.Iio 0) = 0 :=
    spectralCondition_diagonalMeasure_nonneg_dense Wfn hSCD hsc F
  -- Step 2: Convert diagonal measure = 0 to ‖proj‖² = 0
  have h_sq := P.diagonalMeasure_apply_norm_sq
    (F : GNSHilbertSpace Wfn) (Set.Iio 0) measurableSet_Iio
  rw [h_diag, ENNReal.toReal_zero] at h_sq
  -- h_sq : 0 = ‖P.proj (Set.Iio 0) (↑F)‖ ^ 2
  -- Step 3: ‖v‖² = 0 → ‖v‖ = 0 → v = 0
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h_sq.symm)

/-- The spectral projection onto negative energies is zero on the full GNS space.

    Proved by extending the dense-vector result via continuity: the projection
    `P((-∞, 0))` is a bounded operator, and the set `{ψ | P((-∞,0))ψ = 0}` is closed.
    Since it contains the dense image of `PreHilbertSpace`, it equals the whole space. -/
private lemma gns_negative_energy_projection_zero
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn)) :
    let P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
    let hT := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
    let hsa := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
    (P₀.spectralMeasure hT hsa).proj (Set.Iio 0) = 0 := by
  intro P₀ hT hsa
  set P := P₀.spectralMeasure hT hsa
  apply ContinuousLinearMap.ext
  intro ψ
  simp only [ContinuousLinearMap.zero_apply]
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · exact isClosed_eq (P.proj (Set.Iio 0)).continuous continuous_const
  · exact fun F => gns_negative_energy_proj_dense_zero Wfn hSCD hsc F

/-- The diagonal spectral measure of P₀ for any vector on the GNS Hilbert space
    is supported on `[0, ∞)`.

    Derived from `gns_negative_energy_projection_zero`: since the spectral projection
    `P((-∞, 0)) = 0`, we have `‖P((-∞,0))ψ‖ = 0` for all `ψ`, hence
    `μ_ψ((-∞,0)) = ‖P((-∞,0))ψ‖² = 0` by `diagonalMeasure_apply_norm_sq`. -/
private lemma gns_energy_spectral_support_nonneg
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (ψ : GNSHilbertSpace Wfn) :
    let P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
    let hT := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
    let hsa := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
    (P₀.spectralMeasure hT hsa).diagonalMeasure ψ (Set.Iio 0) = 0 := by
  intro P₀ hT hsa
  set P := P₀.spectralMeasure hT hsa
  have hproj : P.proj (Set.Iio 0) = 0 :=
    gns_negative_energy_projection_zero Wfn hSCD hsc
  have hpsi : P.proj (Set.Iio 0) ψ = 0 := by
    simp [hproj]
  have htoReal : (P.diagonalMeasure ψ (Set.Iio 0)).toReal = 0 := by
    rw [P.diagonalMeasure_apply_norm_sq ψ (Set.Iio 0) measurableSet_Iio, hpsi, norm_zero]
    norm_num
  haveI := P.diagonalMeasure_isFiniteMeasure ψ
  exact ((ENNReal.toReal_eq_zero_iff _).mp htoReal).resolve_right
    (MeasureTheory.measure_ne_top _ _)

/-- **Energy non-negativity** from the distribution-level spectral condition.

    For ψ ∈ dom(P₀) on the GNS Hilbert space, `⟪ψ, P₀ψ⟫.re ≥ 0`.

    **Proof:** By `gns_energy_spectral_support_nonneg`, the spectral measure of P₀
    is supported on [0, ∞). The spectral truncation T_n = ∫ λ·χ_{[-n,n]} dP
    satisfies ⟪ψ, T_n ψ⟫ = ∫ λ·χ_{[-n,n]} dμ_ψ. Since μ_ψ is on [0, ∞),
    the integrand is ≥ 0 a.e., so re⟪ψ, T_n ψ⟫ ≥ 0. By
    `inner_apply_tendsto_spectral_integral`, ⟪ψ, T_n ψ⟫ → ⟪ψ, P₀ψ⟫,
    so the limit is also ≥ 0. -/
private lemma gns_energy_nonneg
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (ψ : GNSHilbertSpace Wfn)
    (hψ : ψ ∈ ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)).domain) :
    (⟪ψ, ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)) ⟨ψ, hψ⟩⟫_ℂ).re ≥ 0 := by
  set P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
  have hT := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
  have hsa := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
  -- ⟪ψ, T_n ψ⟫ → ⟪ψ, P₀ψ⟫ by spectral truncation convergence
  have hlim := inner_apply_tendsto_spectral_integral P₀ hT hsa ⟨ψ, hψ⟩ ψ
  -- Taking real parts (continuous)
  have hlim_re : Filter.Tendsto
      (fun n => (⟪ψ, spectralTruncation P₀ hT hsa n ψ⟫_ℂ).re)
      Filter.atTop (nhds (⟪ψ, P₀ ⟨ψ, hψ⟩⟫_ℂ).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hlim
  -- Each truncated inner product has non-negative real part.
  -- T_n = functionalCalculus(f_n) where f_n(s) = s·χ_{[-n,n]}(s).
  -- ⟪ψ, T_n ψ⟫ = ∫ f_n dμ_ψ by functionalCalculus_inner_self.
  -- Since μ_ψ((-∞,0)) = 0, the integrand is ≥ 0 a.e., giving re ≥ 0.
  have h_trunc_nonneg : ∀ n : ℕ,
      0 ≤ (⟪ψ, spectralTruncation P₀ hT hsa n ψ⟫_ℂ).re := by
    intro n
    set P := P₀.spectralMeasure hT hsa
    -- Define f_n matching spectralTruncation definition
    let f_n : ℝ → ℂ := fun s =>
      (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
    have hf_norm : ∀ s : ℝ, ‖f_n s‖ ≤ n := by
      intro s; simp only [f_n, Set.indicator_apply]
      split_ifs with hs
      · simp only [mul_one, Complex.norm_real]; exact abs_le.mpr (Set.mem_Icc.mp hs)
      · simp
    have hf_meas : Measurable f_n :=
      (Complex.continuous_ofReal.measurable).mul
        (measurable_const.indicator measurableSet_Icc)
    have hf_int : ∀ z : GNSHilbertSpace Wfn,
        MeasureTheory.Integrable f_n (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const ((n : ℂ))).mono
        hf_meas.aestronglyMeasurable
        (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hf_norm s)
    have hf_bdd : ∃ C, 0 ≤ C ∧ ∀ s, ‖f_n s‖ ≤ C := ⟨n, Nat.cast_nonneg n, hf_norm⟩
    -- ⟪ψ, T_n ψ⟫ = ∫ f_n dμ_ψ
    have h_eq : ⟪ψ, spectralTruncation P₀ hT hsa n ψ⟫_ℂ =
        ∫ s, f_n s ∂(P.diagonalMeasure ψ) := by
      rw [show spectralTruncation P₀ hT hsa n =
        functionalCalculus P f_n hf_int hf_bdd from rfl]
      exact functionalCalculus_inner_self P f_n hf_int hf_bdd ψ
    rw [h_eq]
    -- re(∫ f dμ) = ∫ re(f) dμ ≥ 0 since re(f(s)) ≥ 0 a.e.
    show 0 ≤ RCLike.re (∫ s, f_n s ∂P.diagonalMeasure ψ)
    rw [(integral_re (hf_int ψ)).symm]
    apply MeasureTheory.integral_nonneg_of_ae
    -- μ_ψ supported on [0, ∞), so s ≥ 0 a.e.
    have h_supp : P.diagonalMeasure ψ (Set.Iio 0) = 0 :=
      gns_energy_spectral_support_nonneg Wfn hSCD hsc ψ
    have h_ae_nonneg : ∀ᵐ s ∂(P.diagonalMeasure ψ), (0 : ℝ) ≤ s := by
      rw [MeasureTheory.ae_iff]
      have : {s : ℝ | ¬(0 ≤ s)} = Set.Iio 0 := by ext s; simp [not_le]
      rw [this]; exact h_supp
    filter_upwards [h_ae_nonneg] with s hs
    simp only [f_n, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.ofReal_re]; exact hs
    · simp [mul_zero, map_zero]
  -- Limit of non-negative sequence is non-negative
  exact ge_of_tendsto hlim_re (Filter.Eventually.of_forall h_trunc_nonneg)

/-- **Joint strong continuity of the translation orbit map.**
    The map `a ↦ U(translation' a) ψ` from `ℝ^{d+1}` to the GNS Hilbert space is continuous.

    **Proof:**
    1. Each `(s, x) ↦ U(translationInDirection μ s) x` is jointly continuous
       (from isometry `‖U(g)x‖ = ‖x‖` and separate strong continuity `hsc μ`,
       via `‖U(s)x - U(s₀)x₀‖ ≤ ‖x - x₀‖ + ‖U(s)x₀ - U(s₀)x₀‖`).
    2. The decomposition `translation' a = ∏μ translationInDirection μ (a μ)`
       reduces the orbit map to a composition of jointly continuous maps. -/
private theorem translation_orbit_continuous
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (ψ : GNSHilbertSpace Wfn) :
    Continuous (fun a : MinkowskiSpace d =>
      poincareActGNS Wfn (PoincareGroup.translation' a) ψ) := by
  -- Step 1: Joint continuity of (s, x) ↦ U(translationInDirection μ s) x
  have hjoint : ∀ μ : Fin (d + 1),
      Continuous (fun (p : ℝ × GNSHilbertSpace Wfn) =>
        poincareActGNS Wfn
          (PoincareRepresentation.translationInDirection d μ p.1) p.2) := by
    intro μ
    rw [Metric.continuous_iff]
    intro ⟨s₀, x₀⟩ ε hε
    -- Get δ₁ from strong continuity of t ↦ U(t) x₀
    have hsc_x₀ := hsc μ x₀
    rw [Metric.continuous_iff] at hsc_x₀
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hsc_x₀ s₀ (ε / 2) (half_pos hε)
    refine ⟨min (ε / 2) δ₁, lt_min (half_pos hε) hδ₁_pos, ?_⟩
    intro ⟨s, x⟩ hdist
    simp only [Prod.dist_eq, max_lt_iff] at hdist
    -- Triangle inequality: ‖U(s)x - U(s₀)x₀‖ ≤ ‖x - x₀‖ + ‖U(s)x₀ - U(s₀)x₀‖
    calc dist (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s) x)
          (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s₀) x₀)
        ≤ dist (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s) x)
              (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s) x₀) +
          dist (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s) x₀)
              (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s₀) x₀) :=
        dist_triangle _ _ _
      _ = dist x x₀ +
          dist (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s) x₀)
              (poincareActGNS Wfn (PoincareRepresentation.translationInDirection d μ s₀) x₀) := by
        congr 1
        -- U(g) is an isometry: dist(U(g)x, U(g)y) = dist(x, y)
        simp only [dist_eq_norm, ← (poincareActGNS Wfn _).map_sub, poincareActGNS_norm]
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · exact lt_of_lt_of_le hdist.2 (min_le_left _ _)
        · exact hδ₁ s (lt_of_lt_of_le hdist.1 (min_le_right _ _))
      _ = ε := add_halves ε
  -- Step 2: The orbit map is continuous, by decomposing translation' a via
  -- the standard basis and composing jointly continuous directional translations.
  have htrans_mul : ∀ a b : MinkowskiSpace d,
      PoincareGroup.translation' a * PoincareGroup.translation' b =
      PoincareGroup.translation' (a + b) := by
    intro a b
    apply PoincareGroup.ext
    · simp [PoincareGroup.translation', PoincareGroup.mul_translation,
        PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
    · simp [PoincareGroup.translation', PoincareGroup.mul_lorentz]
  -- Basis decomposition: a = ∑ μ, a μ • e_μ
  have hbasis_decomp : ∀ a : MinkowskiSpace d,
      ∑ μ : Fin (d + 1), a μ • PoincareRepresentation.basisVector d μ = a := by
    intro a
    have : ∀ μ : Fin (d + 1),
        PoincareRepresentation.basisVector d μ = Pi.single μ 1 := by
      intro μ; ext ν
      simp [PoincareRepresentation.basisVector, Pi.single, Function.update]
    simp_rw [this]; exact (pi_eq_sum_univ' a).symm
  -- Convert goal to use the basis sum form
  have hfun_eq : (fun a : MinkowskiSpace d =>
      poincareActGNS Wfn (PoincareGroup.translation' a) ψ) =
    (fun a => poincareActGNS Wfn (PoincareGroup.translation'
      (∑ μ, a μ • PoincareRepresentation.basisVector d μ)) ψ) := by
    ext a; rw [hbasis_decomp]
  rw [hfun_eq]
  -- Prove by Finset induction: each direction adds one jointly continuous layer
  suffices h : ∀ S : Finset (Fin (d + 1)),
      Continuous (fun a : MinkowskiSpace d =>
        poincareActGNS Wfn (PoincareGroup.translation'
          (∑ μ ∈ S, a μ • PoincareRepresentation.basisVector d μ)) ψ)
    from h Finset.univ
  intro S
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuous_const
  | @insert μ₀ S' hμ₀ ih =>
    -- Use let-bindings to avoid expensive isDefEq in Continuous.comp
    let f : MinkowskiSpace d → ℝ × GNSHilbertSpace Wfn :=
      fun a => (a μ₀, poincareActGNS Wfn (PoincareGroup.translation'
        (∑ μ ∈ S', a μ • PoincareRepresentation.basisVector d μ)) ψ)
    let g : ℝ × GNSHilbertSpace Wfn → GNSHilbertSpace Wfn :=
      fun p => poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d μ₀ p.1) p.2
    suffices hgf : Continuous (g ∘ f) by
      have heq : (fun a : MinkowskiSpace d =>
          poincareActGNS Wfn (PoincareGroup.translation'
            (∑ μ ∈ Insert.insert μ₀ S', a μ •
              PoincareRepresentation.basisVector d μ)) ψ) = g ∘ f := by
        ext a
        simp only [g, f, Function.comp,
          PoincareRepresentation.translationInDirection]
        rw [Finset.sum_insert hμ₀, ← htrans_mul,
          poincareActGNS_mul Wfn, ContinuousLinearMap.comp_apply]
      rw [heq]; exact hgf
    exact (show Continuous g from hjoint μ₀).comp
      (show Continuous f from Continuous.prodMk (continuous_apply μ₀) ih)

/-- **Multi-dimensional Bochner support from SCD.**

    If `μ` is the Bochner measure representing the translation inner product
    `a ↦ ⟪ψ, U(a)ψ⟫` on `MinkowskiSpace d`, and the Wightman functions satisfy
    `SpectralConditionDistribution`, then `μ` is supported on `ForwardMomentumCone d`.

    **Proof sketch** (multi-dimensional analog of the 1D bridge chain):
    1. For pre-Hilbert vectors `F`, express `⟪F, U(a)F⟫` as a sum of Wightman
       function evaluations via `inner_translate_eq_wip`.
    2. By SCD (at all n), each summand's distributional Fourier transform
       is supported in the product forward cone `V̄₊ⁿ⁺ᵐ⁻¹`. The marginal
       on the total 4-momentum variable is supported in `V̄₊`.
    3. Multi-dimensional Bochner–Fubini: `∫ χ dμ_F = ∫ φ_F(a) · ℱ⁻¹[χ](a) da`
       where `φ_F(a) = ⟪F, U(a)F⟫`. By step (2), this vanishes for Schwartz `χ`
       supported in `(V̄₊)ᶜ`.
    4. Inner regularity + Schwartz test function density: `μ_F((V̄₊)ᶜ) = 0`.
    5. For general `ψ`, approximate by pre-Hilbert vectors. The Bochner
       measures converge weakly (since `⟪ψ_n, U(a)ψ_n⟫ → ⟪ψ, U(a)ψ⟫`
       pointwise), and support on the closed set `V̄₊` is preserved under
       weak limits (Portmanteau theorem).

    This is the multi-dimensional generalization of the 1D bridge chain
    (`scd_inner_hasOneSidedFourierSupport` + `oneSidedSupport_implies_schwartz_vanishing`
    + `measure_Iio_zero_of_schwartz_vanishing`).

    **Ref:** Streater-Wightman, "PCT, Spin and Statistics", §3-1;
    Reed-Simon I, Theorem IX.9. -/
private lemma scd_bochner_forwardCone_support
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (ψ : GNSHilbertSpace Wfn)
    (μ : MeasureTheory.Measure (MinkowskiSpace d))
    [MeasureTheory.IsFiniteMeasure μ]
    (hboch : ∀ x : MinkowskiSpace d,
      @inner ℂ _ _ ψ ((gnsPoincareRep Wfn).U (PoincareGroup.translation' x) ψ) =
      ∫ p : MinkowskiSpace d,
        Complex.exp (↑(∑ i : Fin (d + 1), x i * p i) * Complex.I) ∂μ) :
    μ (ForwardMomentumCone d)ᶜ = 0 := by
  sorry

/-- **Mass-shell condition** from the distribution-level spectral condition.

    For ψ in the appropriate domains, `⟪ψ, P₀²ψ⟫.re ≥ Σᵢ ⟪ψ, Pᵢ²ψ⟫.re`.

    **Proof:**
    1. Self-adjointness of each `Pμ` gives `re(⟪ψ, Pμ²ψ⟫) = ‖Pμψ‖²`, reducing
       the inequality to `‖P₀ψ‖² ≥ Σᵢ ‖Pᵢψ‖²`.
    2. The positive-definite function `a ↦ ⟪ψ, U(a)ψ⟫` on `ℝ^{d+1}` admits a
       finite positive Bochner measure `μ` by `bochner_theorem`.
    3. `SpectralConditionDistribution` implies `supp(μ) ⊆ V̄₊`.
    4. Differentiating the Bochner integral gives the moment identity
       `‖P₀ψ‖² - Σᵢ ‖Pᵢψ‖² = ∫ (p₀² - |p⃗|²) dμ`.
    5. The integral is non-negative since `p₀² ≥ |p⃗|²` on `V̄₊`.

    **Ref:** Reed-Simon I, Theorem IX.8; Streater-Wightman, Chapter 3. -/
private lemma gns_mass_shell
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (ψ : GNSHilbertSpace Wfn)
    (hψ₀ : ψ ∈ ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)).domain)
    (hP₀ψ : ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)) ⟨ψ, hψ₀⟩ ∈
      ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)).domain)
    (hψᵢ : ∀ i : Fin d, ψ ∈
      ((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i))).domain)
    (hPᵢψ : ∀ i : Fin d,
      ((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i))) ⟨ψ, hψᵢ i⟩ ∈
        ((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i))).domain) :
    (⟪ψ, ((gnsPoincareRep Wfn).momentumOp 0 (hsc 0))
      ⟨((gnsPoincareRep Wfn).momentumOp 0 (hsc 0)) ⟨ψ, hψ₀⟩, hP₀ψ⟩⟫_ℂ).re ≥
    ∑ i : Fin d,
      (⟪ψ, ((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
        ⟨((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
          ⟨ψ, hψᵢ i⟩, hPᵢψ i⟩⟫_ℂ).re := by
  -- === Step 1: Self-adjointness reduces inner products to squared norms ===
  -- For self-adjoint T: ⟪ψ, T(Tψ)⟫ = ⟪Tψ, Tψ⟫, so re(⟪ψ, T²ψ⟫) = ‖Tψ‖².
  set P₀ := (gnsPoincareRep Wfn).momentumOp 0 (hsc 0)
  have hT₀ := PoincareRepresentation.momentumOp_denselyDefined (gnsPoincareRep Wfn) 0 (hsc 0)
  have hsa₀ := PoincareRepresentation.momentumOp_selfAdjoint (gnsPoincareRep Wfn) 0 (hsc 0)
  have hsym₀ := P₀.selfadjoint_symmetric hT₀ hsa₀
  -- re(⟪ψ, P₀²ψ⟫) = ‖P₀ψ‖²
  have h₀ : (⟪ψ, P₀ ⟨P₀ ⟨ψ, hψ₀⟩, hP₀ψ⟩⟫_ℂ).re = ‖P₀ ⟨ψ, hψ₀⟩‖ ^ 2 := by
    rw [show @inner ℂ _ _ ψ (P₀ ⟨P₀ ⟨ψ, hψ₀⟩, hP₀ψ⟩) =
      @inner ℂ _ _ (P₀ ⟨ψ, hψ₀⟩) (P₀ ⟨ψ, hψ₀⟩)
      from (hsym₀ ⟨ψ, hψ₀⟩ ⟨P₀ ⟨ψ, hψ₀⟩, hP₀ψ⟩).symm]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (P₀ ⟨ψ, hψ₀⟩)
  -- re(⟪ψ, Pᵢ²ψ⟫) = ‖Pᵢψ‖² for each spatial direction
  have hᵢ : ∀ i : Fin d,
      (⟪ψ, ((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
        ⟨((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
          ⟨ψ, hψᵢ i⟩, hPᵢψ i⟩⟫_ℂ).re =
      ‖((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
        ⟨ψ, hψᵢ i⟩‖ ^ 2 := by
    intro i
    have hTᵢ := PoincareRepresentation.momentumOp_denselyDefined
      (gnsPoincareRep Wfn) (Fin.succ i) (hsc (Fin.succ i))
    have hsaᵢ := PoincareRepresentation.momentumOp_selfAdjoint
      (gnsPoincareRep Wfn) (Fin.succ i) (hsc (Fin.succ i))
    have hsymᵢ := ((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
      (hsc (Fin.succ i))).selfadjoint_symmetric hTᵢ hsaᵢ
    rw [show @inner ℂ _ _ ψ (((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
        (hsc (Fin.succ i))) ⟨((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
        (hsc (Fin.succ i))) ⟨ψ, hψᵢ i⟩, hPᵢψ i⟩) =
      @inner ℂ _ _ (((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
        (hsc (Fin.succ i))) ⟨ψ, hψᵢ i⟩) (((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
        (hsc (Fin.succ i))) ⟨ψ, hψᵢ i⟩)
      from (hsymᵢ ⟨ψ, hψᵢ i⟩ ⟨((gnsPoincareRep Wfn).momentumOp (Fin.succ i)
        (hsc (Fin.succ i))) ⟨ψ, hψᵢ i⟩, hPᵢψ i⟩).symm]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  -- Rewrite goal as ‖P₀ψ‖² ≥ Σᵢ ‖Pᵢψ‖²
  rw [h₀, Finset.sum_congr rfl (fun i _ => hᵢ i)]
  -- === Step 2: Apply Bochner's theorem ===
  -- The positive-definite function φ(a) = ⟪ψ, U(a)ψ⟫ on ℝ^{d+1} has a Bochner measure μ.
  -- By SpectralConditionDistribution, supp(μ) ⊆ V̄₊.
  -- Differentiating the Bochner integral twice gives ‖Pμψ‖² = ∫ pμ² dμ.
  have ⟨μ, _, hsupp, hmoment⟩ : ∃ (μ : MeasureTheory.Measure (MinkowskiSpace d)),
      MeasureTheory.IsFiniteMeasure μ ∧
      μ (ForwardMomentumCone d)ᶜ = 0 ∧
      ‖P₀ ⟨ψ, hψ₀⟩‖ ^ 2 -
        ∑ i : Fin d,
          ‖((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
            ⟨ψ, hψᵢ i⟩‖ ^ 2 =
        ∫ p : MinkowskiSpace d,
          ((p 0) ^ 2 - ∑ i : Fin d, (p (Fin.succ i)) ^ 2) ∂μ := by
    -- === Step 2a: Define the positive-definite function φ(a) = ⟪ψ, U(translation a) ψ⟫ ===
    set φ : MinkowskiSpace d → ℂ := fun a =>
      @inner ℂ _ _ ψ ((gnsPoincareRep Wfn).U (PoincareGroup.translation' a) ψ)
    -- === Step 2b: φ is continuous ===
    -- Follows from joint strong continuity of translations on GNS Hilbert space
    -- (each one-parameter group t ↦ U(t·eμ) is strongly continuous by `hsc`,
    -- and on finite-dimensional ℝ^{d+1} separate continuity in each coordinate
    -- implies joint continuity of the bilinear pairing a ↦ ⟪ψ, U(a)ψ⟫).
    have hφ_cont : Continuous φ :=
      Continuous.inner continuous_const (translation_orbit_continuous Wfn hsc ψ)
    -- === Step 2c: φ is positive-definite ===
    -- For any points aⱼ and coefficients cⱼ:
    --   Σᵢⱼ c̄ᵢ cⱼ φ(aⱼ - aᵢ) = Σᵢⱼ c̄ᵢ cⱼ ⟪U(aᵢ)ψ, U(aⱼ)ψ⟫
    --                             = ‖Σⱼ cⱼ U(aⱼ)ψ‖² ≥ 0
    -- using unitarity U(a-b) = U(a) U(b)* and sesquilinearity of inner product.
    have hφ_pd : IsPositiveDefiniteFunction φ := by
      intro m c x
      -- Key: translation' a * translation' b = translation' (a + b)
      have htrans_mul : ∀ a b : MinkowskiSpace d,
          PoincareGroup.translation' a * PoincareGroup.translation' b =
          PoincareGroup.translation' (a + b) := by
        intro a b
        apply PoincareGroup.ext
        · simp [PoincareGroup.translation', PoincareGroup.mul_translation,
            PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
        · simp [PoincareGroup.translation', PoincareGroup.mul_lorentz]
      -- Key: φ(b - a) = ⟪U(translation' a) ψ, U(translation' b) ψ⟫
      -- Uses: inner product preservation + group homomorphism + translation' decomposition
      have hφ_inner : ∀ i j : Fin m,
          φ (x j - x i) = @inner ℂ _ _
            (poincareActGNS Wfn (PoincareGroup.translation' (x i)) ψ)
            (poincareActGNS Wfn (PoincareGroup.translation' (x j)) ψ) := by
        intro i j
        -- Unfold φ and normalize to poincareActGNS
        simp only [φ, show (gnsPoincareRep Wfn).U = poincareActGNS Wfn from rfl]
        -- Rewrite translation'(xⱼ) = translation'(xᵢ) * translation'(xⱼ - xᵢ)
        conv_rhs =>
          rw [show PoincareGroup.translation' (x j) =
            PoincareGroup.translation' (x i) * PoincareGroup.translation' (x j - x i)
            from by rw [htrans_mul]; congr 1; abel]
          rw [poincareActGNS_mul Wfn, ContinuousLinearMap.comp_apply]
        -- ⟪ψ, U(xⱼ-xᵢ)ψ⟫ = ⟪U(xᵢ)ψ, U(xᵢ)(U(xⱼ-xᵢ)ψ)⟫ by inner product preservation
        exact (poincareActGNS_inner Wfn (PoincareGroup.translation' (x i)) ψ _).symm
      -- Set yᵢ = U(translation'(xᵢ)) ψ
      set y : Fin m → GNSHilbertSpace Wfn :=
        fun i => poincareActGNS Wfn (PoincareGroup.translation' (x i)) ψ
      -- Rewrite φ to inner product
      simp_rw [hφ_inner]
      -- Convert double sum to ⟪v, v⟫ where v = ∑ cᵢ yᵢ, then use ⟪v,v⟫.re ≥ 0
      set v := ∑ i : Fin m, c i • y i
      suffices h : (∑ i : Fin m, ∑ j : Fin m,
          starRingEnd ℂ (c i) * c j * @inner ℂ _ _ (y i) (y j)) =
          @inner ℂ _ _ v v by
        rw [h]; exact inner_self_nonneg (𝕜 := ℂ)
      symm; simp only [v]
      rw [sum_inner (𝕜 := ℂ)]
      simp_rw [_root_.inner_smul_left, inner_sum (𝕜 := ℂ), _root_.inner_smul_right]
      congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j; ring
    -- === Step 2d: Apply Bochner's theorem to get the finite measure μ ===
    obtain ⟨μ, hfin, hboch⟩ := bochner_theorem φ hφ_cont hφ_pd
    -- hboch : ∀ x, φ x = ∫ p, exp(i Σⱼ xⱼ pⱼ) dμ(p)
    -- === Step 2e: Support condition from SpectralConditionDistribution ===
    -- By `scd_bochner_forwardCone_support`, the multi-dimensional analog of the 1D
    -- bridge chain, the Bochner measure μ of a ↦ ⟪ψ, U(a)ψ⟫ is supported on V̄₊.
    have h_supp : μ (ForwardMomentumCone d)ᶜ = 0 := by
      haveI := hfin
      exact scd_bochner_forwardCone_support Wfn hSCD hsc ψ μ (fun x => hboch x)
    -- === Step 2f: Moment identity via differentiation of the Bochner integral ===
    -- Differentiating φ(a) = ∫ exp(i⟨a,p⟩) dμ(p) twice in direction eμ:
    --   -∂²φ/∂aμ²|_{a=0} = ∫ pμ² dμ(p)
    -- Combined with the Stone-generator identity:
    --   -∂²φ/∂aμ²|_{a=0} = ‖Pμ ψ‖²
    -- we get ‖Pμ ψ‖² = ∫ pμ² dμ for each μ. Subtracting:
    --   ‖P₀ ψ‖² - Σᵢ ‖Pᵢ ψ‖² = ∫ (p₀² - Σᵢ pᵢ²) dμ
    have h_moment : ‖P₀ ⟨ψ, hψ₀⟩‖ ^ 2 -
        ∑ i : Fin d,
          ‖((gnsPoincareRep Wfn).momentumOp (Fin.succ i) (hsc (Fin.succ i)))
            ⟨ψ, hψᵢ i⟩‖ ^ 2 =
        ∫ p : MinkowskiSpace d,
          ((p 0) ^ 2 - ∑ i : Fin d, (p (Fin.succ i)) ^ 2) ∂μ := by
      haveI := hfin
      -- Per-component Stone-Bochner moment identity: ‖Pμ ψ‖² = ∫ (p μ)² dμ
      -- for each direction μ ∈ Fin (d+1).
      -- Chain: norm_sq_domain_eq_integral gives ‖Pμ ψ‖² = Re(∫ s² d(spectral_diag_μ)).
      -- stone_spectral_representation gives ⟪ψ, Uμ(t)ψ⟫ = ∫ exp(its) d(spectral_diag_μ).
      -- Restricting hboch to x = t · eμ gives ⟪ψ, Uμ(t)ψ⟫ = ∫ exp(it·pμ) dμ(p)
      --   = ∫ exp(its) d(μ.map eval_μ)(s) via integral_map.
      -- bochner_uniqueness: spectral_diag_μ = μ.map (eval μ).
      -- Substitution + integral_map + Re of real = ∫ (p μ)² dμ.
      have h_comp : ∀ (μ_dir : Fin (d + 1))
          (hψ_dir : ψ ∈ ((gnsPoincareRep Wfn).momentumOp μ_dir (hsc μ_dir)).domain),
          MeasureTheory.Integrable (fun p : MinkowskiSpace d => (p μ_dir) ^ 2) μ ∧
          ‖((gnsPoincareRep Wfn).momentumOp μ_dir (hsc μ_dir)) ⟨ψ, hψ_dir⟩‖ ^ 2 =
            ∫ p : MinkowskiSpace d, (p μ_dir) ^ 2 ∂μ := by
        intro μ_dir hψ_dir
        set T := (gnsPoincareRep Wfn).momentumOp μ_dir (hsc μ_dir) with hT_def
        have hT_dd := PoincareRepresentation.momentumOp_denselyDefined
          (gnsPoincareRep Wfn) μ_dir (hsc μ_dir)
        have hT_sa := PoincareRepresentation.momentumOp_selfAdjoint
          (gnsPoincareRep Wfn) μ_dir (hsc μ_dir)
        set P_sp := T.spectralMeasure hT_dd hT_sa
        set ν := P_sp.diagonalMeasure ψ
        haveI : MeasureTheory.IsFiniteMeasure ν := P_sp.diagonalMeasure_isFiniteMeasure ψ
        -- ‖T ψ‖² = Re(∫ (s : ℂ)² dν)
        have h_norm := norm_sq_domain_eq_integral T hT_dd hT_sa ⟨ψ, hψ_dir⟩
        -- Stone spectral: ⟪ψ, 𝒰(t)ψ⟫ = ∫ exp(I*t*s) dν
        set 𝒰 := (gnsPoincareRep Wfn).translationGroup μ_dir (hsc μ_dir)
        have h_stone : ∀ t, @inner ℂ _ _ ψ (𝒰.U t ψ) =
            ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂ν :=
          fun t => stone_spectral_representation Wfn 𝒰 ψ t
        -- Bochner pushforward: ⟪ψ, 𝒰(t)ψ⟫ = ∫ exp(I*t*s) d(μ.map eval_μ)(s)
        set ν' := μ.map (fun p : MinkowskiSpace d => p μ_dir) with hν'_def
        haveI hν'_fin : MeasureTheory.IsFiniteMeasure ν' := by
          constructor
          rw [hν'_def, MeasureTheory.Measure.map_apply (measurable_pi_apply μ_dir)
            MeasurableSet.univ, Set.preimage_univ]
          exact MeasureTheory.measure_lt_top μ _
        have h_boch_dir : ∀ t, @inner ℂ _ _ ψ (𝒰.U t ψ) =
            ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂ν' := by
          intro t
          -- 𝒰.U t ψ = π.U(translationInDirection d μ_dir t) ψ
          --          = π.U(translation'(t • basisVector d μ_dir)) ψ
          -- so inner = φ(t • basisVector d μ_dir) = ∫ exp(↑(∑ᵢ (t•eμ)ᵢ pᵢ) * I) dμ
          have h1 : @inner ℂ _ _ ψ (𝒰.U t ψ) =
              φ (t • PoincareRepresentation.basisVector d μ_dir) := by
            simp only [𝒰, φ, PoincareRepresentation.translationGroup,
              PoincareRepresentation.translationInDirection]
          rw [h1, hboch]
          rw [hν'_def, MeasureTheory.integral_map (measurable_pi_apply μ_dir).aemeasurable
            (Complex.continuous_exp.comp
              (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable]
          congr 1; ext p; congr 1
          -- ↑(∑ i, (t • basisVector d μ_dir) i * p i) * I = I * ↑t * ↑(p μ_dir)
          simp only [PoincareRepresentation.basisVector, Pi.smul_apply, smul_eq_mul]
          rw [show (∑ i : Fin (d + 1), (t * if i = μ_dir then (1 : ℝ) else 0) * p i) =
            t * p μ_dir from by
            simp [Finset.sum_ite_eq', Finset.mem_univ]]
          push_cast; ring
        -- Bochner uniqueness: ν = ν'
        have h_eq : ν = ν' := bochner_uniqueness ν ν' (fun t => by
          rw [← h_stone t, h_boch_dir t])
        -- Substitute into norm identity and simplify
        constructor
        · -- Integrability: ψ ∈ dom(T) implies ∫ (p μ_dir)² dμ < ∞
          -- Since ν = ν' = μ.map eval_μ, the spectral second moment ∫ s² dν < ∞
          -- (from ψ ∈ dom(T)) transfers to ∫ (p μ_dir)² dμ via pushforward.
          have h_sq_int_complex : MeasureTheory.Integrable
              (fun s : ℝ => ((s : ℂ) ^ 2)) ν :=
            (mem_domain_iff_square_integrable T hT_dd hT_sa ψ).mp hψ_dir
          have h_sq_int : MeasureTheory.Integrable (fun s : ℝ => s ^ 2) ν := by
            convert h_sq_int_complex.norm using 1; ext s
            simp [Complex.norm_real, sq_abs]
          rw [h_eq, hν'_def] at h_sq_int
          rw [show (fun p : MinkowskiSpace d => (p μ_dir) ^ 2) =
            (fun s : ℝ => s ^ 2) ∘ (fun p : MinkowskiSpace d => p μ_dir) from rfl]
          exact h_sq_int.comp_measurable (measurable_pi_apply μ_dir)
        · rw [h_norm]
          -- Bridge coercion: ↑⟨ψ, hψ_dir⟩ = ψ, so the spectral diagonal measure is ν
          show (∫ s : ℝ, ((s : ℂ) ^ 2) ∂ν).re = ∫ p : MinkowskiSpace d, (p μ_dir) ^ 2 ∂μ
          rw [h_eq, hν'_def]
          -- Re(∫ (s:ℂ)² d(μ.map eval_μ)) = ∫ (p μ_dir)² dμ
          rw [MeasureTheory.integral_map (measurable_pi_apply μ_dir).aemeasurable
            ((Complex.continuous_ofReal.pow 2).aestronglyMeasurable)]
          -- Re(∫ (↑(p μ_dir))² dμ) = ∫ (p μ_dir)² dμ
          -- Since (↑x : ℂ)² = ↑(x²), the integrand is real-valued.
          simp_rw [show ∀ s : ℝ, (↑s : ℂ) ^ 2 = (↑(s ^ 2) : ℂ) from
            fun s => by push_cast; ring]
          norm_cast
      -- Apply per-component identities
      have h₀ := h_comp 0 hψ₀
      have hᵢ := fun i => h_comp (Fin.succ i) (hψᵢ i)
      rw [h₀.2, Finset.sum_congr rfl (fun i _ => (hᵢ i).2)]
      -- ∫ (p 0)² dμ - ∑ᵢ ∫ (p (succ i))² dμ = ∫ ((p 0)² - ∑ᵢ (p (succ i))²) dμ
      -- by integral linearity (integral_sub + integral_finset_sum)
      have h_int_sum : MeasureTheory.Integrable
          (fun p : MinkowskiSpace d => ∑ i : Fin d, (p (Fin.succ i)) ^ 2) μ :=
        MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => (hᵢ i).1)
      have h_sub := MeasureTheory.integral_sub h₀.1 h_int_sum
      have h_sum := MeasureTheory.integral_finset_sum Finset.univ
        (fun (i : Fin d) (_ : i ∈ Finset.univ) => (hᵢ i).1)
      linarith
    exact ⟨μ, hfin, h_supp, h_moment⟩
  -- === Step 3: The integral is non-negative since p₀² ≥ |p⃗|² on V̄₊ ===
  suffices h : 0 ≤ ∫ p : MinkowskiSpace d,
      ((p 0) ^ 2 - ∑ i : Fin d, (p (Fin.succ i)) ^ 2) ∂μ by linarith
  apply MeasureTheory.integral_nonneg_of_ae
  have h_ae : ∀ᵐ p ∂μ, p ∈ ForwardMomentumCone d := MeasureTheory.ae_iff.mpr hsupp
  filter_upwards [h_ae] with p hp
  simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
    MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq] at hp
  have hcausal := hp.1
  rw [MinkowskiSpace.IsCausal] at hcausal
  have h_decomp := MinkowskiSpace.minkowskiNormSq_decomp d p
  have h_le : MinkowskiSpace.spatialNormSq d p ≤ (p 0) ^ 2 := by linarith
  change 0 ≤ (p 0) ^ 2 - MinkowskiSpace.spatialNormSq d p
  linarith

/-- **Spectrum condition for the GNS Hilbert space.**

    The GNS Poincaré representation satisfies the Streater-Wightman spectral condition:
    P₀ ≥ 0 and P₀² ≥ Σᵢ Pᵢ² on the Stone-generator domains.

    Proved from `SpectralConditionDistribution` (Fourier support of reduced Wightman
    functions in V̄₊ⁿ), which is derived from `Wfn.spectrum_condition` (forward tube
    analyticity) via `spectralConditionDistribution_iff_forwardTubeAnalyticity`. -/
theorem gns_spectrum_condition :
    SpectralConditionQFT d (gnsPoincareRep Wfn) where
  strongly_continuous := gns_translationStronglyContinuous Wfn
  energy_nonneg := gns_energy_nonneg Wfn
    (wfn_spectralConditionDistribution Wfn) (gns_translationStronglyContinuous Wfn)
  mass_shell := gns_mass_shell Wfn
    (wfn_spectralConditionDistribution Wfn) (gns_translationStronglyContinuous Wfn)

/-- The operator-valued distribution on the GNS Hilbert space, extracted as a
    standalone definition so that the cyclicity lemma can reference it. -/
noncomputable def gnsOVD : OperatorValuedDistribution d (GNSHilbertSpace Wfn) where
  domain := gnsDomain Wfn
  operator := gnsFieldOp Wfn
  operator_add := fun f g ψ hψ => by
    obtain ⟨x, hx⟩ := hψ
    rw [← hx, gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe,
      fieldOperator_add_test Wfn f g x, UniformSpace.Completion.coe_add]
  operator_smul := fun c f ψ hψ => by
    obtain ⟨x, hx⟩ := hψ
    rw [← hx, gnsFieldOp_coe, gnsFieldOp_coe,
      fieldOperator_smul_test Wfn c f x, UniformSpace.Completion.coe_smul]
  operator_vector_add := fun f ψ₁ ψ₂ hψ₁ hψ₂ => by
    obtain ⟨x₁, hx₁⟩ := hψ₁; obtain ⟨x₂, hx₂⟩ := hψ₂
    rw [← hx₁, ← hx₂, ← UniformSpace.Completion.coe_add,
      gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe,
      fieldOperator_vector_add Wfn f x₁ x₂, UniformSpace.Completion.coe_add]
  operator_vector_smul := fun f c ψ hψ => by
    obtain ⟨x, hx⟩ := hψ
    rw [← hx, ← UniformSpace.Completion.coe_smul,
      gnsFieldOp_coe, gnsFieldOp_coe,
      fieldOperator_vector_smul Wfn f c x, UniformSpace.Completion.coe_smul]
  operator_domain := fun f ψ hψ => gnsFieldOp_domain Wfn f ψ hψ
  matrix_element_continuous := fun χ ψ hχ hψ => by
    obtain ⟨x, rfl⟩ := hχ; obtain ⟨y, rfl⟩ := hψ
    exact matrix_element_continuous_aux Wfn x y

/-- **Cyclicity of the vacuum in the GNS Hilbert space.**

    The algebraic span of {φ(f₁)···φ(fₙ)Ω | n ∈ ℕ, fᵢ ∈ 𝒮(ℝ^{d+1})} is
    dense in the GNS Hilbert space. The proof requires the
    **Schwartz nuclear theorem**: for each n, finite tensor products
    f₁(x₁)···fₙ(xₙ) are dense in the n-point Schwartz space 𝒮(ℝ^{n(d+1)}).

    Given the nuclear theorem, the argument is:
    1. Each element of PreHilbertSpace is a Borchers sequence (f₀, f₁, f₂, …).
    2. The n-th component fₙ ∈ 𝒮(ℝ^{n(d+1)}) can be approximated by sums of
       product test functions g₁ ⊗ ··· ⊗ gₙ.
    3. The corresponding GNS vectors φ(g₁)···φ(gₙ)Ω lie in the algebraic span.
    4. PreHilbertSpace embeds densely in the completion, so the algebraic span
       is dense in the full Hilbert space.

    The nuclear theorem is not in Mathlib as of 2025. -/
-- Helper: operatorPow of gnsOVD equals the embedding of the iterated field operator.
private theorem operatorPow_gnsOVD_eq (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    (gnsOVD Wfn).operatorPow n fs (gnsVacuum Wfn) =
    ((List.foldr (fun f acc => fieldOperator Wfn f acc)
      (vacuumState Wfn) (List.ofFn fs) : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OperatorValuedDistribution.operatorPow]
    rw [ih (fun i => fs (Fin.succ i))]
    show gnsFieldOp Wfn (fs 0)
      ↑(List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fun i => fs i.succ)) =
      ↑(List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fs))
    rw [gnsFieldOp_coe Wfn (fs 0)]
    simp only [List.ofFn_succ, List.foldr_cons]

-- Abbreviation: the quotient class of a single-component Borchers sequence.
private noncomputable def singlePH (n : ℕ) (g : SchwartzNPointSpace d n) :
    PreHilbertSpace Wfn :=
  Quotient.mk (borchersSetoid Wfn) (BorchersSequence.single n g)

-- Helper: operatorPow equals the embedding of singlePH n (productTensor fs).
private theorem operatorPow_eq_single (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    (gnsOVD Wfn).operatorPow n fs (gnsVacuum Wfn) =
    ((singlePH Wfn n (SchwartzMap.productTensor fs) : PreHilbertSpace Wfn) :
      GNSHilbertSpace Wfn) := by
  rw [operatorPow_gnsOVD_eq, foldr_fieldOperator_eq_mk]
  congr 1
  show Quotient.mk (borchersSetoid Wfn)
    (List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)) =
    singlePH Wfn n (SchwartzMap.productTensor fs)
  exact mk_eq_of_funcs_eq Wfn _ _ (fun k => by
    by_cases hk : k = n
    · subst hk; rw [iteratedAction_funcs_n, BorchersSequence.single_funcs_eq]
    · rw [iteratedAction_funcs_ne fs k hk, BorchersSequence.single_funcs_ne hk])

-- Helper: singlePH is linear in the Schwartz function.
private theorem singlePH_add (n : ℕ) (f g : SchwartzNPoint d n) :
    singlePH Wfn n (f + g) = singlePH Wfn n f + singlePH Wfn n g :=
  mk_eq_of_funcs_eq Wfn _ _ (fun k => by
    show (BorchersSequence.single n (f + g)).funcs k =
      ((BorchersSequence.single n f) + (BorchersSequence.single n g)).funcs k
    simp only [BorchersSequence.add_funcs]
    by_cases hk : k = n
    · subst hk; simp [BorchersSequence.single_funcs_eq]
    · simp [BorchersSequence.single_funcs_ne hk])

private theorem singlePH_smul (n : ℕ) (c : ℂ) (f : SchwartzNPoint d n) :
    singlePH Wfn n (c • f) = c • singlePH Wfn n f :=
  mk_eq_of_funcs_eq Wfn _ _ (fun k => by
    show (BorchersSequence.single n (c • f)).funcs k =
      (c • (BorchersSequence.single n f)).funcs k
    simp only [BorchersSequence.smul_funcs]
    by_cases hk : k = n
    · subst hk; simp [BorchersSequence.single_funcs_eq]
    · simp [BorchersSequence.single_funcs_ne hk])

private theorem singlePH_zero (n : ℕ) :
    singlePH Wfn n (0 : SchwartzNPoint d n) = 0 := by
  show Quotient.mk (borchersSetoid Wfn) (BorchersSequence.single n 0) =
    Quotient.mk (borchersSetoid Wfn) 0
  exact mk_eq_of_funcs_eq Wfn _ _ (fun k => by
    by_cases hk : k = n
    · subst hk; simp [BorchersSequence.single_funcs_eq]
    · simp [BorchersSequence.single_funcs_ne hk])

-- Helper: g ↦ ↑⟦single n g⟧ is continuous SchwartzNPointSpace → GNSHilbertSpace.
--
-- Mathematical justification: The map is linear, and its norm squared
-- ‖⟦single n g⟧‖² = Re(W_{n+n}(g.conjTP g)) is continuous from the Schwartz space
-- to ℝ (by temperedness of W and joint continuity of tensorProduct). A linear map
-- from a Fréchet space to a normed space with continuous norm at 0 is continuous.
-- Alternatively, all matrix elements ⟨↑⟦G⟧, ↑⟦single n g⟧⟩ are continuous in g
-- (inner_coe_single_continuous), so the map is weakly continuous; by the
-- Banach-Steinhaus theorem for barrelled spaces (SchwartzSpace is Fréchet hence
-- barrelled), weak-to-strong continuity follows.
--
-- The proof uses joint continuity of tensorProduct, continuity of borchersConj
-- (reverse ∘ conj), and temperedness. These are all available but connecting them
-- to the norm on PreHilbertSpace (defined via the Core) requires navigating the
-- InnerProductSpace.Core infrastructure.
/-- The map g ↦ ↑(singlePH n g) is continuous from SchwartzNPointSpace to GNSHilbertSpace.

    Mathematical proof: The map is linear, and ‖singlePH n h‖² = Re(W_{n+n}(h.conjTP h))
    which is continuous from SchwartzNPointSpace to ℝ (by temperedness of W and joint
    continuity of tensorProduct). A linear map from a Fréchet space with continuous norm
    at 0 is continuous. -/
-- Helper: borchersConj is continuous on Schwartz n-point space.
-- borchersConj = conj ∘ reverse. We construct it as a continuous ℝ-linear map
-- using compCLMOfContinuousLinearEquiv for reverse and the seminorm bound for conj.
private theorem borchersConj_continuous {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
  -- reverse = compCLMOfContinuousLinearEquiv with the Fin.rev equivalence
  let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := fun y i => y (Fin.rev i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y i => y (Fin.rev i)
      left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      continuous_toFun := by
        apply continuous_pi; intro i; exact continuous_apply (Fin.rev i)
      continuous_invFun := by
        apply continuous_pi; intro i; exact continuous_apply (Fin.rev i) }
  let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
  have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
    intro f; ext x; simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.reverse_apply, revCLE]
  -- conj is continuous (antilinear but ℝ-linear, preserves seminorms)
  -- We show the composition conj ∘ reverse is continuous
  have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
    -- conj is ℝ-linear and preserves seminorms
    let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzMap.conj
        map_add' := fun f g => by ext x; simp [SchwartzMap.conj_apply]
        map_smul' := fun c f => by ext x; simp [SchwartzMap.conj_apply] }
    exact Seminorm.continuous_from_bounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      conjL (fun q => by
        rcases q with ⟨k, l⟩
        refine ⟨{(k, l)}, 1, ?_⟩
        intro f
        simpa [Finset.sup_singleton] using SchwartzMap.seminorm_conj_le k l f)
  -- borchersConj = conj ∘ reverse is the composition of two continuous maps
  show Continuous (fun f => (revCLM f).conj)
  exact hconj_cont.comp revCLM.continuous |>.congr (fun f => by
    show (revCLM f).conj = f.borchersConj
    rw [hrev]; rfl)

private theorem single_embed_continuous (n : ℕ) :
    Continuous (fun g : SchwartzNPointSpace d n =>
      (singlePH Wfn n g : GNSHilbertSpace Wfn)) := by
  -- Use sequential continuity (Schwartz spaces are first countable)
  rw [continuous_iff_seqContinuous]
  intro u a hu
  -- Need: (singlePH n (u k) : GNSHilbertSpace) → (singlePH n a : GNSHilbertSpace)
  -- Equivalently: ‖coe(singlePH n (u k)) - coe(singlePH n a)‖ → 0
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 1: g ↦ g.conjTensorProduct g is continuous from SchwartzNPointSpace to itself
  have hconj_tp_cont : Continuous (fun g : SchwartzNPoint d n => g.conjTensorProduct g) :=
    SchwartzMap.tensorProduct_continuous.comp
      ((borchersConj_continuous (d := d)).prodMk continuous_id)
  -- Step 2: g ↦ W(n+n)(g.conjTP g) is continuous SchwartzNPoint → ℂ
  have hW_cont : Continuous (fun g : SchwartzNPoint d n =>
      Wfn.W (n + n) (g.conjTensorProduct g)) :=
    (Wfn.tempered (n + n)).comp hconj_tp_cont
  -- Step 3: (u k - a) → 0 in Schwartz
  have hv : Filter.Tendsto (fun k => u k - a) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun k => u k - a) Filter.atTop (nhds (a - a)) :=
      hu.sub tendsto_const_nhds
    rwa [sub_self] at this
  -- Step 4: W(n+n)((u k - a).conjTP (u k - a)) → W(n+n)(0.conjTP 0) = 0
  have hW_zero : Wfn.W (n + n) ((0 : SchwartzNPoint d n).conjTensorProduct 0) = 0 := by
    simp [(Wfn.linear _).map_zero]
  have hW_tends : Filter.Tendsto
      (fun k => Wfn.W (n + n) ((u k - a).conjTensorProduct (u k - a)))
      Filter.atTop (nhds 0) := by
    rw [← hW_zero]; exact hW_cont.continuousAt.tendsto.comp hv
  -- Step 5: ‖singlePH n h‖ = √(Re(W(n+n)(h.conjTP h)))
  have hnorm_eq : ∀ h : SchwartzNPoint d n,
      ‖singlePH Wfn n h‖ = Real.sqrt (Wfn.W (n + n) (h.conjTensorProduct h)).re := by
    intro h
    show Real.sqrt (@InnerProductSpace.Core.normSq ℂ _ _ _ _
      (instCore Wfn).toCore (singlePH Wfn n h)) = _
    congr 1
    show RCLike.re (PreHilbertSpace.innerProduct Wfn
      (singlePH Wfn n h) (singlePH Wfn n h)) = _
    -- inner product = WIP(single n h, single n h) = W(n+n)(h.conjTP h)
    show (WightmanInnerProduct d Wfn.W (BorchersSequence.single n h)
      (BorchersSequence.single n h)).re = _
    simp only [WightmanInnerProduct, BorchersSequence.single_bound]
    rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (by omega)) (fun i _ hi => by
      simp [BorchersSequence.single_funcs_ne hi, SchwartzMap.conjTensorProduct_zero_left,
        (Wfn.linear _).map_zero]),
      Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (by omega)) (fun j _ hj => by
      simp [BorchersSequence.single_funcs_ne hj, SchwartzMap.conjTensorProduct_zero_right,
        (Wfn.linear _).map_zero])]
    simp [BorchersSequence.single_funcs_eq]
  -- Step 6: By linearity, coe(singlePH n (u k)) - coe(singlePH n a) has norm
  -- = ‖singlePH n (u k - a)‖  (using singlePH_add, singlePH_smul, coe_add, coe_smul)
  have hdiff_norm : ∀ k, ‖(singlePH Wfn n (u k) : GNSHilbertSpace Wfn) -
      (singlePH Wfn n a : GNSHilbertSpace Wfn)‖ =
      ‖singlePH Wfn n (u k - a)‖ := by
    intro k
    have hsub : singlePH Wfn n (u k) - singlePH Wfn n a =
        singlePH Wfn n (u k - a) := by
      have h1 := singlePH_add Wfn n (u k) (-a)
      have h2 := singlePH_smul Wfn n (-1 : ℂ) a
      simp only [neg_smul, one_smul] at h2
      rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2]
    rw [show (singlePH Wfn n (u k) : GNSHilbertSpace Wfn) -
      (singlePH Wfn n a : GNSHilbertSpace Wfn) =
      ((singlePH Wfn n (u k) - singlePH Wfn n a : PreHilbertSpace Wfn) :
        GNSHilbertSpace Wfn) from by
      rw [UniformSpace.Completion.coe_sub],
      UniformSpace.Completion.norm_coe, hsub]
  -- Step 7: Re(W(...)) → 0
  have hRe_tends : Filter.Tendsto
      (fun k => (Wfn.W (n + n) ((u k - a).conjTensorProduct (u k - a))).re)
      Filter.atTop (nhds (0 : ℝ)) := by
    have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp hW_tends
    simp only [Complex.zero_re, Function.comp_def] at h; exact h
  -- Step 8: √(Re(W(...))) → 0
  have hSqrt_tends : Filter.Tendsto
      (fun k => Real.sqrt (Wfn.W (n + n) ((u k - a).conjTensorProduct (u k - a))).re)
      Filter.atTop (nhds 0) := by
    rw [← Real.sqrt_zero]
    exact (Real.continuous_sqrt.tendsto 0).comp hRe_tends
  -- Step 9: ‖singlePH n (u k - a)‖ → 0
  have hNorm_tends : Filter.Tendsto
      (fun k => ‖singlePH Wfn n (u k - a)‖) Filter.atTop (nhds 0) := by
    exact hSqrt_tends.congr (fun k => (hnorm_eq (u k - a)).symm)
  -- Step 10: dist(singlePH n (u k), singlePH n a) < ε eventually
  have hDist_tends : Filter.Tendsto
      (fun k => dist (singlePH Wfn n (u k) : GNSHilbertSpace Wfn)
        (singlePH Wfn n a : GNSHilbertSpace Wfn))
      Filter.atTop (nhds 0) := by
    refine hNorm_tends.congr (fun k => ?_)
    rw [dist_eq_norm, hdiff_norm]
  -- Convert dist(x, 0) < ε to the actual distance condition
  have := (Metric.tendsto_nhds.mp hDist_tends) ε hε
  exact this.mono (fun k hk => by
    simp only [Function.comp_apply]
    rwa [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg] at hk)

-- Helper: each pre-Hilbert element decomposes as a finite sum of single components.
-- The proof avoids raw Quotient.mk and works entirely with singlePH and mk_eq_of_funcs_eq.
private theorem quotient_eq_sum_singles (F : BorchersSequence d) :
    (Quotient.mk (borchersSetoid Wfn) F : PreHilbertSpace Wfn) =
    ∑ k ∈ Finset.range (F.bound + 1), singlePH Wfn k (F.funcs k) := by
  -- Auxiliary: for any Finset s containing the support, F decomposes as a sum of singles.
  suffices h : ∀ (s : Finset ℕ) (G : BorchersSequence d),
      (∀ k, k ∉ s → G.funcs k = 0) →
      (Quotient.mk (borchersSetoid Wfn) G : PreHilbertSpace Wfn) =
      ∑ k ∈ s, singlePH Wfn k (G.funcs k) from
    h (Finset.range (F.bound + 1)) F (fun k hk => F.bound_spec k (by
      simp only [Finset.mem_range, not_lt] at hk; omega))
  intro s
  induction s using Finset.cons_induction with
  | empty =>
    intro G hG
    -- All funcs are 0, so ⟦G⟧ = ⟦0⟧ = 0
    show (Quotient.mk (borchersSetoid Wfn) G : PreHilbertSpace Wfn) = _
    rw [Finset.sum_empty, show (0 : PreHilbertSpace Wfn) =
      Quotient.mk (borchersSetoid Wfn) (0 : BorchersSequence d) from rfl]
    exact mk_eq_of_funcs_eq Wfn G 0 (fun k => by simp [hG k (by simp)])
  | cons a s ha ih =>
    intro G hG
    rw [Finset.sum_cons]
    -- Split G into the a-th component and the rest
    let G' : BorchersSequence d := {
      funcs := fun k => if k = a then 0 else G.funcs k
      bound := max G.bound a
      bound_spec := fun k hk => by
        show (if k = a then (0 : SchwartzNPoint d k) else G.funcs k) = 0
        split
        · rfl
        · next hka => exact G.bound_spec k (by omega)
    }
    -- G' has support in s (not a)
    have hG'supp : ∀ k, k ∉ s → G'.funcs k = 0 := by
      intro k hk
      simp only [G']
      by_cases hka : k = a
      · simp [hka]
      · simp [hka]; exact hG k (fun hmem => (Finset.mem_cons.mp hmem).elim hka hk)
    -- ⟦G⟧ = ⟦G' + single a (G.funcs a)⟧ = ⟦G'⟧ + singlePH a (G.funcs a)
    -- We show: G and G' + single a (G.funcs a) have the same funcs
    have h_split : (Quotient.mk (borchersSetoid Wfn) G : PreHilbertSpace Wfn) =
        (Quotient.mk (borchersSetoid Wfn)
          (G' + BorchersSequence.single a (G.funcs a)) : PreHilbertSpace Wfn) :=
      mk_eq_of_funcs_eq Wfn G (G' + BorchersSequence.single a (G.funcs a)) (fun k => by
        simp only [BorchersSequence.add_funcs, G']
        by_cases hka : k = a
        · subst hka; simp [BorchersSequence.single_funcs_eq]
        · simp [hka])
    -- ⟦G' + single a ...⟧ = ⟦G'⟧ + ⟦single a ...⟧ by definition of instAdd
    -- (instAdd is Quotient.map₂, so Quotient.mk _ (A + B) = Quotient.mk _ A + Quotient.mk _ B)
    -- This is definitionally true since instAdd.add is Quotient.map₂
    rw [h_split]
    -- Goal: ⟦G' + single a (G.funcs a)⟧ = singlePH a (G.funcs a) + ∑ k ∈ s, singlePH k (G.funcs k)
    -- Apply IH to G'
    have hG'eq : (Quotient.mk (borchersSetoid Wfn) G' : PreHilbertSpace Wfn) =
        ∑ k ∈ s, singlePH Wfn k (G.funcs k) := by
      rw [show ∑ k ∈ s, singlePH Wfn k (G.funcs k) =
        ∑ k ∈ s, singlePH Wfn k (G'.funcs k) from
        Finset.sum_congr rfl (fun k hk => by
          show singlePH Wfn k (G.funcs k) = singlePH Wfn k (G'.funcs k)
          congr 1; show G.funcs k = if k = a then 0 else G.funcs k
          split
          · next h => subst h; exact absurd hk ha
          · rfl)]
      exact ih G' hG'supp
    -- Now combine: ⟦G' + single a ...⟧ = ⟦G'⟧ + singlePH a ... = (∑ s ...) + singlePH a ...
    show (Quotient.mk (borchersSetoid Wfn)
      (G' + BorchersSequence.single a (G.funcs a)) : PreHilbertSpace Wfn) =
      singlePH Wfn a (G.funcs a) + ∑ k ∈ s, singlePH Wfn k (G.funcs k)
    rw [← hG'eq]
    -- Goal: ⟦G' + single a (G.funcs a)⟧ = singlePH a (G.funcs a) + ⟦G'⟧
    -- This should hold by commutativity of + on PreHilbertSpace + the definitional equality
    -- ⟦A + B⟧ = ⟦A⟧ + ⟦B⟧
    rw [show (Quotient.mk (borchersSetoid Wfn)
      (G' + BorchersSequence.single a (G.funcs a)) : PreHilbertSpace Wfn) =
      (Quotient.mk (borchersSetoid Wfn)
        (BorchersSequence.single a (G.funcs a) + G') : PreHilbertSpace Wfn) from
      mk_eq_of_funcs_eq Wfn _ _ (fun k => by simp [BorchersSequence.add_funcs, add_comm])]
    rfl

theorem gns_cyclicity :
    Dense ((gnsOVD Wfn).algebraicSpan (gnsVacuum Wfn)).carrier := by
  -- Strategy: show (algebraicSpan)ᗮ = ⊥ via the orthogonal complement, then
  -- conclude density using Submodule.orthogonal_closure + orthogonal_eq_bot_iff.
  --
  -- Steps:
  -- 1. operatorPow n fs Ω = ↑(singlePH n (productTensor fs)) [operatorPow_eq_single]
  -- 2. z ⊥ (productTensor span) ⟹ z ⊥ all singles [nuclear density + continuity]
  -- 3. Every pre-Hilbert element decomposes as ∑ singles [quotient_eq_sum_singles]
  -- 4. z ⊥ range(coe) ⟹ z = 0 [Dense.eq_zero_of_inner_left]
  --
  -- single_embed_continuous (now proved) shows g ↦ ⟦single n g⟧ is continuous
  -- from the Schwartz space to PreHilbertSpace, using
  -- ‖⟦single n h⟧‖² = Re(W_{n+n}(h.conjTP h)) and temperedness of W.
  let S := (gnsOVD Wfn).algebraicSpan (gnsVacuum Wfn)
  change Dense (S : Set (GNSHilbertSpace Wfn))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff (K := S.topologicalClosure),
    Submodule.orthogonal_closure, Submodule.eq_bot_iff]
  intro z hz
  rw [Submodule.mem_orthogonal'] at hz
  -- Step 1: z ⊥ ↑(singlePH n (productTensor fs))
  have horth_prod : ∀ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
      @inner ℂ _ _ z (singlePH Wfn n (SchwartzMap.productTensor fs) :
        GNSHilbertSpace Wfn) = 0 := by
    intro n fs
    rw [← operatorPow_eq_single Wfn n fs]
    exact hz _ (Submodule.subset_span ⟨n, fs, rfl⟩)
  -- Step 2: z ⊥ ↑(singlePH n g) for ALL g (extend from product tensors by density)
  have horth_all_single : ∀ (n : ℕ) (g : SchwartzNPoint d n),
      @inner ℂ _ _ z (singlePH Wfn n g : GNSHilbertSpace Wfn) = 0 := by
    intro n
    -- The functional vanishes on the ℂ-span of product tensors
    have hL_span : ∀ h ∈ (Submodule.span ℂ
        {F : SchwartzNPointSpace d n |
          ∃ fs : Fin n → SchwartzSpacetime d, F = SchwartzMap.productTensor fs} :
        Set (SchwartzNPointSpace d n)),
        @inner ℂ _ _ z (singlePH Wfn n h : GNSHilbertSpace Wfn) = 0 := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem x hx => obtain ⟨fs, rfl⟩ := hx; exact horth_prod n fs
      | zero =>
        rw [show singlePH Wfn n 0 = (0 : PreHilbertSpace Wfn) from
          singlePH_zero (Wfn := Wfn) n,
          UniformSpace.Completion.coe_zero, inner_zero_right]
      | add x y _ _ ihx ihy =>
        rw [show singlePH Wfn n (x + y) = singlePH Wfn n x + singlePH Wfn n y from
          singlePH_add (Wfn := Wfn) n x y,
          UniformSpace.Completion.coe_add, inner_add_right, ihx, ihy, add_zero]
      | smul c x _ ih =>
        rw [show singlePH Wfn n (c • x) = c • singlePH Wfn n x from
          singlePH_smul (Wfn := Wfn) n c x,
          UniformSpace.Completion.coe_smul, inner_smul_right, ih, mul_zero]
    -- ⟨z, ↑(singlePH n ·)⟩ is continuous (inner product ∘ continuous embedding)
    have hL_cont : Continuous (fun g : SchwartzNPointSpace d n =>
        @inner ℂ _ _ z (singlePH Wfn n g : GNSHilbertSpace Wfn)) := by
      have h1 := single_embed_continuous (Wfn := Wfn) n
      have h2 : Continuous (fun w : GNSHilbertSpace Wfn => @inner ℂ _ _ z w) :=
        continuous_const.inner continuous_id
      exact h2.comp h1
    intro g
    exact congr_fun (Continuous.ext_on (productTensor_span_dense d n) hL_cont
      continuous_const (fun h hh => hL_span h hh)) g
  -- Step 3: z ⊥ ↑x for every pre-Hilbert element x
  have horth_all : ∀ x : PreHilbertSpace Wfn,
      @inner ℂ _ _ z (x : GNSHilbertSpace Wfn) = 0 := by
    intro x
    induction x using Quotient.inductionOn with | h F =>
    rw [quotient_eq_sum_singles Wfn F]
    -- Distribute coe over finite sum using coe_add induction, then use inner_sum.
    -- coe(∑ f_k) = ∑ coe(f_k) by induction on Finset using coe_add.
    have hcoe_sum : (↑(∑ k ∈ Finset.range (F.bound + 1), singlePH Wfn k (F.funcs k)) :
        GNSHilbertSpace Wfn) =
      ∑ k ∈ Finset.range (F.bound + 1),
        (singlePH Wfn k (F.funcs k) : GNSHilbertSpace Wfn) := by
      induction Finset.range (F.bound + 1) using Finset.cons_induction with
      | empty => simp [UniformSpace.Completion.coe_zero]
      | cons a s ha ih =>
        rw [Finset.sum_cons, UniformSpace.Completion.coe_add, Finset.sum_cons, ih]
    rw [hcoe_sum, inner_sum]
    exact Finset.sum_eq_zero (fun k _ => horth_all_single k (F.funcs k))
  -- Step 4: z = 0 by density of the pre-Hilbert space image in the completion.
  exact Dense.eq_zero_of_inner_left (𝕜 := ℂ) (gnsDomain_dense Wfn) (fun v hv => by
    obtain ⟨x, rfl⟩ := hv; exact horth_all x)

/-! ### Vacuum Uniqueness via Cluster Decomposition (Streater-Wightman, Theorem 3-5)

The vacuum uniqueness proof avoids Stone's theorem and spectral theory entirely.
It uses the cluster decomposition property (`Wfn.cluster`) directly:

1. Lift `Wfn.cluster` to the GNS inner product level (pre-Hilbert space)
2. Extend to the Hilbert space completion by density + unitarity
3. For Poincaré-invariant ψ: use invariance + clustering to show ψ ∝ Ω
-/

/-! ### Helper lemmas for cluster decomposition -/

/-- W(n+0)(f.conjTP vac₀) = W(n)(f.borchersConj): the vacuum conjTensorProduct from
    the right reduces to the borchersConj (up to the n+0 = n identification). -/
private theorem W_conjTP_vacuum_right (n : ℕ) (f : SchwartzNPoint d n) :
    Wfn.W (n + 0) (f.conjTensorProduct ((vacuumSequence (d := d)).funcs 0)) =
    Wfn.W n (f.borchersConj) := by
  apply W_eq_of_cast Wfn.W _ _ (Nat.add_zero n)
  intro x
  simp only [SchwartzMap.conjTensorProduct_apply]
  have hvac : ∀ y, (vacuumSequence (d := d)).funcs 0 y = 1 := fun _ => rfl
  rw [hvac, mul_one]
  simp only [SchwartzMap.borchersConj_apply, splitFirst]
  congr 1

/-- W(0+m)(vac₀.conjTP h) = W(m)(h): the vacuum conjTensorProduct from
    the left reduces to the function itself (up to the 0+m = m identification).
    Local copy of the private lemma in GNSConstruction.lean. -/
private theorem W_conjTP_vacuum_zero (m : ℕ) (h : SchwartzNPoint d m) :
    Wfn.W (0 + m) (((vacuumSequence (d := d)).funcs 0).conjTensorProduct h) = Wfn.W m h := by
  apply W_eq_of_cast Wfn.W _ _ (Nat.zero_add m)
  intro x
  simp only [SchwartzMap.conjTensorProduct_apply, splitFirst]
  have hvac : ∀ y, (vacuumSequence (d := d)).funcs 0 y = 1 := fun _ => rfl
  rw [hvac, map_one, one_mul]
  unfold splitLast
  congr 1; ext j; congr 1; ext; simp [Fin.val_cast]

/-- For a pure translation, the Poincaré action on n-point functions is a pointwise shift:
    (translation'(b) · g)(x) = g(x - b). -/
private theorem poincareActNPoint_translation_shift {m : ℕ}
    (b : SpacetimeDim d) (g : SchwartzNPoint d m) :
    ∀ x : NPointDomain d m,
      (poincareActNPoint (PoincareGroup.translation' b) g) x =
      g (fun i => x i - b) := by
  intro x
  simp only [poincareActNPoint_apply]
  -- Goal: g (poincareActNPointDomain (translation' b)⁻¹ x) = g (fun i => x i - b)
  congr 1; funext i
  -- Goal: poincareActNPointDomain (translation' b)⁻¹ x i = x i - b
  -- Definitionally: PoincareGroup.act (translation' b)⁻¹ (x i) = x i - b
  show PoincareGroup.act (PoincareGroup.translation' b)⁻¹ (x i) = x i - b
  rw [PoincareGroup.act_def]
  simp only [PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
    PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
    inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
  -- Goal: x i + -b = x i - b
  abel

omit [NeZero d] in
/-- For a purely spatial direction `a` with nonzero spatial part,
    the spatial norm `∑ i, ((r • a)(succ i))²` exceeds any bound for large `r`. -/
private theorem spatial_norm_smul_large (a : SpacetimeDim d)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0)
    (R : ℝ) (hR : R > 0) :
    ∃ N : ℝ, ∀ r : ℝ, r ≥ N →
      (∑ i : Fin d, ((r • a) (Fin.succ i)) ^ 2) > R ^ 2 := by
  -- Factor: (r • a)(succ i) = r * a(succ i), so ∑ = r² * S where S = ∑ (a(succ i))²
  set S := ∑ i : Fin d, (a (Fin.succ i)) ^ 2
  have hS_pos : 0 < S := by
    obtain ⟨j, hj⟩ := ha_nonzero
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, by positivity⟩
  have key : ∀ r : ℝ, ∑ i : Fin d, ((r • a) (Fin.succ i)) ^ 2 = r ^ 2 * S := by
    intro r
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum]
  refine ⟨R / Real.sqrt S + 1, fun r hr => ?_⟩
  rw [key]
  have hN_pos : 0 < R / Real.sqrt S + 1 := by positivity
  have hr_pos : 0 < r := lt_of_lt_of_le hN_pos hr
  have hRS : R / Real.sqrt S < r := by linarith
  calc r ^ 2 * S > (R / Real.sqrt S) ^ 2 * S := by
        apply mul_lt_mul_of_pos_right _ hS_pos
        exact sq_lt_sq' (by linarith [div_pos hR (Real.sqrt_pos.mpr hS_pos)]) hRS
    _ = R ^ 2 := by rw [div_pow, Real.sq_sqrt hS_pos.le]; field_simp

/-- Each (n,m)-term in the GNS inner product converges under spatial translation:
    W(n+m)(f ⊗ τ_{r·a} g) → W(n)(f) · W(m)(g) as r → ∞. -/
private theorem cluster_term_tendsto (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0) :
    Filter.Tendsto
      (fun r : ℝ => Wfn.W (n + m) (f.tensorProduct
        (poincareActNPoint (PoincareGroup.translation' (r • a)) g)))
      Filter.atTop
      (nhds (Wfn.W n f * Wfn.W m g)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR, hcluster⟩ := Wfn.cluster n m f g ε hε
  obtain ⟨N, hN⟩ := spatial_norm_smul_large a ha_nonzero R hR
  refine ⟨N, fun r hr => ?_⟩
  rw [Complex.dist_eq]
  have ha0_r : (r • a) 0 = 0 := by simp [Pi.smul_apply, ha0]
  have hR_r := hN r hr
  have hga := poincareActNPoint_translation_shift (r • a) g
  exact hcluster (r • a) ha0_r hR_r
    (poincareActNPoint (PoincareGroup.translation' (r • a)) g) hga

/-- ⟨F, Ω⟩ decomposes as ∑_n W(n)(F.funcs(n).borchersConj). -/
private theorem WIP_F_vacuum_eq_sum (F : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W F vacuumSequence =
    ∑ n ∈ Finset.range (F.bound + 1), Wfn.W n ((F.funcs n).borchersConj) := by
  simp only [WightmanInnerProduct]
  rw [show (vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  -- Use sum_congr to work inside each term of the outer sum (avoids expanding it)
  apply Finset.sum_congr rfl; intro n _
  -- Now only the inner sum over range 2 is present
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hv1 : (vacuumSequence (d := d)).funcs 1 = 0 := rfl
  rw [hv1, SchwartzMap.conjTensorProduct_zero_right, (Wfn.linear _).map_zero, add_zero]
  exact W_conjTP_vacuum_right Wfn n (F.funcs n)

/-- ⟨Ω, G⟩ decomposes as ∑_m W(m)(G.funcs(m)). -/
private theorem WIP_vacuum_G_eq_sum (G : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W vacuumSequence G =
    ∑ m ∈ Finset.range (G.bound + 1), Wfn.W m (G.funcs m) := by
  simp only [WightmanInnerProduct]
  rw [show (vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  -- Expand only the outer sum (range 2) using rw, not simp
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- Kill the n=1 term: vacuumSequence.funcs 1 = 0
  have hv1 : (vacuumSequence (d := d)).funcs 1 = 0 := rfl
  simp only [hv1, SchwartzMap.conjTensorProduct_zero_left,
    (Wfn.linear _).map_zero, Finset.sum_const_zero, add_zero]
  -- Remaining: ∑ m, W(0+m)(vac₀.conjTP (G.funcs m)) = ∑ m, W m (G.funcs m)
  apply Finset.sum_congr rfl; intro m _
  exact W_conjTP_vacuum_zero Wfn m (G.funcs m)

/-- **Hilbert-space cluster property (pre-Hilbert space).**

    For Borchers sequences F, G and a purely spatial direction a,
    ⟨F, U(λa)G⟩ → ⟨F, Ω⟩ · ⟨Ω, G⟩ as λ → ∞.

    Each (n,m) term in the GNS inner product is
      W_{n+m}(F.funcs(n).borchersConj ⊗ τ_{λa}(G.funcs(m)))
    Since `conjTensorProduct = borchersConj.tensorProduct`, `Wfn.cluster` applies
    to each term. The limit passes through the finite sum (bounded by F.bound
    and G.bound), and the factorized result reassembles as ⟨F, Ω⟩ · ⟨Ω, G⟩. -/
private theorem gns_cluster_preHilbert (F G : BorchersSequence d)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0) :
    Filter.Tendsto
      (fun r : ℝ => WightmanInnerProduct d Wfn.W F
        (poincareActBorchers (PoincareGroup.translation' (r • a)) G))
      Filter.atTop
      (nhds (WightmanInnerProduct d Wfn.W F vacuumSequence *
             WightmanInnerProduct d Wfn.W vacuumSequence G)) := by
  -- Step 1: Rewrite RHS vacuum inner products as explicit sums
  rw [WIP_F_vacuum_eq_sum Wfn F, WIP_vacuum_G_eq_sum Wfn G, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  -- Step 2: Unfold LHS inner product and conjTensorProduct to expose double sum
  simp only [WightmanInnerProduct, SchwartzMap.conjTensorProduct]
  -- Step 3: Pass the limit through the finite double sum
  apply tendsto_finset_sum; intro n _
  apply tendsto_finset_sum; intro m _
  -- Step 4: Each (n,m)-term converges by the cluster decomposition axiom
  exact cluster_term_tendsto Wfn n m (F.funcs n).borchersConj (G.funcs m) a ha0 ha_nonzero

/-- **Hilbert-space cluster property (completion).**

    Extends `gns_cluster_preHilbert` from pre-Hilbert vectors to the completion.
    For any pre-Hilbert vector Φ and completion vector ψ:
      ⟨Φ, U(λa)ψ⟩ → ⟨Φ, Ω⟩ · ⟨Ω, ψ⟩ as λ → ∞.

    Proof: approximate ψ by pre-Hilbert ⟦G⟧ within δ. By unitarity,
    |⟨Φ, U(λa)(ψ - ⟦G⟧)⟩| ≤ ‖Φ‖ · δ. The cluster property for ⟦G⟧
    handles the main term, and Cauchy–Schwarz bounds the remaining error. -/
private theorem gns_cluster_completion (Φ : PreHilbertSpace Wfn)
    (ψ : GNSHilbertSpace Wfn)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0) :
    Filter.Tendsto
      (fun r : ℝ => @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (r • a)) ψ))
      Filter.atTop
      (nhds (@inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
             @inner ℂ _ _ (gnsVacuum Wfn) ψ)) := by
  -- Step 0: Reduce Φ to a BorchersSequence representative
  induction Φ using Quotient.inductionOn with | h F =>
  -- Abbreviate the pre-Hilbert vectors (coerce with (pF : GNSHilbertSpace Wfn))
  set pF : PreHilbertSpace Wfn := ⟦F⟧
  -- Step 1: Unfold to ε-δ
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 2: Choose δ for approximation
  set C := ‖(pF : GNSHilbertSpace Wfn)‖ + ‖gnsVacuum Wfn‖ + 1
  have hC_pos : 0 < C := by positivity
  set δ := ε / (3 * C) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε (by positivity)
  -- Step 3: Approximate ψ by an embedded pre-Hilbert vector
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt ψ hδ_pos
  induction y using Quotient.inductionOn with | h G =>
  set pG : PreHilbertSpace Wfn := ⟦G⟧
  -- hy : dist (pG : GNSHilbertSpace Wfn) ψ < δ
  -- Step 4: Get N from the cluster property for F and G
  have h_cluster := gns_cluster_preHilbert Wfn F G a ha0 ha_nonzero
  rw [Metric.tendsto_atTop] at h_cluster
  obtain ⟨N, hN⟩ := h_cluster (ε / 3) (by linarith)
  -- Step 5: The same N works
  refine ⟨N, fun r hr => ?_⟩
  set Ug := poincareActGNS Wfn (PoincareGroup.translation' (r • a))
  -- (A) Cluster error on G: bridge to WightmanInnerProduct and apply hN
  have h_clust : dist
      (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn)))
      (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
       @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn)) < ε / 3 := by
    have h1 : @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn)) =
        WightmanInnerProduct d Wfn.W F
          (poincareActBorchers (PoincareGroup.translation' (r • a)) G) := by
      rw [show Ug (pG : GNSHilbertSpace Wfn) =
          ((poincareActPreHilbert Wfn (PoincareGroup.translation' (r • a)) pG :
            PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) from
          poincareActGNS_coe Wfn _ pG,
        UniformSpace.Completion.inner_coe]; rfl
    have h2 : @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) =
        WightmanInnerProduct d Wfn.W F vacuumSequence := by
      show @inner ℂ _ _ (pF : GNSHilbertSpace Wfn)
        ((vacuumState Wfn : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) = _
      rw [UniformSpace.Completion.inner_coe]; rfl
    have h3 : @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) =
        WightmanInnerProduct d Wfn.W vacuumSequence G := by
      show @inner ℂ _ _ ((vacuumState Wfn : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn)
        (pG : GNSHilbertSpace Wfn) = _
      rw [UniformSpace.Completion.inner_coe]; rfl
    rw [h1, h2, h3]; exact hN r hr
  -- Helper: ‖↑pF‖ ≤ C
  have hpF_le_C : ‖(pF : GNSHilbertSpace Wfn)‖ ≤ C := by
    linarith [norm_nonneg (gnsVacuum Wfn)]
  -- Helper: C * δ = ε / 3
  have hCδ : C * δ = ε / 3 := by
    rw [hδ_def]; field_simp
  -- (B) Action error: ‖⟨↑pF, Ug ψ⟩ - ⟨↑pF, Ug ↑pG⟩‖ < ε/3
  have h_err_action : ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug ψ) -
      @inner ℂ _ _ (pF : GNSHilbertSpace Wfn)
        (Ug (pG : GNSHilbertSpace Wfn))‖ < ε / 3 := by
    rw [← inner_sub_right,
      show Ug ψ - Ug (pG : GNSHilbertSpace Wfn) = Ug (ψ - (pG : GNSHilbertSpace Wfn)) from
        (Ug.map_sub ψ (pG : GNSHilbertSpace Wfn)).symm]
    calc ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn)
            (Ug (ψ - (pG : GNSHilbertSpace Wfn)))‖
        ≤ ‖(pF : GNSHilbertSpace Wfn)‖ *
          ‖Ug (ψ - (pG : GNSHilbertSpace Wfn))‖ := norm_inner_le_norm _ _
      _ = ‖(pF : GNSHilbertSpace Wfn)‖ *
          ‖ψ - (pG : GNSHilbertSpace Wfn)‖ := by rw [poincareActGNS_norm]
      _ = ‖(pF : GNSHilbertSpace Wfn)‖ * dist ψ (pG : GNSHilbertSpace Wfn) := by
          rw [dist_eq_norm]
      _ ≤ C * dist ψ (pG : GNSHilbertSpace Wfn) :=
          mul_le_mul_of_nonneg_right hpF_le_C dist_nonneg
      _ < C * δ := mul_lt_mul_of_pos_left hy hC_pos
      _ = ε / 3 := hCδ
  -- (C) Limit error: ‖⟨↑pF, Ω⟩ * ⟨Ω, ↑pG⟩ - ⟨↑pF, Ω⟩ * ⟨Ω, ψ⟩‖ < ε/3
  have h_err_limit :
      ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
        @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) -
       @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
        @inner ℂ _ _ (gnsVacuum Wfn) ψ‖ < ε / 3 := by
    rw [show @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) -
        @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) ψ =
        @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
        (@inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) -
         @inner ℂ _ _ (gnsVacuum Wfn) ψ) from by ring]
    rw [norm_mul, ← inner_sub_right]
    calc ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn)‖ *
          ‖@inner ℂ _ _ (gnsVacuum Wfn) ((pG : GNSHilbertSpace Wfn) - ψ)‖
        ≤ ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn)‖ *
          (‖gnsVacuum Wfn‖ * ‖(pG : GNSHilbertSpace Wfn) - ψ‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ (‖(pF : GNSHilbertSpace Wfn)‖ * ‖gnsVacuum Wfn‖) *
          (‖gnsVacuum Wfn‖ * ‖(pG : GNSHilbertSpace Wfn) - ψ‖) :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (by positivity)
      _ = ‖(pF : GNSHilbertSpace Wfn)‖ * (‖gnsVacuum Wfn‖ ^ 2 *
          ‖(pG : GNSHilbertSpace Wfn) - ψ‖) := by rw [sq]; ring
      _ ≤ ‖(pF : GNSHilbertSpace Wfn)‖ * (1 * dist ψ (pG : GNSHilbertSpace Wfn)) := by
          have h1 : ‖gnsVacuum Wfn‖ = 1 := gnsVacuum_norm Wfn
          rw [h1, one_pow, one_mul, one_mul, ← dist_eq_norm, dist_comm]
      _ = ‖(pF : GNSHilbertSpace Wfn)‖ * dist ψ (pG : GNSHilbertSpace Wfn) := by ring
      _ ≤ C * dist ψ (pG : GNSHilbertSpace Wfn) :=
          mul_le_mul_of_nonneg_right hpF_le_C dist_nonneg
      _ < C * δ := mul_lt_mul_of_pos_left hy hC_pos
      _ = ε / 3 := hCδ
  -- Step 6: Combine by triangle inequality
  rw [Complex.dist_eq]
  calc ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug ψ) -
        @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
        @inner ℂ _ _ (gnsVacuum Wfn) ψ‖
      = ‖(@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug ψ) -
          @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn))) +
        (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn)) -
          @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn)) +
        (@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) -
         @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) ψ)‖ := by ring_nf
    _ ≤ ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug ψ) -
          @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn))‖ +
        ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn)) -
          @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn)‖ +
        ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn) -
         @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
          @inner ℂ _ _ (gnsVacuum Wfn) ψ‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h_mid :
            ‖@inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (Ug (pG : GNSHilbertSpace Wfn)) -
             @inner ℂ _ _ (pF : GNSHilbertSpace Wfn) (gnsVacuum Wfn) *
             @inner ℂ _ _ (gnsVacuum Wfn) (pG : GNSHilbertSpace Wfn)‖ < ε / 3 := by
          rw [← Complex.dist_eq]; exact h_clust
        linarith [h_err_action, h_err_limit, h_mid]
    _ = ε := by ring

/-- **Vacuum uniqueness in the GNS Hilbert space** (Streater-Wightman, Thm 3-5).

    Any Poincaré-invariant vector is proportional to the vacuum. The proof
    uses the cluster decomposition property directly, avoiding Stone's theorem.

    For invariant ψ and any pre-Hilbert Φ, the function λ ↦ ⟨Φ, U(λa)ψ⟩ is
    constant (= ⟨Φ, ψ⟩) by invariance, and converges to ⟨Φ, Ω⟩ · ⟨Ω, ψ⟩
    by clustering. Uniqueness of limits gives ⟨Φ, ψ⟩ = ⟨Φ, ⟨Ω,ψ⟩ • Ω⟩
    for all Φ in a dense set, so ψ = ⟨Ω, ψ⟩ • Ω. -/
theorem gns_vacuum_unique_of_poincare_invariant (ψ : GNSHilbertSpace Wfn)
    (h : IsPoincareInvariant d (gnsPoincareRep Wfn) ψ) :
    ∃ c : ℂ, ψ = c • gnsVacuum Wfn := by
  -- Set c := ⟨Ω, ψ⟩
  refine ⟨@inner ℂ _ _ (gnsVacuum Wfn) ψ, ?_⟩
  set c := @inner ℂ _ _ (gnsVacuum Wfn) ψ
  -- Pick a nonzero purely spatial direction e₁ = (0, 1, 0, ..., 0)
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let a : SpacetimeDim d := fun i => if (i : ℕ) = 1 then 1 else 0
  have ha0 : a 0 = 0 := if_neg (by simp)
  have ha_nz : ∃ i : Fin d, a (Fin.succ i) ≠ 0 :=
    ⟨⟨0, hd_pos⟩, by show a (Fin.succ ⟨0, hd_pos⟩) ≠ 0; simp [a]; omega⟩
  -- Step 1: ⟨Φ, ψ⟩ = ⟨Φ, c • Ω⟩ for all pre-Hilbert Φ (invariance + cluster)
  have hfactor : ∀ Φ : PreHilbertSpace Wfn,
      @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) ψ =
      @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (c • gnsVacuum Wfn) := by
    intro Φ
    -- Cluster: λ ↦ ⟨Φ, U(λa)ψ⟩ → ⟨Φ, Ω⟩ * c
    have h_cluster := gns_cluster_completion Wfn Φ ψ a ha0 ha_nz
    -- Invariance: U(λa)ψ = ψ, so the function is constant
    have h_eq : (fun (r : ℝ) => @inner ℂ _ _ (↑Φ : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (r • a)) ψ)) =
        fun _ => @inner ℂ _ _ (↑Φ : GNSHilbertSpace Wfn) ψ := by
      ext r; congr 1; exact h (PoincareGroup.translation' (r • a))
    rw [h_eq] at h_cluster
    -- Uniqueness of limits in T₂ space: constant value = cluster limit
    have heq := tendsto_nhds_unique tendsto_const_nhds h_cluster
    -- heq : ⟨Φ, ψ⟩ = ⟨Φ, Ω⟩ * c;  goal : ⟨Φ, ψ⟩ = c * ⟨Φ, Ω⟩ (= ⟨Φ, c•Ω⟩)
    rw [heq, inner_smul_right, mul_comm]
  -- Step 2: ψ = c • Ω by density of pre-Hilbert space in the completion
  suffices h_zero : ψ - c • gnsVacuum Wfn = 0 from eq_of_sub_eq_zero h_zero
  rw [← @inner_self_eq_zero ℂ]
  -- Show ⟨x, ψ - c•Ω⟩ = 0 for all x by density, then specialize to x = ψ - c•Ω
  suffices h_ortho : ∀ x : GNSHilbertSpace Wfn,
      @inner ℂ _ _ x (ψ - c • gnsVacuum Wfn) = 0 from h_ortho _
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
      continuous_const
  · intro Φ
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (hfactor Φ)

/-- The Wightman QFT reconstructed from Wightman functions.
    The key result is that the Wightman functions are correctly reproduced.
    The domain is the image of the pre-Hilbert space (dense in the completion).

    The three remaining gaps are isolated in helper lemmas:
    * `gns_spectrum_condition` — spectrum condition (deferred)
    * `gns_cyclicity` — cyclicity (needs Schwartz nuclear theorem)
    * `gns_vacuum_unique_of_poincare_invariant` — vacuum uniqueness (via cluster decomposition) -/
noncomputable def gnsQFT : WightmanQFT d where
  HilbertSpace := GNSHilbertSpace Wfn
  poincare_rep := gnsPoincareRep Wfn
  spectrum_condition := gns_spectrum_condition Wfn
  vacuum := gnsVacuum Wfn
  vacuum_normalized := gnsVacuum_norm Wfn
  vacuum_invariant := gnsVacuum_poincare_invariant Wfn
  field := gnsOVD Wfn
  vacuum_in_domain := gnsVacuum_in_domain Wfn
  cyclicity := gns_cyclicity Wfn
  poincareActionOnSchwartz := poincareActSchwartz
  poincareAction_spec := fun g f x => poincareActSchwartz_toFun g f x
  covariance := fun g f χ ψ hχ hψ => by
    obtain ⟨x, rfl⟩ := hχ; obtain ⟨y, rfl⟩ := hψ
    have hUx : (gnsPoincareRep Wfn).U g (↑x : GNSHilbertSpace Wfn) =
        (↑(poincareActPreHilbert Wfn g x) : GNSHilbertSpace Wfn) :=
      poincareActGNS_coe Wfn g x
    have hUy : (gnsPoincareRep Wfn).U g (↑y : GNSHilbertSpace Wfn) =
        (↑(poincareActPreHilbert Wfn g y) : GNSHilbertSpace Wfn) :=
      poincareActGNS_coe Wfn g y
    rw [hUy, hUx]
    have h : ⟪(↑(poincareActPreHilbert Wfn g x) : GNSHilbertSpace Wfn),
        gnsFieldOp Wfn f ↑(poincareActPreHilbert Wfn g y)⟫_ℂ =
      ⟪(↑x : GNSHilbertSpace Wfn),
        gnsFieldOp Wfn (poincareActSchwartz g⁻¹ f) ↑y⟫_ℂ := by
      rw [gnsFieldOp_coe Wfn f (poincareActPreHilbert Wfn g y),
        covariance_preHilbert Wfn g f y,
        ← poincareActGNS_coe Wfn g (fieldOperator Wfn (poincareActSchwartz g⁻¹ f) y),
        ← poincareActGNS_coe Wfn g x,
        poincareActGNS_inner Wfn g,
        ← gnsFieldOp_coe Wfn (poincareActSchwartz g⁻¹ f) y]
    exact h
  field_hermitian := fun f χ ψ hχ hψ => by
    obtain ⟨x, rfl⟩ := hχ; obtain ⟨y, rfl⟩ := hψ
    show ⟪gnsFieldOp Wfn f ↑x, ↑y⟫_ℂ = ⟪↑x, gnsFieldOp Wfn (SchwartzMap.conj f) ↑y⟫_ℂ
    exact Quotient.inductionOn₂ x y (fun F G => by
      rw [gnsFieldOp_coe, gnsFieldOp_coe,
        UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
      exact field_adjoint Wfn f F G)
  locality := fun f g hfg ψ hψ => by
    obtain ⟨x, rfl⟩ := hψ
    show gnsFieldOp Wfn f (gnsFieldOp Wfn g (↑x)) = gnsFieldOp Wfn g (gnsFieldOp Wfn f (↑x))
    rw [gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe]
    congr 1
    exact Quotient.inductionOn x (fun F =>
      Quotient.sound (locality_setoid Wfn f g hfg F))
  vacuum_unique :=
    ⟨gnsVacuum_poincare_invariant Wfn,
    gns_vacuum_unique_of_poincare_invariant Wfn⟩

/-- The reconstructed QFT's field operatorPow applied to the vacuum gives
    the iterated field operator from the pre-Hilbert space, embedded in
    the completion. -/
theorem operatorPow_gnsQFT_eq (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    (gnsQFT Wfn).field.operatorPow n fs (gnsVacuum Wfn) =
    ((List.foldr (fun f acc => fieldOperator Wfn f acc)
      (vacuumState Wfn) (List.ofFn fs) : PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OperatorValuedDistribution.operatorPow]
    rw [ih (fun i => fs (Fin.succ i))]
    show gnsFieldOp Wfn (fs 0)
      ↑(List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fun i => fs i.succ)) =
      ↑(List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fs))
    rw [gnsFieldOp_coe Wfn (fs 0)]
    simp only [List.ofFn_succ, List.foldr_cons]

/-- **Wightman Reconstruction Theorem**: Given a collection of Wightman functions
    satisfying all the Wightman axioms, there exists a Wightman QFT whose
    n-point functions reproduce the given Wightman functions on product test functions.

    The Hilbert space is constructed via the GNS construction:
    1. Form the Borchers algebra of test function sequences
    2. Define the inner product from the Wightman 2-point function
    3. Quotient by null vectors to get the pre-Hilbert space
    4. Complete to obtain the Hilbert space
    5. Field operators act by prepending test functions to sequences -/
theorem wightman_reconstruction' :
    ∃ (qft : WightmanQFT.{0} d),
      ∀ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
        qft.wightmanFunction n fs = Wfn.W n (SchwartzMap.productTensor fs) := by
  refine ⟨gnsQFT Wfn, fun n fs => ?_⟩
  -- The wightmanFunction unfolds to ⟪vacuum, operatorPow n fs vacuum⟫
  -- which is ⟪gnsVacuum, operatorPow n fs gnsVacuum⟫
  unfold WightmanQFT.wightmanFunction
  -- Step 1: operatorPow matches iterated fieldOperator
  have hop := operatorPow_gnsQFT_eq Wfn n fs
  -- (gnsQFT Wfn).field.operatorPow n fs (gnsVacuum Wfn) = ↑(List.foldr ...)
  -- Since (gnsQFT Wfn).vacuum = gnsVacuum Wfn by definition:
  conv_lhs => rw [show (gnsQFT Wfn).vacuum = gnsVacuum Wfn from rfl]
  rw [hop]
  -- Step 2: inner product on completion agrees with pre-Hilbert inner product
  rw [show (gnsVacuum Wfn : GNSHilbertSpace Wfn) =
    (vacuumState Wfn : GNSHilbertSpace Wfn) from rfl]
  rw [UniformSpace.Completion.inner_coe]
  -- Step 3: pre-Hilbert inner product gives Wightman function
  exact gns_reproduces_wightman Wfn n fs

end
