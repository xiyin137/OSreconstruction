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

noncomputable section

open Reconstruction
open scoped InnerProductSpace

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

/-- The Wightman QFT reconstructed from Wightman functions.
    The key result is that the Wightman functions are correctly reproduced.
    The domain is the image of the pre-Hilbert space (dense in the completion).
    Remaining sorrys: spectrum condition, cyclicity, vacuum uniqueness. -/
noncomputable def gnsQFT : WightmanQFT d where
  HilbertSpace := GNSHilbertSpace Wfn
  poincare_rep := gnsPoincareRep Wfn
  -- Spectrum condition requires Stone's theorem (one-parameter unitary groups ↔ self-adjoint
  -- generators) and spectral theory for unbounded operators, neither of which are in Mathlib.
  -- The proof would connect the Wightman functions' forward tube analyticity to the operator
  -- spectral measure via: forward tube analyticity ⟹ Fourier support in forward cone
  -- ⟹ σ(P) ⊆ V̄₊ ⟹ energy_nonneg and mass_shell.
  spectrum_condition := sorry
  vacuum := gnsVacuum Wfn
  vacuum_normalized := gnsVacuum_norm Wfn
  vacuum_invariant := gnsVacuum_poincare_invariant Wfn
  field := {
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
      obtain ⟨x₁, hx₁⟩ := hψ₁
      obtain ⟨x₂, hx₂⟩ := hψ₂
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
  }
  vacuum_in_domain := gnsVacuum_in_domain Wfn
  -- Cyclicity requires the Schwartz nuclear theorem: finite tensor products
  -- f₁(x₁)···fₙ(xₙ) are dense in the n-point Schwartz space S(ℝ^{nd}).
  -- This is used to show that vectors φ(f₁)···φ(fₙ)Ω (whose n-th Borchers component
  -- is productTensor [f₁,...,fₙ]) span all of PreHilbertSpace in the Wightman norm.
  -- The nuclear theorem is not in Mathlib.
  cyclicity := sorry
  poincareActionOnSchwartz := poincareActSchwartz
  poincareAction_spec := fun g f x => poincareActSchwartz_toFun g f x
  covariance := fun g f χ ψ hχ hψ => by
    obtain ⟨x, rfl⟩ := hχ; obtain ⟨y, rfl⟩ := hψ
    -- Bridge U(g) terms: (gnsPoincareRep Wfn).U g ↑z = ↑(poincareActPreHilbert Wfn g z)
    have hUx : (gnsPoincareRep Wfn).U g (↑x : GNSHilbertSpace Wfn) =
        (↑(poincareActPreHilbert Wfn g x) : GNSHilbertSpace Wfn) :=
      poincareActGNS_coe Wfn g x
    have hUy : (gnsPoincareRep Wfn).U g (↑y : GNSHilbertSpace Wfn) =
        (↑(poincareActPreHilbert Wfn g y) : GNSHilbertSpace Wfn) :=
      poincareActGNS_coe Wfn g y
    rw [hUy, hUx]
    -- Goal: ⟪↑(U_pre g x), φ(f)(↑(U_pre g y))⟫ = ⟪↑x, φ(g⁻¹·f)(↑y)⟫
    -- where {anon}.operator is definitionally gnsFieldOp Wfn
    -- Construct proof with explicit gnsFieldOp, then exact handles defEq
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
  locality := fun f g hfg ψ hψ => by
    obtain ⟨x, rfl⟩ := hψ
    show gnsFieldOp Wfn f (gnsFieldOp Wfn g (↑x)) = gnsFieldOp Wfn g (gnsFieldOp Wfn f (↑x))
    rw [gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe, gnsFieldOp_coe]
    congr 1
    exact Quotient.inductionOn x (fun F =>
      Quotient.sound (locality_setoid Wfn f g hfg F))
  vacuum_unique :=
    -- Part 1: Time-translation invariance follows from full Poincaré invariance
    ⟨fun t => gnsVacuum_poincare_invariant Wfn _,
    -- Part 2: Uniqueness (any time-translation-invariant vector is ∝ Ω)
    -- This requires spectral theory: Stone's theorem gives H = P₀ as self-adjoint
    -- generator of time translations, spectrum condition gives σ(H) ⊆ [0,∞),
    -- and time-translation invariance ⟹ Hψ = 0 ⟹ ψ ∈ ker(H) = ℂ·Ω.
    sorry⟩

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
