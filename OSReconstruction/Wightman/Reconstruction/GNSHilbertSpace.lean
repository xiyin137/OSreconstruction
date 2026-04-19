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
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import OSReconstruction.Wightman.NuclearSpaces.BochnerMinlos
import OSReconstruction.GeneralResults.SchwartzFubini

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

/-! ### Spectrum condition and remaining GNS properties

* `gns_spectrum_condition` — PROVED (via SpectralConditionDistribution)
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
    (fun n => let ⟨W_an, hDiff, _, hBV⟩ := Wfn.spectrum_condition n
      ⟨W_an, hDiff, hBV⟩)

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
theorem bochner_uniqueness_real (μ₁ μ₂ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ₁] [MeasureTheory.IsFiniteMeasure μ₂]
    (h : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂μ₁ =
                    ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂μ₂) :
    μ₁ = μ₂ := by
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply_real]
  -- charFun gives ∫ x, cexp (↑t * ↑x * I) ∂μ; hypothesis gives ∫ x, exp (I * ↑t * ↑x) ∂μ.
  -- These differ only by commutativity of complex multiplication.
  simp_rw [show ∀ (x : ℝ), (↑t : ℂ) * (↑x : ℂ) * Complex.I =
    Complex.I * (↑t : ℂ) * (↑x : ℂ) from fun x => by ring]
  exact h t

/-- **Bochner's theorem** (multi-dimensional). Every continuous positive-definite
    function on `ℝⁿ` is the Fourier-Stieltjes transform of a unique finite positive
    Borel measure.

    **Ref:** Reed-Simon I, Theorem IX.9; Rudin, *Fourier Analysis on Groups*, §1.4.3. -/
theorem bochner_finiteMeasure {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (hcont : Continuous φ)
    (hpd : IsPositiveDefiniteFn φ) :
    ∃ (μ : MeasureTheory.Measure (Fin n → ℝ)),
      MeasureTheory.IsFiniteMeasure μ ∧
      ∀ x, φ x = ∫ p, Complex.exp (↑(∑ i : Fin n, x i * p i) * Complex.I) ∂μ := by
  by_cases hφ0 : φ 0 = 0
  · -- φ ≡ 0 by |φ(x)| ≤ φ(0).re = 0; zero measure works
    refine ⟨0, inferInstance, fun x => ?_⟩
    have hzero : φ x = 0 := by
      have h := hpd.norm_le_eval_zero x
      simp only [hφ0, Complex.zero_re] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    simp [hzero]
  · -- φ(0) is a positive real. Normalize ψ = φ / φ(0), apply bochner_existence, scale.
    have hφ0_im : (φ 0).im = 0 := hpd.eval_zero_im
    have hφ0_re_pos : 0 < (φ 0).re := by
      rcases eq_or_lt_of_le hpd.eval_zero_nonneg with h | h
      · exfalso; apply hφ0
        apply Complex.ext_iff.mpr
        exact ⟨by simp only [Complex.zero_re]; linarith, hφ0_im⟩
      · exact h
    set a := (φ 0).re with ha_def
    have ha_pos : (0 : ℝ) < a := hφ0_re_pos
    have hφ0_eq : φ 0 = (↑a : ℂ) := by
      apply Complex.ext_iff.mpr
      exact ⟨rfl, by simp [hφ0_im, Complex.ofReal_im]⟩
    -- ψ = φ / a
    set ψ : (Fin n → ℝ) → ℂ := fun t => φ t * (↑a)⁻¹
    have hψ_cont : Continuous ψ := hcont.mul_const _
    have hψ0 : ψ 0 = 1 := by
      simp only [ψ, hφ0_eq]
      rw [mul_inv_cancel₀]
      exact_mod_cast ha_pos.ne'
    have hψ_pd : IsPositiveDefiniteFn ψ := by
      intro m x c
      simp only [ψ]
      have h_factor : (∑ i : Fin m, ∑ j : Fin m,
          starRingEnd ℂ (c i) * c j * (φ (x j - x i) * (↑a)⁻¹)) =
          (∑ i : Fin m, ∑ j : Fin m,
          starRingEnd ℂ (c i) * c j * φ (x j - x i)) * (↑a)⁻¹ := by
        conv_lhs =>
          arg 2; ext i; arg 2; ext j
          rw [show starRingEnd ℂ (c i) * c j * (φ (x j - x i) * (↑a)⁻¹) =
            starRingEnd ℂ (c i) * c j * φ (x j - x i) * (↑a)⁻¹ from by ring]
        simp_rw [← Finset.sum_mul]
      rw [h_factor, show (↑a : ℂ)⁻¹ = (↑(a⁻¹) : ℂ) from by push_cast; rfl]
      obtain ⟨him, hre⟩ := hpd m x c
      exact ⟨by simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, him,
                  mul_zero, zero_mul, add_zero],
             by simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, him,
                  mul_zero, sub_zero]
                exact mul_nonneg hre (le_of_lt (inv_pos.mpr ha_pos))⟩
    obtain ⟨μ, hμ_prob, hμ_cf⟩ := bochner_existence ψ hψ_cont hψ_pd hψ0
    refine ⟨a.toNNReal • μ, inferInstance, fun x => ?_⟩
    have hφ_eq : φ x = ↑a * ψ x := by
      simp only [ψ]
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha_pos.ne'), mul_one]
    rw [hφ_eq, hμ_cf x]
    -- ↑a * ∫ ... ∂μ = ∫ ... ∂(a.toNNReal • μ)
    have hsmul : a.toNNReal • μ = (a.toNNReal : ENNReal) • μ := rfl
    symm
    rw [hsmul, MeasureTheory.integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
    congr 1
    exact_mod_cast Real.coe_toNNReal a ha_pos.le

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

/-- Integrability of a per-(n,m) summand in the WIP expansion multiplied by a Schwartz
    function. The function `t ↦ W_{n+m}(fₙ*.conjTP(τ_{te₀} fₘ))` is continuous and of
    tempered growth (bounded by Schwartz seminorms that grow polynomially under translation).
    The product with any Schwartz function is therefore integrable. -/
private lemma scd_summand_integrable
    {n m : ℕ} (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (ψ : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) *
      (ψ : ℝ → ℂ) t) := by
  -- The first factor t ↦ W(n+m)(fn.conjTP(τ_t fm)) is continuous.
  have hcont : Continuous (fun t : ℝ =>
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm))) :=
    (Wfn.tempered (n + m)).comp
      ((SchwartzMap.conjTensorProduct_continuous_right fn).comp
        (continuous_translate_npoint_schwartz 0 fm))
  -- GNS vectors for the Cauchy-Schwarz bound.
  set F : PreHilbertSpace Wfn := ⟦BorchersSequence.single n fn⟧
  set G : PreHilbertSpace Wfn := ⟦BorchersSequence.single m fm⟧
  set C := ‖(F : GNSHilbertSpace Wfn)‖ * ‖(G : GNSHilbertSpace Wfn)‖
  -- The first factor equals ⟪F, U(τ_t)G⟫ in GNS, hence ‖h(t)‖ ≤ ‖F‖·‖G‖.
  have hbound : ∀ t : ℝ, ‖Wfn.W (n + m) (fn.conjTensorProduct
      (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm))‖ ≤ C := by
    intro t
    set τt := PoincareRepresentation.translationInDirection d 0 t
    -- Chain: h(t) = WIP(single n fn, single m (τ_t fm))
    --            = inner_pre(F, ⟦single m (τ_t fm)⟧)
    --            = inner_pre(F, poincareActPreHilbert(τ_t)(G))
    --            = inner_GNS(F, U(τ_t)G)
    have h_eq : Wfn.W (n + m) (fn.conjTensorProduct (poincareActNPoint τt fm)) =
        @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
          (poincareActGNS Wfn τt (G : GNSHilbertSpace Wfn)) := by
      -- h(t) = WIP(single n fn, single m (τ_t fm))
      rw [← WightmanInnerProduct_single_single d Wfn.W Wfn.linear n m fn
        (poincareActNPoint τt fm)]
      -- WIP = inner_pre(F, ⟦single m (τ_t fm)⟧)
      rw [← inner_eq Wfn (BorchersSequence.single n fn)
        (BorchersSequence.single m (poincareActNPoint τt fm))]
      -- ⟦single m (τ_t fm)⟧ = poincareActPreHilbert(τ_t)(G)
      have h_q : (⟦BorchersSequence.single m (poincareActNPoint τt fm)⟧ :
          PreHilbertSpace Wfn) = poincareActPreHilbert Wfn τt G := by
        show _ = ⟦poincareActBorchers τt (BorchersSequence.single m fm)⟧
        exact (mk_eq_of_funcs_eq Wfn _ _ (fun n' => by
          by_cases h : n' = m
          · subst h; simp [poincareActBorchers]
          · simp [poincareActBorchers, BorchersSequence.single_funcs_ne h, poincareActNPoint_zero])).symm
      rw [h_q]
      -- inner_pre(F, poincareActPreHilbert(τ_t)(G)) = inner_GNS(F, U(τ_t)G)
      exact (inner_translate_eq_wip Wfn 0 F G t).symm
    -- Cauchy-Schwarz + unitarity
    rw [h_eq]
    calc ‖@inner ℂ _ _ (F : GNSHilbertSpace Wfn)
            (poincareActGNS Wfn τt (G : GNSHilbertSpace Wfn))‖
        ≤ ‖(F : GNSHilbertSpace Wfn)‖ *
          ‖poincareActGNS Wfn τt (G : GNSHilbertSpace Wfn)‖ :=
          norm_inner_le_norm _ _
      _ = C := by rw [poincareActGNS_norm]
  -- Integrability: bounded × Schwartz is L¹.
  exact (ψ.integrable.norm.const_mul C).mono'
    (hcont.mul ψ.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))

/-- The Fourier integral `∫ ℱ[φ](t) dt = φ(0)`, by Fourier inversion at the origin. -/
private lemma integral_fourierTransform_eq_apply_zero
    (φ : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, ((SchwartzMap.fourierTransformCLM ℂ φ) : ℝ → ℂ) t = (φ : ℝ → ℂ) 0 := by
  set g := SchwartzMap.fourierTransformCLM ℂ φ with hg_def
  have hinv : FourierTransform.fourierInv (g : ℝ → ℂ) = (φ : ℝ → ℂ) := by
    have h := congrArg (fun (f : SchwartzMap ℝ ℂ) => (f : ℝ → ℂ))
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) φ)
    dsimp only at h
    rwa [SchwartzMap.fourierInv_coe] at h
  have h_fi_zero : FourierTransform.fourierInv (g : ℝ → ℂ) 0 =
      ∫ t : ℝ, (g : ℝ → ℂ) t := by
    rw [Real.fourierInv_eq' (f := (g : ℝ → ℂ)) (w := (0 : ℝ))]
    congr 1; ext v
    simp [inner_zero_left v, smul_eq_mul]
  calc ∫ t : ℝ, (g : ℝ → ℂ) t
      = FourierTransform.fourierInv (g : ℝ → ℂ) 0 := h_fi_zero.symm
    _ = (φ : ℝ → ℂ) 0 := congrFun hinv 0

/-- A function `g : ℝ → ℂ` has **nonnegative distributional Fourier support** if
    `∫ g(t) · ℱ[ψ](t) dt = 0` for every Schwartz `ψ` with `supp(ψ) ⊆ (-∞, 0)`.
    Equivalently, the distributional Fourier transform of `g` is supported on `[0, ∞)`. -/
private def HasNonnegDistrFourierSupport (g : ℝ → ℂ) : Prop :=
  ∀ (ψ : SchwartzMap ℝ ℂ), (∀ x ∈ Function.support (ψ : ℝ → ℂ), x < 0) →
    ∫ t : ℝ, g t * ((SchwartzMap.fourierTransformCLM ℂ ψ) : ℝ → ℂ) t = 0

/-- Constant functions have nonnegative distributional Fourier support:
    `∫ C · ℱ[ψ] dt = C · ψ(0) = 0` since `0 ∉ supp(ψ)`. -/
private lemma hasNonnegDistrFourierSupport_const (c : ℂ) :
    HasNonnegDistrFourierSupport (fun _ => c) := by
  intro ψ hψ
  have hψ0 : (ψ : ℝ → ℂ) 0 = 0 := by
    by_contra h; exact absurd (hψ 0 (Function.mem_support.mpr h)) (lt_irrefl 0)
  show ∫ t : ℝ, c * ((SchwartzMap.fourierTransformCLM ℂ ψ) : ℝ → ℂ) t = 0
  rw [MeasureTheory.integral_const_mul, integral_fourierTransform_eq_apply_zero, hψ0, mul_zero]

/-- Time-translation of the fm-argument in diffVarReduction coordinates equals
    a shift in the time component of the boundary difference variable `ξ_{n-1}(0)`.

    `diffVarSection` embeds difference variables as cumulative sums
    `x_k(μ) = Σ_{j<k} ξ_j(μ)`. Translation by `te₀` shifts fm-arguments (indices ≥ n)
    by `-te₀`. In difference variables, the shift cancels for all `ξ_j` with `j ≠ n-1`
    (both endpoints move together), and only `ξ_{n-1}(0)` is shifted by `-t`. -/
private lemma diffVarReduction_translate_eq_shift {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (hk : (n + m - 1) + 1 = n + m) (hbdry : n - 1 < n + m - 1) (t : ℝ)
    (ξ : NPointSpacetime d (n + m - 1)) :
    diffVarReduction d (n + m - 1)
      (hk.symm ▸ fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) ξ =
    diffVarReduction d (n + m - 1)
      (hk.symm ▸ fn.conjTensorProduct fm)
      (Function.update ξ ⟨n - 1, hbdry⟩
        (Function.update (ξ ⟨n - 1, hbdry⟩) 0 (ξ ⟨n - 1, hbdry⟩ 0 - t))) := by
  -- Both sides are fiber integrals; the integrands are pointwise equal in `a`.
  -- Step 1: Unfold diffVarReduction to the fiber integral
  show (∫ a : Fin (d + 1) → ℝ,
      (hk.symm ▸ fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm))
        (fun k μ => a μ + diffVarSection d (n + m - 1) ξ k μ)) =
    (∫ a : Fin (d + 1) → ℝ,
      (hk.symm ▸ fn.conjTensorProduct fm)
        (fun k μ => a μ + diffVarSection d (n + m - 1)
          (Function.update ξ ⟨n - 1, hbdry⟩
            (Function.update (ξ ⟨n - 1, hbdry⟩) 0 (ξ ⟨n - 1, hbdry⟩ 0 - t))) k μ))
  -- Step 2: The integrands are pointwise equal
  congr 1; ext a
  -- Step 3: Establish how the ▸ cast interacts with SchwartzMap evaluation
  have heval : ∀ (f : SchwartzNPointSpace d (n + m))
      (y : NPointSpacetime d ((n + m - 1) + 1)),
      (hk.symm ▸ f : SchwartzNPointSpace d ((n + m - 1) + 1)) y =
      f (fun (i : Fin (n + m)) (μ : Fin (d + 1)) => y ⟨i.val, by omega⟩ μ) := by
    have := fun (K : ℕ) (hK : K = (n + m - 1) + 1)
        (f : SchwartzNPointSpace d K) (y : NPointSpacetime d ((n + m - 1) + 1)) =>
      show (hK ▸ f : SchwartzNPointSpace d ((n + m - 1) + 1)) y =
        f (fun i μ => y ⟨i.val, hK ▸ i.isLt⟩ μ) from by subst hK; rfl
    exact this (n + m) hk.symm
  simp only [heval]
  -- Step 4: Unfold conjTensorProduct to split into fn and fm parts
  simp only [SchwartzMap.conjTensorProduct_apply]
  simp only [splitFirst, poincareActNPoint_apply]
  -- Both sides: starRingEnd ℂ (fn (fn_args)) * (fm or τtfm) (fm_args)
  -- with fn_args and fm_args involving a + diffVarSection sums
  dsimp [diffVarSection]
  congr 1
  · -- fn parts: sums at indices < n don't include the update at n-1
    congr 2; funext i; funext μ; congr 1
    apply Finset.sum_congr rfl
    intro ⟨j, hj⟩ _
    simp only [Function.update, Fin.mk.injEq]
    split_ifs with h
    · omega
    · rfl
  · -- fm parts: the Poincaré translation matches the shift in cumulative sums
    congr 1; funext j; funext μ
    dsimp
    simp only [Function.update_apply, splitLast, poincareActNPointDomain,
      PoincareRepresentation.translationInDirection, PoincareGroup.act_def,
      PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
      PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
      inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      PoincareRepresentation.basisVector]
    -- Goal: a μ + ∑ ξ_i(μ) + -(t * δ_{μ,0}) = a μ + ∑ (if cond then update else ξ)(μ)
    -- Strategy: show the if-sum and the plain sum differ only at n-1,
    -- and the difference accounts for the -(t * δ_{μ,0}) offset.
    -- First, handle μ = 0 vs μ ≠ 0
    split_ifs with hμ
    · -- Case μ = 0: the offset is -t, and the n-1 term changes by -t
      subst hμ
      simp only [mul_one]
      -- Suffices: ∑(if cond then update else ξ)(0) = ∑ ξ(0) - t
      suffices h : ∀ x : Fin (n + ↑j),
          (if (⟨↑x, by omega⟩ : Fin (n + m - 1)) = ⟨n - 1, hbdry⟩
           then Function.update (ξ ⟨n - 1, hbdry⟩) 0 (ξ ⟨n - 1, hbdry⟩ 0 - t)
           else ξ ⟨↑x, by omega⟩) 0 =
          ξ ⟨↑x, by omega⟩ 0 +
            if x = (⟨n - 1, by omega⟩ : Fin (n + ↑j)) then -t else 0 by
        simp_rw [h, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]; ring
      intro x
      simp only [Fin.mk.injEq, Fin.ext_iff]
      split_ifs with hx
      · simp only [Function.update_self]
        rw [show ξ ⟨↑x, by omega⟩ = ξ ⟨n - 1, hbdry⟩ from
          congr_arg ξ (Fin.ext hx : (⟨↑x, _⟩ : Fin (n + m - 1)) = ⟨n - 1, hbdry⟩)]
        ring
      · simp
    · -- Case μ ≠ 0: the offset is 0, and the n-1 term is unchanged
      simp only [mul_zero, neg_zero, add_zero]
      congr 1
      apply Finset.sum_congr rfl; intro x _
      simp only [Fin.mk.injEq]
      split_ifs with hx
      · have : (⟨↑x, by omega⟩ : Fin (n + m - 1)) = ⟨n - 1, hbdry⟩ := Fin.ext hx
        rw [show ξ ⟨↑x, by omega⟩ = ξ ⟨n - 1, hbdry⟩ from congr_arg ξ this]
        exact (Function.update_of_ne hμ _ _).symm
      · rfl

/-- **Partial convolution Fourier factorization.**

    If `Θ(ξ)` is a partial convolution of `ℱ[φ]` with `G` in the time component of
    the `j`-th variable:
      `Θ(ξ) = ∫ ℱ[φ](t) · G(ξ with ξ_j(0) ← ξ_j(0) - t) dt`
    then `ψ = ℱ⁻¹[Θ]` factorizes as `ψ(q) = φ(q_j(0)) · ℱ⁻¹[G](q)`.

    In particular, `ψ(q) ≠ 0` implies `φ(q_j(0)) ≠ 0`.

    Proof: apply full inverse Fourier transform to Θ. Substituting `u = ξ_j(0) - t`
    and separating the `e^{2πi q_j(0) t}` factor gives
    `∫ ℱ[φ](t) e^{2πi q_j(0) t} dt = ℱ⁻¹[ℱ[φ]](q_j(0)) = φ(q_j(0))` by Fourier
    inversion, times the remaining full inverse Fourier transform of G. -/
private theorem partial_convolution_fourier_factorization
    {n_pts : ℕ} (j : Fin n_pts)
    (G : SchwartzNPointSpace d n_pts)
    (φ : SchwartzMap ℝ ℂ)
    (Θ : SchwartzNPointSpace d n_pts)
    (hΘ : ∀ ξ : NPointSpacetime d n_pts,
        Θ ξ = ∫ t : ℝ,
          ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
            G (Function.update ξ j (Function.update (ξ j) 0 (ξ j 0 - t)))) :
    ∃ ψ : SchwartzNPointSpace d n_pts,
        ψ.fourierTransform = Θ ∧
        ∀ q : NPointSpacetime d n_pts,
          ψ q ≠ 0 → (φ : ℝ → ℂ) (q j 0) ≠ 0 := by
  -- Construct ψ = ℱ⁻¹[Θ] and K = ℱ⁻¹[G] explicitly via nPointToEuclidean
  let e := nPointToEuclidean d n_pts
  let ψ : SchwartzNPointSpace d n_pts :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (FourierTransform.fourierInv
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ))
  let K : SchwartzNPointSpace d n_pts :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (FourierTransform.fourierInv
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G))
  -- Step 1: Show ψ.fourierTransform = Θ
  have hψ_ft : ψ.fourierTransform = Θ := by
    simp only [SchwartzNPointSpace.fourierTransform, ψ]
    ext x
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      SchwartzMap.fourierTransformCLM_apply]
    have h_cancel : ∀ (f : SchwartzMap _ ℂ),
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) = f := by
      intro f; ext y
      simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [h_cancel]
    exact congrFun (congrArg _ (FourierTransform.fourier_fourierInv_eq _)) _
  refine ⟨ψ, hψ_ft, fun q hq => ?_⟩
  -- Step 2: Show ψ q = φ(q j 0) * K q, then conclude
  suffices hfactor : ψ q = (φ : ℝ → ℂ) (q j 0) * K q by
    rw [hfactor] at hq; exact left_ne_zero_of_mul hq
  -- ψ and K are let-bound and unfold to fourierInv at (e q)
  simp only [ψ, K, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  -- Goal: (fourierInv (Θ ∘ e.symm))(e q) = φ(q j 0) * (fourierInv (G ∘ e.symm))(e q)
  -- Convert SchwartzMap fourierInv to function-level
  rw [show (FourierTransform.fourierInv
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ) : _ → ℂ) (e q) =
    FourierTransform.fourierInv
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ : _ → ℂ)) (e q) from
    congrFun (SchwartzMap.fourierInv_coe _) (e q)]
  rw [show (FourierTransform.fourierInv
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G) : _ → ℂ) (e q) =
    FourierTransform.fourierInv
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G : _ → ℂ)) (e q) from
    congrFun (SchwartzMap.fourierInv_coe _) (e q)]
  -- Goal: fourierInv(Θ ∘ e⁻¹)(e q) = φ(q j 0) * fourierInv(G ∘ e⁻¹)(e q)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  -- Goal: FourierTransformInv.fourierInv (⇑Θ ∘ ⇑e.symm) (e q) =
  --   φ (q j 0) * FourierTransformInv.fourierInv (⇑G ∘ ⇑e.symm) (e q)
  -- Express as explicit integrals
  rw [Real.fourierInv_eq' (f := (⇑Θ ∘ ⇑e.symm)) (w := e q),
      Real.fourierInv_eq' (f := (⇑G ∘ ⇑e.symm)) (w := e q)]
  -- LHS: ∫ v, exp(2πi⟨v, e q⟩) • (Θ(e⁻¹ v))
  -- RHS: φ(q j 0) * ∫ v, exp(2πi⟨v, e q⟩) • (G(e⁻¹ v))
  -- Substitute Θ(e⁻¹ v) = ∫ ℱ[φ](t) * G(shift(e⁻¹ v)) dt via hΘ
  simp_rw [Function.comp_apply, hΘ]
  -- Goal: ∫ v, exp(2πi⟨v, eq⟩) • (∫ t, ℱ[φ](t) * G(shift(e⁻¹ v))) =
  --   φ(q j 0) * ∫ v, exp(2πi⟨v, eq⟩) • G(e⁻¹ v)
  -- ══ Partial convolution theorem ══════════════════════════════════
  -- Strategy: relate the NPointSpacetime shift to a EuclideanSpace translation,
  -- then for each fixed v, change variables t → t in the inner integral,
  -- rewrite ∫_v of ∫_t as ∫_t of ∫_v via Fubini, do COV v → v + t·ej0,
  -- decompose the inner product, factor the exponential, and apply Fourier inversion.
  -- ─── Abbreviations ─────────────────────────────────────────────
  set ej0 : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) :=
    EuclideanSpace.single (j, (0 : Fin (d + 1))) 1 with hej0_def
  set w := e q with hw_def
  set FTφ_s := (SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) with hFTφ_s_def
  -- ─── Step 1: Shift = EuclideanSpace translation ────────────────
  have h_shift : ∀ (v : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1))) (t : ℝ),
      Function.update (e.symm v) j
        (Function.update (e.symm v j) 0 (e.symm v j 0 - t)) =
      e.symm (v - t • ej0) := by
    intro v t; ext i μ
    simp only [Function.update_apply]
    -- Unfold e.symm(...) through definitions and simplify
    simp only [e, ej0, nPointToEuclidean, uncurryLinearEquiv, PiLp.single_apply,
      PiLp.continuousLinearEquiv_symm_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Prod.mk.injEq, and_comm, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_trans_apply]
    split_ifs <;> simp_all [Function.update_apply] <;> split_ifs <;> simp_all <;> ring
  simp_rw [h_shift]
  -- ─── Step 2: Key coordinate / inner-product facts ─────────────
  have h_coord : w (j, (0 : Fin (d + 1))) = q j 0 := by
    simp [w, e, nPointToEuclidean, uncurryLinearEquiv,
      PiLp.continuousLinearEquiv_symm_apply]
  have h_inner_ej0 : @inner ℝ _ _ ej0 w = q j 0 := by
    rw [EuclideanSpace.inner_single_left]; simp [h_coord]
  -- ─── Step 3: 1-D Fourier inversion ∫ ℱ[φ](t)·exp(2πi·t·k) = φ(k) ──
  have h_fourier_inv_at :
      ∫ t : ℝ, (FTφ_s : ℝ → ℂ) t *
        Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ (t • ej0) w) * Complex.I) =
      (φ : ℝ → ℂ) (q j 0) := by
    -- Rewrite ⟪t • ej0, w⟫ = t * ⟪ej0, w⟫ = t * (q j 0)
    simp only [real_inner_smul_left, h_inner_ej0]
    -- Now: ∫ t, FTφ(t) * exp(↑(2π(t*(q j 0))) * I) = φ(q j 0)
    -- This is ℱ⁻¹[ℱ[φ]](q j 0) by Real.fourierInv_eq'
    have hinv : FourierTransform.fourierInv (FTφ_s : ℝ → ℂ) = (φ : ℝ → ℂ) := by
      have h := congrArg (fun (f : SchwartzMap ℝ ℂ) => (f : ℝ → ℂ))
        (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) φ)
      dsimp only at h; rwa [SchwartzMap.fourierInv_coe] at h
    have h_eval := congrFun hinv (q j 0)
    rw [Real.fourierInv_eq'] at h_eval
    rw [← h_eval]; refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t; rw [smul_eq_mul, mul_comm (Complex.exp _)]
    congr 1; congr 1; congr 1; congr 1
    simp [inner, mul_comm]
  -- ─── Step 4: Integrable helpers ───────────────────────────────
  -- G ∘ e.symm as a SchwartzMap on EuclideanSpace (for integrability)
  set Ge : SchwartzMap (EuclideanSpace ℝ (Fin n_pts × Fin (d + 1))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G with hGe_def
  have hGe_eq : ∀ v, Ge v = G (e.symm v) := fun v => by
    simp [Ge, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  -- ─── Step 5: For each v, change variables in the inner integral ──
  -- We show: ∫ t, FTφ(t) * G(e⁻¹(v - t•ej0))
  --        = ∫ t, FTφ(t) * exp(2πi⟪t•ej0, w⟫ I) * G(e⁻¹ v)
  -- is FALSE in general (the inner integral depends on v through the shift).
  -- Instead we work with the DOUBLE integral.
  --
  -- We show ∫ v exp(⟨v,w⟩) * ∫ t FTφ(t) * G(e⁻¹(v-t·ej0))
  --       = ∫ v exp(⟨v,w⟩) * G(e⁻¹ v) * ∫ t FTφ(t) * exp(2πi t (q j 0))
  --       = (∫ t FTφ(t) * exp(2πi t (q j 0))) * ∫ v exp(⟨v,w⟩) * G(e⁻¹ v)
  --       = φ(q j 0) * ∫ v exp(⟨v,w⟩) • G(e⁻¹ v)
  --
  -- The key step replaces each inner integral with a factored form via
  -- an integral identity that uses translation-invariance of Lebesgue measure.
  -- Instead of Fubini on the full product, we express the v-integral of
  -- the partial convolution via the substitution v ↦ v + t·ej0.
  --
  -- Identity: for each v,
  --   ∫ t, FTφ(t) * G(e⁻¹(v - t·ej0)) dt                 (original)
  -- = ∫ t, FTφ(t) * G(e⁻¹(v - t·ej0)) dt                 (rename)
  --
  -- After multiplying by exp(⟨v,w⟩) and integrating over v:
  -- ∫ v, exp(⟨v,w⟩) * (∫ t, FTφ(t) * G(e⁻¹(v - t·ej0)))
  --
  -- We need Fubini to swap. Instead, we use a direct calculation.
  -- Observe: the function v ↦ exp(⟨v,w⟩) * (∫ t ...) is the inverse FT of
  -- Θ ∘ e⁻¹ evaluated at w, and similarly for the RHS. We already know
  -- ℱ⁻¹(ℱ ψ) = ψ and ψ.fourierTransform = Θ, so it suffices to show
  -- the FOURIER TRANSFORMS of both sides agree.
  --
  -- This is a circular argument at the integral level. So we really do Fubini.
  -- We proceed by establishing product integrability, then doing the calc.
  --
  -- *** Product integrability ***
  have hGe_int : MeasureTheory.Integrable (Ge : _ → ℂ) := Ge.integrable
  have hFTφ_int : MeasureTheory.Integrable (FTφ_s : ℝ → ℂ) := FTφ_s.integrable
  -- The integrand (after h_shift) uses G (e.symm ...). Rewrite with Ge.
  -- *** Main calc chain ***
  -- Instead of explicit Fubini + COV, use integral manipulations with translation invariance.
  -- We show:  ∫ v, E(v) • (∫ t, F(t) * G(e⁻¹(v-t·ej0)))
  --         = φ(q j 0) * ∫ v, E(v) • G(e⁻¹ v)
  -- by rewriting G(e⁻¹ ·) as Ge, applying Fubini, COV, factoring, and Fourier inversion.
  -- Rewrite G(e.symm ·) as Ge throughout using hGe_eq
  simp_rw [← hGe_eq]
  -- Push smul into inner integral
  simp_rw [smul_eq_mul]
  -- The proof proceeds by integral manipulations.
  -- We combine Fubini + COV + exp factoring + Fourier inversion into one block.
  -- Key claim: ∫ v, E(v) * ∫ t, F(t) * Ge(v - t•ej0) = φ(k) * ∫ v, E(v) * Ge(v)
  -- where E(v) = exp(2πi⟪v,w⟫*I), F = FTφ_s, k = q j 0.
  -- Step: push E(v) inside inner integral and swap via Fubini
  have h_fubini_cov : ∀ t : ℝ,
      ∫ v, Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
        Ge (v - t • ej0) =
      Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I) *
        ∫ v, Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) * Ge v := by
    intro t
    -- COV: v → v + t•ej0
    have h_cov := (MeasureTheory.integral_add_right_eq_self
      (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)))))
      (fun v => Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
        Ge (v - t • ej0)) (t • ej0))
    simp only [add_sub_cancel_right] at h_cov
    rw [← h_cov]
    -- Decompose inner product and factor exponential
    simp_rw [_root_.inner_add_left, real_inner_smul_left, h_inner_ej0]
    simp_rw [show ∀ (a b : ℝ), ↑(2 * Real.pi * (a + b)) * Complex.I =
      ↑(2 * Real.pi * a) * Complex.I + ↑(2 * Real.pi * b) * Complex.I from by
      intro a b; push_cast; ring]
    simp_rw [Complex.exp_add]
    -- Pull constant factor out of integral
    simp_rw [show ∀ u, (Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ u w) * Complex.I) *
        Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I)) * Ge u =
      Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I) *
        (Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ u w) * Complex.I) * Ge u) from
      fun u => by ring]
    rw [← smul_eq_mul (a := Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I)),
        ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
  -- Now use Fubini + h_fubini_cov to rewrite the double integral.
  -- Goal: ∫ v, E(v) * (∫ t, F(t) * Ge(v - t•ej0)) = φ(k) * ∫ v, E(v) * Ge(v)
  -- Push E(v) into the inner integral, swap via Fubini, apply h_fubini_cov, factor.
  -- ─── Integrability for Fubini ───────────────────────────────
  set E_fun := fun v : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) =>
    Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I)
  have hE_norm : ∀ v, ‖E_fun v‖ = 1 := fun v => Complex.norm_exp_ofReal_mul_I _
  have h_int_prod : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) × ℝ =>
        E_fun p.1 * ((FTφ_s : ℝ → ℂ) p.2 * Ge (p.1 - p.2 • ej0)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hcont_prod : Continuous (fun p : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) × ℝ =>
        E_fun p.1 * ((FTφ_s : ℝ → ℂ) p.2 * Ge (p.1 - p.2 • ej0))) := by
      apply Continuous.mul
      · exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp
            (continuous_const.mul (continuous_inner.comp
              (Continuous.prodMk continuous_fst continuous_const)))).mul
            continuous_const))
      · exact (FTφ_s.continuous.comp continuous_snd).mul
            (Ge.continuous.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))
    rw [MeasureTheory.integrable_prod_iff' hcont_prod.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · -- Fiberwise integrability: for fixed t, v ↦ ... is integrable
      -- |E(v) * (F(t) * Ge(v-shift))| = |F(t)| * |Ge(v-shift)|, both integrable
      refine ((hGe_int.comp_sub_right (t • ej0)).norm.const_mul
        ‖(FTφ_s : ℝ → ℂ) t‖).mono'
        ((hcont_prod.comp (Continuous.prodMk continuous_id
          (continuous_const (y := t)))).aestronglyMeasurable) ?_
      filter_upwards with v; simp [norm_mul, hE_norm]
    · -- Outer integrability: t ↦ ∫ ‖...‖ dv is integrable
      have h_bound : ∀ t : ℝ,
          ∫ v, ‖E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0))‖ =
          ‖(FTφ_s : ℝ → ℂ) t‖ * ∫ v, ‖Ge v‖ := by
        intro t; simp only [norm_mul, hE_norm, one_mul]
        rw [← smul_eq_mul (a := ‖(FTφ_s : ℝ → ℂ) t‖),
            ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
        exact MeasureTheory.integral_sub_right_eq_self
          (fun v => ‖(FTφ_s : ℝ → ℂ) t‖ * ‖Ge v‖) (t • ej0)
      simp_rw [h_bound]
      exact hFTφ_int.norm.mul_const _
  -- ─── Fubini + h_fubini_cov + Fourier inversion ─────────────
  -- Push E(v) inside inner integral
  have h_push : ∀ v, E_fun v * (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) =
      ∫ t, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) := by
    intro v; rw [← smul_eq_mul (a := E_fun v), ← MeasureTheory.integral_smul]
    simp_rw [smul_eq_mul]
  conv_lhs => arg 2; ext v; rw [show Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
    (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) = E_fun v * (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) from rfl,
    h_push]
  -- Fubini: swap v and t
  rw [MeasureTheory.integral_integral_swap h_int_prod]
  -- For each t, use h_fubini_cov
  have h_inner : ∀ t, ∫ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) =
      (FTφ_s : ℝ → ℂ) t * (Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I) *
        ∫ v, E_fun v * Ge v) := by
    intro t
    have : ∫ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) =
        (FTφ_s : ℝ → ℂ) t * ∫ v, E_fun v * Ge (v - t • ej0) := by
      simp_rw [show ∀ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ej0)) =
        (FTφ_s : ℝ → ℂ) t * (E_fun v * Ge (v - t • ej0)) from fun v => by ring]
      rw [← smul_eq_mul (a := (FTφ_s : ℝ → ℂ) t),
          ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
    rw [this, h_fubini_cov]
  simp_rw [h_inner]
  -- Factor and apply Fourier inversion
  simp_rw [show ∀ t, (FTφ_s : ℝ → ℂ) t *
      (Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I) *
        ∫ u, E_fun u * Ge u) =
    ((FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I)) *
      (∫ u, E_fun u * Ge u) from fun t => by ring]
  -- Pull constant (∫ u, E_fun u * Ge u) out of the t-integral and apply Fourier inversion
  -- The goal is: ∫ y, f(y) * C = φ(k) * C'  where C = ∫ v, E_fun v * Ge v
  -- Commute inside the integral, pull out C, apply Fourier inversion
  simp_rw [show ∀ y, (FTφ_s : ℝ → ℂ) y *
      Complex.exp (↑(2 * Real.pi * (y * (q j 0))) * Complex.I) *
      (∫ v, E_fun v * Ge v) =
    (∫ v, E_fun v * Ge v) •
      ((FTφ_s : ℝ → ℂ) y *
        Complex.exp (↑(2 * Real.pi * (y * (q j 0))) * Complex.I)) from
    fun y => by rw [smul_eq_mul]; ring]
  rw [MeasureTheory.integral_smul, smul_eq_mul]
  simp_rw [show ∀ t, (FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * (t * (q j 0))) * Complex.I) =
    (FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ (t • ej0) w) * Complex.I) from
    fun t => by rw [real_inner_smul_left, h_inner_ej0]]
  rw [h_fourier_inv_at, mul_comm]

/-- **Fourier inversion and support condition for the SCD translate witness.**

    Given `Θ : SchwartzNPointSpace d (n + m - 1)` defined pointwise as the Schwartz integral
    of `t ↦ ℱ[φ](t) * diffVarReduction(fn.conjTP(τ_{te₀} fm))`, there exists
    `ψ = ℱ⁻¹[Θ] : SchwartzNPointSpace d (n + m - 1)` satisfying:
    1. `ψ.fourierTransform = Θ`                            (ℱ ∘ ℱ⁻¹ = id on Schwartz space)
    2. `ψ(q) ≠ 0 → φ(q ⟨n-1, hbdry⟩ 0) ≠ 0`            (support from partial convolution)

    **Proof sketch of (2):** The time-translation `τ_{te₀}` shifts all `m` fm-arguments by
    `-t·e₀`. In difference variables, `F(t)(ξ)` is a translation of `F(0)(ξ)` by `-t` in
    the sum `(Σ_{j<n} ξ_j)(0)` (the boundary slot adjacent to ξ_{n-1}). Thus Θ is a partial
    convolution of G₀ = F(0) with ℱ[φ] in that slot. Inverting the full Fourier transform
    converts the convolution to pointwise multiplication: `ψ(q) ∝ φ(q_{n-1,0}) · Ĝ₀(q)`,
    so `ψ(q) ≠ 0` forces `φ(q_{n-1,0}) ≠ 0`. -/
private lemma scd_fourierInv_translate_witness {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0)
    (hk : (n + m - 1) + 1 = n + m) (hbdry : n - 1 < n + m - 1)
    (Θ : SchwartzNPointSpace d (n + m - 1))
    (hΘ : ∀ ξ : NPointSpacetime d (n + m - 1),
        Θ ξ = ∫ t : ℝ,
          ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
            diffVarReduction d (n + m - 1)
              (hk.symm ▸ fn.conjTensorProduct
                (poincareActNPoint
                  (PoincareRepresentation.translationInDirection d 0 t) fm)) ξ) :
    ∃ ψ : SchwartzNPointSpace d (n + m - 1),
        ψ.fourierTransform = Θ ∧
        ∀ q : NPointSpacetime d (n + m - 1),
          ψ q ≠ 0 → (φ : ℝ → ℂ) (q ⟨n - 1, hbdry⟩ 0) ≠ 0 := by
  -- Step 1: Rewrite the integrand using the shift structure (Lemma 1).
  -- F(t)(ξ) = G₀(ξ with ξ_{n-1}(0) shifted by -t)
  let G₀ := diffVarReduction d (n + m - 1) (hk.symm ▸ fn.conjTensorProduct fm)
  have hΘ_shift : ∀ ξ : NPointSpacetime d (n + m - 1),
      Θ ξ = ∫ t : ℝ,
        ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
          G₀ (Function.update ξ ⟨n - 1, hbdry⟩
            (Function.update (ξ ⟨n - 1, hbdry⟩) 0 (ξ ⟨n - 1, hbdry⟩ 0 - t))) := by
    intro ξ
    rw [hΘ ξ]
    congr 1; ext t; congr 1
    exact diffVarReduction_translate_eq_shift hn hm fn fm hk hbdry t ξ
  -- Step 2: Apply the partial convolution factorization (Lemma 2).
  -- ψ = ℱ⁻¹[Θ] satisfies ψ(q) = φ(q_{n-1,0}) · ℱ⁻¹[G₀](q)
  exact partial_convolution_fourier_factorization ⟨n - 1, hbdry⟩ G₀ φ Θ hΘ_shift

/-- **SCD ⟹ nonneg distributional Fourier support of the WIP summand.**

    The function `t ↦ W_{n+m}(fₙ* ⊗ τ_{te₀} fₘ)` has distributional Fourier transform
    supported on `[0, ∞)`. The proof applies the Fourier transform to the full integrand
    and uses `ℱ ∘ ℱ = id` (up to reflection) to reduce to a support comparison:
    `ℱ_distr[g]` is supported on non-negative energies by SCD, while `φ` is supported
    on `(-∞, 0)`, so the distributional pairing `⟨ℱ[g], φ⟩ = ∫ g(t) · ℱ[φ](t) dt = 0`.

    - **Degenerate cases** (`m = 0` or `n = 0`): `g(t)` is constant (trivial action
      on `Fin 0` or translation invariance), giving `ℱ_distr[g] = C · δ₀` supported
      at `{0} ⊆ [0, ∞)`.
    - **Non-degenerate case** (`n, m ≥ 1`): Factor through the SCD reduced distribution
      `w`. By the shift structure, time-translation shifts only the boundary difference
      variable `ξ_{n-1}`. Exchanging `w` with the `t`-integral and applying
      `ℱ ∘ ℱ = reflection` yields a Schwartz witness with support contradicting `V̄₊`,
      so SCD gives vanishing.

    **Ref:** Streater-Wightman, §3-1; Reed-Simon II, Theorem X.40. -/
private lemma scd_summand_nonneg_fourier_support
    (hSCD : SpectralConditionDistribution d Wfn.W)
    {n m : ℕ} (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m) :
    HasNonnegDistrFourierSupport (fun t =>
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm))) := by
  intro φ hφ
  by_cases hm : m = 0
  · -- m = 0: τ acts trivially on fm (Fin 0 domain), so g(t) is constant.
    -- ℱ_distr[const] = C · δ₀ supported at {0} ⊆ [0, ∞).
    have h_act_fm : ∀ t, poincareActNPoint
        (PoincareRepresentation.translationInDirection d 0 t) fm = fm := by
      intro t; subst hm; ext x; simp only [poincareActNPoint_apply]
      congr 1; ext i; exact Fin.elim0 i
    simp_rw [h_act_fm]
    exact hasNonnegDistrFourierSupport_const (Wfn.W (n + m) (fn.conjTensorProduct fm)) φ hφ
  · by_cases hn : n = 0
    · -- n = 0, m ≥ 1: g(t) is constant by translation invariance of W.
      -- When n = 0, the Poincaré action on fn is trivial (Fin 0 domain is empty),
      -- so W(fn.conjTP(τ_t fm)) = W((τ_t fn).conjTP(τ_t fm)) = W(fn.conjTP(fm))
      -- by translation invariance. ℱ_distr[const] = C · δ₀ ⊆ [0, ∞).
      have h_const : ∀ t : ℝ,
          Wfn.W (n + m) (fn.conjTensorProduct
            (poincareActNPoint
              (PoincareRepresentation.translationInDirection d 0 t) fm)) =
          Wfn.W (n + m) (fn.conjTensorProduct fm) := by
        intro t
        set τ := PoincareRepresentation.translationInDirection d 0 t with hτ_def
        have h_act_fn : poincareActNPoint τ fn = fn := by
          subst hn; ext x; simp only [poincareActNPoint_apply]
          congr 1; ext i; exact Fin.elim0 i
        conv_lhs => rw [← h_act_fn]
        symm
        apply Wfn.translation_invariant (n + m)
          (-(t • PoincareRepresentation.basisVector d 0))
        intro x
        rw [poincareActNPoint_conjTensorProduct]
        congr 1; ext i
        simp only [poincareActNPointDomain, PoincareGroup.act_def,
          PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
          hτ_def, PoincareRepresentation.translationInDirection,
          PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
          inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
      simp_rw [h_const]
      exact hasNonnegDistrFourierSupport_const (Wfn.W (n + m) (fn.conjTensorProduct fm)) φ hφ
    · -- n ≥ 1, m ≥ 1: Non-degenerate SCD argument.
      -- Factor W through the reduced distribution w from SCD.
      have hpos : 0 < n + m := by omega
      have hk : (n + m - 1) + 1 = n + m := Nat.sub_add_cancel hpos
      obtain ⟨w, hw_cont, hw_lin, hw_factor, hw_vanish⟩ := hSCD (n + m - 1)
      have cast_W : ∀ (ℓ : ℕ) (hℓ : ℓ = n + m) (f : SchwartzNPointSpace d (n + m)),
          Wfn.W ℓ (hℓ.symm ▸ f) = Wfn.W (n + m) f := fun ℓ hℓ f => by subst hℓ; rfl
      have hw_eq : ∀ (f : SchwartzNPointSpace d (n + m)),
          Wfn.W (n + m) f = w (diffVarReduction d (n + m - 1) (hk.symm ▸ f)) :=
        fun f => by rw [← cast_W _ hk f]; exact hw_factor _
      simp_rw [hw_eq]
      have hbdry : n - 1 < n + m - 1 := by omega
      -- Apply ℱ to the full integrand via distributional Parseval:
      --   ∫ w(F(t)) · ℱ[φ](t) dt = ⟨ℱ_distr[g], φ⟩
      -- where g(t) = w(F(t)), F(t) = diffVarReduction(fₙ* ⊗ τ_{te₀} fₘ).
      --
      -- Step 1 (CLM exchange): ∫ w(F(t)) · ℱ[φ](t) dt = w(∫ ℱ[φ](t) • F(t) dt) =: w(Θ)
      -- Step 2 (Shift structure): F(t)(ξ) = G₀(ξ', ξ_{n-1} - te₀, ξ'')
      --   → Θ is a partial convolution of ℱ[φ] with G₀ in ξ_{n-1,0}
      -- Step 3 (ℱ ∘ ℱ = reflection): Set ψ = ℱ⁻¹[Θ]. Then
      --   ψ(q) = φ(±q_{n-1,0}) · ℱ⁻¹[G₀](...), so
      --   ψ(q) ≠ 0 ⟹ φ(q_{n-1,0}) ≠ 0 ⟹ q_{n-1,0} < 0 ⟹ q_{n-1} ∉ V̄₊
      -- Step 4 (Disjoint supports): w(ℱ[ψ]) = w(Θ) = ∫ ... = 0 by SCD vanishing.
      suffices h_main : ∃ ψ : SchwartzNPointSpace d (n + m - 1),
          (w (ψ.fourierTransform) =
            ∫ t : ℝ,
              w (diffVarReduction d (n + m - 1) (hk.symm ▸ fn.conjTensorProduct
                  (poincareActNPoint
                    (PoincareRepresentation.translationInDirection d 0 t) fm))) *
              ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) ∧
          (∀ q : NPointSpacetime d (n + m - 1),
            ψ q ≠ 0 → (φ : ℝ → ℂ) (q ⟨n - 1, hbdry⟩ 0) ≠ 0) by
        -- Step 4: Disjoint supports ⟹ vanishing.
        obtain ⟨ψ, h_eq, h_factor⟩ := h_main
        have h_zero : w (ψ.fourierTransform) = 0 := hw_vanish ψ fun q hq =>
          ⟨⟨n - 1, hbdry⟩, fun hmem => by
            -- ψ(q) ≠ 0 ⟹ φ(q_{n-1,0}) ≠ 0 ⟹ q_{n-1,0} ∈ supp(φ) ⊆ (-∞,0)
            have hφ_ne := h_factor q hq
            have h_neg := hφ _ (Function.mem_support.mpr hφ_ne)
            -- But V̄₊ = ForwardMomentumCone requires timeComponent ≥ 0
            simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
              MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
              MinkowskiSpace.timeComponent] at hmem
            linarith [hmem.2]⟩
        exact h_eq.symm.trans h_zero
      -- Steps 1–3: Construct ψ via CLM exchange, shift structure, and ℱ ∘ ℱ = reflection.
      -- ── Step 1a: Continuity of the translate family in the Schwartz topology ──────────
      have hF_cont : Continuous (fun t : ℝ =>
          diffVarReduction d (n + m - 1)
            (hk.symm ▸ fn.conjTensorProduct
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm))) := by
        -- The inner map is continuous: conjugate tensor product is continuous in the right
        -- argument (conjTensorProduct_continuous_right), and translation is continuous in the
        -- Schwartz topology (continuous_translate_npoint_schwartz).
        have h_inner : Continuous (fun t : ℝ =>
            fn.conjTensorProduct
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) :=
          (SchwartzMap.conjTensorProduct_continuous_right fn).comp
            (continuous_translate_npoint_schwartz 0 fm)
        -- Compose with the CLM diffVarReduction and the continuous Nat-cast transport hk.symm ▸.
        -- The cast hk.symm ▸ : SchwartzNPointSpace d (n + m) → SchwartzNPointSpace d ((n+m-1)+1)
        -- is a continuous linear equivalence (same type up to the proof hk).
        have h_eqMpr_cont : ∀ {a b : ℕ} (h : a = b),
            Continuous (fun f : SchwartzNPointSpace d a =>
              (h ▸ f : SchwartzNPointSpace d b)) :=
          fun h => by subst h; exact continuous_id
        exact (diffVarReduction d (n + m - 1)).continuous.comp
          ((h_eqMpr_cont hk.symm).comp h_inner)
      -- ── Step 1b: CLM exchange — produce Θ with w(Θ) = ∫ w(F t) · ℱ[φ](t) dt ─────────
      -- Polynomial growth of F t in every Schwartz seminorm: time-translation τ_{te₀} of fm
      -- satisfies ‖τ_{te₀} fm‖_{k,j} ≤ C_{k,j} · (1+|t|)^{k+j+1} (standard estimate),
      -- and CLMs (diffVarReduction, conjTensorProduct, eqMpr) compose to preserve this.
      have hF_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
          SchwartzMap.seminorm ℝ k j
            (diffVarReduction d (n + m - 1)
              (hk.symm ▸ fn.conjTensorProduct
                (poincareActNPoint
                  (PoincareRepresentation.translationInDirection d 0 t) fm))) ≤
          C * (1 + ‖t‖) ^ N := by
        intro k j
        -- Step 1: Polynomial bound for the m-point translate family
        -- ∃ Dτ, ∀ t, seminorm ℝ p q (τ_t fm) ≤ Dτ * (1 + ‖t‖)^p
        -- Uses: seminorm_translateSchwartz_le + CLE precomposition ≤ 1
        have hτ : ∀ (p q : ℕ), ∃ (Dτ : ℝ), 0 ≤ Dτ ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ p q
              (poincareActNPoint
                (PoincareRepresentation.translationInDirection d 0 t) fm) ≤
            Dτ * (1 + ‖t‖) ^ p := by
          intro p q
          obtain ⟨D, hD_nn, hD⟩ := SCV.seminorm_translateSchwartz_le p q
            (flattenSchwartzNPointLocal (d := d) fm)
          set η := flatTranslationDirection (d := d) (n := m) 0 with hη_def
          refine ⟨D * (1 + ‖η‖) ^ p, by positivity, fun t => ?_⟩
          rw [poincareActNPoint_translationInDirection_eq_unflatten_translate]
          set ψ_t := SCV.translateSchwartz (t • η) (flattenSchwartzNPointLocal (d := d) fm)
          -- Precomposition with flattenCLEquivRealLocal (a CLE) does not increase seminorm
          have h_unflatten_le : SchwartzMap.seminorm ℝ p q
              (unflattenSchwartzNPointLocal (d := d) ψ_t) ≤
              SchwartzMap.seminorm ℝ p q ψ_t := by
            apply SchwartzMap.seminorm_le_bound ℝ p q _ (by positivity)
            intro x
            -- unflattenSchwartzNPointLocal ψ_t = ψ_t ∘ flattenCLEquivRealLocal m (d+1)
            set e := (flattenCLEquivRealLocal m (d + 1)).toContinuousLinearMap
            have hcomp : (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) =
                ↑ψ_t ∘ flattenCLEquivRealLocal m (d + 1) := by
              ext y
              simp [unflattenSchwartzNPointLocal, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
            -- Chain rule: iteratedFDeriv of ψ_t ∘ e = compContinuousLinearMap of iteratedFDeriv ψ_t
            have hiter : iteratedFDeriv ℝ q
                (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x =
                ContinuousMultilinearMap.compContinuousLinearMap
                  (iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x))
                  (fun _ => e) := by
              rw [hcomp]
              exact ContinuousLinearMap.iteratedFDeriv_comp_right e ψ_t.smooth' x
                (by exact_mod_cast le_top)
            have hnorm_le : ‖x‖ ≤ ‖flattenCLEquivRealLocal m (d + 1) x‖ := by
              -- For each i : Fin m, j : Fin (d+1), |x i j| = |(flatten x)(finProdFinEquiv(i,j))|
              -- ≤ ‖flatten x‖, so ‖x‖ = sup_i ‖x i‖ = sup_i sup_j |x i j| ≤ ‖flatten x‖
              rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
              intro i
              rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
              intro j
              have heval : flattenCLEquivRealLocal m (d + 1) x (finProdFinEquiv (i, j)) = x i j :=
                by simp [flattenCLEquivRealLocal_apply]
              rw [show ‖x i j‖ = ‖flattenCLEquivRealLocal m (d + 1) x (finProdFinEquiv (i, j))‖
                  from by rw [heval]]
              exact norm_le_pi_norm _ _
            have hprod_le : ∏ _ : Fin q, ‖e‖ ≤ 1 := by
              -- ‖e‖ ≤ 1: for all y, ‖e y‖ = ‖flattenCLEquivRealLocal m (d+1) y‖ ≤ ‖y‖
              -- since each component (flatten y) k = y i j with |y i j| ≤ ‖y i‖ ≤ ‖y‖
              have he_norm : ‖e‖ ≤ 1 := by
                apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
                intro y
                rw [one_mul]
                rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
                intro k
                -- e y k = flattenCLEquivRealLocal m (d+1) y k = y (finProdFinEquiv.symm k).1 ...
                change ‖y (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2‖ ≤ ‖y‖
                calc ‖y (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2‖
                    ≤ ‖y (finProdFinEquiv.symm k).1‖ := norm_le_pi_norm _ _
                  _ ≤ ‖y‖ := norm_le_pi_norm _ _
              calc ∏ _ : Fin q, ‖e‖ ≤ ∏ _ : Fin q, (1 : ℝ) := by gcongr
                _ = 1 := Finset.prod_const_one
            have hiter_norm : ‖iteratedFDeriv ℝ q
                (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x‖ ≤
                ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ := by
              rw [hiter]
              calc ‖ContinuousMultilinearMap.compContinuousLinearMap
                      (iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x))
                      (fun _ => e)‖
                  ≤ ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ *
                      ∏ _ : Fin q, ‖e‖ :=
                    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
                _ ≤ ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ * 1 := by
                    gcongr
                _ = ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ :=
                    mul_one _
            calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ q
                    (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x‖
                ≤ ‖flattenCLEquivRealLocal m (d + 1) x‖ ^ p *
                    ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ := by
                  gcongr
              _ ≤ SchwartzMap.seminorm ℝ p q ψ_t :=
                  SchwartzMap.le_seminorm ℝ p q ψ_t (flattenCLEquivRealLocal m (d + 1) x)
          -- Apply seminorm_translateSchwartz_le and algebra
          have h_translate_le : SchwartzMap.seminorm ℝ p q ψ_t ≤
              D * (1 + ‖η‖) ^ p * (1 + ‖t‖) ^ p := by
            have heq : SchwartzMap.seminorm ℝ p q ψ_t = SchwartzMap.seminorm ℂ p q ψ_t := rfl
            rw [heq]
            calc SchwartzMap.seminorm ℂ p q ψ_t ≤ D * (1 + ‖t • η‖) ^ p := hD _
              _ = D * (1 + |t| * ‖η‖) ^ p := by rw [norm_smul, Real.norm_eq_abs]
              _ ≤ D * ((1 + ‖η‖) * (1 + |t|)) ^ p := by
                    gcongr; nlinarith [norm_nonneg η, abs_nonneg t]
              _ = D * (1 + ‖η‖) ^ p * (1 + |t|) ^ p := by rw [mul_pow]; ring
              _ = D * (1 + ‖η‖) ^ p * (1 + ‖t‖) ^ p := by
                    rw [← Real.norm_eq_abs t]
          linarith
        -- Step 2: Polynomial bound for the tensor product
        -- fn.conjTensorProduct = fn.borchersConj.tensorProduct (fixed in fn)
        -- Use tensorProduct_seminorm_le + hτ bounds for each Leibniz term
        have htens : ∃ (Ctens : ℝ), 0 ≤ Ctens ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ k j
              (fn.conjTensorProduct
                (poincareActNPoint
                  (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤
            Ctens * (1 + ‖t‖) ^ k := by
          classical
          let Dτ := fun p q => (hτ p q).choose
          have hDτ_nn : ∀ p q, 0 ≤ Dτ p q := fun p q => (hτ p q).choose_spec.1
          have hDτ_bound : ∀ p q t, SchwartzMap.seminorm ℝ p q
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm) ≤
              Dτ p q * (1 + ‖t‖) ^ p := fun p q => (hτ p q).choose_spec.2
          refine ⟨2 ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              (SchwartzMap.seminorm ℝ k i fn.borchersConj * Dτ 0 (j - i) +
               SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ k (j - i)),
            ?_, fun t => ?_⟩
          · apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
            apply Finset.sum_nonneg
            intro i _
            apply mul_nonneg (by exact_mod_cast Nat.zero_le _)
            apply add_nonneg
            · exact mul_nonneg (apply_nonneg _ _) (hDτ_nn 0 (j - i))
            · exact mul_nonneg (apply_nonneg _ _) (hDτ_nn k (j - i))
          show SchwartzMap.seminorm ℝ k j (fn.borchersConj.tensorProduct
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤ _
          have htens_base := SchwartzMap.tensorProduct_seminorm_le k j fn.borchersConj
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)
          have h1_le_pow : (1 : ℝ) ≤ (1 + ‖t‖) ^ k := by
            apply one_le_pow₀; linarith [norm_nonneg t]
          have hstep : SchwartzMap.seminorm ℝ k j (fn.borchersConj.tensorProduct
              (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤
              2 ^ k * ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
                (SchwartzMap.seminorm ℝ k i fn.borchersConj * (Dτ 0 (j - i) * (1 + ‖t‖) ^ k) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                   (Dτ k (j - i) * (1 + ‖t‖) ^ k)) := by
            apply htens_base.trans
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le _)
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
              exact (hDτ_bound 0 (j - i) t).trans
                (by simp only [pow_zero, mul_one];
                    exact le_mul_of_one_le_right (hDτ_nn 0 (j - i)) h1_le_pow)
            · exact mul_le_mul_of_nonneg_left (hDτ_bound k (j - i) t) (apply_nonneg _ _)
          have h_factor : ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
              (SchwartzMap.seminorm ℝ k i fn.borchersConj * (Dτ 0 (j - i) * (1 + ‖t‖) ^ k) +
               SchwartzMap.seminorm ℝ 0 i fn.borchersConj * (Dτ k (j - i) * (1 + ‖t‖) ^ k)) =
              (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
                (SchwartzMap.seminorm ℝ k i fn.borchersConj * Dτ 0 (j - i) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ k (j - i))) *
              (1 + ‖t‖) ^ k := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _; push_cast; ring
          linarith [hstep.trans (by rw [h_factor, ← mul_assoc])]
        -- Step 3: use Seminorm.bound_of_continuous on the composed seminorm
        -- (diffVarReduction is a CLM, so the (k,j)-seminorm on the target is
        --  bounded by finitely many source seminorms; each of those is bounded
        --  polynomially via htens_all)
        have hFpoly : ∃ (Cred : ℝ) (Nred : ℕ), 0 ≤ Cred ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ k j
              (diffVarReduction d (n + m - 1)
                (hk.symm ▸ fn.conjTensorProduct
                  (poincareActNPoint
                    (PoincareRepresentation.translationInDirection d 0 t) fm))) ≤
            Cred * (1 + ‖t‖) ^ Nred := by
          -- Generalize htens to all seminorm indices (p, q)
          have htens_all : ∀ (p q : ℕ), ∃ (D : ℝ), 0 ≤ D ∧ ∀ t : ℝ,
              SchwartzMap.seminorm ℝ p q
                (fn.conjTensorProduct
                  (poincareActNPoint
                    (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤
              D * (1 + ‖t‖) ^ p := by
            intro p q
            classical
            let Dτ' := fun p' q' => (hτ p' q').choose
            have hDτ'_nn : ∀ p' q', 0 ≤ Dτ' p' q' :=
              fun p' q' => (hτ p' q').choose_spec.1
            have hDτ'_bound : ∀ p' q' t, SchwartzMap.seminorm ℝ p' q'
                (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm) ≤
                Dτ' p' q' * (1 + ‖t‖) ^ p' :=
              fun p' q' => (hτ p' q').choose_spec.2
            refine ⟨2 ^ p * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
                (SchwartzMap.seminorm ℝ p i fn.borchersConj * Dτ' 0 (q - i) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ' p (q - i)),
              ?_, fun t => ?_⟩
            · apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
              apply Finset.sum_nonneg; intro i _
              apply mul_nonneg (by exact_mod_cast Nat.zero_le _)
              apply add_nonneg
              · exact mul_nonneg (apply_nonneg _ _) (hDτ'_nn 0 (q - i))
              · exact mul_nonneg (apply_nonneg _ _) (hDτ'_nn p (q - i))
            · show SchwartzMap.seminorm ℝ p q (fn.borchersConj.tensorProduct
                  (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤ _
              have htens_base' := SchwartzMap.tensorProduct_seminorm_le p q fn.borchersConj
                  (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)
              have h1_le_pow' : (1 : ℝ) ≤ (1 + ‖t‖) ^ p := by
                apply one_le_pow₀; linarith [norm_nonneg t]
              have hstep' : SchwartzMap.seminorm ℝ p q (fn.borchersConj.tensorProduct
                  (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤
                  2 ^ p * ∑ i ∈ Finset.range (q + 1), ↑(q.choose i) *
                    (SchwartzMap.seminorm ℝ p i fn.borchersConj *
                        (Dτ' 0 (q - i) * (1 + ‖t‖) ^ p) +
                     SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                       (Dτ' p (q - i) * (1 + ‖t‖) ^ p)) := by
                apply htens_base'.trans
                apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) p)
                apply Finset.sum_le_sum; intro i _
                apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le _)
                apply add_le_add
                · apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
                  exact (hDτ'_bound 0 (q - i) t).trans
                    (by simp only [pow_zero, mul_one];
                        exact le_mul_of_one_le_right (hDτ'_nn 0 (q - i)) h1_le_pow')
                · exact mul_le_mul_of_nonneg_left (hDτ'_bound p (q - i) t) (apply_nonneg _ _)
              have h_factor' : ∑ i ∈ Finset.range (q + 1), ↑(q.choose i) *
                  (SchwartzMap.seminorm ℝ p i fn.borchersConj *
                      (Dτ' 0 (q - i) * (1 + ‖t‖) ^ p) +
                   SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                     (Dτ' p (q - i) * (1 + ‖t‖) ^ p)) =
                  (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
                    (SchwartzMap.seminorm ℝ p i fn.borchersConj * Dτ' 0 (q - i) +
                     SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ' p (q - i))) *
                  (1 + ‖t‖) ^ p := by
                rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
              linarith [hstep'.trans (by rw [h_factor', ← mul_assoc])]
          -- Cast transparency: seminorm is insensitive to Eq.mpr transport
          have hcast_pq : ∀ (p q ℓ : ℕ) (hℓ : ℓ = n + m) (f : SchwartzNPointSpace d (n + m)),
              SchwartzMap.seminorm ℝ p q (hℓ.symm ▸ f) = SchwartzMap.seminorm ℝ p q f :=
            fun p q ℓ hℓ f => by subst hℓ; rfl
          -- Composed seminorm: (k,j)-seminorm on target precomposed with diffVarReduction
          let qkj : Seminorm ℝ (SchwartzNPointSpace d (n + m - 1 + 1)) :=
            (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1)) ℂ (k, j)).comp
              ((diffVarReduction d (n + m - 1)).restrictScalars ℝ).toLinearMap
          have hqkj_cont : Continuous ⇑qkj :=
            ((schwartz_withSeminorms ℝ (NPointSpacetime d (n + m - 1)) ℂ).continuous_seminorm
                (k, j)).comp (diffVarReduction d (n + m - 1)).continuous
          -- Bound qkj by finitely many source seminorms (Seminorm.bound_of_continuous)
          obtain ⟨s, C₀, _, hbound⟩ :=
            Seminorm.bound_of_continuous
              (schwartz_withSeminorms ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ) qkj hqkj_cont
          -- Extract polynomial witnesses from htens_all for each index in s
          let Ds := fun i : ℕ × ℕ => (htens_all i.1 i.2).choose
          have hDs_nn : ∀ i, 0 ≤ Ds i := fun i => (htens_all i.1 i.2).choose_spec.1
          have hDs_bound : ∀ (i : ℕ × ℕ) t, SchwartzMap.seminorm ℝ i.1 i.2
              (fn.conjTensorProduct
                (poincareActNPoint
                  (PoincareRepresentation.translationInDirection d 0 t) fm)) ≤
              Ds i * (1 + ‖t‖) ^ i.1 := fun i => (htens_all i.1 i.2).choose_spec.2
          refine ⟨↑C₀ * ∑ i ∈ s, Ds i, s.sup (·.1), ?_, fun t => ?_⟩
          · exact mul_nonneg C₀.prop (Finset.sum_nonneg (fun i _ => hDs_nn i))
          set g_t := fn.conjTensorProduct
            (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)
            with hg_t_def
          -- qkj unfolds to the (k,j)-seminorm of diffVarReduction applied to the input
          have h_qkj : qkj (hk.symm ▸ g_t) =
              SchwartzMap.seminorm ℝ k j
                (diffVarReduction d (n + m - 1) (hk.symm ▸ g_t)) := rfl
          rw [← h_qkj]
          -- h1: apply the CLM bound from Seminorm.bound_of_continuous
          have h1 : qkj (hk.symm ▸ g_t) ≤
              ↑C₀ * (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                (hk.symm ▸ g_t) := by
            have h := hbound (hk.symm ▸ g_t)
            simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h
            linarith
          -- h2: bound each source seminorm using htens_all + hcast_pq
          have h2 : (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                (hk.symm ▸ g_t) ≤ ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 := by
            apply Seminorm.finset_sup_apply_le
              (Finset.sum_nonneg (fun i _ => mul_nonneg (hDs_nn i) (by positivity)))
            intro ⟨p, q⟩ hi
            simp only [SchwartzMap.schwartzSeminormFamily_apply]
            rw [hcast_pq p q ((n + m - 1) + 1) hk g_t]
            exact (hDs_bound (p, q) t).trans
              (Finset.single_le_sum
                (fun j _ => mul_nonneg (hDs_nn j)
                  (pow_nonneg (by linarith [norm_nonneg t]) j.1)) hi)
          -- h3: factor out the largest power using monotonicity
          have h3 : ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 ≤
              (∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1) := by
            rw [Finset.sum_mul]
            apply Finset.sum_le_sum; intro i hi
            apply mul_le_mul_of_nonneg_left _ (hDs_nn i)
            exact pow_le_pow_right₀ (by linarith [norm_nonneg t])
              (Finset.le_sup (f := (·.1)) hi)
          calc qkj (hk.symm ▸ g_t)
              ≤ ↑C₀ * (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                  (hk.symm ▸ g_t) := h1
            _ ≤ ↑C₀ * ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 :=
                mul_le_mul_of_nonneg_left h2 C₀.prop
            _ ≤ ↑C₀ * ((∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1)) :=
                mul_le_mul_of_nonneg_left h3 C₀.prop
            _ = (↑C₀ * ∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1) := by ring
        obtain ⟨Cred, Nred, hCred_nn, hCred⟩ := hFpoly
        exact ⟨Cred + 1, Nred, by linarith, fun t =>
          (hCred t).trans (mul_le_mul_of_nonneg_right (by linarith)
            (pow_nonneg (by linarith [norm_nonneg t]) _))⟩
      -- Bundle w as a CLM for schwartz_clm_fubini_exchange_real
      -- w is already Continuous + IsLinearMap ℂ
      obtain ⟨Θ, hΘ_pointwise, hΘ_w⟩ :=
        schwartz_clm_fubini_exchange_real w hw_cont hw_lin _ hF_cont hF_poly
          (SchwartzMap.fourierTransformCLM ℂ φ)
      -- ── Steps 2+3: ℱ⁻¹ of Θ gives ψ with ψ.fourierTransform = Θ and support condition ─
      obtain ⟨ψ, hψ_ft, hψ_supp⟩ :=
        scd_fourierInv_translate_witness (by omega : 0 < n) (by omega : 0 < m)
          fn fm φ hφ hk hbdry Θ hΘ_pointwise
      exact ⟨ψ, by rw [hψ_ft]; exact hΘ_w, hψ_supp⟩

/-- **Per-summand one-sided Fourier vanishing for the WIP expansion.**

    For each `(n,m)`-summand in the WightmanInnerProduct, the integral
    `∫ W_{n+m}(fₙ*.conjTP(τ_{te₀} fₘ)) · ℱ[φ](t) dt` vanishes when
    `supp(φ) ⊆ (-∞, 0)`.

    This follows directly from `scd_summand_nonneg_fourier_support`: the spectral
    condition forces the distributional Fourier transform of `t ↦ W(fₙ* ⊗ τ_{te₀} fₘ)`
    to be supported on `[0, ∞)`, and `supp(φ) ⊆ (-∞, 0)`, so the distributional
    pairing vanishes.

    **Ref:** Streater-Wightman, §3-1; Reed-Simon II, Theorem X.40. -/
private lemma scd_summand_fourier_vanishing
    (hSCD : SpectralConditionDistribution d Wfn.W)
    {n m : ℕ} (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    ∫ t : ℝ,
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareRepresentation.translationInDirection d 0 t) fm)) *
      ((SchwartzMap.fourierTransformCLM ℂ φ) : ℝ → ℂ) t = 0 :=
  scd_summand_nonneg_fourier_support Wfn hSCD fn fm φ hφ

/-- **Step 1+2: SCD → one-sided Fourier support of the GNS inner product function.**

    The tempered distribution `T_F(ψ) = ∫ ⟪F, U₀(t)F⟫ · ψ(t) dt` has
    one-sided Fourier support in `[0,∞)`, i.e., `T_F(ℱ[φ]) = 0` for every
    Schwartz φ with `supp(φ) ⊆ (-∞, 0)`.

    **Proof:**
    1. By `inner_translate_eq_wip`, lift to the pre-Hilbert space and choose
       a Borchers representative `B` of `F`. Then
       `⟪F, U₀(t)F⟫ = ∑_{n,m} W_{n+m}(f*_n ⊗ τ_{te₀} f_m)`.
    2. Exchange integral and finite sum (each summand is integrable:
       continuous tempered function × Schwartz is L¹).
    3. Each per-(n,m) summand integrates to zero by `scd_summand_fourier_vanishing`.
    4. The sum of zeros is zero.

    **Ref:** Streater-Wightman, §3-1; Reed-Simon II, Theorem X.40. -/
private lemma scd_inner_hasOneSidedFourierSupport
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (F : PreHilbertSpace Wfn) :
    let 𝒰₀ := (gnsPoincareRep Wfn).translationGroup 0 (hsc 0)
    SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ, @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
        (𝒰₀.U t (F : GNSHilbertSpace Wfn)) * (ψ : ℝ → ℂ) t) := by
  intro 𝒰₀
  -- Unfold HasOneSidedFourierSupport: for every Schwartz φ with supp(φ) ⊆ (-∞,0),
  -- show T(FT[φ]) = 0 where T(ψ) = ∫ ⟪F, U₀(t)F⟫ · ψ(t) dt.
  intro φ hφ
  -- Step 1: Quotient induction — choose Borchers representative B of F.
  induction F using Quotient.inductionOn with | h B =>
  set pB : PreHilbertSpace Wfn := ⟦B⟧
  -- Step 2: Bridge GNS inner product → WightmanInnerProduct.
  -- 𝒰₀.U t = poincareActGNS Wfn (translationInDirection d 0 t) by definition,
  -- and inner_translate_eq_wip lifts from GNS to PreHilbert level.
  have hinner_eq : ∀ t : ℝ,
      @inner ℂ _ _ (pB : GNSHilbertSpace Wfn)
        (𝒰₀.U t (pB : GNSHilbertSpace Wfn)) =
      WightmanInnerProduct d Wfn.W B
        (poincareActBorchers
          (PoincareRepresentation.translationInDirection d 0 t) B) := by
    intro t
    have h_U : 𝒰₀.U t = poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d 0 t) := rfl
    rw [h_U, inner_translate_eq_wip Wfn 0 pB pB t]; rfl
  simp_rw [hinner_eq]
  -- Step 3: Unfold WightmanInnerProduct as a finite double sum.
  show ∫ t : ℝ,
    (∑ n ∈ Finset.range (B.bound + 1), ∑ m ∈ Finset.range (B.bound + 1),
      Wfn.W (n + m) ((B.funcs n).conjTensorProduct
        (poincareActNPoint
          (PoincareRepresentation.translationInDirection d 0 t) (B.funcs m)))) *
    ((SchwartzMap.fourierTransformCLM ℂ φ) : ℝ → ℂ) t = 0
  -- Step 4: Distribute FT[φ](t) multiplication into the finite sum.
  simp_rw [Finset.sum_mul]
  -- Step 5: Exchange integral and finite sum, then show each summand is 0.
  set FTφ := SchwartzMap.fourierTransformCLM ℂ φ with hFTφ_def
  rw [MeasureTheory.integral_finset_sum _ (fun n _ =>
    MeasureTheory.integrable_finset_sum _ (fun m _ =>
      scd_summand_integrable Wfn (B.funcs n) (B.funcs m) FTφ))]
  apply Finset.sum_eq_zero; intro n _
  rw [MeasureTheory.integral_finset_sum _ (fun m _ =>
    scd_summand_integrable Wfn (B.funcs n) (B.funcs m) FTφ)]
  apply Finset.sum_eq_zero; intro m _
  exact scd_summand_fourier_vanishing Wfn hSCD (B.funcs n) (B.funcs m) φ hφ

/-! ### Generalized direction chain: `e₀` → arbitrary `y ∈ V̄₊`

The following lemmas generalize the SCD → one-sided Fourier support chain
from the time direction `e₀` to an arbitrary direction `y ∈ V̄₊`. This is
needed for `scd_bochner_forwardCone_support` (multi-dimensional Bochner measure
support on V̄₊ via per-direction null sets).

The proof structure is identical to the `e₀` chain above, with two changes:
1. The shift `ξ_{n-1}(0) ← ξ_{n-1}(0) - t` becomes `ξ_{n-1} ← ξ_{n-1} - t•y`.
2. The contradiction `q_{n-1,0} < 0 → q_{n-1} ∉ V̄₊` (trivial from `timeComponent ≥ 0`)
   becomes `y·q_{n-1} < 0 → q_{n-1} ∉ V̄₊` (by self-duality of V̄₊). -/

/-- Generalization of `diffVarReduction_translate_eq_shift` to arbitrary translation direction.
    Translation by `t • y` shifts the full boundary difference variable `ξ_{n-1}` by `t • y`,
    instead of shifting only the 0-th component. -/
private lemma diffVarReduction_translate_eq_shift_dir {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (y : MinkowskiSpace d)
    (hk : (n + m - 1) + 1 = n + m) (hbdry : n - 1 < n + m - 1) (t : ℝ)
    (ξ : NPointSpacetime d (n + m - 1)) :
    diffVarReduction d (n + m - 1)
      (hk.symm ▸ fn.conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ξ =
    diffVarReduction d (n + m - 1)
      (hk.symm ▸ fn.conjTensorProduct fm)
      (Function.update ξ ⟨n - 1, hbdry⟩ (ξ ⟨n - 1, hbdry⟩ - t • y)) := by
  -- Both sides are fiber integrals; the integrands are pointwise equal in `a`.
  -- Step 1: Unfold diffVarReduction to the fiber integral
  show (∫ a : Fin (d + 1) → ℝ,
      (hk.symm ▸ fn.conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))
        (fun k μ => a μ + diffVarSection d (n + m - 1) ξ k μ)) =
    (∫ a : Fin (d + 1) → ℝ,
      (hk.symm ▸ fn.conjTensorProduct fm)
        (fun k μ => a μ + diffVarSection d (n + m - 1)
          (Function.update ξ ⟨n - 1, hbdry⟩ (ξ ⟨n - 1, hbdry⟩ - t • y)) k μ))
  -- Step 2: The integrands are pointwise equal
  congr 1; ext a
  -- Step 3: Establish how the ▸ cast interacts with SchwartzMap evaluation
  have heval : ∀ (f : SchwartzNPointSpace d (n + m))
      (y : NPointSpacetime d ((n + m - 1) + 1)),
      (hk.symm ▸ f : SchwartzNPointSpace d ((n + m - 1) + 1)) y =
      f (fun (i : Fin (n + m)) (μ : Fin (d + 1)) => y ⟨i.val, by omega⟩ μ) := by
    have := fun (K : ℕ) (hK : K = (n + m - 1) + 1)
        (f : SchwartzNPointSpace d K) (y : NPointSpacetime d ((n + m - 1) + 1)) =>
      show (hK ▸ f : SchwartzNPointSpace d ((n + m - 1) + 1)) y =
        f (fun i μ => y ⟨i.val, hK ▸ i.isLt⟩ μ) from by subst hK; rfl
    exact this (n + m) hk.symm
  simp only [heval]
  -- Step 4: Unfold conjTensorProduct to split into fn and fm parts
  simp only [SchwartzMap.conjTensorProduct_apply]
  simp only [splitFirst, poincareActNPoint_apply]
  dsimp [diffVarSection]
  congr 1
  · -- fn parts: sums at indices < n don't include the update at n-1
    congr 2; funext i; funext μ; congr 1
    apply Finset.sum_congr rfl
    intro ⟨j, hj⟩ _
    simp only [Function.update, Fin.mk.injEq]
    split_ifs with h
    · omega
    · rfl
  · -- fm parts: translation'(t • y) shifts all fm-arguments by -t • y
    congr 1; funext j; funext μ
    dsimp
    simp only [Function.update_apply, splitLast, poincareActNPointDomain,
      PoincareGroup.act_def,
      PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
      PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
      inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    -- Goal: a μ + ∑ ξ_i(μ) + -(t * y μ) = a μ + ∑ (if cond then (ξ_{n-1} - t•y) else ξ)(μ)
    -- The if-sum differs from plain sum only at n-1, by exactly -t * y(μ).
    suffices h : ∀ x : Fin (n + ↑j),
        (if (⟨↑x, by omega⟩ : Fin (n + m - 1)) = ⟨n - 1, hbdry⟩
         then (ξ ⟨n - 1, hbdry⟩ - t • y)
         else ξ ⟨↑x, by omega⟩) μ =
        ξ ⟨↑x, by omega⟩ μ +
          if x = (⟨n - 1, by omega⟩ : Fin (n + ↑j)) then -(t * y μ) else 0 by
      simp_rw [h, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]; ring
    intro x
    simp only [Fin.ext_iff]
    split_ifs with hx
    · rw [show ξ ⟨↑x, by omega⟩ = ξ ⟨n - 1, hbdry⟩ from
        congr_arg ξ (Fin.ext hx : (⟨↑x, _⟩ : Fin (n + m - 1)) = ⟨n - 1, hbdry⟩)]
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    · simp

/-- Generalization of `partial_convolution_fourier_factorization` to arbitrary direction.
    The partial convolution along `t • y` (shifting the full j-th variable) factorizes as
    `ψ(q) = φ(∑_μ y(μ) · q(j)(μ)) · K(q)` in the Fourier domain. -/
private theorem partial_convolution_fourier_factorization_dir
    {n_pts : ℕ} (j : Fin n_pts)
    (y : MinkowskiSpace d)
    (G : SchwartzNPointSpace d n_pts)
    (φ : SchwartzMap ℝ ℂ)
    (Θ : SchwartzNPointSpace d n_pts)
    (hΘ : ∀ ξ : NPointSpacetime d n_pts,
        Θ ξ = ∫ t : ℝ,
          ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
            G (Function.update ξ j (ξ j - t • y))) :
    ∃ ψ : SchwartzNPointSpace d n_pts,
        ψ.fourierTransform = Θ ∧
        ∀ q : NPointSpacetime d n_pts,
          ψ q ≠ 0 → (φ : ℝ → ℂ) (∑ μ : Fin (d + 1), y μ * q j μ) ≠ 0 := by
  -- Construct ψ = ℱ⁻¹[Θ] and K = ℱ⁻¹[G] via nPointToEuclidean (identical to e₀ version)
  let e := nPointToEuclidean d n_pts
  let ψ : SchwartzNPointSpace d n_pts :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (FourierTransform.fourierInv
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ))
  let K : SchwartzNPointSpace d n_pts :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (FourierTransform.fourierInv
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G))
  -- Step 1: ψ.fourierTransform = Θ (identical to e₀)
  have hψ_ft : ψ.fourierTransform = Θ := by
    simp only [SchwartzNPointSpace.fourierTransform, ψ]
    ext x
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      SchwartzMap.fourierTransformCLM_apply]
    have h_cancel : ∀ (f : SchwartzMap _ ℂ),
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) = f := by
      intro f; ext y
      simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [h_cancel]
    exact congrFun (congrArg _ (FourierTransform.fourier_fourierInv_eq _)) _
  refine ⟨ψ, hψ_ft, fun q hq => ?_⟩
  -- Step 2: ψ q = φ(∑ y μ * q j μ) * K q
  suffices hfactor : ψ q = (φ : ℝ → ℂ) (∑ μ : Fin (d + 1), y μ * q j μ) * K q by
    rw [hfactor] at hq; exact left_ne_zero_of_mul hq
  simp only [ψ, K, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rw [show (FourierTransform.fourierInv
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ) : _ → ℂ) (e q) =
    FourierTransform.fourierInv
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Θ : _ → ℂ)) (e q) from
    congrFun (SchwartzMap.fourierInv_coe _) (e q)]
  rw [show (FourierTransform.fourierInv
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G) : _ → ℂ) (e q) =
    FourierTransform.fourierInv
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G : _ → ℂ)) (e q) from
    congrFun (SchwartzMap.fourierInv_coe _) (e q)]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [Real.fourierInv_eq' (f := (⇑Θ ∘ ⇑e.symm)) (w := e q),
      Real.fourierInv_eq' (f := (⇑G ∘ ⇑e.symm)) (w := e q)]
  simp_rw [Function.comp_apply, hΘ]
  -- ─── Direction vector and abbreviations ────────────────────────
  set ey : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) :=
    ∑ μ : Fin (d + 1), y μ • EuclideanSpace.single (j, μ) 1 with hey_def
  set w := e q with hw_def
  set FTφ_s := (SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) with hFTφ_s_def
  -- ─── Coordinate and inner product identities ──────────────────
  have h_coord : ∀ μ : Fin (d + 1), w (j, μ) = q j μ := by
    intro μ; simp [w, e, nPointToEuclidean, uncurryLinearEquiv,
      PiLp.continuousLinearEquiv_symm_apply]
  have h_inner_ey : @inner ℝ _ _ ey w = ∑ μ : Fin (d + 1), y μ * q j μ := by
    simp only [ey, sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left]
    congr 1; funext μ; rw [map_one, one_mul, h_coord μ]
  -- ─── Shift = EuclideanSpace translation ────────────────────────
  have h_shift : ∀ (v : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1))) (t : ℝ),
      Function.update (e.symm v) j ((e.symm v) j - t • y) =
      e.symm (v - t • ey) := by
    intro v t; ext i μ
    simp only [Function.update_apply]
    simp only [e, ey, nPointToEuclidean, uncurryLinearEquiv,
      PiLp.continuousLinearEquiv_symm_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_trans_apply, Finset.sum_apply,
      EuclideanSpace.single_apply, PiLp.single_apply, Prod.mk.injEq]
    split_ifs <;> simp_all <;> ring
  simp_rw [h_shift]
  -- ─── 1-D Fourier inversion ────────────────────────────────────
  have h_fourier_inv_at :
      ∫ t : ℝ, (FTφ_s : ℝ → ℂ) t *
        Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ (t • ey) w) * Complex.I) =
      (φ : ℝ → ℂ) (∑ μ : Fin (d + 1), y μ * q j μ) := by
    simp only [real_inner_smul_left, h_inner_ey]
    have hinv : FourierTransform.fourierInv (FTφ_s : ℝ → ℂ) = (φ : ℝ → ℂ) := by
      have h := congrArg (fun (f : SchwartzMap ℝ ℂ) => (f : ℝ → ℂ))
        (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) φ)
      dsimp only at h; rwa [SchwartzMap.fourierInv_coe] at h
    have h_eval := congrFun hinv (∑ μ : Fin (d + 1), y μ * q j μ)
    rw [Real.fourierInv_eq'] at h_eval
    rw [← h_eval]; refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t; rw [smul_eq_mul, mul_comm (Complex.exp _)]
    congr 1; congr 1; congr 1; congr 1
    simp [inner, mul_comm]
  -- ─── Integrability ─────────────────────────────────────────────
  set Ge : SchwartzMap (EuclideanSpace ℝ (Fin n_pts × Fin (d + 1))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G with hGe_def
  have hGe_eq : ∀ v, Ge v = G (e.symm v) := fun v => by
    simp [Ge, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  have hGe_int : MeasureTheory.Integrable (Ge : _ → ℂ) := Ge.integrable
  have hFTφ_int : MeasureTheory.Integrable (FTφ_s : ℝ → ℂ) := FTφ_s.integrable
  simp_rw [← hGe_eq]
  simp_rw [smul_eq_mul]
  -- ─── Fubini + COV ─────────────────────────────────────────────
  set E_fun := fun v : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) =>
    Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I)
  have hE_norm : ∀ v, ‖E_fun v‖ = 1 := fun v => Complex.norm_exp_ofReal_mul_I _
  have h_int_prod : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) × ℝ =>
        E_fun p.1 * ((FTφ_s : ℝ → ℂ) p.2 * Ge (p.1 - p.2 • ey)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hcont_prod : Continuous (fun p : EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)) × ℝ =>
        E_fun p.1 * ((FTφ_s : ℝ → ℂ) p.2 * Ge (p.1 - p.2 • ey))) := by
      apply Continuous.mul
      · exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp
            (continuous_const.mul (continuous_inner.comp
              (Continuous.prodMk continuous_fst continuous_const)))).mul
            continuous_const))
      · exact (FTφ_s.continuous.comp continuous_snd).mul
            (Ge.continuous.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))
    rw [MeasureTheory.integrable_prod_iff' hcont_prod.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · refine ((hGe_int.comp_sub_right (t • ey)).norm.const_mul
        ‖(FTφ_s : ℝ → ℂ) t‖).mono'
        ((hcont_prod.comp (Continuous.prodMk continuous_id
          (continuous_const (y := t)))).aestronglyMeasurable) ?_
      filter_upwards with v; simp [norm_mul, hE_norm]
    · have h_bound : ∀ t : ℝ,
          ∫ v, ‖E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ey))‖ =
          ‖(FTφ_s : ℝ → ℂ) t‖ * ∫ v, ‖Ge v‖ := by
        intro t; simp only [norm_mul, hE_norm, one_mul]
        rw [← smul_eq_mul (a := ‖(FTφ_s : ℝ → ℂ) t‖),
            ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
        exact MeasureTheory.integral_sub_right_eq_self
          (fun v => ‖(FTφ_s : ℝ → ℂ) t‖ * ‖Ge v‖) (t • ey)
      simp_rw [h_bound]
      exact hFTφ_int.norm.mul_const _
  -- ─── COV step ──────────────────────────────────────────────────
  have h_fubini_cov : ∀ t : ℝ,
      ∫ v, Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
        Ge (v - t • ey) =
      Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I) *
        ∫ v, Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) * Ge v := by
    intro t
    have h_cov := (MeasureTheory.integral_add_right_eq_self
      (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n_pts × Fin (d + 1)))))
      (fun v => Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
        Ge (v - t • ey)) (t • ey))
    simp only [add_sub_cancel_right] at h_cov
    rw [← h_cov]
    simp_rw [_root_.inner_add_left, real_inner_smul_left, h_inner_ey]
    simp_rw [show ∀ (a b : ℝ), ↑(2 * Real.pi * (a + b)) * Complex.I =
      ↑(2 * Real.pi * a) * Complex.I + ↑(2 * Real.pi * b) * Complex.I from by
      intro a b; push_cast; ring]
    simp_rw [Complex.exp_add]
    simp_rw [show ∀ u, (Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ u w) * Complex.I) *
        Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I)) * Ge u =
      Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I) *
        (Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ u w) * Complex.I) * Ge u) from
      fun u => by ring]
    rw [← smul_eq_mul (a := Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I)),
        ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
  -- ─── Main calc chain ──────────────────────────────────────────
  have h_push : ∀ v, E_fun v * (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) =
      ∫ t, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) := by
    intro v; rw [← smul_eq_mul (a := E_fun v), ← MeasureTheory.integral_smul]
    simp_rw [smul_eq_mul]
  conv_lhs => arg 2; ext v; rw [show Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ v w) * Complex.I) *
    (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) = E_fun v * (∫ t, (FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) from rfl,
    h_push]
  rw [MeasureTheory.integral_integral_swap h_int_prod]
  have h_inner : ∀ t, ∫ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) =
      (FTφ_s : ℝ → ℂ) t * (Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I) *
        ∫ v, E_fun v * Ge v) := by
    intro t
    have : ∫ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) =
        (FTφ_s : ℝ → ℂ) t * ∫ v, E_fun v * Ge (v - t • ey) := by
      simp_rw [show ∀ v, E_fun v * ((FTφ_s : ℝ → ℂ) t * Ge (v - t • ey)) =
        (FTφ_s : ℝ → ℂ) t * (E_fun v * Ge (v - t • ey)) from fun v => by ring]
      rw [← smul_eq_mul (a := (FTφ_s : ℝ → ℂ) t),
          ← MeasureTheory.integral_smul]; simp_rw [smul_eq_mul]
    rw [this, h_fubini_cov]
  simp_rw [h_inner]
  simp_rw [show ∀ t, (FTφ_s : ℝ → ℂ) t *
      (Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I) *
        ∫ u, E_fun u * Ge u) =
    ((FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I)) *
      (∫ u, E_fun u * Ge u) from fun t => by ring]
  simp_rw [show ∀ y_val, (FTφ_s : ℝ → ℂ) y_val *
      Complex.exp (↑(2 * Real.pi * (y_val * (∑ μ, y μ * q j μ))) * Complex.I) *
      (∫ v, E_fun v * Ge v) =
    (∫ v, E_fun v * Ge v) •
      ((FTφ_s : ℝ → ℂ) y_val *
        Complex.exp (↑(2 * Real.pi * (y_val * (∑ μ, y μ * q j μ))) * Complex.I)) from
    fun y_val => by rw [smul_eq_mul]; ring]
  rw [MeasureTheory.integral_smul, smul_eq_mul]
  simp_rw [show ∀ t, (FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * (t * (∑ μ, y μ * q j μ))) * Complex.I) =
    (FTφ_s : ℝ → ℂ) t *
      Complex.exp (↑(2 * Real.pi * @inner ℝ _ _ (t • ey) w) * Complex.I) from
    fun t => by rw [real_inner_smul_left, h_inner_ey]]
  rw [h_fourier_inv_at, mul_comm]

/-- Generalization of `scd_fourierInv_translate_witness` to arbitrary direction. -/
private lemma scd_fourierInv_translate_witness_dir {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (y : MinkowskiSpace d)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0)
    (hk : (n + m - 1) + 1 = n + m) (hbdry : n - 1 < n + m - 1)
    (Θ : SchwartzNPointSpace d (n + m - 1))
    (hΘ : ∀ ξ : NPointSpacetime d (n + m - 1),
        Θ ξ = ∫ t : ℝ,
          ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
            diffVarReduction d (n + m - 1)
              (hk.symm ▸ fn.conjTensorProduct
                (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ξ) :
    ∃ ψ : SchwartzNPointSpace d (n + m - 1),
        ψ.fourierTransform = Θ ∧
        ∀ q : NPointSpacetime d (n + m - 1),
          ψ q ≠ 0 → (φ : ℝ → ℂ) (∑ μ : Fin (d + 1), y μ * q ⟨n - 1, hbdry⟩ μ) ≠ 0 := by
  -- Combine shift_dir + partial_convolution_dir, exactly as the e₀ version.
  let G₀ := diffVarReduction d (n + m - 1) (hk.symm ▸ fn.conjTensorProduct fm)
  have hΘ_shift : ∀ ξ : NPointSpacetime d (n + m - 1),
      Θ ξ = ∫ t : ℝ,
        ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
          G₀ (Function.update ξ ⟨n - 1, hbdry⟩ (ξ ⟨n - 1, hbdry⟩ - t • y)) := by
    intro ξ; rw [hΘ ξ]; congr 1; ext t; congr 1
    exact diffVarReduction_translate_eq_shift_dir hn hm fn fm y hk hbdry t ξ
  exact partial_convolution_fourier_factorization_dir ⟨n - 1, hbdry⟩ y G₀ φ Θ hΘ_shift

set_option maxHeartbeats 800000 in
/-- Generalization of `scd_summand_nonneg_fourier_support` to arbitrary `y ∈ V̄₊`.
    Uses self-duality of the forward cone: `y, q ∈ V̄₊ → ∑_μ y_μ q_μ ≥ 0`. -/
private lemma scd_summand_nonneg_fourier_support_dir
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (y : MinkowskiSpace d) (hy : y ∈ ForwardMomentumCone d)
    {n m : ℕ} (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m) :
    HasNonnegDistrFourierSupport (fun t =>
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))) := by
  intro φ hφ
  by_cases hm : m = 0
  · -- m = 0: τ acts trivially on fm (Fin 0 domain), so g(t) is constant.
    have h_act_fm : ∀ t : ℝ,
        poincareActNPoint (PoincareGroup.translation' ((t : ℝ) • y)) fm = fm := by
      intro t; subst hm; ext x; simp only [poincareActNPoint_apply]
      congr 1; ext i; exact Fin.elim0 i
    simp_rw [h_act_fm]
    exact hasNonnegDistrFourierSupport_const (Wfn.W (n + m) (fn.conjTensorProduct fm)) φ hφ
  · by_cases hn : n = 0
    · -- n = 0: g(t) is constant by translation invariance (any direction).
      have h_const : ∀ t : ℝ,
          Wfn.W (n + m) (fn.conjTensorProduct
            (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) =
          Wfn.W (n + m) (fn.conjTensorProduct fm) := by
        intro t
        set τ := PoincareGroup.translation' (t • y) with hτ_def
        have h_act_fn : poincareActNPoint τ fn = fn := by
          subst hn; ext x; simp only [poincareActNPoint_apply]
          congr 1; ext i; exact Fin.elim0 i
        conv_lhs => rw [← h_act_fn]
        symm
        apply Wfn.translation_invariant (n + m) (-(t • y))
        intro x
        rw [poincareActNPoint_conjTensorProduct]
        congr 1; ext i
        simp only [poincareActNPointDomain, PoincareGroup.act_def,
          PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
          hτ_def, PoincareGroup.translation'_translation,
          PoincareGroup.translation'_lorentz,
          inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
      simp_rw [h_const]
      exact hasNonnegDistrFourierSupport_const (Wfn.W (n + m) (fn.conjTensorProduct fm)) φ hφ
    · -- n ≥ 1, m ≥ 1: Non-degenerate SCD argument with self-duality.
      have hpos : 0 < n + m := by omega
      have hk : (n + m - 1) + 1 = n + m := Nat.sub_add_cancel hpos
      obtain ⟨w, hw_cont, hw_lin, hw_factor, hw_vanish⟩ := hSCD (n + m - 1)
      have cast_W : ∀ (ℓ : ℕ) (hℓ : ℓ = n + m) (f : SchwartzNPointSpace d (n + m)),
          Wfn.W ℓ (hℓ.symm ▸ f) = Wfn.W (n + m) f := fun ℓ hℓ f => by subst hℓ; rfl
      have hw_eq : ∀ (f : SchwartzNPointSpace d (n + m)),
          Wfn.W (n + m) f = w (diffVarReduction d (n + m - 1) (hk.symm ▸ f)) :=
        fun f => by rw [← cast_W _ hk f]; exact hw_factor _
      simp_rw [hw_eq]
      have hbdry : n - 1 < n + m - 1 := by omega
      -- The key `h_main`: construct ψ with ψ.fourierTransform = Θ and support condition
      suffices h_main : ∃ ψ : SchwartzNPointSpace d (n + m - 1),
          (w (ψ.fourierTransform) =
            ∫ t : ℝ,
              w (diffVarReduction d (n + m - 1) (hk.symm ▸ fn.conjTensorProduct
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))) *
              ((SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) ∧
          (∀ q : NPointSpacetime d (n + m - 1),
            ψ q ≠ 0 → (φ : ℝ → ℂ) (∑ μ : Fin (d + 1), y μ * q ⟨n - 1, hbdry⟩ μ) ≠ 0) by
        -- Self-duality contradiction: y·q_{n-1} < 0 contradicts y, q_{n-1} ∈ V̄₊
        obtain ⟨ψ, h_eq, h_factor⟩ := h_main
        have h_zero : w (ψ.fourierTransform) = 0 := hw_vanish ψ fun q hq =>
          ⟨⟨n - 1, hbdry⟩, fun hmem => by
            have hφ_ne := h_factor q hq
            have h_neg := hφ _ (Function.mem_support.mpr hφ_ne)
            -- Self-duality: y ∈ V̄₊ and q_{n-1} ∈ V̄₊ → ∑_μ y_μ q_{n-1,μ} ≥ 0
            have h_nn : ∑ μ : Fin (d + 1), y μ * q ⟨n - 1, hbdry⟩ μ ≥ 0 :=
              euclideanDot_nonneg_closedCone y hy (q ⟨n - 1, hbdry⟩) hmem
            linarith⟩
        exact h_eq.symm.trans h_zero
      -- Steps 1–3: Construct ψ via CLM exchange + shift_dir + partial_convolution_dir.
      -- Follows the e₀ version with translation'(t•y) replacing translationInDirection d 0 t.
      -- ── Flat translation equivalence ──────────────────────────────────────────
      set η_y : Fin (m * (d + 1)) → ℝ :=
        fun k => -(y ((finProdFinEquiv.symm k).2)) with hη_y_def
      have h_translate_eq : ∀ t : ℝ,
          poincareActNPoint (PoincareGroup.translation' (t • y)) fm =
          unflattenSchwartzNPointLocal (d := d)
            (SCV.translateSchwartz (t • η_y)
              (flattenSchwartzNPointLocal (d := d) fm)) := by
        intro t; ext x
        simp only [poincareActNPoint_apply, SCV.translateSchwartz_apply,
          unflattenSchwartzNPointLocal_apply, flattenSchwartzNPointLocal_apply]
        congr 1; funext i; ext ν
        simp only [poincareActNPointDomain, PoincareGroup.act_def,
          PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
          PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
          inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec,
          flattenCLEquivRealLocal_symm_apply, flattenCLEquivRealLocal_apply,
          Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hη_y_def,
          Equiv.symm_apply_apply]
        ring
      -- ── Step 1a: Continuity ────────────────────────────────────────────────
      have hF_cont : Continuous (fun t : ℝ =>
          diffVarReduction d (n + m - 1)
            (hk.symm ▸ fn.conjTensorProduct
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))) := by
        have h_inner : Continuous (fun t : ℝ =>
            fn.conjTensorProduct
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) := by
          simp_rw [h_translate_eq]
          exact (SchwartzMap.conjTensorProduct_continuous_right fn).comp
            ((unflattenSchwartzNPointLocal (d := d) : _ →L[ℂ] _).continuous.comp
              (continuous_translateSchwartz_smul
                (η := η_y) (flattenSchwartzNPointLocal (d := d) fm)))
        have h_eqMpr_cont : ∀ {a b : ℕ} (h : a = b),
            Continuous (fun f : SchwartzNPointSpace d a =>
              (h ▸ f : SchwartzNPointSpace d b)) :=
          fun h => by subst h; exact continuous_id
        exact (diffVarReduction d (n + m - 1)).continuous.comp
          ((h_eqMpr_cont hk.symm).comp h_inner)
      -- ── Step 1b: Polynomial growth bounds ──────────────────────────────────
      have hF_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
          SchwartzMap.seminorm ℝ k j
            (diffVarReduction d (n + m - 1)
              (hk.symm ▸ fn.conjTensorProduct
                (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))) ≤
          C * (1 + ‖t‖) ^ N := by
        intro k j
        -- Polynomial bound for the translate family
        have hτ : ∀ (p q : ℕ), ∃ (Dτ : ℝ), 0 ≤ Dτ ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ p q
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm) ≤
            Dτ * (1 + ‖t‖) ^ p := by
          intro p q
          obtain ⟨D, hD_nn, hD⟩ := SCV.seminorm_translateSchwartz_le p q
            (flattenSchwartzNPointLocal (d := d) fm)
          refine ⟨D * (1 + ‖η_y‖) ^ p, by positivity, fun t => ?_⟩
          rw [h_translate_eq]
          set ψ_t := SCV.translateSchwartz (t • η_y) (flattenSchwartzNPointLocal (d := d) fm)
          have h_unflatten_le : SchwartzMap.seminorm ℝ p q
              (unflattenSchwartzNPointLocal (d := d) ψ_t) ≤
              SchwartzMap.seminorm ℝ p q ψ_t := by
            apply SchwartzMap.seminorm_le_bound ℝ p q _ (by positivity)
            intro x
            set e := (flattenCLEquivRealLocal m (d + 1)).toContinuousLinearMap
            have hcomp : (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) =
                ↑ψ_t ∘ flattenCLEquivRealLocal m (d + 1) := by
              ext y; simp [unflattenSchwartzNPointLocal,
                SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
            have hiter : iteratedFDeriv ℝ q
                (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x =
                ContinuousMultilinearMap.compContinuousLinearMap
                  (iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x))
                  (fun _ => e) := by
              rw [hcomp]
              exact ContinuousLinearMap.iteratedFDeriv_comp_right e ψ_t.smooth' x
                (by exact_mod_cast le_top)
            have hnorm_le : ‖x‖ ≤ ‖flattenCLEquivRealLocal m (d + 1) x‖ := by
              rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
              intro i; rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
              intro j
              rw [show ‖x i j‖ =
                  ‖flattenCLEquivRealLocal m (d + 1) x (finProdFinEquiv (i, j))‖
                from by simp [flattenCLEquivRealLocal_apply]]
              exact norm_le_pi_norm _ _
            have hprod_le : ∏ _ : Fin q, ‖e‖ ≤ 1 := by
              have he_norm : ‖e‖ ≤ 1 := by
                apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
                intro y_val; rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
                intro k
                change ‖y_val (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2‖ ≤ ‖y_val‖
                calc ‖y_val (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2‖
                    ≤ ‖y_val (finProdFinEquiv.symm k).1‖ := norm_le_pi_norm _ _
                  _ ≤ ‖y_val‖ := norm_le_pi_norm _ _
              calc ∏ _ : Fin q, ‖e‖ ≤ ∏ _ : Fin q, (1 : ℝ) := by gcongr
                _ = 1 := Finset.prod_const_one
            have hiter_norm : ‖iteratedFDeriv ℝ q
                (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x‖ ≤
                ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ := by
              rw [hiter]
              calc ‖ContinuousMultilinearMap.compContinuousLinearMap _ _‖
                  ≤ ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ *
                      ∏ _ : Fin q, ‖e‖ :=
                    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
                _ ≤ ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ * 1 :=
                    by gcongr
                _ = _ := mul_one _
            calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ q
                    (unflattenSchwartzNPointLocal (d := d) ψ_t : NPointDomain d m → ℂ) x‖
                ≤ ‖flattenCLEquivRealLocal m (d + 1) x‖ ^ p *
                    ‖iteratedFDeriv ℝ q ↑ψ_t (flattenCLEquivRealLocal m (d + 1) x)‖ :=
                  by gcongr
              _ ≤ SchwartzMap.seminorm ℝ p q ψ_t :=
                  SchwartzMap.le_seminorm ℝ p q ψ_t (flattenCLEquivRealLocal m (d + 1) x)
          have h_translate_le : SchwartzMap.seminorm ℝ p q ψ_t ≤
              D * (1 + ‖η_y‖) ^ p * (1 + ‖t‖) ^ p := by
            have heq : SchwartzMap.seminorm ℝ p q ψ_t = SchwartzMap.seminorm ℂ p q ψ_t := rfl
            rw [heq]
            calc SchwartzMap.seminorm ℂ p q ψ_t ≤ D * (1 + ‖t • η_y‖) ^ p := hD _
              _ = D * (1 + |t| * ‖η_y‖) ^ p := by rw [norm_smul, Real.norm_eq_abs]
              _ ≤ D * ((1 + ‖η_y‖) * (1 + |t|)) ^ p := by
                    gcongr; nlinarith [norm_nonneg η_y, abs_nonneg t]
              _ = D * (1 + ‖η_y‖) ^ p * (1 + |t|) ^ p := by rw [mul_pow]; ring
              _ = D * (1 + ‖η_y‖) ^ p * (1 + ‖t‖) ^ p := by rw [← Real.norm_eq_abs t]
          linarith
        -- Tensor product bounds (same structure as e₀)
        have htens : ∃ (Ctens : ℝ), 0 ≤ Ctens ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ k j
              (fn.conjTensorProduct
                (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤
            Ctens * (1 + ‖t‖) ^ k := by
          classical
          let Dτ := fun p q => (hτ p q).choose
          have hDτ_nn : ∀ p q, 0 ≤ Dτ p q := fun p q => (hτ p q).choose_spec.1
          have hDτ_bound : ∀ p q t, SchwartzMap.seminorm ℝ p q
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm) ≤
              Dτ p q * (1 + ‖t‖) ^ p := fun p q => (hτ p q).choose_spec.2
          refine ⟨2 ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              (SchwartzMap.seminorm ℝ k i fn.borchersConj * Dτ 0 (j - i) +
               SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ k (j - i)),
            ?_, fun t => ?_⟩
          · apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
            apply Finset.sum_nonneg; intro i _
            apply mul_nonneg (by exact_mod_cast Nat.zero_le _)
            apply add_nonneg
            · exact mul_nonneg (apply_nonneg _ _) (hDτ_nn 0 (j - i))
            · exact mul_nonneg (apply_nonneg _ _) (hDτ_nn k (j - i))
          show SchwartzMap.seminorm ℝ k j (fn.borchersConj.tensorProduct
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤ _
          have htens_base := SchwartzMap.tensorProduct_seminorm_le k j fn.borchersConj
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)
          have h1_le_pow : (1 : ℝ) ≤ (1 + ‖t‖) ^ k := by
            apply one_le_pow₀; linarith [norm_nonneg t]
          have hstep : SchwartzMap.seminorm ℝ k j (fn.borchersConj.tensorProduct
              (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤
              2 ^ k * ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
                (SchwartzMap.seminorm ℝ k i fn.borchersConj * (Dτ 0 (j - i) * (1 + ‖t‖) ^ k) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                   (Dτ k (j - i) * (1 + ‖t‖) ^ k)) := by
            apply htens_base.trans
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
            apply Finset.sum_le_sum; intro i _
            apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le _)
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
              exact (hDτ_bound 0 (j - i) t).trans
                (by simp only [pow_zero, mul_one];
                    exact le_mul_of_one_le_right (hDτ_nn 0 (j - i)) h1_le_pow)
            · exact mul_le_mul_of_nonneg_left (hDτ_bound k (j - i) t) (apply_nonneg _ _)
          have h_factor : ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
              (SchwartzMap.seminorm ℝ k i fn.borchersConj * (Dτ 0 (j - i) * (1 + ‖t‖) ^ k) +
               SchwartzMap.seminorm ℝ 0 i fn.borchersConj * (Dτ k (j - i) * (1 + ‖t‖) ^ k)) =
              (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
                (SchwartzMap.seminorm ℝ k i fn.borchersConj * Dτ 0 (j - i) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ k (j - i))) *
              (1 + ‖t‖) ^ k := by
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
          linarith [hstep.trans (by rw [h_factor, ← mul_assoc])]
        -- Composed with diffVarReduction (same structure as e₀)
        have hFpoly : ∃ (Cred : ℝ) (Nred : ℕ), 0 ≤ Cred ∧ ∀ t : ℝ,
            SchwartzMap.seminorm ℝ k j
              (diffVarReduction d (n + m - 1)
                (hk.symm ▸ fn.conjTensorProduct
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm))) ≤
            Cred * (1 + ‖t‖) ^ Nred := by
          have htens_all : ∀ (p q : ℕ), ∃ (D : ℝ), 0 ≤ D ∧ ∀ t : ℝ,
              SchwartzMap.seminorm ℝ p q
                (fn.conjTensorProduct
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤
              D * (1 + ‖t‖) ^ p := by
            intro p q; classical
            let Dτ' := fun p' q' => (hτ p' q').choose
            have hDτ'_nn : ∀ p' q', 0 ≤ Dτ' p' q' :=
              fun p' q' => (hτ p' q').choose_spec.1
            have hDτ'_bound : ∀ p' q' t, SchwartzMap.seminorm ℝ p' q'
                (poincareActNPoint (PoincareGroup.translation' (t • y)) fm) ≤
                Dτ' p' q' * (1 + ‖t‖) ^ p' :=
              fun p' q' => (hτ p' q').choose_spec.2
            refine ⟨2 ^ p * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
                (SchwartzMap.seminorm ℝ p i fn.borchersConj * Dτ' 0 (q - i) +
                 SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ' p (q - i)),
              ?_, fun t => ?_⟩
            · apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
              apply Finset.sum_nonneg; intro i _
              apply mul_nonneg (by exact_mod_cast Nat.zero_le _)
              apply add_nonneg
              · exact mul_nonneg (apply_nonneg _ _) (hDτ'_nn 0 (q - i))
              · exact mul_nonneg (apply_nonneg _ _) (hDτ'_nn p (q - i))
            · show SchwartzMap.seminorm ℝ p q (fn.borchersConj.tensorProduct
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤ _
              have htens_base' := SchwartzMap.tensorProduct_seminorm_le p q fn.borchersConj
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)
              have h1_le_pow' : (1 : ℝ) ≤ (1 + ‖t‖) ^ p := by
                apply one_le_pow₀; linarith [norm_nonneg t]
              have hstep' : SchwartzMap.seminorm ℝ p q (fn.borchersConj.tensorProduct
                  (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤
                  2 ^ p * ∑ i ∈ Finset.range (q + 1), ↑(q.choose i) *
                    (SchwartzMap.seminorm ℝ p i fn.borchersConj *
                        (Dτ' 0 (q - i) * (1 + ‖t‖) ^ p) +
                     SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                       (Dτ' p (q - i) * (1 + ‖t‖) ^ p)) := by
                apply htens_base'.trans
                apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) p)
                apply Finset.sum_le_sum; intro i _
                apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le _)
                apply add_le_add
                · apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
                  exact (hDτ'_bound 0 (q - i) t).trans
                    (by simp only [pow_zero, mul_one];
                        exact le_mul_of_one_le_right (hDτ'_nn 0 (q - i)) h1_le_pow')
                · exact mul_le_mul_of_nonneg_left (hDτ'_bound p (q - i) t) (apply_nonneg _ _)
              have h_factor' : ∑ i ∈ Finset.range (q + 1), ↑(q.choose i) *
                  (SchwartzMap.seminorm ℝ p i fn.borchersConj *
                      (Dτ' 0 (q - i) * (1 + ‖t‖) ^ p) +
                   SchwartzMap.seminorm ℝ 0 i fn.borchersConj *
                     (Dτ' p (q - i) * (1 + ‖t‖) ^ p)) =
                  (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
                    (SchwartzMap.seminorm ℝ p i fn.borchersConj * Dτ' 0 (q - i) +
                     SchwartzMap.seminorm ℝ 0 i fn.borchersConj * Dτ' p (q - i))) *
                  (1 + ‖t‖) ^ p := by
                rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
              linarith [hstep'.trans (by rw [h_factor', ← mul_assoc])]
          have hcast_pq : ∀ (p q ℓ : ℕ) (hℓ : ℓ = n + m) (f : SchwartzNPointSpace d (n + m)),
              SchwartzMap.seminorm ℝ p q (hℓ.symm ▸ f) = SchwartzMap.seminorm ℝ p q f :=
            fun p q ℓ hℓ f => by subst hℓ; rfl
          let qkj : Seminorm ℝ (SchwartzNPointSpace d (n + m - 1 + 1)) :=
            (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1)) ℂ (k, j)).comp
              ((diffVarReduction d (n + m - 1)).restrictScalars ℝ).toLinearMap
          have hqkj_cont : Continuous ⇑qkj :=
            ((schwartz_withSeminorms ℝ (NPointSpacetime d (n + m - 1)) ℂ).continuous_seminorm
                (k, j)).comp (diffVarReduction d (n + m - 1)).continuous
          obtain ⟨s, C₀, _, hbound⟩ :=
            Seminorm.bound_of_continuous
              (schwartz_withSeminorms ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ) qkj hqkj_cont
          let Ds := fun i : ℕ × ℕ => (htens_all i.1 i.2).choose
          have hDs_nn : ∀ i, 0 ≤ Ds i := fun i => (htens_all i.1 i.2).choose_spec.1
          have hDs_bound : ∀ (i : ℕ × ℕ) t, SchwartzMap.seminorm ℝ i.1 i.2
              (fn.conjTensorProduct
                (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) ≤
              Ds i * (1 + ‖t‖) ^ i.1 := fun i => (htens_all i.1 i.2).choose_spec.2
          refine ⟨↑C₀ * ∑ i ∈ s, Ds i, s.sup (·.1), ?_, fun t => ?_⟩
          · exact mul_nonneg C₀.prop (Finset.sum_nonneg (fun i _ => hDs_nn i))
          set g_t := fn.conjTensorProduct
            (poincareActNPoint (PoincareGroup.translation' (t • y)) fm) with hg_t_def
          have h_qkj : qkj (hk.symm ▸ g_t) =
              SchwartzMap.seminorm ℝ k j
                (diffVarReduction d (n + m - 1) (hk.symm ▸ g_t)) := rfl
          rw [← h_qkj]
          have h1 : qkj (hk.symm ▸ g_t) ≤
              ↑C₀ * (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                (hk.symm ▸ g_t) := by
            have h := hbound (hk.symm ▸ g_t)
            simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h; linarith
          have h2 : (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                (hk.symm ▸ g_t) ≤ ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 := by
            apply Seminorm.finset_sup_apply_le
              (Finset.sum_nonneg (fun i _ => mul_nonneg (hDs_nn i) (by positivity)))
            intro ⟨p, q⟩ hi
            simp only [SchwartzMap.schwartzSeminormFamily_apply]
            rw [hcast_pq p q ((n + m - 1) + 1) hk g_t]
            exact (hDs_bound (p, q) t).trans
              (Finset.single_le_sum
                (fun j _ => mul_nonneg (hDs_nn j) (pow_nonneg (by linarith [norm_nonneg t]) j.1))
                hi)
          have h3 : ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 ≤
              (∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1) := by
            rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi
            apply mul_le_mul_of_nonneg_left _ (hDs_nn i)
            exact pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup (f := (·.1)) hi)
          calc qkj (hk.symm ▸ g_t)
              ≤ ↑C₀ * (s.sup (schwartzSeminormFamily ℝ (NPointSpacetime d (n + m - 1 + 1)) ℂ))
                  (hk.symm ▸ g_t) := h1
            _ ≤ ↑C₀ * ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ i.1 := mul_le_mul_of_nonneg_left h2 C₀.prop
            _ ≤ ↑C₀ * ((∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1)) :=
                mul_le_mul_of_nonneg_left h3 C₀.prop
            _ = (↑C₀ * ∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ s.sup (·.1) := by ring
        obtain ⟨Cred, Nred, hCred_nn, hCred⟩ := hFpoly
        exact ⟨Cred + 1, Nred, by linarith, fun t =>
          (hCred t).trans (mul_le_mul_of_nonneg_right (by linarith)
            (pow_nonneg (by linarith [norm_nonneg t]) _))⟩
      -- ── CLM exchange + Fourier inversion ───────────────────────────────────
      -- w is already Continuous + IsLinearMap ℂ
      obtain ⟨Θ, hΘ_pointwise, hΘ_w⟩ :=
        schwartz_clm_fubini_exchange_real w hw_cont hw_lin _ hF_cont hF_poly
          (SchwartzMap.fourierTransformCLM ℂ φ)
      obtain ⟨ψ, hψ_ft, hψ_supp⟩ :=
        scd_fourierInv_translate_witness_dir (by omega : 0 < n) (by omega : 0 < m)
          fn fm y φ hφ hk hbdry Θ hΘ_pointwise
      exact ⟨ψ, by rw [hψ_ft]; exact hΘ_w, hψ_supp⟩

/-- Generalization of `scd_summand_fourier_vanishing` to arbitrary `y ∈ V̄₊`. -/
private lemma scd_summand_fourier_vanishing_dir
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (y : MinkowskiSpace d) (hy : y ∈ ForwardMomentumCone d)
    {n m : ℕ} (fn : SchwartzNPointSpace d n) (fm : SchwartzNPointSpace d m)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    ∫ t : ℝ,
      Wfn.W (n + m) (fn.conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) fm)) *
      ((SchwartzMap.fourierTransformCLM ℂ φ) : ℝ → ℂ) t = 0 :=
  scd_summand_nonneg_fourier_support_dir Wfn hSCD y hy fn fm φ hφ

/-- **Generalized one-sided Fourier support for arbitrary `y ∈ V̄₊`.**

    For any `y ∈ V̄₊` and pre-Hilbert vector `F`, the tempered distribution
    `T_F(ψ) = ∫ ⟪F, U(ty)F⟫ · ψ(t) dt` has one-sided Fourier support in `[0,∞)`.
    This generalizes `scd_inner_hasOneSidedFourierSupport` from `e₀` to arbitrary `y`. -/
private lemma scd_inner_hasOneSidedFourierSupport_dir
    (hSCD : SpectralConditionDistribution d Wfn.W)
    (hsc : PoincareRepresentation.translationStronglyContinuous (gnsPoincareRep Wfn))
    (y : MinkowskiSpace d) (hy : y ∈ ForwardMomentumCone d)
    (F : PreHilbertSpace Wfn) :
    SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ, @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (t • y))
          (F : GNSHilbertSpace Wfn)) * (ψ : ℝ → ℂ) t) := by
  -- Follows `scd_inner_hasOneSidedFourierSupport` exactly.
  intro φ hφ
  -- Step 1: Quotient induction — choose Borchers representative B of F.
  induction F using Quotient.inductionOn with | h B =>
  set pB : PreHilbertSpace Wfn := ⟦B⟧
  -- Step 2: Bridge GNS inner product → WightmanInnerProduct.
  have hinner_eq : ∀ t : ℝ,
      @inner ℂ _ _ (pB : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (t • y))
          (pB : GNSHilbertSpace Wfn)) =
      WightmanInnerProduct d Wfn.W B
        (poincareActBorchers (PoincareGroup.translation' (t • y)) B) := by
    intro t
    rw [show poincareActGNS Wfn (PoincareGroup.translation' (t • y))
          (pB : GNSHilbertSpace Wfn) =
        ((poincareActPreHilbert Wfn (PoincareGroup.translation' (t • y)) pB :
          PreHilbertSpace Wfn) : GNSHilbertSpace Wfn) from
      poincareActGNS_coe Wfn (PoincareGroup.translation' (t • y)) pB,
      UniformSpace.Completion.inner_coe]; rfl
  simp_rw [hinner_eq]
  -- Step 3: Unfold WightmanInnerProduct as a finite double sum.
  show ∫ t : ℝ,
    (∑ n ∈ Finset.range (B.bound + 1), ∑ m ∈ Finset.range (B.bound + 1),
      Wfn.W (n + m) ((B.funcs n).conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) (B.funcs m)))) *
    ((SchwartzMap.fourierTransformCLM ℂ φ) : ℝ → ℂ) t = 0
  -- Step 4: Distribute, exchange integral and finite sum, apply per-summand vanishing.
  simp_rw [Finset.sum_mul]
  set FTφ := SchwartzMap.fourierTransformCLM ℂ φ with hFTφ_def
  -- Integrability of each summand (bounded × Schwartz is L¹)
  have hint_dir : ∀ (n' : ℕ) (m' : ℕ) (fn' : SchwartzNPointSpace d n')
      (fm' : SchwartzNPointSpace d m'),
      MeasureTheory.Integrable (fun t : ℝ =>
        Wfn.W (n' + m') (fn'.conjTensorProduct
          (poincareActNPoint (PoincareGroup.translation' (t • y)) fm')) *
        (FTφ : ℝ → ℂ) t) := by
    intro n' m' fn' fm'
    -- Continuity of the translation family in Schwartz topology
    have hcont_translate : Continuous (fun t : ℝ =>
        poincareActNPoint (PoincareGroup.translation' (t • y)) fm') := by
      set η_y' : Fin (m' * (d + 1)) → ℝ := fun k => -(y ((finProdFinEquiv.symm k).2)) with hη_y'_def
      have h_eq : ∀ t : ℝ,
          poincareActNPoint (PoincareGroup.translation' (t • y)) fm' =
          unflattenSchwartzNPointLocal (d := d)
            (SCV.translateSchwartz (t • η_y') (flattenSchwartzNPointLocal (d := d) fm')) := by
        intro t; ext x
        simp only [poincareActNPoint_apply, SCV.translateSchwartz_apply,
          unflattenSchwartzNPointLocal_apply, flattenSchwartzNPointLocal_apply]
        congr 1; funext i; ext ν
        simp only [poincareActNPointDomain, PoincareGroup.act_def,
          PoincareGroup.inv_translation, PoincareGroup.inv_lorentz,
          PoincareGroup.translation'_translation, PoincareGroup.translation'_lorentz,
          inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec,
          flattenCLEquivRealLocal_symm_apply, flattenCLEquivRealLocal_apply,
          Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
          hη_y'_def, Equiv.symm_apply_apply]; ring
      simp_rw [h_eq]
      exact (unflattenSchwartzNPointLocal (d := d) : _ →L[ℂ] _).continuous.comp
        (continuous_translateSchwartz_smul (η := η_y') (flattenSchwartzNPointLocal (d := d) fm'))
    have hcont : Continuous (fun t : ℝ =>
        Wfn.W (n' + m') (fn'.conjTensorProduct
          (poincareActNPoint (PoincareGroup.translation' (t • y)) fm'))) :=
      (Wfn.tempered (n' + m')).comp
        ((SchwartzMap.conjTensorProduct_continuous_right fn').comp hcont_translate)
    -- Boundedness via GNS Cauchy-Schwarz
    set F' : PreHilbertSpace Wfn := ⟦BorchersSequence.single n' fn'⟧
    set G' : PreHilbertSpace Wfn := ⟦BorchersSequence.single m' fm'⟧
    set C' := ‖(F' : GNSHilbertSpace Wfn)‖ * ‖(G' : GNSHilbertSpace Wfn)‖
    have hbound : ∀ t : ℝ, ‖Wfn.W (n' + m') (fn'.conjTensorProduct
        (poincareActNPoint (PoincareGroup.translation' (t • y)) fm'))‖ ≤ C' := by
      intro t
      set τt := PoincareGroup.translation' (t • y)
      have h_eq : Wfn.W (n' + m') (fn'.conjTensorProduct (poincareActNPoint τt fm')) =
          @inner ℂ _ _ (F' : GNSHilbertSpace Wfn)
            (poincareActGNS Wfn τt (G' : GNSHilbertSpace Wfn)) := by
        rw [← WightmanInnerProduct_single_single d Wfn.W Wfn.linear n' m' fn'
          (poincareActNPoint τt fm')]
        rw [← inner_eq Wfn (BorchersSequence.single n' fn')
          (BorchersSequence.single m' (poincareActNPoint τt fm'))]
        have h_q : (⟦BorchersSequence.single m' (poincareActNPoint τt fm')⟧ :
            PreHilbertSpace Wfn) = poincareActPreHilbert Wfn τt G' := by
          show _ = ⟦poincareActBorchers τt (BorchersSequence.single m' fm')⟧
          exact (mk_eq_of_funcs_eq Wfn _ _ (fun n'' => by
            by_cases h : n'' = m'
            · subst h; simp [poincareActBorchers]
            · simp [poincareActBorchers, BorchersSequence.single_funcs_ne h,
                poincareActNPoint_zero])).symm
        rw [h_q, show poincareActGNS Wfn τt (G' : GNSHilbertSpace Wfn) =
            ((poincareActPreHilbert Wfn τt G' : PreHilbertSpace Wfn) :
              GNSHilbertSpace Wfn) from poincareActGNS_coe Wfn τt G',
          UniformSpace.Completion.inner_coe]
      rw [h_eq]
      calc ‖@inner ℂ _ _ (F' : GNSHilbertSpace Wfn)
              (poincareActGNS Wfn τt (G' : GNSHilbertSpace Wfn))‖
          ≤ ‖(F' : GNSHilbertSpace Wfn)‖ *
            ‖poincareActGNS Wfn τt (G' : GNSHilbertSpace Wfn)‖ :=
            norm_inner_le_norm _ _
        _ = C' := by rw [poincareActGNS_norm]
    exact (FTφ.integrable.norm.const_mul C').mono'
      (hcont.mul FTφ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))
  -- Exchange integral and finite sums, apply per-summand vanishing
  rw [MeasureTheory.integral_finset_sum _ (fun n' _ =>
    MeasureTheory.integrable_finset_sum _ (fun m' _ =>
      hint_dir n' m' (B.funcs n') (B.funcs m')))]
  apply Finset.sum_eq_zero; intro n' _
  rw [MeasureTheory.integral_finset_sum _ (fun m' _ =>
    hint_dir n' m' (B.funcs n') (B.funcs m'))]
  apply Finset.sum_eq_zero; intro m' _
  exact scd_summand_fourier_vanishing_dir Wfn hSCD y hy (B.funcs n') (B.funcs m') φ hφ

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
private theorem fourierInv_eq_cexp_integral'
    (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourierInv (φ : ℝ → ℂ) ξ =
      ∫ x : ℝ, Complex.exp (2 * ↑Real.pi * Complex.I * ↑ξ * ↑x) * (φ : ℝ → ℂ) x := by
  rw [Real.fourierInv_eq' (f := (φ : ℝ → ℂ)) (w := ξ)]
  congr 1; ext v
  have hinner : ∀ a b : ℝ, @inner ℝ ℝ _ a b = b * a := by
    intro a b; simp [inner, mul_comm]
  simp only [smul_eq_mul, hinner, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem oneSidedSupport_implies_schwartz_vanishing
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (hsupp : SCV.HasOneSidedFourierSupport (fun ψ : SchwartzMap ℝ ℂ =>
      ∫ t : ℝ, (∫ s : ℝ, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) * (ψ : ℝ → ℂ) t))
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∀ x ∈ Function.support (ψ : ℝ → ℂ), x < 0) :
    ∫ s : ℝ, (ψ : ℝ → ℂ) s ∂μ = 0 := by
  -- === Setup ===
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
  -- === Step 1: Construct χ(x) = ψ(2πx) as a Schwartz function ===
  -- The continuous linear equivalence x ↦ (2π) • x on ℝ
  set scaleCLE : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (M₁ := ℝ) (Units.mk0 (2 * Real.pi) h2pi_ne) with
    hscaleCLE_def
  set χ : SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleCLE ψ with hχ_def
  -- Pointwise: χ(x) = ψ(2πx)
  have hχ_apply : ∀ x : ℝ, (χ : ℝ → ℂ) x = (ψ : ℝ → ℂ) (2 * Real.pi * x) := by
    intro x
    simp only [hχ_def, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hscaleCLE_def,
      Function.comp_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_def, Units.val_mk0, smul_eq_mul]
  -- === Step 2: χ has support in (-∞, 0) ===
  have hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0 := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [hχ_apply] at hx
    have h2pix_neg := hψ (2 * Real.pi * x) (Function.mem_support.mpr hx)
    -- 2π * x < 0 and 2π > 0 implies x < 0
    by_contra h_nonneg
    push_neg at h_nonneg
    linarith [mul_nonneg (le_of_lt h2pi_pos) h_nonneg]
  -- === Step 3: Apply HasOneSidedFourierSupport to χ ===
  have h_zero := hsupp χ hχ_supp
  -- h_zero : ∫ t, (∫ s, exp(I*t*s) dμ(s)) * (FT χ)(t) dt = 0
  -- === Step 4: Apply Fubini to swap integrals ===
  set g := SchwartzMap.fourierTransformCLM ℂ χ with hg_def
  have h_fubini := bochner_fourier_fubini μ g
  -- ∫ s, (∫ t, exp(I*t*s) * g(t) dt) dμ(s) = 0
  have h_G_zero :
      ∫ s, (∫ t, Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t) ∂μ = 0 := by
    rw [← h_fubini]; exact h_zero
  -- === Step 5: Fourier inversion: G(s) = ψ(s) pointwise ===
  -- G(s) := ∫ exp(its) (FT χ)(t) dt = FourierInv(FT χ)(s/(2π)) = χ(s/(2π)) = ψ(s)
  suffices h_inner_eq : ∀ s : ℝ,
      ∫ t, Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t = (ψ : ℝ → ℂ) s by
    -- Conclude: ∫ ψ dμ = ∫ G dμ = 0
    calc ∫ s, (ψ : ℝ → ℂ) s ∂μ
        = ∫ s, (∫ t, Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t) ∂μ := by
          congr 1; ext s; exact (h_inner_eq s).symm
      _ = 0 := h_G_zero
  -- Prove the pointwise Fourier inversion identity
  intro s
  -- Sub-step (a): Kernel convention change
  -- exp(I*t*s) = exp(2πI*(s/(2π))*t) since I*t*s = 2πI*(s/(2π))*t
  have h_kernel_eq : ∀ t : ℝ,
      Complex.exp (Complex.I * ↑t * ↑s) * (g : ℝ → ℂ) t =
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑(s / (2 * Real.pi)) * ↑t) *
        (g : ℝ → ℂ) t := by
    intro t; congr 1; congr 1
    push_cast; field_simp
  simp_rw [h_kernel_eq]
  -- Sub-step (b): Recognize as FourierInv(g) at s/(2π)
  rw [← fourierInv_eq_cexp_integral' g (s / (2 * Real.pi))]
  -- Goal: FourierTransform.fourierInv (g : ℝ → ℂ) (s / (2 * Real.pi)) = ψ s
  -- Sub-step (c): Fourier inversion: FourierInv(FT χ) = χ
  have h_fi_eq : FourierTransform.fourierInv (g : ℝ → ℂ) = (χ : ℝ → ℂ) := by
    -- FourierTransform.fourierInv_fourier_eq gives SchwartzMap equality:
    -- FourierTransform.fourierInv (FT χ) = χ
    have h_inv := FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) χ
    -- Coerce to function equality
    have h_fn := congrArg (fun (f : SchwartzMap ℝ ℂ) => (f : ℝ → ℂ)) h_inv
    -- h_fn : ⇑(FourierTransform.fourierInv (FT χ)) = ⇑χ
    -- Bridge SchwartzMap-level and function-level fourierInv via fourierInv_coe
    dsimp only at h_fn
    rw [SchwartzMap.fourierInv_coe] at h_fn
    -- h_fn : FourierTransform.fourierInv (⇑(FT χ)) = ⇑χ
    exact h_fn
  rw [h_fi_eq]
  -- Sub-step (d): χ(s/(2π)) = ψ(2π * (s/(2π))) = ψ(s)
  rw [hχ_apply]
  congr 1; field_simp

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
  -- Step 1: Reduce to showing μ(Ioo (-(n+1)) 0) = 0 for each n : ℕ
  suffices key : ∀ n : ℕ, μ (Set.Ioo (-(↑n + 1 : ℝ)) 0) = 0 by
    apply le_antisymm _ (zero_le _)
    calc μ (Set.Iio 0)
        ≤ μ (⋃ n : ℕ, Set.Ioo (-(↑n + 1 : ℝ)) 0) := by
          apply MeasureTheory.measure_mono
          intro x hx
          simp only [Set.mem_Iio] at hx
          simp only [Set.mem_iUnion, Set.mem_Ioo]
          exact ⟨⌈-x⌉₊, by
            refine ⟨?_, hx⟩; linarith [Nat.le_ceil (-x)]⟩
      _ = 0 := MeasureTheory.measure_iUnion_null key
  -- Step 2: For each n, construct a bump and show μ(Ioo (-(n+1)) 0) = 0
  intro n
  set L : ℝ := ↑n + 1 with hL_def
  have hL_pos : (0 : ℝ) < L := by positivity
  set c : ℝ := -L / 2 with hc_def
  -- ContDiffBump centered at c = -L/2 with support = ball c (L/2) = Ioo (-L) 0
  let b : ContDiffBump c := ⟨L / 4, L / 2, by linarith, by linarith⟩
  have hball : Metric.ball c (L / 2) = Set.Ioo (-L) 0 := by
    rw [Real.ball_eq_Ioo]
    congr 1 <;> simp [hc_def] <;> ring
  -- Complex-valued version for the SchwartzMap
  set f : ℝ → ℂ := fun x => (b x : ℂ) with hf_def
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  set ψ : SchwartzMap ℝ ℂ := hf_compact.toSchwartzMap hf_smooth
  -- Support of ψ is contained in Iio 0
  have hsupp_neg : ∀ x ∈ Function.support (ψ : ℝ → ℂ), x < 0 := by
    intro x hx
    by_contra hge
    simp only [not_lt] at hge
    -- x ≥ 0 implies x ∉ ball c (L/2) = Ioo (-L) 0
    have hx_ball : x ∉ Metric.ball c (L / 2) := by
      rw [hball]; intro ⟨_, hx0⟩; linarith
    -- So b x = 0 (since support b = ball c (L/2))
    have hbx : b x = 0 := by
      by_contra h; exact hx_ball (b.support_eq ▸ Function.mem_support.mpr h)
    -- Hence ψ x = (b x : ℂ) = 0, contradicting x ∈ support ψ
    exact absurd (show (ψ : ℝ → ℂ) x = 0 from by
      show f x = 0; simp [hf_def, hbx]) (Function.mem_support.mp hx)
  -- Apply hypothesis: ∫ ψ dμ = 0
  have h_int := h ψ hsupp_neg
  -- Convert complex integral to real: ∫ (↑(b s)) dμ = ↑(∫ b s dμ) = 0, so ∫ b dμ = 0
  have h_real : ∫ s : ℝ, b s ∂μ = 0 := by
    have h_eq : ∫ s : ℝ, (ψ : ℝ → ℂ) s ∂μ = ↑(∫ s : ℝ, b s ∂μ) := by
      change ∫ s : ℝ, f s ∂μ = _
      exact integral_ofReal
    rw [h_eq] at h_int
    exact_mod_cast h_int
  -- b ≥ 0 and integrable with ∫ = 0 implies b = 0 μ-a.e.
  have hb_int : MeasureTheory.Integrable (⇑b) μ :=
    (b.contDiff (n := 0)).continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hb_ae : (⇑b) =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => b.nonneg' x) hb_int).mp h_real
  -- μ({b ≠ 0}) = 0, and {b ≠ 0} = support b = ball c (L/2) = Ioo (-L) 0
  have h_meas : μ (Function.support (⇑b)) = 0 := by
    have : μ {x : ℝ | ¬(b x = 0)} = 0 := MeasureTheory.ae_iff.mp hb_ae
    convert this using 1
  rw [b.support_eq, hball] at h_meas
  exact h_meas

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
    have hpd₁ : IsPositiveDefiniteFn φ₁ := by
      intro m x c
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
        rw [h]; exact ⟨inner_self_im (𝕜 := ℂ) v, inner_self_nonneg (𝕜 := ℂ)⟩
      symm; simp only [v]
      rw [sum_inner (𝕜 := ℂ)]
      simp_rw [_root_.inner_smul_left, inner_sum (𝕜 := ℂ), _root_.inner_smul_right]
      congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j; ring
    -- Bochner's theorem gives a representing measure μ₁ on Fin 1 → ℝ.
    obtain ⟨μ₁, hfin₁, hrepr₁⟩ := bochner_finiteMeasure φ₁ hcont₁ hpd₁
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
  have h_eq := bochner_uniqueness_real ν μ_F hν_fs
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

set_option maxHeartbeats 800000 in
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
  -- === Step 1: For each y ∈ V̄₊, the null set μ({p | y·p < 0}) = 0. ===
  -- The 1D pushforward ν_y = μ.map(p ↦ Σᵢ yᵢpᵢ) satisfies ν_y((-∞,0)) = 0.
  -- Proof chain: restrict hboch to x = ty → Bochner representation of
  -- t ↦ ⟪ψ, U(ty)ψ⟫ as ∫ exp(its) dν_y → one-sided Fourier support via
  -- the SCD argument for direction y → 1D pipeline gives ν_y((-∞,0)) = 0.
  have h_null : ∀ y : MinkowskiSpace d, y ∈ ForwardMomentumCone d →
      μ {p : MinkowskiSpace d | ∑ i : Fin (d + 1), y i * p i < 0} = 0 := by
    intro y hy
    -- The 1D pushforward ν_y = μ.map(p ↦ y·p)
    set dotY := (fun p : MinkowskiSpace d => ∑ i : Fin (d + 1), y i * p i) with hdotY
    set ν_y := μ.map dotY with hν_y_def
    have h_meas : Measurable dotY :=
      Finset.measurable_sum _ (fun i _ => (measurable_const.mul (measurable_pi_apply i)))
    haveI : MeasureTheory.IsFiniteMeasure ν_y :=
      ⟨by rw [hν_y_def, MeasureTheory.Measure.map_apply h_meas MeasurableSet.univ,
        Set.preimage_univ]; exact MeasureTheory.measure_lt_top μ _⟩
    -- Convert: μ({p | y·p < 0}) = ν_y((-∞,0))
    rw [show {p : MinkowskiSpace d | ∑ i, y i * p i < 0} = dotY ⁻¹' Set.Iio 0 from rfl]
    rw [← MeasureTheory.Measure.map_apply h_meas measurableSet_Iio]
    -- === Step 1a: FS transform of ν_y equals inner product function ===
    have hU : (gnsPoincareRep Wfn).U = poincareActGNS Wfn := rfl
    have hν_fs : ∀ t : ℝ, ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂ν_y =
        @inner ℂ _ _ ψ (poincareActGNS Wfn (PoincareGroup.translation' ((t : ℝ) • y)) ψ) := by
      intro t
      -- integral_map: ∫ exp(I*t*s) d(μ.map dotY) = ∫ exp(I*t*(dotY p)) dμ
      have h_aesm : MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Complex.exp (Complex.I * ↑t * ↑s))
          (MeasureTheory.Measure.map dotY μ) :=
        Continuous.aestronglyMeasurable (f := fun s : ℝ => Complex.exp (Complex.I * ↑t * ↑s))
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
      have h_map := MeasureTheory.integral_map h_meas.aemeasurable h_aesm
      trans (∫ p, Complex.exp (↑(∑ i, (t • y) i * p i) * Complex.I) ∂μ)
      · rw [hν_y_def, h_map]; congr 1; ext p; congr 1
        simp only [hdotY, Pi.smul_apply, smul_eq_mul]; push_cast
        conv_rhs => rw [mul_comm]
        rw [mul_assoc, Finset.mul_sum]; congr 1
        apply Finset.sum_congr rfl; intro i _; ring
      · exact (hboch (t • y)).symm
    -- === Step 1b: One-sided Fourier support via density ===
    have h_ofs_ν : SCV.HasOneSidedFourierSupport (fun φ : SchwartzMap ℝ ℂ =>
        ∫ t : ℝ, (∫ s : ℝ, Complex.exp (Complex.I * ↑t * ↑s) ∂ν_y) *
          (φ : ℝ → ℂ) t) := by
      intro φ hφ
      simp_rw [hν_fs]
      set FTφ := (SchwartzMap.fourierTransformCLM ℂ φ : SchwartzMap ℝ ℂ)
      -- For PreHilbertSpace F, the integral vanishes by the generalized SCD chain
      have h_vanish : ∀ F : PreHilbertSpace Wfn,
          ∫ t : ℝ, @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
            (poincareActGNS Wfn (PoincareGroup.translation' ((t : ℝ) • y))
              (F : GNSHilbertSpace Wfn)) * (FTφ : ℝ → ℂ) t = 0 :=
        fun F => scd_inner_hasOneSidedFourierSupport_dir Wfn hSCD hsc y hy F φ hφ
      -- Norm preservation: ‖U(g)x‖ = ‖x‖
      have h_norm_pres : ∀ (g : PoincareGroup d) (x : GNSHilbertSpace Wfn),
          ‖poincareActGNS Wfn g x‖ = ‖x‖ := by
        intro g x
        have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (poincareActGNS Wfn g x)
        have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
        have h3 := congr_arg Complex.re (poincareActGNS_inner Wfn g x x)
        -- ‖Ux‖² = re⟪Ux,Ux⟫ = re⟪x,x⟫ = ‖x‖²
        have hsq : ‖poincareActGNS Wfn g x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [← h1, ← h2]; exact h3
        -- a² = b², a ≥ 0, b ≥ 0 → a = b
        have h_diff_sq : (‖poincareActGNS Wfn g x‖ - ‖x‖) *
            (‖poincareActGNS Wfn g x‖ + ‖x‖) = 0 := by nlinarith
        rcases mul_eq_zero.mp h_diff_sq with h | h
        · linarith
        · linarith [norm_nonneg (poincareActGNS Wfn g x), norm_nonneg x]
      -- Density: PreHilbertSpace is dense in GNSHilbertSpace.
      -- Strategy: by contradiction, pick F close to ψ, bound the integral difference.
      rw [← norm_eq_zero]
      apply le_antisymm _ (norm_nonneg _)
      by_contra h_pos
      push_neg at h_pos
      set val := ∫ t : ℝ, @inner ℂ _ _ ψ (poincareActGNS Wfn
        (PoincareGroup.translation' ((t : ℝ) • y)) ψ) * (FTφ : ℝ → ℂ) t
      set L := ∫ t : ℝ, ‖(FTφ : ℝ → ℂ) t‖
      have hL_nn : 0 ≤ L := MeasureTheory.integral_nonneg (fun t => norm_nonneg _)
      set δ₀ := min 1 (‖val‖ / (4 * (‖ψ‖ + 1) * (L + 1)))
      have hδ : (0 : ℝ) < δ₀ := lt_min one_pos (by positivity)
      obtain ⟨F, hF⟩ := (UniformSpace.Completion.denseRange_coe
        (α := PreHilbertSpace Wfn)).exists_dist_lt ψ hδ
      -- Pointwise inner product difference bound:
      -- ‖⟪ψ,Uψ⟫ - ⟪F,UF⟫‖ ≤ ‖ψ-F‖·(‖ψ‖+‖F‖)
      have h_inner_diff : ∀ t : ℝ,
          ‖@inner ℂ _ _ ψ (poincareActGNS Wfn
              (PoincareGroup.translation' ((t : ℝ) • y)) ψ) -
            @inner ℂ _ _ (F : GNSHilbertSpace Wfn)
              (poincareActGNS Wfn (PoincareGroup.translation' ((t : ℝ) • y))
                (F : GNSHilbertSpace Wfn))‖ ≤
          ‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) := by
        intro t
        set g := PoincareGroup.translation' ((t : ℝ) • y)
        have h_decomp : @inner ℂ _ _ ψ (poincareActGNS Wfn g ψ) -
            @inner ℂ _ _ (↑F) (poincareActGNS Wfn g ↑F) =
          @inner ℂ _ _ (ψ - ↑F) (poincareActGNS Wfn g ψ) +
          @inner ℂ _ _ (↑F : GNSHilbertSpace Wfn)
            (poincareActGNS Wfn g (ψ - ↑F)) := by
          simp only [inner_sub_left, map_sub, inner_sub_right]; ring
        rw [h_decomp]
        calc ‖_ + _‖
            ≤ ‖@inner ℂ _ _ (ψ - ↑F) (poincareActGNS Wfn g ψ)‖ +
              ‖@inner ℂ _ _ (↑F : GNSHilbertSpace Wfn)
                (poincareActGNS Wfn g (ψ - ↑F))‖ := norm_add_le _ _
          _ ≤ ‖ψ - ↑F‖ * ‖poincareActGNS Wfn g ψ‖ +
              ‖(F : GNSHilbertSpace Wfn)‖ * ‖poincareActGNS Wfn g (ψ - ↑F)‖ := by
              gcongr <;> exact norm_inner_le_norm _ _
          _ = ‖ψ - ↑F‖ * ‖ψ‖ +
              ‖(F : GNSHilbertSpace Wfn)‖ * ‖ψ - ↑F‖ := by
              rw [h_norm_pres g ψ, h_norm_pres g (ψ - ↑F)]
          _ = ‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) := by ring
      -- Integral bound: ‖val - ∫⟪F,UF⟫g‖ ≤ ‖ψ-F‖·(‖ψ‖+‖F‖)·L
      -- Uses h_inner_diff pointwise, then integrates against |g|.
      have h_val_bound : ‖val‖ ≤
          ‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) * L := by
        rw [show val = val - 0 from (sub_zero _).symm, ← h_vanish F]
        -- Orbit continuity → integrand continuity → integrability
        have hcont_int : ∀ x : GNSHilbertSpace Wfn, Continuous (fun t : ℝ =>
            @inner ℂ _ _ x (poincareActGNS Wfn
              (PoincareGroup.translation' (t • y)) x) * (FTφ : ℝ → ℂ) t) :=
          fun x => (continuous_inner.comp (continuous_const.prodMk
            ((translation_orbit_continuous Wfn hsc x).comp
              (continuous_id.smul continuous_const)))).mul FTφ.continuous
        have hint : ∀ x : GNSHilbertSpace Wfn, MeasureTheory.Integrable (fun t : ℝ =>
            @inner ℂ _ _ x (poincareActGNS Wfn
              (PoincareGroup.translation' (t • y)) x) * (FTφ : ℝ → ℂ) t) := by
          intro x
          exact MeasureTheory.Integrable.mono'
            ((SchwartzMap.integrable FTφ).norm.const_mul (‖x‖ ^ 2))
            (hcont_int x).aestronglyMeasurable
            (Filter.Eventually.of_forall fun t => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right
                ((norm_inner_le_norm _ _).trans (by rw [h_norm_pres]; exact le_of_eq (sq ‖x‖).symm))
                (norm_nonneg _))
        -- Combine integrals and bound
        simp only [val]
        rw [← MeasureTheory.integral_sub (hint ψ) (hint ↑F)]
        calc ‖∫ t, _‖
            ≤ ∫ t, ‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) *
                ‖(FTφ : ℝ → ℂ) t‖ :=
              MeasureTheory.norm_integral_le_of_norm_le
                ((SchwartzMap.integrable FTφ).norm.const_mul
                  (‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖)))
                (Filter.Eventually.of_forall fun t => by
                  have hfact : ∀ (a b c : ℂ), a * c - b * c = (a - b) * c :=
                    fun a b c => by ring
                  rw [hfact, norm_mul]
                  exact mul_le_mul_of_nonneg_right (h_inner_diff t) (norm_nonneg _))
          _ = ‖ψ - ↑F‖ * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) * L :=
              MeasureTheory.integral_const_mul _ _
      -- ‖F‖ ≤ ‖ψ‖ + dist(ψ,F)
      have hF_norm : ‖(F : GNSHilbertSpace Wfn)‖ ≤ ‖ψ‖ + dist ψ ↑F :=
        calc ‖(F : GNSHilbertSpace Wfn)‖
            = ‖ψ - (ψ - (F : GNSHilbertSpace Wfn))‖ := by congr 1; abel
          _ ≤ ‖ψ‖ + ‖ψ - (F : GNSHilbertSpace Wfn)‖ := norm_sub_le _ _
          _ = ‖ψ‖ + dist ψ (F : GNSHilbertSpace Wfn) := by rw [dist_eq_norm]
      -- Contradiction: ‖val‖ ≤ dist·(2‖ψ‖+dist)·L < ‖val‖
      -- Since dist < δ = ‖val‖/(2(‖ψ‖+1)(L+1)), the product < ‖val‖.
      rw [dist_eq_norm] at hF hF_norm
      -- ‖val‖ ≤ ‖ψ-F‖ * (‖ψ‖+‖F‖) * L ≤ ‖ψ-F‖ * (2‖ψ‖+‖ψ-F‖) * L
      -- ‖ψ-F‖ < δ = ‖val‖ / (2(‖ψ‖+1)(L+1))
      -- So ‖val‖ < δ * (2‖ψ‖+δ) * L ≤ δ * 2(‖ψ‖+1) * (L+1) = ‖val‖
      -- Contradiction.
      set ε := ‖ψ - (F : GNSHilbertSpace Wfn)‖
      have hε_nn : 0 ≤ ε := norm_nonneg _
      have hε_lt : ε < δ₀ := hF
      have h_prod : 2 * (‖ψ‖ + 1) * (L + 1) > 0 := by positivity
      -- Chain of inequalities
      -- ε < δ₀ ≤ 1, so ε < 1 and 2‖ψ‖ + ε ≤ 2(‖ψ‖ + 1)
      have hε_lt1 : ε < 1 := lt_of_lt_of_le hε_lt (min_le_left 1 _)
      -- ε < ‖val‖/(4(‖ψ‖+1)(L+1))
      have hε_lt2 : ε < ‖val‖ / (4 * (‖ψ‖ + 1) * (L + 1)) :=
        lt_of_lt_of_le hε_lt (min_le_right 1 _)
      have h_4prod : 4 * (‖ψ‖ + 1) * (L + 1) > 0 := by positivity
      -- Direct: ‖val‖ ≤ ε*(‖ψ‖+‖F‖)*L ≤ ε*(2‖ψ‖+ε)*L
      --       ≤ ε²*(2‖ψ‖+1)*L + ε*(2‖ψ‖)*L  ... too complex
      -- Simpler: ε*(‖ψ‖+‖F‖)*L ≤ ε*(2‖ψ‖+1)*(L+1)
      --   since ‖F‖ ≤ ‖ψ‖+ε ≤ ‖ψ‖+1 and L ≤ L+1
      have hF_le : ‖(F : GNSHilbertSpace Wfn)‖ ≤ ‖ψ‖ + 1 := by linarith
      have : ‖val‖ < ‖val‖ := calc
        ‖val‖ ≤ ε * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) * L := h_val_bound
        _ ≤ ε * (2 * ‖ψ‖ + 1) * (L + 1) := by
            have h1 : ‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖ ≤ 2 * ‖ψ‖ + 1 := by linarith [hF_le]
            have h2 : ε * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) ≤ ε * (2 * ‖ψ‖ + 1) :=
              mul_le_mul_of_nonneg_left h1 hε_nn
            calc ε * (‖ψ‖ + ‖(F : GNSHilbertSpace Wfn)‖) * L
                ≤ ε * (2 * ‖ψ‖ + 1) * L := by nlinarith
              _ ≤ ε * (2 * ‖ψ‖ + 1) * (L + 1) := by nlinarith [norm_nonneg ψ]
        _ ≤ ε * (4 * (‖ψ‖ + 1) * (L + 1)) := by nlinarith [norm_nonneg ψ]
        _ < ‖val‖ / (4 * (‖ψ‖ + 1) * (L + 1)) * (4 * (‖ψ‖ + 1) * (L + 1)) :=
            mul_lt_mul_of_pos_right hε_lt2 h_4prod
        _ = ‖val‖ := by field_simp
      linarith
    -- === Step 1c: Apply the 1D pipeline ===
    exact measure_Iio_zero_of_schwartz_vanishing ν_y (fun ψ_test hψ_test =>
      oneSidedSupport_implies_schwartz_vanishing ν_y h_ofs_ν ψ_test hψ_test)
  -- === Step 2: V̄₊ᶜ ⊆ countable union of null sets. ===
  -- For each p ∉ V̄₊, self-duality gives y ∈ V̄₊ with y·p < 0.
  -- Covering V̄₊ᶜ by open half-spaces {p | y·p < 0} for y in a countable
  -- dense subset of V̄₊ gives the result.
  -- Part A: {p | p₀ < 0} is null (y = e₀).
  -- Part B: {p | p₀ ≥ 0, not causal} covered by countably many null half-spaces.
  --
  -- We show V̄₊ᶜ ⊆ ⋃_{q ∈ ℚ^{d+1} ∩ V̄₊} {p | q·p < 0}, then use measure_iUnion_null.
  -- Separation: if p ∉ V̄₊, ∃ y ∈ V̄₊ with y·p < 0 (reverse self-duality).
  -- Continuity: y ↦ y·p is continuous, so a nearby rational y' still satisfies y'·p < 0.
  --
  -- Implementation: decompose V̄₊ᶜ into Part A ∪ Part B and handle each.
  apply le_antisymm _ (zero_le _)
  -- Part A: {p | p₀ < 0}
  have hA : μ {p : MinkowskiSpace d | p 0 < 0} = 0 := by
    -- e₀ ∈ V̄₊: IsCausal (minkowskiNormSq ≤ 0 since -1 + 0 ≤ 0) and timeComponent ≥ 0
    have he₀ : (fun i : Fin (d + 1) => if i = 0 then (1 : ℝ) else 0) ∈
        ForwardMomentumCone d := by
      simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
        MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
        MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent]
      constructor
      · -- minkowskiNormSq ≤ 0
        simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
          MinkowskiSpace.metricSignature]
        simp [Fin.sum_univ_succ, ite_mul, mul_ite, Fin.succ_ne_zero]
      · -- timeComponent ≥ 0
        simp
    -- {p | p₀ < 0} = {p | e₀·p < 0}
    have : {p : MinkowskiSpace d | p 0 < 0} =
        {p | ∑ i : Fin (d + 1), (fun i => if i = 0 then (1 : ℝ) else 0) i * p i < 0} := by
      ext p; simp [Fin.sum_univ_succ]
    rw [this]; exact h_null _ he₀
  -- Part B: {p | p₀ ≥ 0, spatialNormSq > p₀²} — covered by countable null sets
  -- V̄₊ᶜ ⊆ {p | p₀ < 0} ∪ {p | p₀ ≥ 0 ∧ spatialNormSq > p₀²}
  have h_decomp : (ForwardMomentumCone d)ᶜ ⊆
      {p | p 0 < 0} ∪ {p | p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2} := by
    intro p hp
    simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
      MinkowskiSpace.ForwardLightCone, Set.mem_compl_iff, Set.mem_setOf_eq,
      MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent, not_and_or,
      not_le] at hp
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hp with hncausal | htime
    · -- not causal: 0 < minkowskiNormSq d p, i.e., spatialNormSq > p₀²
      by_cases hp0 : p 0 < 0
      · left; exact hp0
      · right
        push_neg at hp0
        refine ⟨hp0, ?_⟩
        have h_decomp := MinkowskiSpace.minkowskiNormSq_decomp d p
        linarith
    · -- ¬(p 0 ≥ 0), i.e., p 0 < 0
      left; linarith
  -- Part B is null: for each p with p₀ ≥ 0 and spatialNormSq > p₀²,
  -- the separating direction argument gives y ∈ V̄₊ with y·p < 0.
  -- This requires a countable covering. We use the fact that {p | y·p < 0}
  -- for y ranging over a countable dense subset of V̄₊ covers Part B.
  have hB : μ {p : MinkowskiSpace d |
      p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2} = 0 := by
    -- Cover Part B by countably many null half-spaces indexed by q : Fin d → ℚ.
    -- For each q with ∑ qᵢ² ≤ 1, define y_q = (1, q₁, ..., q_d) ∈ V̄₊.
    -- Direction: y_q(0) = 1, y_q(succ i) = ↑(q i)
    set yDir : (Fin d → ℚ) → MinkowskiSpace d :=
      fun q i => if h : i = 0 then 1 else ↑(q (i.pred h))
    -- y_q ∈ V̄₊ when ∑ (q i)² ≤ 1
    have hyDir_mem : ∀ q : Fin d → ℚ, (∑ i, (q i : ℝ) ^ 2) ≤ 1 →
        yDir q ∈ ForwardMomentumCone d := by
      intro q hq
      simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
        MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
        MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent]
      constructor
      · -- minkowskiNormSq(y_q) = -1 + ∑ qᵢ² ≤ 0
        have : MinkowskiSpace.minkowskiNormSq d (yDir q) = -1 + ∑ i : Fin d, (q i : ℝ) ^ 2 := by
          rw [MinkowskiSpace.minkowskiNormSq_decomp]
          have h0 : (yDir q) 0 = 1 := dif_pos rfl
          have hsucc : ∀ i : Fin d, (yDir q) (Fin.succ i) = (q i : ℝ) := by
            intro i; simp [yDir, Fin.succ_ne_zero, Fin.pred_succ]
          simp only [h0, MinkowskiSpace.spatialNormSq, hsucc]; ring
        linarith
      · -- timeComponent ≥ 0: y_q(0) = 1 ≥ 0
        simp [yDir]
    -- Each null set: conditioned on ∑ qᵢ² ≤ 1 (empty otherwise)
    set S : (Fin d → ℚ) → Set (MinkowskiSpace d) :=
      fun q => if (∑ i, (q i : ℝ) ^ 2) ≤ 1
        then {p | ∑ i, yDir q i * p i < 0} else ∅
    have hS_null : ∀ q, μ (S q) = 0 := by
      intro q; simp only [S]
      split_ifs with h
      · exact h_null (yDir q) (hyDir_mem q h)
      · exact MeasureTheory.measure_empty
    -- Covering: Part B ⊆ ⋃_q S(q)
    -- For each p in Part B, find q with ∑ qᵢ² ≤ 1 and y_q · p < 0.
    -- Use shrunk direction r' = -p_spatial/(2s) (∑ r'ᵢ² = 1/4 < 1)
    -- then approximate by rational via density of ℚ^d in ℝ^d.
    have h_cover : {p : MinkowskiSpace d |
        p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2} ⊆ ⋃ q, S q := by
      intro p ⟨hp0, hpσ⟩
      simp only [Set.mem_iUnion]
      -- Let σ = spatialNormSq, s = √σ
      set σ := MinkowskiSpace.spatialNormSq d p with hσ_def
      have hσ_pos : (0 : ℝ) < σ := by linarith [sq_nonneg (p 0)]
      set s := Real.sqrt σ with hs_def
      have hs_pos : (0 : ℝ) < s := Real.sqrt_pos_of_pos hσ_pos
      have hs_sq : s * s = σ := Real.mul_self_sqrt hσ_pos.le
      -- s > p 0 (from σ > p₀²)
      have hs_gt : s > p 0 := by
        calc p 0 ≤ |p 0| := le_abs_self _
          _ = Real.sqrt ((p 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ < Real.sqrt σ := Real.sqrt_lt_sqrt (sq_nonneg _) hpσ
      -- Separating direction: r_i = -(s + p₀) * p_{i+1} / (2σ)
      -- satisfies ∑ rᵢ² < 1 and p₀ + ∑ rᵢ * p_{i+1} < 0
      set r : Fin d → ℝ := fun i => -(s + p 0) / (2 * σ) * p (Fin.succ i)
      -- Key computations
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
      have hr_sq_sum : ∑ i : Fin d, (r i) ^ 2 = (s + p 0) ^ 2 / (4 * σ) := by
        simp only [r, mul_pow, div_pow]
        rw [← Finset.mul_sum]
        have hσ_eq : ∑ i : Fin d, (p (Fin.succ i)) ^ 2 = σ := by
          simp [hσ_def, MinkowskiSpace.spatialNormSq]
        rw [hσ_eq]; field_simp; ring
      have hr_sum_lt : ∑ i : Fin d, (r i) ^ 2 < 1 := by
        rw [hr_sq_sum]
        rw [div_lt_one (by positivity)]
        have : s + p 0 < 2 * s := by linarith
        nlinarith
      have hr_dot : p 0 + ∑ i : Fin d, r i * p (Fin.succ i) = (p 0 - s) / 2 := by
        simp only [r]
        have hsum : ∀ i : Fin d, -(s + p 0) / (2 * σ) * p (Fin.succ i) * p (Fin.succ i) =
            -(s + p 0) / (2 * σ) * (p (Fin.succ i) * p (Fin.succ i)) := fun i => by ring
        simp_rw [hsum, ← Finset.mul_sum]
        have hσ_eq : ∑ i : Fin d, p (Fin.succ i) * p (Fin.succ i) = σ := by
          simp [hσ_def, MinkowskiSpace.spatialNormSq, sq]
        rw [hσ_eq]; field_simp; ring
      have hr_dot_neg : p 0 + ∑ i : Fin d, r i * p (Fin.succ i) < 0 := by
        rw [hr_dot]; linarith
      -- The open set U = {v | ∑ vᵢ² < 1 ∧ p₀ + ∑ vᵢ*p_{i+1} < 0}
      -- is open, nonempty, and we approximate by rational via density of ℚ^d
      have hU_open : IsOpen ({v : Fin d → ℝ | ∑ i, v i ^ 2 < 1} ∩
          {v | p 0 + ∑ i, v i * p (Fin.succ i) < 0}) :=
        (isOpen_lt (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
            continuous_const).inter
          (isOpen_lt (continuous_const.add (continuous_finset_sum _ fun i _ =>
              (continuous_apply i).mul continuous_const)) continuous_const)
      have hr_in_U : r ∈ {v : Fin d → ℝ | ∑ i, v i ^ 2 < 1} ∩
          {v | p 0 + ∑ i, v i * p (Fin.succ i) < 0} :=
        ⟨hr_sum_lt, hr_dot_neg⟩
      -- Density of ℚ^d in ℝ^d
      have hDense : DenseRange (fun q : Fin d → ℚ => fun i : Fin d => (q i : ℝ)) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      obtain ⟨q, hq⟩ := hDense.exists_mem_open hU_open ⟨r, hr_in_U⟩
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hq
      -- q satisfies ∑ (q i : ℝ)² < 1 and p₀ + ∑ (q i : ℝ) * p_{i+1} < 0
      refine ⟨q, ?_⟩
      dsimp only [S]
      rw [if_pos (le_of_lt hq.1)]
      simp only [Set.mem_setOf_eq]
      -- Show ∑ yDir q i * p i < 0
      rw [Fin.sum_univ_succ]
      simp only [yDir, dif_pos rfl, one_mul]
      have : ∀ i : Fin d, (if h : Fin.succ i = 0 then (1 : ℝ) else
          ↑(q ((Fin.succ i).pred h))) * p (Fin.succ i) = ↑(q i) * p (Fin.succ i) := by
        intro i; simp [Fin.succ_ne_zero, Fin.pred_succ]
      simp_rw [this]; exact hq.2
    apply le_antisymm _ (zero_le _)
    calc μ {p | p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2}
        ≤ μ (⋃ q, S q) := MeasureTheory.measure_mono h_cover
      _ = 0 := MeasureTheory.measure_iUnion_null hS_null
  calc μ (ForwardMomentumCone d)ᶜ
      ≤ μ ({p | p 0 < 0} ∪ {p | p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2}) :=
        MeasureTheory.measure_mono h_decomp
    _ ≤ μ {p | p 0 < 0} +
        μ {p | p 0 ≥ 0 ∧ MinkowskiSpace.spatialNormSq d p > (p 0) ^ 2} :=
        MeasureTheory.measure_union_le _ _
    _ = 0 := by rw [hA, hB, add_zero]

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
    have hφ_pd : IsPositiveDefiniteFn φ := by
      intro m x c
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
        rw [h]; exact ⟨inner_self_im (𝕜 := ℂ) v, inner_self_nonneg (𝕜 := ℂ)⟩
      symm; simp only [v]
      rw [sum_inner (𝕜 := ℂ)]
      simp_rw [_root_.inner_smul_left, inner_sum (𝕜 := ℂ), _root_.inner_smul_right]
      congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j; ring
    -- === Step 2d: Apply Bochner's theorem to get the finite measure μ ===
    obtain ⟨μ, hfin, hboch⟩ := bochner_finiteMeasure φ hφ_cont hφ_pd
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
        have h_eq : ν = ν' := bochner_uniqueness_real ν ν' (fun t => by
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
