/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction

/-!
# GNS Construction for the Wightman Reconstruction Theorem

This file implements the Gelfand-Naimark-Segal (GNS) construction that builds
a Hilbert space and field operators from Wightman functions, completing the
Wightman reconstruction theorem.

## Construction Overview

Starting from Wightman functions W = {W_n : S(ℝ^{n(d+1)}) → ℂ} satisfying
the required axioms, the reconstruction proceeds as follows:

### Step 1: Borchers Algebra (already in Reconstruction.lean)
- Elements are "Borchers sequences" F = (f_0, f_1, f_2, ...) where f_n ∈ S(ℝ^{n(d+1)})
  and only finitely many f_n are nonzero
- This forms a *-algebra under:
  - Addition: (F + G)_n = f_n + g_n
  - Scalar multiplication: (cF)_n = c · f_n
  - *-operation (Borchers involution): (F*)_n(x₁,...,xₙ) = conj(f_n(xₙ,...,x₁))

### Step 2: Inner Product (already in Reconstruction.lean)
- ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f*_n ⊗ g_m)
- Positive-definiteness from the Wightman positivity axiom
- Hermiticity from W_n(f̃) = conj(W_n(f)) and the Borchers involution
- Sesquilinearity from linearity of W_n

### Step 3: Null Space and Pre-Hilbert Space (already in Reconstruction.lean)
- N = {F : ⟨F,F⟩ = 0} is a left ideal (from Cauchy-Schwarz)
- PreHilbertSpace = BorchersSequence / N
- The inner product descends to the quotient (proven: well-definiteness)

### Step 4: Completion to Hilbert Space
- Complete the pre-Hilbert space using Mathlib's uniform completion
- The inner product extends by continuity

### Step 5: Field Operators
- For f ∈ S(ℝ^{d+1}), define φ(f) on Borchers sequences by:
    (φ(f)F)_n = δ_{n≥1} · f ⊗ f_{n-1}  (prepend f to the sequence)
- This preserves N, so descends to the pre-Hilbert space
- Extends to an unbounded operator on the Hilbert space (on a dense domain)

### Step 6: Vacuum
- Ω = equivalence class of (1, 0, 0, ...) (the sequence with f_0 = 1, rest zero)
- ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ) by construction

### Step 7: Verify Wightman Axioms
- Poincaré covariance: from translation invariance and Lorentz covariance of W_n
- Spectrum condition: from the spectral condition on W_n
- Locality: from local commutativity of W_n
- Cyclicity: from the density of Borchers sequences

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Wightman, "Quantum Field Theory in Terms of Vacuum Expectation Values" (1956)
* Borchers, "On Structure of the Algebra of Field Operators" (1962)
-/

noncomputable section

open Reconstruction

variable {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)

/-! ### Step 4: Completion to Hilbert Space -/

/- The pre-inner product space structure on the Borchers quotient.

    This collects all the pieces proven in Reconstruction.lean:
    - The quotient type (PreHilbertSpace Wfn)
    - The inner product (PreHilbertSpace.innerProduct)
    - Sesquilinearity, positive semi-definiteness, hermiticity

    The completion gives the physical Hilbert space. -/

/-- The inner product on PreHilbertSpace is positive semi-definite with
    respect to the real part: Re⟨[F], [F]⟩ ≥ 0. -/
theorem preHilbert_inner_pos (F : PreHilbertSpace Wfn) :
    (PreHilbertSpace.innerProduct Wfn F F).re ≥ 0 := by
  -- The inner product on the quotient inherits positivity from BorchersSequence
  induction F using Quotient.inductionOn with
  | h a => exact Wfn.positive_definite a

/-- The inner product on PreHilbertSpace is actually real on the diagonal:
    ⟨[F], [F]⟩ ∈ ℝ (i.e., the imaginary part is zero). -/
theorem preHilbert_inner_real (F : PreHilbertSpace Wfn) :
    (PreHilbertSpace.innerProduct Wfn F F).im = 0 := by
  -- From hermiticity: ⟨F,F⟩ = conj(⟨F,F⟩), so ⟨F,F⟩ is real
  induction F using Quotient.inductionOn with
  | h a =>
    have hdef : PreHilbertSpace.innerProduct Wfn ⟦a⟧ ⟦a⟧ =
        WightmanInnerProduct d Wfn.W a a := rfl
    have herm := WightmanInnerProduct_hermitian Wfn a a
    have heq : starRingEnd ℂ (WightmanInnerProduct d Wfn.W a a) =
        WightmanInnerProduct d Wfn.W a a := herm.symm
    have him := congr_arg Complex.im heq
    simp [Complex.conj_im] at him
    linarith [congr_arg Complex.im hdef]

/-- The vacuum in PreHilbertSpace.
    Uses `Reconstruction.vacuumSequence` (f_0 = 1, f_n = 0 for n ≥ 1)
    defined in Reconstruction.lean. -/
def vacuumState : PreHilbertSpace Wfn :=
  Quotient.mk _ (vacuumSequence (d := d))

/-- The vacuum is normalized: ⟨Ω, Ω⟩ = W_0(1) = 1 -/
theorem vacuum_normalized :
    PreHilbertSpace.innerProduct Wfn (vacuumState Wfn) (vacuumState Wfn) = 1 := by
  -- Reduce quotient inner product to WightmanInnerProduct on representatives
  show WightmanInnerProduct d Wfn.W (vacuumSequence (d := d)) (vacuumSequence (d := d)) = 1
  -- Unfold the double sum: Σ_{n ∈ range 2} Σ_{m ∈ range 2} W(n+m)(Ω*_n ⊗ Ω_m)
  simp only [WightmanInnerProduct]
  -- Expand range(bound + 1) = range(2) into individual terms
  rw [show (vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- For n=1 or m=1: vacuumSequence.funcs 1 = 0
  have hv1 : (vacuumSequence (d := d)).funcs 1 = 0 := rfl
  simp only [hv1, SchwartzMap.conjTensorProduct_zero_left,
    SchwartzMap.conjTensorProduct_zero_right, (Wfn.linear _).map_zero, add_zero]
  -- Remaining: W(0+0)(f₀.conjTensorProduct f₀) = 1
  -- Simplify 0 + 0 to 0 and apply normalization: W 0 f = f 0
  show Wfn.W 0 (((vacuumSequence (d := d)).funcs 0).conjTensorProduct
    ((vacuumSequence (d := d)).funcs 0)) = 1
  rw [Wfn.normalized]
  -- Goal: (f₀.conjTensorProduct f₀) 0 = 1
  rw [SchwartzMap.conjTensorProduct_apply]
  -- vacuumSequence.funcs 0 is the constant 1 function, so all applications give 1
  have hconst : ∀ x, (vacuumSequence (d := d)).funcs 0 x = 1 := fun _ => rfl
  rw [hconst, hconst, map_one, one_mul]

/-! ### Step 5: Field Operators on Pre-Hilbert Space

The adjoint relation ⟨φ(f)F, G⟩ = ⟨F, φ(f̄)G⟩ and its consequences
(fieldOperator_preserves_null, fieldOperator_well_defined) are proven
in Reconstruction.lean, making fieldOperator sorry-free. -/

/-! ### Step 6: The Key Property

Infrastructure for proving that ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ):
1. The iterated field operator action on vacuum has exactly one nonzero component
   at position n, equal to productTensor fs.
2. The WightmanInnerProduct of vacuum with such a sequence picks out W_n. -/

/-- The iterated fieldOperator on the quotient equals the quotient of the iterated
    fieldOperatorAction on representatives. -/
theorem foldr_fieldOperator_eq_mk {n : ℕ} (fs : Fin n → SchwartzSpacetime d) :
    List.foldr (fun f acc => fieldOperator Wfn f acc)
      (vacuumState Wfn) (List.ofFn fs) =
    ⟦List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)⟧ := by
  induction n with
  | zero => simp [List.ofFn_zero]; rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons, ih (fun i => fs i.succ)]
    rfl

/-- The n-th component of the iterated field action on vacuum equals productTensor. -/
theorem iteratedAction_funcs_n {n : ℕ} (fs : Fin n → SchwartzSpacetime d) :
    (List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)).funcs n =
    SchwartzMap.productTensor fs := by
  induction n with
  | zero => simp [List.ofFn_zero]; rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons, fieldOperatorAction_funcs_succ, ih (fun i => fs i.succ)]
    rfl

/-- Components ≠ n of the iterated field action on vacuum are zero. -/
theorem iteratedAction_funcs_ne {n : ℕ} (fs : Fin n → SchwartzSpacetime d)
    (k : ℕ) (hk : k ≠ n) :
    (List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)).funcs k = 0 := by
  induction n generalizing k with
  | zero =>
    simp only [List.ofFn_zero, List.foldr_nil]
    cases k with
    | zero => exact absurd rfl hk
    | succ k => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons]
    cases k with
    | zero => exact fieldOperatorAction_funcs_zero _ _
    | succ k =>
      rw [fieldOperatorAction_funcs_succ, ih (fun i => fs i.succ) k (by omega)]
      exact SchwartzMap.prependField_zero_right _

/-- The bound of the iterated field action on vacuum. -/
private theorem iteratedAction_bound {n : ℕ} (fs : Fin n → SchwartzSpacetime d) :
    (List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)).bound = n + 1 := by
  induction n with
  | zero => simp [List.ofFn_zero]; rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons, fieldOperatorAction_bound, ih (fun i => fs i.succ)]

/-- W(0+m)(vacuumConj ⊗ h) = W(m)(h): the vacuum conjTensorProduct with any
    function reduces to the function itself (up to the 0+m = m identification). -/
private theorem W_conjTP_vacuum_zero (m : ℕ) (h : SchwartzNPoint d m) :
    Wfn.W (0 + m) (((vacuumSequence (d := d)).funcs 0).conjTensorProduct h) = Wfn.W m h := by
  apply W_eq_of_cast Wfn.W _ _ (Nat.zero_add m)
  intro x
  simp only [SchwartzMap.conjTensorProduct_apply, splitFirst]
  have hvac : ∀ y, (vacuumSequence (d := d)).funcs 0 y = 1 := fun _ => rfl
  rw [hvac, map_one, one_mul]
  -- Goal: h (splitLast 0 m x) = h (fun i => x (Fin.cast _ i))
  unfold splitLast
  -- Goal: h (fun j => x (Fin.natAdd 0 j)) = h (fun i => x (Fin.cast _ i))
  -- Both Fin values have the same .val (= j.val)
  congr 1; ext j; congr 1; ext; simp [Fin.val_cast]

/-- The fundamental property of the GNS construction:
    ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)

    This is what makes the reconstruction work — the matrix elements of the
    constructed field operators between vacuum states reproduce the original
    Wightman functions on product test functions. -/
theorem gns_reproduces_wightman (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    PreHilbertSpace.innerProduct Wfn (vacuumState Wfn)
      (List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fs)) =
    Wfn.W n (SchwartzMap.productTensor fs) := by
  -- Step 1: Lift to Borchers sequence level
  rw [foldr_fieldOperator_eq_mk Wfn fs]
  -- Now: WIP vacuumSequence (foldr fieldOperatorAction vacuumSequence (ofFn fs))
  show WightmanInnerProduct d Wfn.W vacuumSequence
    (List.foldr fieldOperatorAction (vacuumSequence (d := d)) (List.ofFn fs)) =
    Wfn.W n (SchwartzMap.productTensor fs)
  -- Step 2: Expand the WIP sum
  simp only [WightmanInnerProduct]
  -- vacuumSequence.bound = 1, so k ∈ {0, 1}
  rw [show (vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- k=1: vacuumSequence.funcs 1 = 0, so all terms vanish
  have hvac1 : (vacuumSequence (d := d)).funcs 1 = 0 := rfl
  simp only [hvac1, SchwartzMap.conjTensorProduct_zero_left,
    (Wfn.linear _).map_zero, Finset.sum_const_zero, add_zero]
  -- Step 3: The inner sum was split by the earlier simp (sum_range_succ) into
  -- (∑ m ∈ range G.bound, f m) + f G.bound = target.
  -- Substitute G.bound = n + 1, then handle term-by-term.
  rw [iteratedAction_bound fs]
  -- Goal: (∑ m ∈ range (n+1), f m) + f(n+1) = W n (productTensor fs)
  -- Show f(n+1) = 0 (component n+1 of iterated action is zero since n+1 ≠ n)
  rw [iteratedAction_funcs_ne fs (n + 1) (by omega),
    SchwartzMap.conjTensorProduct_zero_right, (Wfn.linear _).map_zero, add_zero]
  -- Goal: ∑ m ∈ range (n+1), f m = W n (productTensor fs)
  -- Extract the single nonzero term at m = n
  rw [Finset.sum_eq_single n
    (fun m _ hm => by
      rw [iteratedAction_funcs_ne fs m hm,
        SchwartzMap.conjTensorProduct_zero_right, (Wfn.linear _).map_zero])
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
  -- Step 4: W(0+n)(vac₀.conjTP(productTensor fs)) = W(n)(productTensor fs)
  rw [iteratedAction_funcs_n fs]
  exact W_conjTP_vacuum_zero Wfn n (SchwartzMap.productTensor fs)

/-! ### Step 7: Poincaré Covariance -/

/- The Poincaré group acts on Borchers sequences via the pull-back:
    (g · F)_n = F_n ∘ g⁻¹

    For the translation subgroup: (T_a · F)_n(x₁,...,xₙ) = F_n(x₁-a,...,xₙ-a)
    For the Lorentz subgroup: (Λ · F)_n(x₁,...,xₙ) = F_n(Λ⁻¹x₁,...,Λ⁻¹xₙ)

    This action preserves the inner product by translation/Lorentz invariance of W_n,
    and hence descends to a unitary representation on the Hilbert space. -/

/-- The translation action on Borchers sequences preserves the inner product.

    If F' and G' are the translations of F and G by a ∈ ℝ^{d+1}, meaning
    F'_n(x₁,...,xₙ) = F_n(x₁-a,...,xₙ-a), then ⟨F', G'⟩ = ⟨F, G⟩.

    Proof: Each summand W_{n+m}((f')*_n ⊗ g'_m) = W_{n+m}(f*_n ⊗ g_m) by
    the translation invariance of the Wightman functions. -/
theorem translation_preserves_inner (a : SpacetimeDim d)
    (F G F' G' : BorchersSequence d)
    (hF' : ∀ n (x : NPointDomain d n), (F'.funcs n) x = (F.funcs n) (fun i => x i - a))
    (hG' : ∀ n (x : NPointDomain d n), (G'.funcs n) x = (G.funcs n) (fun i => x i - a)) :
    WightmanInnerProduct d Wfn.W F' G' = WightmanInnerProduct d Wfn.W F G := by
  -- Extend both inner products to a common summation range
  set N₁ := max F.bound F'.bound + 1
  set N₂ := max G.bound G'.bound + 1
  rw [WightmanInnerProduct_eq_extended d Wfn.W Wfn.linear F' G' N₁ N₂
        (by omega) (by omega),
      WightmanInnerProduct_eq_extended d Wfn.W Wfn.linear F G N₁ N₂
        (by omega) (by omega)]
  -- Both are now WightmanInnerProductN with the same range. Show term-by-term equality.
  unfold WightmanInnerProductN
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro m _
  -- Goal: W(k+m)(F'.funcs k .conjTP G'.funcs m) = W(k+m)(F.funcs k .conjTP G.funcs m)
  -- Use translation invariance: g(x) = f(x + a) → W f = W g
  -- Here f = F'.conjTP G', g = F.conjTP G, and g(x) = f(x + a).
  apply Wfn.translation_invariant (k + m) a
  intro x
  -- Convert .toFun to coercion form
  show (F.funcs k).conjTensorProduct (G.funcs m) x =
       (F'.funcs k).conjTensorProduct (G'.funcs m) (fun i => x i + a)
  simp only [SchwartzMap.conjTensorProduct_apply]
  -- F' evaluated at (splitFirst(x+a)) = F evaluated at (splitFirst(x))
  have hF_eq : (F'.funcs k) (fun i => splitFirst k m (fun j => x j + a) (Fin.rev i)) =
      (F.funcs k) (fun i => splitFirst k m x (Fin.rev i)) := by
    rw [hF' k]; congr 1; funext i; simp [splitFirst, add_sub_cancel_right]
  -- G' evaluated at (splitLast(x+a)) = G evaluated at (splitLast(x))
  have hG_eq : (G'.funcs m) (splitLast k m (fun j => x j + a)) =
      (G.funcs m) (splitLast k m x) := by
    rw [hG' m]; congr 1; funext j; simp [splitLast, add_sub_cancel_right]
  rw [hF_eq, hG_eq]

/-! ### Connecting Everything: The Full Reconstruction -/

/- Summary of what the Wightman reconstruction theorem proves:

    Given: WightmanFunctions d (satisfying temperedness, Poincaré covariance,
    spectrum condition, locality, positive-definiteness, hermiticity, normalization)

    Construct:
    1. Hilbert space H = completion of BorchersSequence / {null vectors}
    2. Vacuum Ω = [vacuumSequence] ∈ H, with ‖Ω‖ = 1
    3. Field operators φ(f) : H → H (unbounded, on dense domain)
    4. Unitary representation U of Poincaré group on H

    Properties:
    - ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)
    - U(g)Ω = Ω (vacuum is Poincaré-invariant)
    - U(g)φ(f)U(g)⁻¹ = φ(g·f) (covariance)
    - [φ(f), φ(g)] = 0 when supports of f, g are spacelike separated (locality)
    - Energy spectrum in forward cone (from spectrum condition)
    - span{φ(f₁)···φ(fₙ)Ω} is dense in H (cyclicity, from construction) -/

end
