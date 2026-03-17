/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import OSReconstruction.Wightman.Basic
import OSReconstruction.Wightman.OperatorDistribution
import OSReconstruction.Wightman.SchwartzTensorProduct

/-!
# Wightman Axioms

This file provides a rigorous mathematical formulation of the Wightman axioms for
quantum field theory. The axioms are formalized as a structure `WightmanQFT` that
contains all the required data and properties.

## Main Definitions

* `WightmanQFT` - The complete structure satisfying all Wightman axioms
* `WightmanQFT.spectrumCondition` - Energy-momentum spectrum lies in forward light cone
* `WightmanQFT.locality` - Spacelike-separated fields commute

## The Wightman Axioms

The Wightman axioms (W1-W4) as formalized here:

**W1 (Covariance)**:
- There is a continuous unitary representation U of the Poincaré group on H
- The generators P_μ (energy-momentum) have spectrum in the forward light cone V₊
- There exists a unique vacuum vector Ω invariant under U(g)

**W2 (Field Operators)**:
- There exist field operators φ(f) for each test function f ∈ 𝒮(ℝ^{d+1})
- The domain D is dense and invariant under all φ(f)
- The subspace spanned by φ(f₁)···φ(fₙ)Ω is dense in H
- The field is covariant: U(g) φ(f) U(g)⁻¹ = φ(f ∘ g⁻¹)

**W3 (Locality)**:
- If supp(f) and supp(g) are spacelike separated, then [φ(f), φ(g)] = 0 on D

**W4 (Vacuum Uniqueness)**:
- The vacuum Ω is the unique vector (up to phase) invariant under time translations

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Haag, "Local Quantum Physics"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable (d : ℕ) [NeZero d]

/-! ### Spectrum Condition -/

/-- The forward light cone in momentum space: p₀ ≥ 0, p² ≤ 0.
    In the mostly positive signature, p² = -p₀² + |p⃗|², so p² ≤ 0 means p₀ ≥ |p⃗|.
    This is the region where timelike and lightlike momenta with positive energy lie. -/
def ForwardMomentumCone : Set (MinkowskiSpace d) :=
  MinkowskiSpace.ClosedForwardLightCone d

/-- The spectrum condition: the joint spectrum of the energy-momentum operators
    lies in the closed forward light cone.

    Mathematically: For any state ψ in the domain of the momentum operators,
    the spectral support of ψ (the support of its spectral measure) lies in V̄₊.

    Equivalently, for any translation-covariant state:
      ⟨ψ, U(a) ψ⟩ = ∫_{V̄₊} e^{ip·a} dμ_ψ(p)

    where V̄₊ = {p : p₀ ≥ 0 and p² ≤ 0} is the closed forward light cone
    (in mostly positive signature, p² = -p₀² + |p⃗|² ≤ 0 means p₀ ≥ |p⃗|).

    We express this via the Fourier transform of the 2-point function having
    support in the forward cone. -/
structure SpectralCondition (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  /-- The energy is non-negative: for all states ψ, ⟨ψ, Hψ⟩ ≥ 0 where H = P₀ -/
  energy_nonneg : ∀ ψ : H, (⟪ψ, π.hamiltonian ψ⟫_ℂ).re ≥ 0
  /-- The mass-shell condition: p² ≤ 0 (in mostly positive signature).
      For any state ψ, the expectation value of P² = -P₀² + Σᵢ Pᵢ² is ≤ 0.
      This encodes that the spectral support lies in the forward cone. -/
  mass_shell : ∀ ψ : H, (⟪ψ, π.hamiltonian (π.hamiltonian ψ)⟫_ℂ).re ≥
    ∑ i : Fin d, (⟪ψ, π.spatialMomentum i (π.spatialMomentum i ψ)⟫_ℂ).re

/-! ### Locality -/

/-- Two Schwartz functions have spacelike-separated supports -/
def AreSpacelikeSeparatedSupports (f g : SchwartzSpacetime d) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g,
    MinkowskiSpace.AreSpacelikeSeparated d x y

/-- The commutator of two operators on a domain -/
def Commutator {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H → H) (D : Set H) : Prop :=
  ∀ ψ ∈ D, A (B ψ) = B (A ψ)

/-- Locality: spacelike-separated fields commute -/
def IsLocal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : OperatorValuedDistribution d H) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    AreSpacelikeSeparatedSupports d f g →
    Commutator (φ.operator f) (φ.operator g) φ.domain.toSubmodule

/-! ### Vacuum Properties -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector is invariant under the Poincaré representation -/
def IsPoincareInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ g : PoincareGroup d, π.U g Ω = Ω

/-- A vector is invariant under time translations only -/
def IsTimeTranslationInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ t : ℝ, π.U (PoincareGroup.translation' (fun i => if i = 0 then t else 0)) Ω = Ω

/-- Uniqueness of the vacuum: Ω is the unique (up to phase) translation-invariant vector -/
def VacuumUnique (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  IsTimeTranslationInvariant d π Ω ∧
  ∀ ψ : H, IsTimeTranslationInvariant d π ψ → ∃ c : ℂ, ψ = c • Ω

/-! ### The Complete Wightman QFT Structure -/

/-- A Wightman quantum field theory consists of:
    - A Hilbert space H (the state space)
    - A unitary representation of the Poincaré group
    - Field operators satisfying the Wightman axioms

    This structure encapsulates all the Wightman axioms (W1-W4). -/
structure WightmanQFT (d : ℕ) [NeZero d] where
  /-- The Hilbert space of states -/
  HilbertSpace : Type*
  /-- Hilbert space is a normed additive commutative group -/
  [instNormedAddCommGroup : NormedAddCommGroup HilbertSpace]
  /-- Hilbert space has inner product structure -/
  [instInnerProductSpace : InnerProductSpace ℂ HilbertSpace]
  /-- Hilbert space is complete -/
  [instCompleteSpace : CompleteSpace HilbertSpace]

  -- W1: Poincaré Covariance and Spectrum Condition
  /-- The unitary representation of the Poincaré group -/
  poincare_rep : @PoincareRepresentation d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- Spectrum condition: energy-momentum spectrum in forward cone -/
  spectrum_condition : @SpectralCondition d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep
  /-- The vacuum vector -/
  vacuum : HilbertSpace
  /-- The vacuum is normalized -/
  vacuum_normalized : @norm HilbertSpace instNormedAddCommGroup.toNorm vacuum = 1
  /-- The vacuum is Poincaré invariant -/
  vacuum_invariant : @IsPoincareInvariant d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

  -- W2: Field Operators
  /-- The field operator-valued distribution -/
  field : @OperatorValuedDistribution d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- The vacuum is in the domain -/
  vacuum_in_domain : vacuum ∈ field.domain
  /-- Hermiticity of the field: ⟨φ(f)χ, ψ⟩ = ⟨χ, φ(f̄)ψ⟩ for χ, ψ ∈ D.
      Here `SchwartzMap.conj` is pointwise complex conjugation. This is standard
      Wightman axiom W2' (Streater-Wightman §3.1). -/
  field_hermitian : ∀ (f : SchwartzSpacetime d) (χ ψ : HilbertSpace),
    χ ∈ field.domain → ψ ∈ field.domain →
    ⟪field.operator f χ, ψ⟫_ℂ = ⟪χ, field.operator (SchwartzMap.conj f) ψ⟫_ℂ
  /-- Cyclicity: the algebraic span of field operators on vacuum is dense -/
  cyclicity : @Dense HilbertSpace (instNormedAddCommGroup.toUniformSpace.toTopologicalSpace)
              (field.algebraicSpan vacuum).carrier
  /-- The action of Poincaré transformations on test functions.
      (g · f)(x) = f(g⁻¹ · x) where g · x = Λx + a.

      Note: Proving that Poincaré transformations preserve the Schwartz class
      requires substantial analysis infrastructure. We include this as data
      with the consistency constraint `poincareAction_spec` below. -/
  poincareActionOnSchwartz : PoincareGroup d → SchwartzSpacetime d → SchwartzSpacetime d
  /-- Consistency: the Schwartz-wrapped action agrees with the pointwise action.
      This prevents axiom smuggling — the Schwartz wrapper must have the correct
      underlying function f(g⁻¹ · x). -/
  poincareAction_spec : ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (x : SpacetimeDim d),
    (poincareActionOnSchwartz g f).toFun x = f.toFun (PoincareGroup.act g⁻¹ x)
  /-- Covariance: U(g) φ(f) U(g)⁻¹ = φ(g·f) where (g·f)(x) = f(g⁻¹·x).

      Expressed via matrix elements: for all g ∈ ISO(1,d), f ∈ 𝒮, and ψ, χ ∈ D,
        ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, φ(g⁻¹·f) ψ⟩

      Derivation: U(g)⁻¹ φ(f) U(g) = φ(g⁻¹·f) (substitute g → g⁻¹ in U(g)φ(f)U(g)⁻¹ = φ(g·f)),
      so ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, U(g)⁻¹ φ(f) U(g) ψ⟩ = ⟨χ, φ(g⁻¹·f) ψ⟩. -/
  covariance : ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (χ ψ : HilbertSpace),
    χ ∈ field.domain → ψ ∈ field.domain →
    ⟪poincare_rep.U g χ, field.operator f (poincare_rep.U g ψ)⟫_ℂ =
    ⟪χ, field.operator (poincareActionOnSchwartz g⁻¹ f) ψ⟫_ℂ

  -- W3: Locality
  /-- Locality: spacelike-separated fields commute -/
  locality : @IsLocal d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace field

  -- W4: Vacuum Uniqueness
  /-- Uniqueness of vacuum -/
  vacuum_unique : @VacuumUnique d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

namespace WightmanQFT

variable {d : ℕ} [NeZero d]

-- Expose instances from WightmanQFT for use in definitions
attribute [instance] WightmanQFT.instNormedAddCommGroup
attribute [instance] WightmanQFT.instInnerProductSpace
attribute [instance] WightmanQFT.instCompleteSpace

/-- The Wightman n-point functions of a Wightman QFT.
    W_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ -/
def wightmanFunction (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ

/-- The 2-point function (propagator) W₂(f,g) = ⟨Ω, φ(f)φ(g)Ω⟩ -/
def twoPointFunction (qft : WightmanQFT d) :
    SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => qft.wightmanFunction 2 ![f, g]

/-- Symmetry property for bosonic fields: [φ(f), φ(g)] = 0 for any f, g -/
def IsBosonic (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    Commutator (qft.field.operator f) (qft.field.operator g) qft.field.domain.toSubmodule

/-- The Reeh-Schlieder property: the vacuum is cyclic for local algebras.
    For any open region O, the vectors φ(f₁)···φ(fₙ)Ω with supp(fᵢ) ⊆ O are dense. -/
def ReehSchlieder (qft : WightmanQFT d) (O : Set (SpacetimeDim d)) : Prop :=
  let localSpan := Submodule.span ℂ
    { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
      (∀ i, Function.support (fs i) ⊆ O) ∧
      ψ = qft.field.operatorPow n fs qft.vacuum }
  Dense localSpan.carrier

/-- The Wightman functions are positive (reflection positivity).
    ‖φ(f₁)···φ(fₙ)Ω‖² ≥ 0, equivalently Re⟨ψ, ψ⟩ ≥ 0.
    For inner products in Hilbert space, ⟨ψ, ψ⟩ is real and equals ‖ψ‖². -/
def WightmanPositivity (qft : WightmanQFT d) : Prop :=
  ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
    (⟪qft.field.operatorPow n fs qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ).re ≥ 0

/-- Hermiticity of the 2-point function: W₂(f, g)* = W₂(ḡ, f̄).
    This follows from the hermiticity of the field. -/
def TwoPointHermitian (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    starRingEnd ℂ (qft.twoPointFunction f g) = qft.twoPointFunction g f

end WightmanQFT

/-! ### Wightman Functions as Distributions -/

/-- The n-point domain: n copies of (d+1)-dimensional spacetime.
    Points are functions Fin n → Fin (d+1) → ℝ, i.e., n spacetime points. -/
abbrev NPointSpacetime (d n : ℕ) := Fin n → Fin (d + 1) → ℝ

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPointSpace (d n : ℕ) := SchwartzMap (NPointSpacetime d n) ℂ

/-- The Wightman n-point function on product test functions.

    W_n(f₁, ..., fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩

    This is defined for factored test functions (f₁,...,fₙ) where each fᵢ ∈ 𝒮(ℝ^{d+1}).
    Extension to general test functions F ∈ 𝒮(ℝ^{n(d+1)}) requires the nuclear
    theorem for Schwartz spaces, which guarantees that the multilinear functional
    on 𝒮(ℝ^{d+1})^⊗n extends uniquely to a continuous linear functional on
    the completed projective tensor product 𝒮(ℝ^{n(d+1)}). -/
def WightmanDistributionProduct (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  qft.wightmanFunction n

/-- **Schwartz kernel / nuclear theorem for Schwartz spaces.**

    Let `E = S(R^(d+1))`. Every continuous multilinear functional on `E^n`
    extends uniquely to a continuous linear functional on `S(R^(n(d+1)))`,
    after the standard identification of the completed projective tensor product
    `E ⊗̂π ... ⊗̂π E` with the Schwartz space on the product domain.

    Concretely, the extension agrees with the original multilinear functional on
    pure tensors `f_1 ⊗ ... ⊗ f_n`, encoded here by `SchwartzMap.productTensor`.

    **Status**: The nuclearity of Schwartz space (`S(ℝⁿ)` is a nuclear space)
    is now proved in the `gaussian-field` Lean 4 library
    (https://github.com/or-n/gaussian-field). The remaining gap is the
    formal bridge: importing the `NuclearSpace` instance for `SchwartzMap`
    and deriving this kernel theorem from it. See `GAUSSIAN_FIELD_INTEGRATION.md`
    for the planned integration route.

    Ref: Gel'fand-Vilenkin, "Generalized Functions IV", Ch. I, 3;
    Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13;
    Treves, "Topological Vector Spaces", Ch. 51. -/
axiom schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (SchwartzMap.productTensor fs) = Phi fs

/-- Linearity of `operatorPow` in a fixed test-function slot under scalar multiplication. -/
private theorem operatorPow_smul_at
    (qft : WightmanQFT d)
    (n : ℕ) (k : Fin n) (c : ℂ) (f : SchwartzSpacetime d)
    (fs : Fin n → SchwartzSpacetime d) (ψ : qft.HilbertSpace)
    (hψ : ψ ∈ qft.field.domain) :
    qft.field.operatorPow n (Function.update fs k (c • f)) ψ =
      c • qft.field.operatorPow n (Function.update fs k f) ψ := by
  induction n with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      simp only [OperatorValuedDistribution.operatorPow]
      by_cases hk : k.val = 0
      · have hk0 : k = 0 := Fin.ext hk
        subst hk0
        have htail_eq : ∀ h : SchwartzSpacetime d,
            (fun i => Function.update fs 0 h (Fin.succ i)) = (fun i => fs (Fin.succ i)) := by
          intro h
          ext i
          rw [Function.update_of_ne (Fin.succ_ne_zero i)]
        simp only [Function.update_self, htail_eq]
        have h_domain := OperatorValuedDistribution.operatorPow_domain qft.field n
          (fun i => fs (Fin.succ i)) ψ hψ
        rw [qft.field.operator_smul c f _ h_domain]
      · have hk_pred : k.val - 1 < n := by omega
        let k' : Fin n := ⟨k.val - 1, hk_pred⟩
        have h0_ne : k ≠ 0 := fun h => hk (congrArg Fin.val h)
        simp only [Function.update_of_ne h0_ne.symm]
        have htail : ∀ h : SchwartzSpacetime d,
            (fun i => Function.update fs k h (Fin.succ i)) =
              Function.update (fun i => fs (Fin.succ i)) k' h := by
          intro h
          ext i
          simp only [Function.update]
          by_cases hi : i = k'
          · simp only [hi]
            have : Fin.succ k' = k := by
              ext
              simp only [Fin.val_succ, k']
              omega
            simp [this]
          · simp only [hi]
            have : Fin.succ i ≠ k := by
              intro heq
              apply hi
              ext
              simp only [k']
              have := congrArg Fin.val heq
              simp only [Fin.val_succ] at this
              omega
            simp [this]
        rw [htail (c • f), htail f]
        rw [ih k' (fun i => fs (Fin.succ i))]
        have h1 :
            qft.field.operatorPow n (Function.update (fun i => fs (Fin.succ i)) k' f) ψ ∈
              qft.field.domain :=
          OperatorValuedDistribution.operatorPow_domain qft.field n _ ψ hψ
        rw [qft.field.operator_vector_smul (fs 0) c _ h1]

/-- The Wightman product functional as a multilinear map on Schwartz factors. -/
private def wightmanMultilinearMap (qft : WightmanQFT d) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ where
  toFun := qft.wightmanFunction n
  map_update_add' := by
    intro hdec fs i f g
    have hupdate :
        @Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (f + g) =
          Function.update fs i (f + g) := by
      ext j
      by_cases hj : j = i <;> simp [Function.update, hj]
    change ⟪qft.vacuum,
        qft.field.operatorPow n
          (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (f + g))
          qft.vacuum⟫_ℂ =
      ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ +
        ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i g) qft.vacuum⟫_ℂ
    have hpow :
        qft.field.operatorPow n
            (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (f + g))
            qft.vacuum =
          qft.field.operatorPow n (Function.update fs i (f + g)) qft.vacuum := by
      simpa [hupdate]
    have hadd' :
        ⟪qft.vacuum,
            qft.field.operatorPow n
              (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (f + g))
              qft.vacuum⟫_ℂ =
          ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ +
            ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i g) qft.vacuum⟫_ℂ := by
      have hinner :
          ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i (f + g)) qft.vacuum⟫_ℂ =
            ⟪qft.vacuum,
              qft.field.operatorPow n
                (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (f + g))
                qft.vacuum⟫_ℂ := by
        simpa using congrArg (fun v => ⟪qft.vacuum, v⟫_ℂ) hpow.symm
      have hadd0 :
          ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i (f + g)) qft.vacuum⟫_ℂ =
            ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ +
              ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i g) qft.vacuum⟫_ℂ := by
        have hdec_eq : hdec = instDecidableEqFin n := Subsingleton.elim _ _
        subst hdec_eq
        simpa [WightmanNPoint] using
          (WightmanNPoint.linear_arg (d := d) qft.field qft.vacuum qft.vacuum_in_domain
            n i f g fs)
      exact hinner.symm.trans hadd0
    exact hadd'
  map_update_smul' := by
    intro hdec fs i c f
    have hupdate :
        @Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (c • f) =
          Function.update fs i (c • f) := by
      ext j
      by_cases hj : j = i <;> simp [Function.update, hj]
    change ⟪qft.vacuum,
        qft.field.operatorPow n
          (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (c • f))
          qft.vacuum⟫_ℂ =
      c * ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ
    have hpow :
        qft.field.operatorPow n
            (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (c • f))
            qft.vacuum =
          qft.field.operatorPow n (Function.update fs i (c • f)) qft.vacuum := by
      simpa [hupdate]
    have hsmul' :
        ⟪qft.vacuum,
            qft.field.operatorPow n
              (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (c • f))
              qft.vacuum⟫_ℂ =
          c * ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ := by
      have hinner :
          ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i (c • f)) qft.vacuum⟫_ℂ =
            ⟪qft.vacuum,
              qft.field.operatorPow n
                (@Function.update (Fin n) (fun _ => SchwartzSpacetime d) hdec fs i (c • f))
                qft.vacuum⟫_ℂ := by
        simpa using congrArg (fun v => ⟪qft.vacuum, v⟫_ℂ) hpow.symm
      have hsmul0 :
          ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i (c • f)) qft.vacuum⟫_ℂ =
            c * ⟪qft.vacuum, qft.field.operatorPow n (Function.update fs i f) qft.vacuum⟫_ℂ := by
        have hdec_eq : hdec = instDecidableEqFin n := Subsingleton.elim _ _
        subst hdec_eq
        have hkey := operatorPow_smul_at (d := d) qft n i c f fs qft.vacuum qft.vacuum_in_domain
        exact (congrArg (fun v => ⟪qft.vacuum, v⟫_ℂ) hkey).trans (inner_smul_right _ _ _)
      exact hinner.symm.trans hsmul0
    exact hsmul'

/-- Banach-Steinhaus / Fréchet-space bridge for finite multilinear maps on Schwartz space.

    This is the standard theorem that separately continuous multilinear maps on products of
    Schwartz spaces are jointly continuous. It is pure functional analysis and carries no QFT
    content; here it is used only to promote a multilinear map to a `ContinuousMultilinearMap`
    so the fixed nuclear axiom can be applied. -/
axiom exists_continuousMultilinear_ofSeparatelyContinuous {n : ℕ}
    (Phi : MultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ)
    (hPhi : ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
      Continuous (fun f => Phi (Function.update fs i f))) :
    ∃ PhiCont : ContinuousMultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d, PhiCont fs = Phi fs

/-- Helper: the Wightman n-point function is separately continuous in each test-function slot. -/
private theorem inner_operatorPow_update_continuous (qft : WightmanQFT d)
    (n : ℕ) (i : Fin n) (fs : Fin n → SchwartzSpacetime d)
    (χ ψ : qft.HilbertSpace) (hχ : χ ∈ qft.field.domain) (hψ : ψ ∈ qft.field.domain) :
    Continuous (fun f => ⟪χ, qft.field.operatorPow n (Function.update fs i f) ψ⟫_ℂ) := by
  -- Induction on n, generalizing χ (needed for hermiticity step)
  induction n generalizing χ with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    by_cases hi : i.val = 0
    · -- i = 0: φ(f) applied to fixed tail
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
      have heq : ∀ f, ⟪χ, qft.field.operatorPow (n + 1) (Function.update fs i f) ψ⟫_ℂ =
          ⟪χ, qft.field.operator f
            (qft.field.operatorPow n (fun j => fs j.succ) ψ)⟫_ℂ := by
        intro f; rw [hi0]; simp only [OperatorValuedDistribution.operatorPow]; congr 2
      simp_rw [heq]
      exact qft.field.matrix_element_continuous χ _ hχ
        (qft.field.operatorPow_domain n _ ψ hψ)
    · -- i > 0: use hermiticity to move φ(fs 0) left, then induct with new χ
      let i' : Fin n := ⟨i.val - 1, by omega⟩
      let χ' := qft.field.operator (SchwartzMap.conj (fs 0)) χ
      have hχ' : χ' ∈ qft.field.domain := qft.field.operator_domain _ χ hχ
      -- Show: the function equals ⟨χ', operatorPow n (update(tail)(i') f) ψ⟩
      suffices key : ∀ f, ⟪χ, qft.field.operatorPow (n + 1) (Function.update fs i f) ψ⟫_ℂ =
          ⟪χ', qft.field.operatorPow n (Function.update (fun j => fs j.succ) i' f) ψ⟫_ℂ by
        simp_rw [key]
        exact ih i' (fun j => fs j.succ) χ' hχ'
      intro f
      -- Unfold operatorPow (n+1)
      show ⟪χ, qft.field.operator (Function.update fs i f 0)
          (qft.field.operatorPow n (fun j => Function.update fs i f j.succ) ψ)⟫_ℂ = _
      -- fs 0 unchanged since i > 0
      rw [Function.update_of_ne (show (0 : Fin (n+1)) ≠ i from
        fun h => hi (by rw [← h]; rfl)) f fs]
      -- Use hermiticity: ⟨χ, φ(g) v⟩ = ⟨φ(conj g) χ, v⟩
      -- field_hermitian gives: ⟨φ(f) χ, ψ⟩ = ⟨χ, φ(conj f) ψ⟩
      -- Apply with f := conj(fs 0): ⟨φ(conj(fs 0)) χ, v⟩ = ⟨χ, φ(conj(conj(fs 0))) v⟩ = ⟨χ, φ(fs 0) v⟩
      have hv_dom := qft.field.operatorPow_domain n
        (fun j => Function.update fs i f j.succ) ψ hψ
      have := qft.field_hermitian (SchwartzMap.conj (fs 0)) χ _ hχ hv_dom
      simp only [SchwartzMap.conj_conj] at this
      rw [this.symm]; clear this
      -- Now need: operatorPow n (fun j => update fs i f j.succ) ψ
      --         = operatorPow n (update (fun j => fs j.succ) i' f) ψ
      have htail : (fun j => Function.update fs i f j.succ) =
          Function.update (fun j => fs j.succ) i' f := by
        funext j
        simp only [Function.update_apply, i']
        congr 1; ext
        simp only [Fin.ext_iff, Fin.val_succ]
        omega
      rw [htail]

private theorem wightman_separately_continuous (qft : WightmanQFT d) (n : ℕ)
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d) :
    Continuous (fun f => qft.wightmanFunction n (Function.update fs i f)) := by
  exact inner_operatorPow_update_continuous (d := d) qft n i fs qft.vacuum qft.vacuum
    qft.vacuum_in_domain qft.vacuum_in_domain

/-- The Wightman product functional is jointly continuous multilinear on the Schwartz factors. -/
private theorem exists_wightman_continuousMultilinear (qft : WightmanQFT d) (n : ℕ) :
    ∃ Phi : ContinuousMultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d, Phi fs = qft.wightmanFunction n fs := by
  refine exists_continuousMultilinear_ofSeparatelyContinuous (d := d)
    (Phi := wightmanMultilinearMap (d := d) qft n) ?_
  intro i fs
  simpa [wightmanMultilinearMap] using wightman_separately_continuous (d := d) qft n i fs

/-- **Wightman n-point functions extend to tempered distributions.**

    The multilinear Wightman functional (f_1,...,f_n) -> Omega, phi(f_1)...phi(f_n) Omega
    extends to a continuous linear functional on the full Schwartz space S(R^{n(d+1)}).

    This uses the nuclear theorem (`schwartz_nuclear_extension`) together with
    separate continuity of the Wightman functional in each test function argument.
    Separate continuity follows from the field operators being tempered distributions
    (continuous linear maps from S to operators on D) and the inner product being
    separately continuous. -/
theorem wightmanDistribution_extends (qft : WightmanQFT d) (n : ℕ) :
    ∃ (W_n : SchwartzNPointSpace d n →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzSpacetime d,
        W_n (SchwartzMap.productTensor fs) = qft.wightmanFunction n fs := by
  obtain ⟨Phi, hPhi⟩ := exists_wightman_continuousMultilinear (d := d) qft n
  obtain ⟨W_n, hW_n, _⟩ := schwartz_nuclear_extension (d := d) (n := n) Phi
  refine ⟨W_n, ?_⟩
  intro fs
  rw [hW_n]
  exact hPhi fs

/-- A chosen tempered-distribution extension of the `n`-point Wightman functional. -/
noncomputable def chosenWightmanDistribution (qft : WightmanQFT d) (n : ℕ) :
    SchwartzNPointSpace d n →L[ℂ] ℂ :=
  Classical.choose (wightmanDistribution_extends (d := d) qft n)

@[simp] theorem chosenWightmanDistribution_productTensor
    (qft : WightmanQFT d) (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    chosenWightmanDistribution (d := d) qft n (SchwartzMap.productTensor fs) =
      qft.wightmanFunction n fs :=
  (Classical.choose_spec (wightmanDistribution_extends (d := d) qft n)) fs

/-- Temperedness of Wightman functions: The multilinear Wightman n-point function
    (f₁,...,fₙ) ↦ ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ is separately continuous in each argument.

    Full temperedness (continuity of the extension to 𝒮(ℝ^{n(d+1)})) follows from
    the nuclear theorem; see `wightmanDistribution_extends`. -/
def WightmanTempered (qft : WightmanQFT d) (n : ℕ) : Prop :=
  ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
    Continuous (fun f => qft.wightmanFunction n (Function.update fs i f))

/-! ### Analytic Continuation -/

/-- A vector η ∈ ℝ^{d+1} lies in the open forward light cone V₊ if η₀ > 0 and η² < 0. -/
def InOpenForwardCone (d : ℕ) [NeZero d] (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0

/-- An approach direction η has successive differences in V⁺.

    This is the correct condition for `x + iε·η` to lie in the forward tube:
    `Im(z_k - z_{k-1}) = ε·(η_k - η_{k-1}) ∈ V⁺` for all k (with η_{-1} = 0).

    This matches the definition of `ForwardConeAbs` in `ForwardTubeDistributions.lean`
    and is equivalent to `(fun k μ => ε * η k μ) ∈ ForwardConeAbs d n` for ε > 0. -/
def InForwardCone (d n : ℕ) [NeZero d] (η : Fin n → Fin (d + 1) → ℝ) : Prop :=
  ∀ k : Fin n,
    let prev : Fin (d + 1) → ℝ := if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩
    InOpenForwardCone d (fun μ => η k μ - prev μ)

/-- The forward tube T_n in n copies of complexified spacetime.

    T_n = {(z₁,...,zₙ) ∈ ℂ^{n(d+1)} : Im(z₁) ∈ V₊, Im(z₂-z₁) ∈ V₊, ..., Im(zₙ-zₙ₋₁) ∈ V₊}

    where V₊ is the open forward light cone {η : η₀ > 0, η² < 0}.

    This is the domain to which Wightman functions analytically continue.

    We define the successive difference of imaginary parts η_k and require each
    to lie in V₊. -/
def ForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- Cumulative sum of approach directions, a utility for convention conversion.

    Given directions η_k for k = 0,...,n-1, tubeCumSum(η, k) = ∑_{j≤k} η_j.
    If each η_k ∈ V⁺, then z_k = x_k + iε · tubeCumSum(η, k) has successive
    imaginary differences Im(z_k - z_{k-1}) = ε · η_k ∈ V⁺.

    Note: The BV integrands use x_k + iε · η_k directly, with the hypothesis
    `InForwardCone d n η` ensuring successive diffs η_k - η_{k-1} ∈ V⁺. -/
def tubeCumSum {d : ℕ} {n : ℕ} (η : Fin n → Fin (d + 1) → ℝ)
    (k : Fin n) (μ : Fin (d + 1)) : ℝ :=
  (Finset.Iic k).sum (fun j => η j μ)

@[simp] lemma tubeCumSum_zero {d : ℕ} {n : ℕ} (η : Fin (n + 1) → Fin (d + 1) → ℝ)
    (μ : Fin (d + 1)) : tubeCumSum η 0 μ = η 0 μ := by
  simp only [tubeCumSum]
  have : Finset.Iic (0 : Fin (n + 1)) = {0} := by
    ext x; simp [Fin.le_def]
  rw [this, Finset.sum_singleton]

lemma tubeCumSum_sub {d : ℕ} {n : ℕ} (η : Fin n → Fin (d + 1) → ℝ)
    (k : Fin n) (hk : 0 < k.val) (μ : Fin (d + 1)) :
    tubeCumSum η k μ - tubeCumSum η ⟨k.val - 1, by omega⟩ μ = η k μ := by
  simp only [tubeCumSum]
  have hsub : Finset.Iic (⟨k.val - 1, by omega⟩ : Fin n) ⊆ Finset.Iic k :=
    Finset.Iic_subset_Iic.mpr (by simp [Fin.le_def])
  have hsdiff : Finset.Iic k \ Finset.Iic (⟨k.val - 1, by omega⟩ : Fin n) = {k} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_singleton,
      Fin.le_def, Fin.ext_iff]
    omega
  have := Finset.sum_sdiff hsub (f := fun j => η j μ)
  rw [hsdiff, Finset.sum_singleton] at this
  linarith

/-- The extended forward tube T_n^{ext} obtained by Lorentz covariance.

    T_n^{ext} = ⋃_{Λ ∈ L₊↑} Λ T_n

    where L₊↑ is the proper orthochronous Lorentz group.
    The edge-of-the-wedge theorem shows W_n extends to T_n^{ext}. -/
def ExtendedForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ Λ : LorentzGroup.Restricted (d := d),
    { z | ∃ w ∈ ForwardTube d n, z = fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * w k ν }

/-- Convert a Euclidean spacetime point to a complex point via Wick rotation:
    (τ, x⃗) ↦ (iτ, x⃗).

    This is the fundamental map relating Euclidean and Minkowski spacetime. -/
def wickRotatePoint {d : ℕ} (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * (x 0 : ℂ) else (x μ : ℂ)

/-- The Wightman functions have analytic continuation to the forward tube.

    The n-point Wightman function W_n(x₁,...,xₙ), initially defined as a
    distribution on real spacetime points, extends to a holomorphic function
    on the forward tube T_n.

    By Lorentz covariance, it further extends to the extended forward tube T_n^{ext}.
    The edge-of-the-wedge theorem (Bargmann-Hall-Wightman) shows this extension
    is single-valued.

    We define `analyticContinuation` on the full ambient space ℂ^{n(d+1)} and
    constrain holomorphicity to the forward tube via `DifferentiableOn`.

    The current `SpectralCondition` surface only records the weak Hamiltonian/mass-shell
    inequalities, not the full Fourier-Laplace boundary-value theorem or the boundary
    regularity input needed for pointwise limits. Therefore both the distributional
    boundary-value package and the pointwise boundary-limit package are included
    explicitly here rather than derived from `qft.spectrum_condition` inside this file. -/
structure WightmanAnalyticity (qft : WightmanQFT d) where
  /-- The analytic continuation of the n-point function, defined on all of ℂ^{n(d+1)}.
      Only meaningful on the forward tube; values outside are auxiliary. -/
  analyticContinuation : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ
  /-- The continuation is holomorphic on the forward tube -/
  isHolomorphic : ∀ n : ℕ, DifferentiableOn ℂ (analyticContinuation n) (ForwardTube d n)
  /-- The analytic continuation approaches the chosen tempered Wightman distribution
      in the distributional sense along forward-cone directions. -/
  boundaryValue : ∀ n : ℕ,
    ∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          analyticContinuation n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((chosenWightmanDistribution (d := d) qft n) f))
  /-- Pointwise boundary limits along forward-cone directions. This is the additional
      regularity input needed to talk about honest pointwise boundary values rather than
      only distributional convergence. -/
  boundaryPointwise : ∀ (n : ℕ) (x : Fin n → Fin (d + 1) → ℝ)
      (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      ∃ (limit : ℂ), Filter.Tendsto
        (fun ε : ℝ => analyticContinuation n
          (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds limit)

private theorem wightman_analyticity_distributional_bv (qft : WightmanQFT d)
    (ha : WightmanAnalyticity d qft) (n : ℕ) :
    ∃ (T : SchwartzNPointSpace d n → ℂ),
    ∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          ha.analyticContinuation n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
  refine ⟨chosenWightmanDistribution (d := d) qft n, ?_⟩
  intro f η hη
  simpa using ha.boundaryValue n f η hη

/-- Boundary values of the analytic continuation recover Wightman functions.

    For any approach direction η ∈ ForwardConeAbs (successive diffs in V₊) and any
    real configuration x, the limit from within the forward tube exists:
      lim_{ε→0⁺} W_analytic(x₁ + iε·η₁, ..., xₙ + iε·ηₙ) exists

    The pointwise boundary-limit input is carried explicitly by
    `WightmanAnalyticity.boundaryPointwise`.

    Ref: Streater-Wightman, "PCT, Spin and Statistics", Theorem 3-7 -/
theorem wightman_analyticity_boundary (qft : WightmanQFT d)
    (ha : WightmanAnalyticity d qft) (n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    -- The limit of the analytic continuation from within the forward tube exists
    ∃ (limit : ℂ), Filter.Tendsto
      (fun ε : ℝ => ha.analyticContinuation n
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds limit) := by
  exact ha.boundaryPointwise n x η hη

end
