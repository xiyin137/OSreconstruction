/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import GeneralResults.NuclearExtensionComplex
import GeneralResults.SeparatelyContMultilinear
import OSReconstruction.SCV.SchwartzComplete
import Init
import OSReconstruction.Wightman.Spacetime.Metric
import OSReconstruction.Wightman.Groups.Lorentz
import OSReconstruction.Wightman.Groups.Poincare
import OSReconstruction.Wightman.OperatorDistribution
import OSReconstruction.Wightman.SchwartzTensorProduct











































noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable (d : ℕ) [NeZero d]



/-- The forward light cone in momentum space: p₀ ≥ 0, p² ≤ 0.
    In the mostly positive signature, p² = -p₀² + |p⃗|², so p² ≤ 0 means p₀ ≥ |p⃗|.
    This is the region where timelike and lightlike momenta with positive energy lie. -/
def ForwardMomentumCone : Set (MinkowskiSpace d) :=
  MinkowskiSpace.ClosedForwardLightCone d

/-- **Quadratic-form spectral condition surface** (Axiom II proxy).

    This exported structure records the spectral-condition data currently used on
    the Hilbert-space side: strong continuity of translations, nonnegative energy,
    and the quadratic-form inequality `P₀² ≥ Σᵢ Pᵢ²` on the relevant Stone-generator
    domains.

    It should be viewed as a proved proxy for the full Streater-Wightman joint-spectrum
    statement, not as the full support theorem itself. -/
structure SpectralConditionQFT (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  strongly_continuous : PoincareRepresentation.translationStronglyContinuous π
  energy_nonneg :
    ∀ (ψ : H) (hψ : ψ ∈ (π.momentumOp 0 (strongly_continuous 0)).domain),
    (⟪ψ, (π.momentumOp 0 (strongly_continuous 0)) ⟨ψ, hψ⟩⟫_ℂ).re ≥ 0
  mass_shell :
    ∀ (ψ : H)
      (hψ₀ : ψ ∈ (π.momentumOp 0 (strongly_continuous 0)).domain)
      (hP₀ψ : (π.momentumOp 0 (strongly_continuous 0)) ⟨ψ, hψ₀⟩ ∈
        (π.momentumOp 0 (strongly_continuous 0)).domain)
      (hψᵢ : ∀ i : Fin d, ψ ∈
        (π.momentumOp (Fin.succ i) (strongly_continuous (Fin.succ i))).domain)
      (hPᵢψ : ∀ i : Fin d,
        (π.momentumOp (Fin.succ i) (strongly_continuous (Fin.succ i))) ⟨ψ, hψᵢ i⟩ ∈
          (π.momentumOp (Fin.succ i) (strongly_continuous (Fin.succ i))).domain),
    (⟪ψ, (π.momentumOp 0 (strongly_continuous 0))
      ⟨(π.momentumOp 0 (strongly_continuous 0)) ⟨ψ, hψ₀⟩, hP₀ψ⟩⟫_ℂ).re ≥
    ∑ i : Fin d,
      (⟪ψ, (π.momentumOp (Fin.succ i) (strongly_continuous (Fin.succ i)))
        ⟨(π.momentumOp (Fin.succ i) (strongly_continuous (Fin.succ i)))
          ⟨ψ, hψᵢ i⟩, hPᵢψ i⟩⟫_ℂ).re



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



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector is invariant under the Poincaré representation -/
def IsPoincareInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ g : PoincareGroup d, π.U g Ω = Ω

/-- A vector is invariant under time translations only -/
def IsTimeTranslationInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ t : ℝ, π.U (PoincareGroup.translation' (fun i => if i = 0 then t else 0)) Ω = Ω

/-- Uniqueness of the vacuum: Ω is the unique (up to phase) Poincaré-invariant vector -/
def VacuumUnique (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  IsPoincareInvariant d π Ω ∧
  ∀ ψ : H, IsPoincareInvariant d π ψ → ∃ c : ℂ, ψ = c • Ω



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
  /-- **Spectral-condition proxy field**: the current exported Hilbert-space
      surface consisting of strong continuity, nonnegative energy, and the
      quadratic-form mass-shell inequality. See `SpectralConditionQFT` for the
      precise scope. -/
  spectrum_condition :
    @SpectralConditionQFT d _ HilbertSpace
      instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep
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

end WightmanQFT



/-- The n-point domain: n copies of (d+1)-dimensional spacetime.
    Points are functions Fin n → Fin (d+1) → ℝ, i.e., n spacetime points. -/
abbrev NPointSpacetime (d n : ℕ) := Fin n → Fin (d + 1) → ℝ

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPointSpace (d n : ℕ) := SchwartzMap (NPointSpacetime d n) ℂ

/-- **Schwartz kernel / nuclear theorem for Schwartz spaces.**

    Let `E = S(R^(d+1))`. Every continuous multilinear functional on `E^n`
    extends uniquely to a continuous linear functional on `S(R^(n(d+1)))`,
    after the standard identification of the completed projective tensor product
    `E ⊗̂π ... ⊗̂π E` with the Schwartz space on the product domain.

    Concretely, the extension agrees with the original multilinear functional on
    pure tensors `f_1 ⊗ ... ⊗ f_n`, encoded here by `SchwartzMap.productTensor`.

    This is derived from the proved complex nuclear-extension theorem in the
    pinned `GaussianField` dependency. The only local bridge identifies its
    pointwise product tensor with `SchwartzMap.productTensor`.

    Ref: Gel'fand-Vilenkin, "Generalized Functions IV", Ch. I, 3;
    Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13;
    Treves, "Topological Vector Spaces", Ch. 51. -/
theorem schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (SchwartzMap.productTensor fs) = Phi fs := by
  rcases GaussianField.schwartz_nuclear_extension d n Phi with
    ⟨W, hW, hW_unique⟩
  have hproduct :
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        GaussianField.complexProductTensor fs =
          SchwartzMap.productTensor fs := by
    intro fs
    ext x
    rw [GaussianField.complexProductTensor_apply,
      SchwartzMap.productTensor_apply]
  refine ⟨W, ?_, ?_⟩
  · intro fs
    rw [← hproduct fs]
    exact hW fs
  · intro W' hW'
    apply hW_unique W'
    intro fs
    rw [hproduct fs]
    exact hW' fs

/-- Banach-Steinhaus / Fréchet-space bridge for finite multilinear maps on Schwartz space.

    This is the standard theorem that separately continuous multilinear maps on products of
    Schwartz spaces are jointly continuous. It is pure functional analysis and carries no QFT
    content; here it is used only to promote a multilinear map to a `ContinuousMultilinearMap`
    so the nuclear extension theorem can be applied. -/
theorem exists_continuousMultilinear_ofSeparatelyContinuous {n : ℕ}
    (Phi : MultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ)
    (hPhi : ∀ (i : Fin n) (fs : Fin n → SchwartzSpacetime d),
      Continuous (fun f => Phi (Function.update fs i f))) :
    ∃ PhiCont : ContinuousMultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs : Fin n → SchwartzSpacetime d, PhiCont fs = Phi fs := by
  letI :
      (uniformity (SchwartzSpacetime d)).IsCountablyGenerated := by
    set_option backward.isDefEq.respectTransparency false in
      exact IsUniformAddGroup.uniformity_countably_generated
  let hcomplete :
      TopologicalSpace.IsCompletelyPseudoMetrizableSpace
        (SchwartzSpacetime d) :=
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
  letI := hcomplete
  letI : BaireSpace (SchwartzSpacetime d) :=
    @BaireSpace.of_completelyPseudoMetrizable
      (SchwartzSpacetime d) inferInstance hcomplete
  exact
    GaussianField.exists_continuousMultilinear_ofSeparatelyContinuous
      Phi hPhi



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

/-- The repo's current forward tube for the public literal `n`-point family.

    `ForwardTube d n` consists of complex configurations `z₀, ..., z_{n-1}` such
    that
    - `Im(z₀) ∈ V₊`, and
    - `Im(z_k - z_{k-1}) ∈ V₊` for `k = 1, ..., n - 1`.

    Thus the formalized domain is an absolute-coordinate tube with one extra
    basepoint condition `Im(z₀) ∈ V₊` in addition to the successive-difference
    conditions. This is slightly stronger than the minimal literal `n`-point
    forward tube often used in the literature, but it is the public analytic
    domain used throughout the current repo formalization.

    The internal Route 1 reduced layer later descends from this absolute tube
    to reduced `(m + 1) -> m` difference-variable data. -/
def ForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- Convert a Euclidean spacetime point to a complex point via Wick rotation:
    (τ, x⃗) ↦ (iτ, x⃗).

    This is the fundamental map relating Euclidean and Minkowski spacetime. -/
def wickRotatePoint {d : ℕ} (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * (x 0 : ℂ) else (x μ : ℂ)

end
