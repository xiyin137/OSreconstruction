/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.Basic
import OSReconstruction.vNA.Unbounded.Graph

/-!
# Unbounded Linear Operators

This file develops the basic theory of unbounded linear operators on Hilbert spaces,
which is essential for Tomita-Takesaki modular theory.

## Main definitions

* `UnboundedOperator` - a linear operator defined on a dense subspace
* `UnboundedOperator.domain` - the domain of an unbounded operator
* `UnboundedOperator.graph` - the graph of an unbounded operator

## Main results

* `UnboundedOperator.closable` - an operator is closable iff its graph closure is a graph
* `UnboundedOperator.closed_iff_graph_closed` - an operator is closed iff its graph is closed

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis"
* Kato, "Perturbation Theory for Linear Operators"
-/

noncomputable section

open scoped InnerProduct ComplexConjugate

-- Disable unused section variable warnings; CompleteSpace is needed for most theorems
-- but not all, and restructuring would be more complex than beneficial
set_option linter.unusedSectionVars false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Unbounded operators -/

/-- An unbounded linear operator on a Hilbert space H.
    It consists of a dense subspace (domain) and a linear map on that subspace. -/
structure UnboundedOperator (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The domain of the operator -/
  domain : Submodule ℂ H
  /-- The operator is a linear map on its domain -/
  toFun : domain → H
  /-- The operator is linear -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- The operator respects scalar multiplication -/
  map_smul' : ∀ (c : ℂ) x, toFun (c • x) = c • toFun x

namespace UnboundedOperator

variable (T : UnboundedOperator H)

instance : CoeFun (UnboundedOperator H) (fun T => T.domain → H) := ⟨UnboundedOperator.toFun⟩

/-- The domain of T is dense in H -/
def IsDenselyDefined : Prop :=
  T.domain.topologicalClosure = ⊤

/-- The graph of an unbounded operator as a subspace of H × H -/
def graph : Set (H × H) :=
  { p | ∃ x : T.domain, (x : H) = p.1 ∧ T x = p.2 }

/-- Two unbounded operators are equal if and only if their graphs are equal -/
theorem eq_of_graph_eq {S T : UnboundedOperator H} (h : S.graph = T.graph) : S = T := by
  -- First establish domain equality
  have hdom : S.domain = T.domain := by
    ext x
    constructor
    · intro hx
      have : (x, S ⟨x, hx⟩) ∈ S.graph := ⟨⟨x, hx⟩, rfl, rfl⟩
      rw [h] at this
      obtain ⟨y, hy1, _⟩ := this
      simp only at hy1
      rw [← hy1]; exact y.2
    · intro hx
      have : (x, T ⟨x, hx⟩) ∈ T.graph := ⟨⟨x, hx⟩, rfl, rfl⟩
      rw [← h] at this
      obtain ⟨y, hy1, _⟩ := this
      simp only at hy1
      rw [← hy1]; exact y.2
  -- Show function equality using graph membership
  have hfun : ∀ (x : S.domain), S x = T ⟨x, hdom ▸ x.2⟩ := by
    intro x
    have hmem : ((x : H), S x) ∈ S.graph := ⟨x, rfl, rfl⟩
    rw [h] at hmem
    obtain ⟨y, hy1, hy2⟩ := hmem
    simp only at hy1 hy2
    have hxy : y = ⟨(x : H), hdom ▸ x.2⟩ := by ext; exact hy1
    rw [hxy] at hy2
    exact hy2.symm
  -- Now construct the equality
  rcases S with ⟨domS, toFunS, map_addS, map_smulS⟩
  rcases T with ⟨domT, toFunT, map_addT, map_smulT⟩
  simp only [mk.injEq]
  simp only at hdom hfun
  refine ⟨hdom, ?_⟩
  subst hdom
  simp only [heq_eq_eq]
  funext x
  exact hfun x

/-- An operator is closed if its graph is closed in H × H -/
def IsClosed : Prop :=
  _root_.IsClosed T.graph

/-- An operator is closable if its graph closure is still the graph of an operator.
    Standard definition: if xₙ → 0 and Txₙ → y, then y = 0.
    Equivalently: (0, y) ∈ closure(graph T) implies y = 0. -/
def IsClosable : Prop :=
  ∀ y : H, (0, y) ∈ closure T.graph → y = 0

/-- Extension of an operator: T ⊆ S if dom(T) ⊆ dom(S) and T = S on dom(T) -/
def IsExtension (S : UnboundedOperator H) : Prop :=
  ∃ incl : T.domain →ₗ[ℂ] S.domain,
    (∀ x : T.domain, (incl x : H) = (x : H)) ∧
    (∀ x : T.domain, S (incl x) = T x)

/-- The graph of T as a submodule of H × H -/
def graphSubmodule : Submodule ℂ (H × H) where
  carrier := T.graph
  add_mem' := fun {p q} hp hq => by
    obtain ⟨x, hx1, hx2⟩ := hp
    obtain ⟨y, hy1, hy2⟩ := hq
    use x + y
    constructor
    · simp [hx1, hy1]
    · simp [hx2, hy2, T.map_add']
  zero_mem' := by
    use ⟨0, T.domain.zero_mem⟩
    constructor
    · rfl
    · -- T 0 = 0 follows from linearity: T 0 = T (0 • x) = 0 • T x = 0
      show T.toFun ⟨0, T.domain.zero_mem⟩ = 0
      have : (⟨0, T.domain.zero_mem⟩ : T.domain) = (0 : ℂ) • ⟨0, T.domain.zero_mem⟩ := by simp
      rw [this, T.map_smul']
      simp
  smul_mem' := fun c p hp => by
    obtain ⟨x, hx1, hx2⟩ := hp
    use c • x
    constructor
    · simp [hx1]
    · simp [hx2, T.map_smul']

/-- The closure of the graph as a submodule -/
def graphClosure : Submodule ℂ (H × H) :=
  T.graphSubmodule.topologicalClosure

/-- The domain of the closure: projection of graph closure onto first component -/
def closureDomain (_h : T.IsClosable) : Set H :=
  { x | ∃ y : H, (x, y) ∈ T.graphClosure }

/-- For a closable operator, the graph closure is functional (single-valued) -/
theorem closure_graph_functional (h : T.IsClosable) (x : H) (y₁ y₂ : H)
    (h1 : (x, y₁) ∈ T.graphClosure) (h2 : (x, y₂) ∈ T.graphClosure) : y₁ = y₂ := by
  -- (x, y₁) - (x, y₂) = (0, y₁ - y₂) ∈ graphClosure (since it's a submodule)
  have hdiff : (x, y₁) - (x, y₂) ∈ T.graphClosure := T.graphClosure.sub_mem h1 h2
  simp only [Prod.mk_sub_mk, sub_self] at hdiff
  -- (0, y₁ - y₂) ∈ graphClosure
  -- graphClosure ⊆ closure graph (as sets)
  -- The topological closure of a submodule as a set equals the closure of its carrier
  have hclosure_eq : (T.graphClosure : Set (H × H)) = closure (T.graphSubmodule : Set (H × H)) :=
    Submodule.topologicalClosure_coe T.graphSubmodule
  -- T.graphSubmodule as a set equals T.graph
  have hgraph_eq : (T.graphSubmodule : Set (H × H)) = T.graph := rfl
  have hdiff' : (0, y₁ - y₂) ∈ closure T.graph := by
    have hmem : (0, y₁ - y₂) ∈ (T.graphClosure : Set (H × H)) := hdiff
    rw [hclosure_eq, hgraph_eq] at hmem
    exact hmem
  -- By closability: (0, y) ∈ closure graph → y = 0
  -- We have (0, y₁ - y₂) ∈ closure graph
  have hzero := h (y₁ - y₂) hdiff'
  -- y₁ - y₂ = 0 implies y₁ = y₂
  exact sub_eq_zero.mp hzero

/-- The closure domain is a submodule -/
def closureDomainSubmodule (h : T.IsClosable) : Submodule ℂ H where
  carrier := T.closureDomain h
  add_mem' := fun {a b} ha hb => by
    obtain ⟨ya, hya⟩ := ha
    obtain ⟨yb, hyb⟩ := hb
    use ya + yb
    have hadd : (a, ya) + (b, yb) = (a + b, ya + yb) := rfl
    rw [← hadd]
    exact T.graphClosure.add_mem hya hyb
  zero_mem' := by
    use 0
    exact T.graphClosure.zero_mem
  smul_mem' := fun c a ha => by
    obtain ⟨y, hy⟩ := ha
    use c • y
    have hsmul : c • (a, y) = (c • a, c • y) := rfl
    rw [← hsmul]
    exact T.graphClosure.smul_mem c hy

/-- The closure of a closable operator -/
def closure' (h : T.IsClosable) : UnboundedOperator H where
  domain := T.closureDomainSubmodule h
  toFun := fun x => Classical.choose (x.2 : ∃ y, ((x : H), y) ∈ T.graphClosure)
  map_add' := fun x y => by
    apply T.closure_graph_functional h
    · -- Show (x + y, closure'(x+y)) ∈ graphClosure
      exact Classical.choose_spec ((x + y).2 : ∃ z, ((x + y : H), z) ∈ T.graphClosure)
    · -- Show (x + y, closure'(x) + closure'(y)) ∈ graphClosure
      have hx := Classical.choose_spec (x.2 : ∃ z, ((x : H), z) ∈ T.graphClosure)
      have hy := Classical.choose_spec (y.2 : ∃ z, ((y : H), z) ∈ T.graphClosure)
      -- Convert ↑(x + y) to ↑x + ↑y
      have hcoe : ((x + y : T.closureDomainSubmodule h) : H) = (x : H) + (y : H) :=
        Submodule.coe_add x y
      rw [hcoe]
      exact T.graphClosure.add_mem hx hy
  map_smul' := fun c x => by
    apply T.closure_graph_functional h
    · exact Classical.choose_spec ((c • x).2 : ∃ z, ((c • x : H), z) ∈ T.graphClosure)
    · have hx := Classical.choose_spec (x.2 : ∃ z, ((x : H), z) ∈ T.graphClosure)
      -- Convert ↑(c • x) to c • ↑x
      have hcoe : ((c • x : T.closureDomainSubmodule h) : H) = c • (x : H) :=
        Submodule.coe_smul c x
      rw [hcoe]
      exact T.graphClosure.smul_mem c hx

/-! ### The adjoint of an unbounded operator -/

/-- The domain of the adjoint T*.
    dom(T*) = {y : H | the map x ↦ ⟨Tx, y⟩ is bounded on dom(T)} -/
def adjointDomain : Set H :=
  { y | ∃ C : ℝ, ∀ x : T.domain, ‖@inner ℂ H _ (T x) y‖ ≤ C * ‖(x : H)‖ }

/-- The adjoint domain as a submodule -/
def adjointDomainSubmodule : Submodule ℂ H where
  carrier := T.adjointDomain
  add_mem' := fun {a b} ha hb => by
    obtain ⟨Ca, hCa⟩ := ha
    obtain ⟨Cb, hCb⟩ := hb
    use Ca + Cb
    intro x
    calc ‖@inner ℂ H _ (T x) (a + b)‖
        = ‖@inner ℂ H _ (T x) a + @inner ℂ H _ (T x) b‖ := by rw [inner_add_right]
      _ ≤ ‖@inner ℂ H _ (T x) a‖ + ‖@inner ℂ H _ (T x) b‖ := norm_add_le _ _
      _ ≤ Ca * ‖(x : H)‖ + Cb * ‖(x : H)‖ := add_le_add (hCa x) (hCb x)
      _ = (Ca + Cb) * ‖(x : H)‖ := by ring
  zero_mem' := by
    use 0
    intro x
    simp [inner_zero_right]
  smul_mem' := fun c a ha => by
    obtain ⟨Ca, hCa⟩ := ha
    use ‖c‖ * Ca
    intro x
    calc ‖@inner ℂ H _ (T x) (c • a)‖
        = ‖c‖ * ‖@inner ℂ H _ (T x) a‖ := by rw [inner_smul_right]; simp
      _ ≤ ‖c‖ * (Ca * ‖(x : H)‖) := by apply mul_le_mul_of_nonneg_left (hCa x) (norm_nonneg _)
      _ = (‖c‖ * Ca) * ‖(x : H)‖ := by ring

/-- The adjoint domain forms a subspace -/
theorem adjointDomain_submodule : ∃ S : Submodule ℂ H, (S : Set H) = T.adjointDomain := by
  exact ⟨T.adjointDomainSubmodule, rfl⟩

/-- For densely defined T, if y ∈ dom(T*), there exists z such that
    ⟨Tx, y⟩ = ⟨x, z⟩ for all x ∈ dom(T). -/
theorem adjoint_exists' (hT : T.IsDenselyDefined) (y : H) (hy : y ∈ T.adjointDomain) :
    ∃ z : H, ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z := by
  -- y ∈ adjointDomain means ∃ C, ∀ x, ‖⟨Tx, y⟩‖ ≤ C * ‖x‖
  obtain ⟨C, hC⟩ := hy

  -- Define the linear functional φ : T.domain → ℂ by φ(x) = ⟨Tx, y⟩
  -- Note: we want ⟨Tx, y⟩ = ⟨x, z⟩, so φ(x) = ⟨Tx, y⟩ = conj⟨y, Tx⟩
  -- The inner product is antilinear in first arg, linear in second
  -- So φ is antilinear in x via the first component

  -- Actually, let's think about this more carefully.
  -- ⟨Tx, y⟩ as a function of x is antilinear (since inner is antilinear in first arg)
  -- We need z such that ⟨Tx, y⟩ = ⟨x, z⟩
  -- Since ⟨x, z⟩ is antilinear in x and linear in z, this works.

  -- Use the dual space isomorphism: InnerProductSpace.toDual
  -- toDual : H ≃ₗᵢ⋆[ℂ] StrongDual ℂ H maps z to the functional (x ↦ ⟨z, x⟩)
  -- We have a functional x ↦ ⟨Tx, y⟩ = conj⟨y, Tx⟩

  -- The functional x ↦ ⟨y, Tx⟩ is a bounded linear functional on T.domain
  -- (linear because inner is linear in second argument)
  -- Extend it and use Riesz.

  -- Define the bounded linear functional on T.domain
  let φ : T.domain →ₗ[ℂ] ℂ := {
    toFun := fun x => @inner ℂ H _ y (T x)
    map_add' := fun x₁ x₂ => by simp [T.map_add', inner_add_right]
    map_smul' := fun c x => by simp [T.map_smul', inner_smul_right]
  }

  -- φ is bounded: ‖φ(x)‖ ≤ C * ‖x‖
  have hφ_bound : ∀ x : T.domain, ‖φ x‖ ≤ C * ‖(x : H)‖ := by
    intro x
    -- φ x = ⟨y, Tx⟩
    -- ‖⟨y, Tx⟩‖ = ‖⟨Tx, y⟩‖ by norm_inner_symm
    have hnorm : ‖φ x‖ = ‖@inner ℂ H _ (T x) y‖ := by
      show ‖@inner ℂ H _ y (T x)‖ = ‖@inner ℂ H _ (T x) y‖
      exact norm_inner_symm y (T x)
    rw [hnorm]
    exact hC x

  -- The domain is dense
  have hdense : Dense (T.domain : Set H) := by
    have h : T.domain.topologicalClosure = ⊤ := hT
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact h

  -- Extend φ to a bounded linear functional on H using density
  -- First, make φ into a continuous linear map on T.domain
  have hφ_cont : ∃ φ' : T.domain →L[ℂ] ℂ, ∀ x, φ' x = φ x := by
    -- φ is bounded, hence continuous
    use {
      toLinearMap := φ
      cont := by
        apply AddMonoidHomClass.continuous_of_bound φ (max C 0)
        intro x
        calc ‖φ x‖ ≤ C * ‖(x : H)‖ := hφ_bound x
          _ ≤ max C 0 * ‖(x : H)‖ := by
            apply mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)
          _ = max C 0 * ‖x‖ := rfl
    }
    intro x
    rfl

  obtain ⟨φ', hφ'⟩ := hφ_cont

  -- Extend φ' to all of H
  let φ_ext := φ'.extend (T.domain.subtypeL)

  -- By Riesz representation, there exists w such that φ_ext = ⟨w, ·⟩
  -- Note: toDual maps z to (x ↦ ⟨z, x⟩), so toDual.symm(φ_ext) gives us w
  let w := (InnerProductSpace.toDual ℂ H).symm φ_ext

  -- We have: for all u ∈ H, φ_ext u = ⟨w, u⟩
  -- toDual_symm_apply : ⟪(toDual 𝕜 E).symm y, x⟫ = y x
  have hw : ∀ u : H, φ_ext u = @inner ℂ H _ w u := by
    intro u
    -- w = (toDual ℂ H).symm φ_ext
    -- By toDual_symm_apply: ⟨w, u⟩ = φ_ext u
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := H) (x := u) (y := φ_ext)
    -- h : inner w u = φ_ext u
    exact h.symm

  -- For x ∈ T.domain, φ_ext (x : H) = φ x = ⟨y, Tx⟩
  have hext : ∀ x : T.domain, φ_ext (x : H) = @inner ℂ H _ y (T x) := by
    intro x
    -- φ_ext = φ'.extend (T.domain.subtypeL)
    -- For x in T.domain, the extension agrees with the original
    have hunif : IsUniformInducing (T.domain.subtypeL : T.domain → H) :=
      isUniformEmbedding_subtype_val.isUniformInducing
    have h := ContinuousLinearMap.extend_eq φ' hdense.denseRange_val hunif x
    simp only [Submodule.subtypeL_apply] at h
    rw [h, hφ']
    rfl

  -- Now: ⟨w, x⟩ = ⟨y, Tx⟩, so ⟨Tx, y⟩ = conj⟨y, Tx⟩ = conj⟨w, x⟩ = ⟨x, w⟩
  use w
  intro x
  have h1 := hext x
  have h2 := hw (x : H)
  -- h1: φ_ext (x : H) = ⟨y, Tx⟩
  -- h2: φ_ext (x : H) = ⟨w, x⟩
  -- So ⟨y, Tx⟩ = ⟨w, x⟩
  -- We need ⟨Tx, y⟩ = ⟨x, w⟩
  -- inner_conj_symm a b : conj(inner b a) = inner a b
  -- So: inner (Tx) y = conj(inner y (Tx)) = conj(inner w x) = inner x w
  calc @inner ℂ H _ (T x) y
      = starRingEnd ℂ (@inner ℂ H _ y (T x)) := (inner_conj_symm (T x) y).symm
    _ = starRingEnd ℂ (φ_ext (x : H)) := by rw [← h1]
    _ = starRingEnd ℂ (@inner ℂ H _ w (x : H)) := by rw [h2]
    _ = @inner ℂ H _ (x : H) w := inner_conj_symm (x : H) w

/-- The representing vector z is unique -/
theorem adjoint_unique (hT : T.IsDenselyDefined) (y : H) (z₁ z₂ : H)
    (h₁ : ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z₁)
    (h₂ : ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z₂) :
    z₁ = z₂ := by
  -- If ⟨x, z₁⟩ = ⟨x, z₂⟩ for all x in dense subspace, then z₁ = z₂
  have heq : ∀ x : T.domain, @inner ℂ H _ (x : H) z₁ = @inner ℂ H _ (x : H) z₂ := by
    intro x; rw [← h₁ x, h₂ x]
  -- This means ⟨x, z₁ - z₂⟩ = 0 for all x in dense domain
  have hdiff : ∀ x : T.domain, @inner ℂ H _ (x : H) (z₁ - z₂) = 0 := by
    intro x
    rw [inner_sub_right, heq x, sub_self]
  -- Since domain is dense, z₁ - z₂ = 0
  -- Use that inner product with all vectors in dense subspace being 0 implies the vector is 0
  -- The key is: if ⟨x, v⟩ = 0 for all x in T.domain, and T.domain is dense,
  -- then by continuity of inner product, ⟨w, v⟩ = 0 for all w, hence v = 0.
  --
  -- We prove this by showing z₁ - z₂ is orthogonal to all of H.
  -- Since T.domain is dense, its closure is H, so the orthogonal complement is {0}.
  set v := z₁ - z₂ with hv_def
  -- v is orthogonal to T.domain
  have hv_orth : ∀ x ∈ T.domain, @inner ℂ H _ x v = 0 := by
    intro x hx
    exact hdiff ⟨x, hx⟩
  -- The inner product ⟨·, v⟩ : H → ℂ is continuous and vanishes on T.domain
  -- Since T.domain is dense (its closure is H), and the inner product is continuous,
  -- we have ⟨w, v⟩ = 0 for all w ∈ H.
  -- In particular, ⟨v, v⟩ = 0, so v = 0.
  have hv_eq_zero : v = 0 := by
    -- The map w ↦ ⟨w, v⟩ is continuous
    have hcont : Continuous (fun w : H => @inner ℂ H _ w v) :=
      continuous_inner.comp (continuous_id.prodMk continuous_const)
    -- It vanishes on the dense set T.domain
    have hvanish : ∀ w ∈ T.domain, @inner ℂ H _ w v = 0 := hv_orth
    -- Therefore it vanishes on the closure, which is all of H
    have hvanish_all : ∀ w : H, @inner ℂ H _ w v = 0 := by
      intro w
      -- w is in the closure of T.domain since T.domain is dense
      have hw_closure : w ∈ T.domain.topologicalClosure := by
        rw [hT]; trivial
      -- By continuity, the inner product is 0
      -- The set {x | ⟨x, v⟩ = 0} is closed as preimage of {0} under continuous map
      have hclosed : _root_.IsClosed {x : H | @inner ℂ H _ x v = 0} :=
        isClosed_eq hcont continuous_const
      exact hclosed.closure_subset_iff.mpr (fun x hx => hvanish x hx) hw_closure
    -- In particular, ⟨v, v⟩ = 0
    have hself := hvanish_all v
    exact inner_self_eq_zero.mp hself
  -- v = z₁ - z₂ = 0 implies z₁ = z₂
  rw [hv_def] at hv_eq_zero
  exact sub_eq_zero.mp hv_eq_zero

/-- The choice of T*y for y ∈ dom(T*) -/
def adjointApply (hT : T.IsDenselyDefined) (y : T.adjointDomainSubmodule) : H :=
  Classical.choose (T.adjoint_exists' hT y.1 y.2)

/-- The defining property of adjointApply -/
theorem adjointApply_spec (hT : T.IsDenselyDefined) (y : T.adjointDomainSubmodule) :
    ∀ x : T.domain, @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (x : H) (T.adjointApply hT y) :=
  Classical.choose_spec (T.adjoint_exists' hT y.1 y.2)

/-- The adjoint of a densely defined operator -/
def adjoint (hT : T.IsDenselyDefined) : UnboundedOperator H where
  domain := T.adjointDomainSubmodule
  toFun := T.adjointApply hT
  map_add' := fun x y => by
    -- T*(x+y) = T*x + T*y follows from uniqueness of the representing vector
    apply T.adjoint_unique hT ((x : H) + (y : H))
    · exact T.adjointApply_spec hT (x + y)
    · intro z
      calc @inner ℂ H _ (T z) ((x : H) + (y : H))
          = @inner ℂ H _ (T z) (x : H) + @inner ℂ H _ (T z) (y : H) := inner_add_right _ _ _
        _ = @inner ℂ H _ (z : H) (T.adjointApply hT x) +
            @inner ℂ H _ (z : H) (T.adjointApply hT y) := by
            rw [T.adjointApply_spec hT x z, T.adjointApply_spec hT y z]
        _ = @inner ℂ H _ (z : H) (T.adjointApply hT x + T.adjointApply hT y) := by
            rw [inner_add_right]
  map_smul' := fun c x => by
    apply T.adjoint_unique hT (c • (x : H))
    · exact T.adjointApply_spec hT (c • x)
    · intro z
      calc @inner ℂ H _ (T z) (c • (x : H))
          = c * @inner ℂ H _ (T z) (x : H) := inner_smul_right _ _ _
        _ = c * @inner ℂ H _ (z : H) (T.adjointApply hT x) := by
            rw [T.adjointApply_spec hT x z]
        _ = @inner ℂ H _ (z : H) (c • T.adjointApply hT x) := by
            rw [inner_smul_right]

/-- T* is always closed -/
theorem adjoint_closed (hT : T.IsDenselyDefined) : (T.adjoint hT).IsClosed := by
  -- The graph of T* is {(y, z) | ∀ x ∈ dom(T), ⟨Tx, y⟩ = ⟨x, z⟩}
  -- This is closed because it's an intersection of closed sets (preimages of 0)
  unfold IsClosed

  -- Alternative characterization: graph(T*) = ⋂_{x ∈ dom(T)} {(y,z) | ⟨Tx, y⟩ = ⟨x, z⟩}
  have hchar : (T.adjoint hT).graph =
      ⋂ (x : T.domain), {p : H × H | @inner ℂ H _ (T x) p.1 = @inner ℂ H _ (x : H) p.2} := by
    ext ⟨y, z⟩
    simp only [graph, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro ⟨w, hw1, hw2⟩ x
      -- w : (T.adjoint hT).domain = T.adjointDomainSubmodule
      -- hw1 : (w : H) = y
      -- hw2 : (T.adjoint hT) w = z
      -- We need: ⟨Tx, y⟩ = ⟨x, z⟩
      have hadj := T.adjointApply_spec hT w x
      -- hadj : ⟨Tx, w⟩ = ⟨x, T.adjointApply hT w⟩ = ⟨x, (T.adjoint hT) w⟩
      rw [← hw1, ← hw2]
      exact hadj
    · intro h
      -- h : ∀ x, ⟨Tx, y⟩ = ⟨x, z⟩
      -- Need to show (y, z) ∈ graph(T*)
      -- First show y ∈ adjointDomain (the map x ↦ ⟨Tx, y⟩ is bounded)
      have hy_mem : y ∈ T.adjointDomain := by
        -- ⟨Tx, y⟩ = ⟨x, z⟩, so |⟨Tx, y⟩| = |⟨x, z⟩| ≤ ‖z‖ · ‖x‖
        use ‖z‖
        intro x
        rw [h x]
        calc ‖@inner ℂ H _ (x : H) z‖
            ≤ ‖(x : H)‖ * ‖z‖ := norm_inner_le_norm (x : H) z
          _ = ‖z‖ * ‖(x : H)‖ := mul_comm _ _
      -- y is in the adjoint domain
      let y' : T.adjointDomainSubmodule := ⟨y, hy_mem⟩
      use y'
      constructor
      · rfl
      · -- Need: (T.adjoint hT) y' = z
        -- (T.adjoint hT) y' = T.adjointApply hT y' is the unique z' such that
        -- ∀ x, ⟨Tx, y⟩ = ⟨x, z'⟩
        -- We have z satisfies this, so by uniqueness, z' = z
        apply T.adjoint_unique hT y
        · exact T.adjointApply_spec hT y'
        · intro x
          exact h x

  rw [hchar]
  -- Intersection of closed sets is closed
  apply isClosed_iInter
  intro x
  -- {(y, z) | ⟨Tx, y⟩ = ⟨x, z⟩} is closed
  -- This is the preimage of {0} under the continuous map (y, z) ↦ ⟨Tx, y⟩ - ⟨x, z⟩
  have hcont : Continuous (fun p : H × H => @inner ℂ H _ (T x) p.1 - @inner ℂ H _ (x : H) p.2) := by
    apply Continuous.sub
    · exact continuous_inner.comp (continuous_const.prodMk continuous_fst)
    · exact continuous_inner.comp (continuous_const.prodMk continuous_snd)
  have heq : {p : H × H | @inner ℂ H _ (T x) p.1 = @inner ℂ H _ (x : H) p.2} =
      (fun p => @inner ℂ H _ (T x) p.1 - @inner ℂ H _ (x : H) p.2) ⁻¹' {0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_zero]
  rw [heq]
  exact isClosed_singleton.preimage hcont

/-- T is closable iff T* is densely defined -/
theorem closable_iff_adjoint_dense (hT : T.IsDenselyDefined) :
    T.IsClosable ↔ (T.adjoint hT).IsDenselyDefined := by
  -- This is a fundamental theorem in unbounded operator theory (von Neumann)
  -- (→) T closable → T* densely defined
  -- (←) T* densely defined → T closable
  constructor
  · -- T closable → T* densely defined
    intro hclosable

    rw [IsDenselyDefined, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    -- hy : y ∈ (T.adjoint hT).domainᗮ, i.e., ⟨z, y⟩ = 0 for all z ∈ dom(T*)
    -- Need to show y = 0

    -- Key: show (0, y) ∈ closure(graph T), then use closability

    have h_in_closure : (0, y) ∈ closure T.graph := by
      -- Use the product Hilbert space WithLp 2 (H × H)
      -- graph(T)^⊥ = {(a, b) | ∀ x ∈ dom(T), ⟨x, a⟩ + ⟨Tx, b⟩ = 0}
      --            = {(-T*z, z) | z ∈ dom(T*)}
      -- (0, y) ⊥ graph(T)^⊥ since y ⊥ dom(T*)
      -- Hence (0, y) ∈ graph(T)^⊥⊥ = closure(graph(T))

      -- Use VonNeumann.graphLp and related infrastructure from Graph.lean
      let f : T.domain →ₗ[ℂ] H := {
        toFun := T.toFun
        map_add' := T.map_add'
        map_smul' := T.map_smul'
      }

      -- The VonNeumann.adjointDomain and T.adjointDomain are essentially the same
      -- VonNeumann.adjointDomain: { y | ∃ C, ∀ x, ‖⟨f x, y⟩‖ ≤ C * ‖x‖ }
      -- T.adjointDomain:          { y | ∃ C, ∀ x, ‖⟨T x, y⟩‖ ≤ C * ‖x‖ }
      have hadj_eq : VonNeumann.adjointDomain T.domain f = T.adjointDomain := rfl

      -- T.adjointDomain = (T.adjoint hT).domain as sets
      have hdomain_eq : T.adjointDomain = ((T.adjoint hT).domain : Set H) := rfl

      -- Convert hy : y ∈ (T.adjoint hT).domainᗮ to the form expected by VonNeumann
      -- hy means ∀ z ∈ dom(T*), ⟨z, y⟩ = 0
      -- Since Submodule.mem_orthogonal is Iff.rfl, hy is definitionally ∀ z ∈ K, ⟪z, y⟫ = 0
      have hy' : ∀ z ∈ VonNeumann.adjointDomain T.domain f, @inner ℂ H _ z y = 0 := by
        intro z hz
        rw [hadj_eq, hdomain_eq] at hz
        exact hy z hz

      -- Apply VonNeumann.mem_closure_graph_set_of_orthogonal_adjDom
      exact VonNeumann.mem_closure_graph_set_of_orthogonal_adjDom T.domain f y hy'

    -- Now use closability
    exact hclosable y h_in_closure
  · -- T* densely defined → T closable
    intro hdense y hy
    -- hy : (0, y) ∈ closure T.graph
    -- We show y ⊥ dom(T*), hence y = 0 by density of dom(T*)

    -- For any w ∈ dom(T*), we have ⟨w, y⟩ = 0
    have hy_orth : ∀ w : (T.adjoint hT).domain, @inner ℂ H _ (w : H) y = 0 := by
      intro w
      -- (0, y) ∈ closure(graph T) means there's a sequence (xₙ, Txₙ) → (0, y)
      rw [mem_closure_iff_seq_limit] at hy
      obtain ⟨seq, hseq_mem, hseq_lim⟩ := hy

      -- Each seq n is in graph T
      have hseq_graph : ∀ n, ∃ xn : T.domain, (xn : H) = (seq n).1 ∧ T xn = (seq n).2 :=
        fun n => hseq_mem n

      choose xseq hxseq using hseq_graph

      -- Convergence of first and second components
      have hconv : Filter.Tendsto seq Filter.atTop (nhds (0, y)) := hseq_lim

      have hx_lim : Filter.Tendsto (fun n => (xseq n : H)) Filter.atTop (nhds 0) := by
        have h : Filter.Tendsto (fun n => (seq n).1) Filter.atTop (nhds 0) :=
          (continuous_fst.tendsto _).comp hconv
        convert h using 1
        ext n; exact (hxseq n).1

      have hTx_lim : Filter.Tendsto (fun n => T (xseq n)) Filter.atTop (nhds y) := by
        have h : Filter.Tendsto (fun n => (seq n).2) Filter.atTop (nhds y) :=
          (continuous_snd.tendsto _).comp hconv
        convert h using 1
        ext n; exact (hxseq n).2

      -- For each n: ⟨w, T xₙ⟩ = ⟨T*w, xₙ⟩ (adjoint property)
      have hadj_eq : ∀ n, @inner ℂ H _ (w : H) (T (xseq n)) =
          @inner ℂ H _ ((T.adjoint hT) w) (xseq n : H) := by
        intro n
        have h := T.adjointApply_spec hT w (xseq n)
        calc @inner ℂ H _ (w : H) (T (xseq n))
            = starRingEnd ℂ (@inner ℂ H _ (T (xseq n)) (w : H)) := (inner_conj_symm _ _).symm
          _ = starRingEnd ℂ (@inner ℂ H _ (xseq n : H) (T.adjointApply hT w)) := by rw [h]
          _ = @inner ℂ H _ (T.adjointApply hT w) (xseq n : H) := inner_conj_symm _ _

      -- Taking limits
      have hlim1 : Filter.Tendsto (fun n => @inner ℂ H _ (w : H) (T (xseq n)))
          Filter.atTop (nhds (@inner ℂ H _ (w : H) y)) :=
        Filter.Tendsto.inner tendsto_const_nhds hTx_lim

      have hlim2 : Filter.Tendsto (fun n => @inner ℂ H _ (T.adjointApply hT w) (xseq n : H))
          Filter.atTop (nhds (@inner ℂ H _ (T.adjointApply hT w) 0)) :=
        Filter.Tendsto.inner tendsto_const_nhds hx_lim

      -- The two sequences are equal
      have heq_seq : (fun n => @inner ℂ H _ (w : H) (T (xseq n))) =
          (fun n => @inner ℂ H _ (T.adjointApply hT w) (xseq n : H)) := by
        ext n; exact hadj_eq n

      -- So the limits are equal
      have heq_lim : @inner ℂ H _ (w : H) y = @inner ℂ H _ (T.adjointApply hT w) 0 := by
        have huniq := tendsto_nhds_unique hlim1 (heq_seq ▸ hlim2)
        exact huniq

      rw [heq_lim]
      simp only [inner_zero_right]

    -- y ⊥ dom(T*) and dom(T*) is dense, so y = 0
    have hclosed : _root_.IsClosed {z : H | @inner ℂ H _ z y = 0} :=
      isClosed_eq (continuous_inner.comp (continuous_id.prodMk continuous_const)) continuous_const

    have hdense' : Dense ((T.adjoint hT).domain : Set H) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top]
      exact hdense

    have hsubset : ((T.adjoint hT).domain : Set H) ⊆ {z : H | @inner ℂ H _ z y = 0} :=
      fun z hz => hy_orth ⟨z, hz⟩

    have hclosure : closure ((T.adjoint hT).domain : Set H) ⊆ {z : H | @inner ℂ H _ z y = 0} :=
      hclosed.closure_subset_iff.mpr hsubset

    have hall : ∀ z : H, @inner ℂ H _ z y = 0 := by
      intro z
      exact hclosure (hdense'.closure_eq ▸ trivial)

    exact inner_self_eq_zero.mp (hall y)

/-- For closed densely defined T, T** = T -/
theorem double_adjoint (hT : T.IsDenselyDefined) (hcl : T.IsClosed)
    (hT' : (T.adjoint hT).IsDenselyDefined) :
    (T.adjoint hT).adjoint hT' = T := by
  -- The proof uses graph characterization:
  -- graph(T) is closed, and graph(T**) = graph(T)^⊥⊥ = graph(T) (since closed)

  -- We show graph equality implies operator equality
  have hgraph_eq : ((T.adjoint hT).adjoint hT').graph = T.graph := by
    -- T** has graph = {(x, z) | ∀ y ∈ dom(T*), ⟨T*y, x⟩ = ⟨y, z⟩}
    -- This equals graph(T)^⊥⊥ where ⊥ is w.r.t. the "flip" inner product
    -- Since graph(T) is closed, graph(T)^⊥⊥ = graph(T)

    ext ⟨x, z⟩
    constructor
    · -- (x, z) ∈ graph(T**) → (x, z) ∈ graph(T)
      intro ⟨w, hw1, hw2⟩
      -- w : dom(T**), (w : H) = x, T** w = z
      simp only at hw1 hw2

      -- The defining property of T**: for all y ∈ dom(T*), ⟨T*y, x⟩ = ⟨y, z⟩
      have hadj_prop : ∀ y : (T.adjoint hT).domain,
          @inner ℂ H _ ((T.adjoint hT) y) x = @inner ℂ H _ (y : H) z := by
        intro y
        rw [← hw1, ← hw2]
        exact (T.adjoint hT).adjointApply_spec hT' w y

      -- Use von Neumann's graph orthogonal theorem
      -- The condition hadj_prop says (x, z) ⊥ graph(T)^⊥ in the product Hilbert space
      -- So (x, z) ∈ graph(T)^⊥⊥ = closure(graph(T)) = graph(T) (since T is closed)

      -- Set up the linear map for VonNeumann infrastructure
      let f : T.domain →ₗ[ℂ] H := {
        toFun := T.toFun
        map_add' := T.map_add'
        map_smul' := T.map_smul'
      }
      let graphLp : Submodule ℂ (WithLp 2 (H × H)) := VonNeumann.graphLp T.domain f

      -- Show (x, z) ∈ graphLp^⊥⊥ by showing it's orthogonal to graphLp^⊥
      have h_in_perp_perp : WithLp.toLp 2 (x, z) ∈ graphLpᗮᗮ := by
        rw [Submodule.mem_orthogonal]
        intro q hq
        -- q ∈ graphLp^⊥ means ∀ u ∈ dom(T), ⟨u, q.1⟩ + ⟨Tu, q.2⟩ = 0
        -- This implies q.2 ∈ dom(T*) and q.1 = -T* q.2
        have hq_char := VonNeumann.mem_graphLp_perp_iff T.domain f q |>.mp hq
        -- hq_char : ∀ u : dom(T), ⟨u, q.1⟩ + ⟨fu, q.2⟩ = 0
        have hq2_adj := VonNeumann.perp_snd_mem_adjDom T.domain f q hq
        -- hq2_adj : q.2 ∈ VonNeumann.adjointDomain = T.adjointDomain

        -- From hq_char: ⟨fu, q.2⟩ = -⟨u, q.1⟩ for all u ∈ dom(T)
        -- This means q.2 ∈ dom(T*) with T* q.2 = -q.1 (by density and Riesz)
        -- Note: T.adjointDomain = (T.adjoint hT).domain
        have hq2_mem : q.snd ∈ (T.adjoint hT).domain := hq2_adj

        -- Get the adjoint value: T* q.2
        let y : (T.adjoint hT).domain := ⟨q.snd, hq2_mem⟩

        -- Compute ⟨(x, z), q⟩ = ⟨x, q.1⟩ + ⟨z, q.2⟩
        -- We show this is 0 using hadj_prop and the orthogonality characterization

        -- From hq_char: for all u ∈ dom(T), ⟨u, q.fst⟩ + ⟨Tu, q.snd⟩ = 0
        -- By adjoint: ⟨Tu, q.snd⟩ = ⟨u, T*q.snd⟩ (where q.snd ∈ dom(T*))
        -- So ⟨u, q.fst⟩ = -⟨u, T*q.snd⟩ for all u ∈ dom(T)
        -- By density, ⟨v, q.fst⟩ = -⟨v, T*q.snd⟩ for all v, hence q.fst = -T*q.snd

        -- The functional φ(v) = ⟨v, q.fst + T*q.snd⟩ is zero on dense dom(T)
        have hzero_on_dom : ∀ u : T.domain, @inner ℂ H _ (u : H) (q.fst + (T.adjoint hT) y) = 0 := by
          intro u
          have h1 := hq_char u
          have hadj := T.adjointApply_spec hT y u
          -- Note: f u = T.toFun u = T u, and (y : H) = q.snd
          have hfu : f u = T u := rfl
          have hy_eq : (y : H) = q.snd := rfl
          -- (T.adjoint hT) y = T.adjointApply hT y by definition
          have hadj_eq : (T.adjoint hT) y = T.adjointApply hT y := rfl
          calc @inner ℂ H _ (u : H) (q.fst + (T.adjoint hT) y)
              = @inner ℂ H _ (u : H) q.fst + @inner ℂ H _ (u : H) ((T.adjoint hT) y) := inner_add_right _ _ _
            _ = @inner ℂ H _ (u : H) q.fst + @inner ℂ H _ (u : H) (T.adjointApply hT y) := by rw [hadj_eq]
            _ = @inner ℂ H _ (u : H) q.fst + @inner ℂ H _ (T u) (y : H) := by rw [hadj]
            _ = @inner ℂ H _ (u : H) q.fst + @inner ℂ H _ (f u) q.snd := by rw [hfu, hy_eq]
            _ = 0 := h1

        -- Since dom(T) is dense and the functional is continuous, it's zero everywhere
        have hsum_eq_zero : q.fst + (T.adjoint hT) y = 0 := by
          -- hT : T.domain.topologicalClosure = ⊤
          have hdense' : Dense (T.domain : Set H) := Submodule.dense_iff_topologicalClosure_eq_top.mpr hT
          by_contra hne
          have hne' : q.fst + (T.adjoint hT) y ≠ 0 := hne
          -- The element itself gives a nonzero inner product with itself
          have hself : @inner ℂ H _ (q.fst + (T.adjoint hT) y) (q.fst + (T.adjoint hT) y) ≠ 0 :=
            inner_self_ne_zero.mpr hne'
          -- But by density, we can approximate q.fst + T*y by elements of dom(T)
          have hmem_closure : q.fst + (T.adjoint hT) y ∈ closure (T.domain : Set H) := by
            rw [hdense'.closure_eq]; trivial
          rw [mem_closure_iff_seq_limit] at hmem_closure
          obtain ⟨seq, hseq_mem, hseq_lim⟩ := hmem_closure
          -- Inner product is continuous
          have hlim : Filter.Tendsto (fun n => @inner ℂ H _ (seq n) (q.fst + (T.adjoint hT) y))
              Filter.atTop (nhds (@inner ℂ H _ (q.fst + (T.adjoint hT) y) (q.fst + (T.adjoint hT) y))) :=
            Filter.Tendsto.inner hseq_lim tendsto_const_nhds
          -- seq n → q.fst + T*y, so ⟨seq n, q.fst + T*y⟩ → ⟨q.fst + T*y, q.fst + T*y⟩
          have hseq_zero : ∀ n, @inner ℂ H _ (seq n) (q.fst + (T.adjoint hT) y) = 0 := by
            intro n
            exact hzero_on_dom ⟨seq n, hseq_mem n⟩
          have hlim_zero : Filter.Tendsto (fun n => @inner ℂ H _ (seq n) (q.fst + (T.adjoint hT) y))
              Filter.atTop (nhds 0) := by simp [hseq_zero]
          have heq := tendsto_nhds_unique hlim hlim_zero
          exact hself heq

        have hq1_eq : q.fst = -((T.adjoint hT) y) := eq_neg_of_add_eq_zero_left hsum_eq_zero

        -- Now compute the inner product
        rw [VonNeumann.inner_prod_eq]
        simp only [WithLp.toLp_fst, WithLp.toLp_snd]
        rw [hq1_eq, inner_neg_left]
        -- Goal: -⟨T*y, x⟩ + ⟨z, y⟩ = 0
        -- hadj_prop: ⟨T*y, x⟩ = ⟨y, z⟩
        have heq := hadj_prop y
        -- Note: (y : H) = q.snd, so goal is: -⟨T*y, x⟩ + ⟨y, z⟩ = 0 (after noting inner product convention)
        -- Wait, the goal has ⟨z, q.snd⟩ = ⟨z, y⟩, and we have heq: ⟨T*y, x⟩ = ⟨y, z⟩
        -- The VonNeumann inner product is ⟨(a,b), (c,d)⟩ = ⟨a,c⟩ + ⟨b,d⟩
        -- So ⟨(x,z), q⟩ = ⟨x, q.1⟩ + ⟨z, q.2⟩
        -- With q.1 = -T*y and q.2 = y, this is ⟨x, -T*y⟩ + ⟨z, y⟩ = -⟨x, T*y⟩ + ⟨z, y⟩
        -- But we rewrote with inner_neg_left, which gives us -⟨T*y, x⟩ + ⟨z, y⟩
        -- Wait no, inner_neg_left is ⟨-a, b⟩ = -⟨a, b⟩, so ⟨-T*y, x⟩ = -⟨T*y, x⟩
        -- The goal is -⟨T*y, x⟩ + ⟨y, z⟩ = 0 (since q.snd = y)
        -- From heq: ⟨T*y, x⟩ = ⟨y, z⟩
        -- So -⟨T*y, x⟩ + ⟨y, z⟩ = -⟨y, z⟩ + ⟨y, z⟩ = 0 ✓
        have hy_eq : (y : H) = q.snd := rfl
        rw [← hy_eq, heq]
        ring

      -- Use double orthogonal = closure
      rw [Submodule.orthogonal_orthogonal_eq_closure] at h_in_perp_perp

      -- Convert from WithLp topology to H × H
      have hcont_of : Continuous (WithLp.ofLp (p := 2) : WithLp 2 (H × H) → H × H) :=
        WithLp.prod_continuous_ofLp 2 H H
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h_in_perp_perp
      rw [mem_closure_iff_seq_limit] at h_in_perp_perp
      obtain ⟨seq, hseq_mem, hseq_lim⟩ := h_in_perp_perp

      -- Since T is closed, closure(graph) = graph
      have hgraph_closed : _root_.IsClosed T.graph := hcl

      -- The sequence converges to (x, z) in the topology
      have h_in_closure : (x, z) ∈ closure T.graph := by
        rw [mem_closure_iff_seq_limit]
        use fun n => WithLp.ofLp (seq n)
        constructor
        · intro n
          obtain ⟨u, hu1, hu2⟩ := hseq_mem n
          exact ⟨u, hu1.symm, hu2.symm⟩
        · exact hcont_of.tendsto (WithLp.toLp 2 (x, z)) |>.comp hseq_lim

      -- Since graph is closed, (x, z) ∈ graph
      rw [hgraph_closed.closure_eq] at h_in_closure
      exact h_in_closure
    · -- (x, z) ∈ graph(T) → (x, z) ∈ graph(T**)
      intro ⟨u, hu1, hu2⟩
      -- u : dom(T), (u : H) = x, T u = z
      -- Need: x ∈ dom(T**) and T** x = z

      -- x ∈ dom(T**) means: the functional y ↦ ⟨T*y, x⟩ is bounded on dom(T*)
      -- For y ∈ dom(T*), ⟨T*y, x⟩ = ⟨T*y, u⟩ = ⟨y, Tu⟩ = ⟨y, z⟩
      -- This is bounded by ‖y‖ · ‖z‖

      -- hu1 : (u : H) = x, hu2 : T u = z
      simp only at hu1 hu2

      have hx_mem : x ∈ (T.adjoint hT).adjointDomain := by
        use ‖z‖
        intro y
        -- Need: ‖⟨(T.adjoint hT) y, x⟩‖ ≤ ‖z‖ * ‖y‖
        have hadj := T.adjointApply_spec hT y u
        -- hadj : ⟨Tu, y⟩ = ⟨u, T*y⟩
        have h : @inner ℂ H _ ((T.adjoint hT) y) x = @inner ℂ H _ (y : H) z := by
          rw [← hu1, ← hu2]
          calc @inner ℂ H _ ((T.adjoint hT) y) (u : H)
              = starRingEnd ℂ (@inner ℂ H _ (u : H) ((T.adjoint hT) y)) := (inner_conj_symm _ _).symm
            _ = starRingEnd ℂ (@inner ℂ H _ (u : H) (T.adjointApply hT y)) := rfl
            _ = starRingEnd ℂ (@inner ℂ H _ (T u) (y : H)) := by rw [← hadj]
            _ = @inner ℂ H _ (y : H) (T u) := inner_conj_symm _ _
        rw [h]
        calc ‖@inner ℂ H _ (y : H) z‖
            ≤ ‖(y : H)‖ * ‖z‖ := norm_inner_le_norm _ _
          _ = ‖z‖ * ‖(y : H)‖ := mul_comm _ _

      let x' : (T.adjoint hT).adjointDomainSubmodule := ⟨x, hx_mem⟩
      use x'
      constructor
      · rfl
      · -- Need: ((T.adjoint hT).adjoint hT') x' = z
        apply (T.adjoint hT).adjoint_unique hT' x
        · exact (T.adjoint hT).adjointApply_spec hT' x'
        · intro y
          -- Need: ⟨(T.adjoint hT) y, x⟩ = ⟨y, z⟩
          have hadj := T.adjointApply_spec hT y u
          rw [← hu1, ← hu2]
          calc @inner ℂ H _ ((T.adjoint hT) y) (u : H)
              = starRingEnd ℂ (@inner ℂ H _ (u : H) (T.adjointApply hT y)) := (inner_conj_symm _ _).symm
            _ = starRingEnd ℂ (@inner ℂ H _ (T u) (y : H)) := by rw [← hadj]
            _ = @inner ℂ H _ (y : H) (T u) := inner_conj_symm _ _

  -- Graph equality implies operator equality
  -- For unbounded operators, graph equality determines domain and function
  -- We use the fact that graph equality implies exact structural equality

  -- The graph determines the operator uniquely
  -- Since both operators have the same graph, they must be equal
  -- We prove this by showing they have the same domain and same action

  -- Use the graph to extract membership and values
  apply UnboundedOperator.eq_of_graph_eq
  exact hgraph_eq

end UnboundedOperator

/-! ### Symmetric and self-adjoint operators -/

namespace UnboundedOperator

variable (T : UnboundedOperator H)

/-- An operator is symmetric if ⟨Tx, y⟩ = ⟨x, Ty⟩ for all x, y ∈ dom(T) -/
def IsSymmetric : Prop :=
  ∀ x y : T.domain, @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (x : H) (T y)

/-- An operator is self-adjoint if T = T* (including equality of domains) -/
def IsSelfAdjoint (hT : T.IsDenselyDefined) : Prop :=
  T = T.adjoint hT

/-- Symmetric operators are closable -/
theorem symmetric_closable (hT : T.IsDenselyDefined) (hsym : T.IsSymmetric) : T.IsClosable := by
  -- For symmetric T, we have T ⊆ T* (symmetric implies contained in adjoint)
  -- Since T* is closed, closure(graph T) ⊆ graph(T*)
  -- If (0, y) ∈ closure(graph T), then (0, y) ∈ graph(T*)
  -- This means T* 0 = y, but T* 0 = 0 by linearity, so y = 0

  intro y hy
  -- hy : (0, y) ∈ closure T.graph
  -- Need to show y = 0

  -- First, show that graph(T) ⊆ graph(T*)
  have hsubset : T.graph ⊆ (T.adjoint hT).graph := by
    intro p hp
    obtain ⟨x, hx1, hx2⟩ := hp
    -- x : T.domain, (x : H) = p.1, T x = p.2
    -- Need to show p ∈ graph(T*)
    -- i.e., there exists w : (T.adjoint hT).domain with (w : H) = p.1 and (T.adjoint hT) w = p.2
    -- This requires x ∈ adjointDomain and T*x = Tx

    -- Show x ∈ adjointDomain: the map z ↦ ⟨Tz, x⟩ is bounded
    have hx_adj : (x : H) ∈ T.adjointDomain := by
      -- For z ∈ dom(T), ⟨Tz, x⟩ = ⟨z, Tx⟩ by symmetry
      -- |⟨Tz, x⟩| = |⟨z, Tx⟩| ≤ ‖z‖ · ‖Tx‖
      use ‖T x‖
      intro z
      rw [hsym z x]
      calc ‖@inner ℂ H _ (z : H) (T x)‖
          ≤ ‖(z : H)‖ * ‖T x‖ := norm_inner_le_norm (z : H) (T x)
        _ = ‖T x‖ * ‖(z : H)‖ := mul_comm _ _

    -- x' : adjoint domain with same underlying element
    let x' : T.adjointDomainSubmodule := ⟨(x : H), hx_adj⟩
    use x'
    constructor
    · exact hx1
    · -- Need: (T.adjoint hT) x' = T x = p.2
      rw [← hx2]
      -- (T.adjoint hT) x' is the unique z such that ∀ w, ⟨Tw, x'⟩ = ⟨w, z⟩
      -- By symmetry, T x satisfies this: ⟨Tw, x⟩ = ⟨w, Tx⟩
      apply T.adjoint_unique hT (x : H)
      · exact T.adjointApply_spec hT x'
      · intro w
        exact hsym w x

  -- closure(graph T) ⊆ closure(graph T*)
  have hclosure_subset : closure T.graph ⊆ closure (T.adjoint hT).graph :=
    closure_mono hsubset

  -- graph(T*) is closed (adjoint is always closed)
  have hclosed : _root_.IsClosed (T.adjoint hT).graph := T.adjoint_closed hT

  -- closure(graph T*) = graph(T*)
  have hclosure_eq : closure (T.adjoint hT).graph = (T.adjoint hT).graph :=
    hclosed.closure_eq

  -- (0, y) ∈ graph(T*)
  have hy' : (0, y) ∈ (T.adjoint hT).graph := by
    rw [← hclosure_eq]
    exact hclosure_subset hy

  -- From hy': there exists w with (w : H) = 0 and (T.adjoint hT) w = y
  obtain ⟨w, hw1, hw2⟩ := hy'
  -- w : (T.adjoint hT).domain, (w : H) = 0, (T.adjoint hT) w = y
  -- By linearity, T* w = T* 0 = 0 when (w : H) = 0
  -- Actually, w = 0 as an element of the domain
  have hw_zero : w = 0 := by
    ext
    exact hw1
  rw [hw_zero] at hw2
  -- (T.adjoint hT) 0 = 0 by linearity: T* 0 = T* (0 • 0) = 0 • T* 0 = 0
  have hadj_zero : (T.adjoint hT) 0 = 0 := by
    have h : (0 : (T.adjoint hT).domain) = (0 : ℂ) • (0 : (T.adjoint hT).domain) := by simp
    rw [h, (T.adjoint hT).map_smul']
    simp
  rw [hadj_zero] at hw2
  exact hw2.symm

/-- Self-adjoint operators are closed -/
theorem selfadjoint_closed (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) : T.IsClosed := by
  -- T = T* and T* is always closed
  rw [hsa]
  exact T.adjoint_closed hT

/-- Self-adjoint operators are symmetric -/
theorem selfadjoint_symmetric (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) :
    T.IsSymmetric := by
  intro x y
  -- For self-adjoint T = T*, the adjoint satisfies: ⟨Tx, y⟩ = ⟨x, T*y⟩ for y in dom(T*)
  -- Since T = T*, dom(T) = dom(T*) and T*y = Ty, giving ⟨Tx, y⟩ = ⟨x, Ty⟩

  -- Domain equality from T = T.adjoint hT
  have hdom : T.domain = T.adjointDomainSubmodule := congrArg UnboundedOperator.domain hsa

  -- y is in the adjoint domain
  have hy_adj : (y : H) ∈ T.adjointDomainSubmodule := hdom ▸ y.2
  let y' : T.adjointDomainSubmodule := ⟨(y : H), hy_adj⟩

  -- The adjoint property: ⟨Tx, y'⟩ = ⟨x, T*y'⟩
  have hadj := T.adjointApply_spec hT y' x

  -- Since (y' : H) = (y : H), the LHS matches
  have hlhs : @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (T x) (y' : H) := rfl

  -- For the RHS, we need (T.adjoint hT) y' = T y
  have hrhs : (T.adjoint hT) y' = T y := by
    -- Use the structural equality hsa : T = T.adjoint hT
    -- Define a function that applies an operator to an element based on underlying value
    let applyAt := fun (S : UnboundedOperator H) (z : H) (hz : z ∈ S.domain) => S.toFun ⟨z, hz⟩

    -- hsa : T = T.adjoint hT, so applyAt T = applyAt (T.adjoint hT)
    have happly : ∀ (z : H) (hz1 : z ∈ T.domain) (hz2 : z ∈ (T.adjoint hT).domain),
        T.toFun ⟨z, hz1⟩ = (T.adjoint hT).toFun ⟨z, hz2⟩ := by
      intro z hz1 hz2
      -- Both sides equal applyAt applied to the appropriate operator
      -- Using hsa, we transport along the equality
      have : T.toFun ⟨z, hz1⟩ = applyAt T z hz1 := rfl
      rw [this]
      -- Now use congrArg on hsa
      have hdom_eq : T.domain = (T.adjoint hT).domain := congrArg UnboundedOperator.domain hsa
      -- The key: use eq_rec to transport the membership proof
      have hz1' : z ∈ (T.adjoint hT).domain := hdom_eq ▸ hz1
      -- Show hz1' = hz2 (both are proofs of same statement)
      have hproof : hz1' = hz2 := rfl
      -- Now compute applyAt T z hz1
      -- = T.toFun ⟨z, hz1⟩
      -- = (by hsa) (T.adjoint hT).toFun ⟨z, hdom_eq ▸ hz1⟩
      -- = (T.adjoint hT).toFun ⟨z, hz2⟩
      show applyAt T z hz1 = (T.adjoint hT).toFun ⟨z, hz2⟩
      unfold applyAt
      -- Use Eq.rec on hsa
      have key : ∀ (S : UnboundedOperator H) (hs : T = S) (hz' : z ∈ S.domain),
          T.toFun ⟨z, hz1⟩ = S.toFun ⟨z, hz'⟩ := by
        intro S hs hz'
        subst hs
        rfl
      exact key (T.adjoint hT) hsa hz2

    -- y' : T.adjointDomainSubmodule with (y' : H) = (y : H)
    -- y : T.domain
    -- (T.adjoint hT).domain = T.adjointDomainSubmodule
    have hy'_mem : (y : H) ∈ (T.adjoint hT).domain := y'.2
    have hy_eq : y' = ⟨(y : H), hy'_mem⟩ := by ext; rfl

    rw [hy_eq]
    exact (happly (y : H) y.2 hy'_mem).symm

  rw [hlhs, hadj]
  -- Goal: ⟨x, T.adjointApply hT y'⟩ = ⟨x, T y⟩
  -- hrhs : (T.adjoint hT).toFun y' = T.toFun y
  -- Note: (T.adjoint hT).toFun = T.adjointApply hT by definition
  have hrhs' : T.adjointApply hT y' = T y := hrhs
  rw [hrhs']

end UnboundedOperator

/-! ### Positive operators -/

namespace UnboundedOperator

variable (T : UnboundedOperator H)

/-- An operator is positive if ⟨Tx, x⟩ ≥ 0 for all x ∈ dom(T) -/
def IsPositive : Prop :=
  ∀ x : T.domain, 0 ≤ (@inner ℂ H _ (T x) (x : H)).re

/-- An operator is strictly positive if ⟨Tx, x⟩ > 0 for all nonzero x ∈ dom(T).
    Equivalently, T is positive and injective (0 is not an eigenvalue).
    In modular theory, the modular operator Δ is always strictly positive. -/
def IsStrictlyPositive : Prop :=
  ∀ x : T.domain, (x : H) ≠ 0 → 0 < (@inner ℂ H _ (T x) (x : H)).re

theorem IsStrictlyPositive.isPositive (h : T.IsStrictlyPositive) : T.IsPositive :=
  fun x => by
    by_cases hx : (x : H) = 0
    · simp [hx]
    · exact le_of_lt (h x hx)

/-- For symmetric operators, ⟨Tx, x⟩ is real -/
theorem symmetric_inner_real (hsym : T.IsSymmetric) (x : T.domain) :
    (@inner ℂ H _ (T x) (x : H)).im = 0 := by
  -- For symmetric T: ⟨Tx, x⟩ = ⟨x, Tx⟩
  -- Also conj(⟨Tx, x⟩) = ⟨x, Tx⟩ (by inner_conj_symm)
  -- So ⟨Tx, x⟩ = conj(⟨Tx, x⟩), meaning ⟨Tx, x⟩ is real
  have h := hsym x x
  -- inner_conj_symm a b: conj(inner b a) = inner a b
  have hconj : starRingEnd ℂ (@inner ℂ H _ (T x) (x : H)) = @inner ℂ H _ (x : H) (T x) :=
    inner_conj_symm (x : H) (T x)
  -- Combining: conj(⟨Tx, x⟩) = ⟨x, Tx⟩ = ⟨Tx, x⟩
  rw [← h] at hconj
  -- hconj: conj(⟨Tx, x⟩) = ⟨Tx, x⟩
  -- For z = conj(z), we have z.im = -z.im, hence z.im = 0
  have him : (@inner ℂ H _ (T x) (x : H)).im = (starRingEnd ℂ (@inner ℂ H _ (T x) (x : H))).im := by
    rw [hconj]
  simp only [Complex.conj_im] at him
  -- him: z.im = -z.im, so z.im = 0
  linarith

/-- Positive symmetric operators satisfy ⟨(T - μ)x, x⟩ ≥ 0 for μ ≤ 0 -/
theorem positive_spectrum_nonneg (_hT : T.IsDenselyDefined) (_hsym : T.IsSymmetric)
    (hpos : T.IsPositive) (μ : ℝ) (hμ : μ ≤ 0) (x : T.domain) :
    0 ≤ (@inner ℂ H _ (T x) (x : H)).re - μ * ‖(x : H)‖^2 := by
  -- ⟨Tx, x⟩ - μ‖x‖² ≥ 0 when ⟨Tx, x⟩ ≥ 0 and μ ≤ 0
  have hTx := hpos x
  have hμnorm : 0 ≤ -μ * ‖(x : H)‖^2 := by
    apply mul_nonneg
    · linarith
    · exact sq_nonneg _
  linarith

end UnboundedOperator
