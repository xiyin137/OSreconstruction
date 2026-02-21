/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import OSReconstruction.ComplexLieGroups.Complexification

/-!
# Bargmann-Hall-Wightman Theorem

This file proves the Bargmann-Hall-Wightman theorem using the connectedness of
the complex Lorentz group SO⁺(1,d;ℂ) and the identity theorem.

## Main results

* `complex_lorentz_invariance` — real Lorentz invariance extends to complex Lorentz invariance
* `bargmann_hall_wightman_theorem` — the full BHW theorem

## Proof outline

### Complex Lorentz invariance (`complex_lorentz_invariance`)

**Step 1 — Near-identity invariance (identity theorem):**
Fix z₀ ∈ FT and a basis X₁,...,Xₘ of so(1,d;ℝ). The map
  Φ(c₁,...,cₘ) = F(exp(c₁X₁)·...·exp(cₘXₘ)·z₀)
is holomorphic in each cᵢ (separately) on an open set in ℂᵐ containing 0.
For real cᵢ, the product is a real Lorentz transformation, so Φ = F(z₀) on ℝᵐ.
By the 1D identity theorem applied variable-by-variable (SCV/Osgood + Analyticity),
Φ = F(z₀) on a polydisc near 0 in ℂᵐ. Since the exponential map is a local
diffeomorphism, this gives F(Λ·z₀) = F(z₀) for Λ near 1 in SO⁺(1,d;ℂ).

**Step 2 — Propagation (open-closed on connected orbit set):**
For fixed z ∈ FT, define U_z = {Λ : Λ·z ∈ FT} (open) and
S_z = {Λ ∈ U_z : F(Λ·z) = F(z)}.
- S_z is **open** in U_z: at Λ₀ ∈ S_z, apply Step 1 at z' = Λ₀·z ∈ FT,
  then translate via Λ ↦ ΛΛ₀ (continuous right multiplication).
- S_z is **closed** in U_z: if Λₙ → Λ₀ with F(Λₙ·z) = F(z) and
  Λ₀·z ∈ FT, then F(Λ₀·z) = lim F(Λₙ·z) = F(z) by continuity.
- 1 ∈ S_z and U_z is connected ⟹ S_z = U_z.

### Bargmann-Hall-Wightman theorem

1. **Extended tube T'_n**: Complex Lorentz invariance makes F_ext(Λ·w) := F(w)
   well-defined on T'_n = ⋃_Λ Λ·FT.
2. **Jost points**: Local commutativity gives F(π·x) = F(x) at real spacelike
   configurations for adjacent transpositions π.
3. **Edge-of-the-wedge**: Adjacent permuted tubes are glued via
   `SCV.edge_of_the_wedge_theorem`.
4. **Identity theorem**: Uniqueness on the connected permuted extended tube.

## References

* Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11.
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Forward tube and related structures

These are defined independently of the Wightman module so that
the BHW theorem can be stated without circular imports. -/

/-- The open forward light cone: η₀ > 0 and η·η < 0 (timelike, future-pointing). -/
def InOpenForwardCone (d : ℕ) (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0

/-- The forward tube T_n: the domain where successive imaginary-part differences
    lie in the open forward light cone. -/
def ForwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- The action of a complex Lorentz transformation on ℂ^{n×(d+1)}. -/
def complexLorentzAction (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ ν, Λ.val μ ν * z k ν

/-! ### Group action properties -/

/-- The complex Lorentz action is compatible with group multiplication. -/
theorem complexLorentzAction_mul (Λ₁ Λ₂ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (Λ₁ * Λ₂) z =
    complexLorentzAction Λ₁ (complexLorentzAction Λ₂ z) := by
  ext k μ
  simp only [complexLorentzAction, ComplexLorentzGroup.mul_val, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext ν
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- The identity acts trivially. -/
theorem complexLorentzAction_one (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (1 : ComplexLorentzGroup d) z = z := by
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The inverse acts by the inverse matrix. -/
theorem complexLorentzAction_inv (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ⁻¹ (complexLorentzAction Λ z) = z := by
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]

/-! ### Complex Lorentz invariance -/

/-- The orbit set U_z = {Λ : Λ·z ∈ ForwardTube} is the set of complex Lorentz
    transformations that keep z in the forward tube. -/
def orbitSet (z : Fin n → Fin (d + 1) → ℂ) : Set (ComplexLorentzGroup d) :=
  { Λ | complexLorentzAction Λ z ∈ ForwardTube d n }

/-- The orbit set contains the identity. -/
theorem mem_orbitSet_one (hz : z ∈ ForwardTube d n) :
    (1 : ComplexLorentzGroup d) ∈ orbitSet z := by
  rw [orbitSet, Set.mem_setOf_eq, complexLorentzAction_one]; exact hz

/-- The forward tube is open (strict inequalities on continuous functions). -/
theorem isOpen_forwardTube : IsOpen (ForwardTube d n) := by
  simp only [ForwardTube, InOpenForwardCone, Set.setOf_forall]
  apply isOpen_iInter_of_finite; intro k
  -- Helper: z ↦ (z k μ - prev(z) μ).im is continuous for each μ
  have hcont : ∀ μ : Fin (d + 1), Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
      (z k μ - (if _ : (k : ℕ) = 0 then 0 else z ⟨(k : ℕ) - 1, by omega⟩) μ).im) := by
    intro μ
    apply Complex.continuous_im.comp
    apply Continuous.sub
    · exact (continuous_apply μ).comp (continuous_apply k)
    · by_cases hk : (k : ℕ) = 0
      · simp [hk]; exact continuous_const
      · simp [hk]
        exact (continuous_apply μ).comp (continuous_apply (⟨(k : ℕ) - 1, by omega⟩ : Fin n))
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (hcont 0)
  · exact isOpen_lt
      (continuous_finset_sum _ fun μ _ => (continuous_const.mul ((hcont μ).pow 2)))
      continuous_const

/-- The action map Λ ↦ Λ·z is continuous (polynomial in entries of Λ). -/
theorem continuous_complexLorentzAction_fst (z : Fin n → Fin (d + 1) → ℂ) :
    Continuous (fun Λ : ComplexLorentzGroup d => complexLorentzAction Λ z) := by
  apply continuous_pi; intro k
  apply continuous_pi; intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => (ComplexLorentzGroup.continuous_entry μ ν).mul continuous_const)

/-- The orbit set is open (preimage of an open set under a continuous map). -/
theorem isOpen_orbitSet (z : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitSet z) :=
  isOpen_forwardTube.preimage (continuous_complexLorentzAction_fst z)

/-- The one-parameter action `t ↦ exp(tX) · z` using the matrix exponential directly.
    Each entry is a power series in t, hence differentiable. -/
private theorem differentiable_expAction
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (z : Fin n → Fin (d + 1) → ℂ) :
    Differentiable ℂ (fun t : ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν) :
      ℂ → Fin n → Fin (d + 1) → ℂ) := by
  have hexp : Differentiable ℂ (fun t : ℂ => (exp (t • X) : Matrix _ _ ℂ)) :=
    fun t => (hasDerivAt_exp_smul_const X t).differentiableAt
  apply differentiable_pi.mpr; intro k
  apply differentiable_pi.mpr; intro μ
  apply Differentiable.fun_sum; intro ν _
  exact ((differentiable_apply ν).comp ((differentiable_apply μ).comp hexp)).mul
    (differentiable_const _)

/-- Bridge lemma: the real matrix exponential maps to complex via `map ofReal`.
    Specifically, `(exp(s • Y)).map ofReal = exp((s : ℂ) • Y.map ofReal)`. -/
private theorem exp_map_ofReal_bridge (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal =
      (exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ) := by
  -- (exp(s•Y)).map ofReal = ofRealHom.mapMatrix (exp(s•Y))
  --                       = exp (ofRealHom.mapMatrix (s•Y))     by map_exp
  --                       = exp ((s:ℂ) • Y.map ofReal)          by smul commutation
  have hcont : Continuous (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have h1 : Complex.ofRealHom.mapMatrix (exp (s • Y)) =
      exp (Complex.ofRealHom.mapMatrix (s • Y)) :=
    map_exp (f := Complex.ofRealHom.mapMatrix) hcont (s • Y)
  have h2 : Complex.ofRealHom.mapMatrix (s • Y) = (s : ℂ) • Y.map Complex.ofReal := by
    ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  -- .map ofReal is the same as ofRealHom.mapMatrix
  change Complex.ofRealHom.mapMatrix (exp (s • Y)) = _
  rw [h1, h2]

/-- **Single-generator identity theorem.** For Y ∈ so(1,d;ℝ) and z ∈ FT,
    the function t ↦ F(exp(t · Y_ℂ) · z) equals F(z) for t near 0 in ℂ.

    Proof: The composed function g(t) = F(exp(tX)·z) - F(z) is:
    1. DifferentiableOn on the open set {t : exp(tX)·z ∈ FT}
    2. AnalyticAt 0 (by DifferentiableOn.analyticAt for ℂ-valued functions)
    3. Zero for real t (by real Lorentz invariance via the bridge lemma)
    4. Zero near 0 (by the 1D identity theorem) -/
private theorem single_generator_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n →
      F (fun k μ =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X := Y.map Complex.ofReal with hX_def
  -- The action map
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  -- The domain U = {t : action(t) ∈ FT} is open
  set U := {t : ℂ | action t ∈ ForwardTube d n} with hU_def
  have hU_open : IsOpen U :=
    isOpen_forwardTube.preimage (differentiable_expAction X z).continuous
  -- 0 ∈ U since action(0) = z ∈ FT
  have h0U : (0 : ℂ) ∈ U := by
    simp only [hU_def, haction_def, Set.mem_setOf_eq]
    convert hz using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]
  -- Define g(t) = F(action(t)) - F(z)
  set g : ℂ → ℂ := fun t => F (action t) - F z with hg_def
  -- g is DifferentiableOn on U
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction X z).differentiableOn (fun t ht => ht)
    · exact differentiableOn_const _
  -- g is AnalyticAt 0
  have hg_analytic : AnalyticAt ℂ g 0 :=
    hg_diff.analyticAt (hU_open.mem_nhds h0U)
  -- g(s) = 0 for s ∈ ℝ (real Lorentz invariance)
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    -- exp((s:ℂ) • X) = (exp(s • Y)).map ofReal
    have hbridge := exp_map_ofReal_bridge Y s
    -- The entries match: (exp((s:ℂ) • X)) μ ν = ((exp(s • Y)) μ ν : ℂ)
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      have : (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal = exp ((s : ℂ) • X) := hbridge
      exact (congr_fun (congr_fun this μ) ν).symm
    -- Rewrite the action to use real Lorentz entries
    have haction_eq : action (s : ℂ) =
        fun k μ => ∑ ν, ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) * z k ν := by
      ext k μ; simp only [haction_def]; congr 1; ext ν; rw [hentry]
    rw [haction_eq]
    -- Apply real Lorentz invariance
    exact hF_real_inv (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s)) z hz
  -- g = 0 frequently near 0 in 𝓝[≠] 0
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    -- Pick a small positive real number s ∈ U' ∩ {0}ᶜ ∩ U
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (r' / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  -- By the identity theorem: g = 0 on a neighborhood of 0
  have hg_zero := hg_analytic.frequently_zero_iff_eventually_zero.mp hg_freq
  -- Translate: F(action(t)) = F(z) eventually near 0
  exact hg_zero.mono (fun t ht _ => by
    simp only [hg_def, sub_eq_zero] at ht; exact ht)

/-- **Near-identity invariance.** If F is holomorphic on the forward tube and
    real-Lorentz invariant, then F is invariant under complex Lorentz transformations
    in a neighborhood of 1 (when the image stays in the forward tube).

    The proof uses the single-generator identity theorem
    (`single_generator_invariance`) along each one-parameter subgroup exp(tX)
    for X in the real Lie algebra so(1,d;ℝ). To extend from one-parameter
    subgroups to a full neighborhood of 1, one needs the inverse function theorem
    for the product-exponential map (t₁,...,tₘ) ↦ exp(t₁X₁)·...·exp(tₘXₘ). -/
private theorem near_identity_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  -- The single-generator identity theorem gives invariance along each
  -- one-parameter subgroup exp(tX) for X in the real Lie algebra.
  -- The product-exponential map (t₁,...,tₘ) ↦ exp(t₁X₁)·...·exp(tₘXₘ)
  -- (X₁,...,Xₘ a basis of so(1,d;ℝ)) covers a neighborhood of 1 by the
  -- inverse function theorem for the matrix exponential.
  -- Iterating single_generator_invariance along each factor and using
  -- the covering gives the full neighborhood result.
  sorry

/-- The orbit set U_z = {Λ : Λ·z ∈ FT} is preconnected.

    This follows from the tube domain structure of the forward tube: the imaginary
    part condition defines a convex cone, and the Lorentz action is linear in
    the imaginary parts. See Jost (1965), Ch. IV for the mathematical argument. -/
private theorem orbitSet_isPreconnected (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    IsPreconnected (orbitSet z) := by
  sorry

/-- **Complex Lorentz invariance on the forward tube.**

    If F is holomorphic on the forward tube and invariant under the real
    restricted Lorentz group SO⁺(1,d;ℝ), then F is invariant under the
    complex Lorentz group SO⁺(1,d;ℂ), whenever the transformed point
    remains in the forward tube.

    The proof uses an **open-closed argument** on the orbit set U_z:
    1. The invariance set S_z = {Λ ∈ U_z : F(Λ·z) = F(z)} is **open** in
       SO⁺(1,d;ℂ) by `near_identity_invariance` (identity theorem).
    2. S_z is **closed** relative to U_z by continuity of F ∘ action.
    3. Since U_z is preconnected and 1 ∈ S_z, we conclude S_z = U_z.

    Ref: Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11. -/
theorem complex_lorentz_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  intro Λ z hz hΛz
  -- === Define the invariance set S ===
  -- S = {Λ' : Λ'·z ∈ FT ∧ F(Λ'·z) = F(z)}
  set S : Set (ComplexLorentzGroup d) :=
    { Λ' | complexLorentzAction Λ' z ∈ ForwardTube d n ∧
           F (complexLorentzAction Λ' z) = F z } with hS_def
  -- === 1 ∈ S ===
  have h1S : (1 : ComplexLorentzGroup d) ∈ S := by
    refine ⟨?_, ?_⟩
    · rwa [complexLorentzAction_one]
    · rw [complexLorentzAction_one]
  -- === Λ ∈ orbitSet z ===
  have hΛU : Λ ∈ orbitSet z := hΛz
  -- === 1 ∈ orbitSet z ===
  have h1U : (1 : ComplexLorentzGroup d) ∈ orbitSet z := mem_orbitSet_one hz
  -- === S is open in the ambient topology ===
  -- At each Λ₀ ∈ S, near_identity_invariance at z' = Λ₀·z gives a nhd of 1
  -- where invariance holds. Translating by Λ₀ (via continuous left multiplication)
  -- gives a nhd of Λ₀ in S.
  have hS_open : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro Λ₀ ⟨hΛ₀_orbit, hΛ₀_inv⟩
    -- Near-identity at z' = Λ₀·z ∈ FT
    have h_near := near_identity_invariance n F hF_holo hF_real_inv
      (complexLorentzAction Λ₀ z) hΛ₀_orbit
    -- Right multiplication by Λ₀⁻¹ is continuous
    have hmul_right : Continuous (· * Λ₀⁻¹ : ComplexLorentzGroup d → ComplexLorentzGroup d) := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      change Continuous (fun x : ComplexLorentzGroup d => x.val * Λ₀⁻¹.val)
      exact ComplexLorentzGroup.continuous_val.mul continuous_const
    -- Λ₁ ↦ Λ₁ * Λ₀⁻¹ tends to 1 at Λ₀
    have htendsto : Tendsto (· * Λ₀⁻¹) (𝓝 Λ₀) (𝓝 (1 : ComplexLorentzGroup d)) := by
      rw [show (1 : ComplexLorentzGroup d) = Λ₀ * Λ₀⁻¹ from (mul_inv_cancel Λ₀).symm]
      exact hmul_right.continuousAt.tendsto
    -- Pull back h_near through the map
    have h_near' := htendsto.eventually h_near
    -- Rewrite: (Λ₁*Λ₀⁻¹)·(Λ₀·z) = Λ₁·z
    have hrewrite : ∀ Λ₁ : ComplexLorentzGroup d,
        complexLorentzAction (Λ₁ * Λ₀⁻¹) (complexLorentzAction Λ₀ z) =
        complexLorentzAction Λ₁ z := by
      intro Λ₁
      rw [← complexLorentzAction_mul, mul_assoc, inv_mul_cancel, mul_one]
    -- Combine: eventually near Λ₀, Λ₁·z ∈ FT → F(Λ₁·z) = F(z)
    have h_near_rw : ∀ᶠ Λ₁ in 𝓝 Λ₀,
        complexLorentzAction Λ₁ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ₁ z) = F z := by
      apply h_near'.mono
      intro Λ₁ h hmem
      rw [hrewrite Λ₁] at h
      exact (h hmem).trans hΛ₀_inv
    -- S ∈ 𝓝 Λ₀
    have hS_nhd : S ∈ 𝓝 Λ₀ :=
      (h_near_rw.and ((isOpen_orbitSet z).mem_nhds hΛ₀_orbit)).mono
        fun Λ₁ ⟨himp, hmem⟩ => ⟨hmem, himp hmem⟩
    exact mem_nhds_iff.mp hS_nhd
  -- === orbitSet z \ S is open (closed part of the clopen argument) ===
  -- The map Λ ↦ F(Λ·z) is continuous on orbitSet z (composition of
  -- continuous action and F continuous on FT). So {Λ ∈ U : F(Λ·z) ≠ F(z)}
  -- is open (preimage of open complement of {F(z)} intersected with U).
  have hUS_open : IsOpen (orbitSet z \ S) := by
    have hU_open := isOpen_orbitSet z
    have hg_cont : ContinuousOn (fun Λ => F (complexLorentzAction Λ z)) (orbitSet z) :=
      hF_holo.continuousOn.comp (continuous_complexLorentzAction_fst z).continuousOn
        fun Λ hΛ => hΛ
    -- orbitSet z \ S = orbitSet z ∩ (fun Λ => F(Λ·z))⁻¹'({F z}ᶜ)
    have hset : orbitSet z \ S = orbitSet z ∩
        (fun Λ => F (complexLorentzAction Λ z)) ⁻¹' {F z}ᶜ := by
      ext Λ
      simp only [hS_def, Set.mem_diff, Set.mem_setOf_eq, orbitSet, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact hg_cont.isOpen_inter_preimage hU_open isOpen_compl_singleton
  -- === orbitSet z is preconnected ===
  have hU_pre := orbitSet_isPreconnected n z hz
  -- === Open-closed argument ===
  -- S is open, orbitSet z \ S is open, they cover orbitSet z, and
  -- orbitSet z ∩ S is nonempty (contains 1). If orbitSet z \ S were nonempty
  -- (containing Λ), preconnectedness would give a point in S ∩ (orbitSet z \ S) = ∅.
  suffices Λ ∈ S from this.2
  by_contra hΛnS
  have h_cover : orbitSet z ⊆ S ∪ (orbitSet z \ S) := by
    intro x hx; by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr ⟨hx, hxS⟩
  have h_inter := hU_pre S (orbitSet z \ S) hS_open hUS_open h_cover
    ⟨1, h1U, h1S⟩ ⟨Λ, hΛU, hΛU, hΛnS⟩
  obtain ⟨_, _, hxS, hxdiff⟩ := h_inter
  exact ((Set.mem_diff _).mp hxdiff).2 hxS

/-! ### The permuted extended tube -/

/-- The extended forward tube: the orbit of the forward tube under the complex
    Lorentz group. T'_n = ⋃_Λ Λ · FT_n -/
def ExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = complexLorentzAction Λ w }

/-- The permuted forward tube for permutation π:
    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}.
    Matches `PermutedForwardTube` in AnalyticContinuation.lean. -/
def PermutedForwardTube (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} ⋃_{Λ ∈ L₊(ℂ)} Λ · π(T_n).
    Matches `PermutedExtendedTube` in AnalyticContinuation.lean. -/
def PermutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = complexLorentzAction Λ w }

/-- The forward tube is contained in the extended tube. -/
theorem forwardTube_subset_extendedTube :
    ForwardTube d n ⊆ ExtendedTube d n := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨1, z, hz, ?_⟩
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The extended tube is contained in the permuted extended tube. -/
theorem extendedTube_subset_permutedExtendedTube :
    ExtendedTube d n ⊆ PermutedExtendedTube d n := by
  intro z hz
  obtain ⟨Λ, w, hw, hzw⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨Equiv.refl _, Λ, w, ?_, hzw⟩
  -- w ∈ PermutedForwardTube (Equiv.refl _) ↔ (fun k => w k) ∈ FT ↔ w ∈ FT
  show (fun k => w ((Equiv.refl _) k)) ∈ ForwardTube d n
  simp only [Equiv.refl_apply]; exact hw

/-- The forward tube is contained in the permuted extended tube. -/
theorem forwardTube_subset_permutedExtendedTube :
    ForwardTube d n ⊆ PermutedExtendedTube d n :=
  fun _ hz => extendedTube_subset_permutedExtendedTube (forwardTube_subset_extendedTube hz)

/-! ### Extension to the extended tube -/

/-- F extends to the extended tube via complex Lorentz transformations:
    F_ext(Λ·w) = F(w) for w ∈ FT. Well-defined by `complex_lorentz_invariance`.

    For z ∈ ExtendedTube, choose a preimage w ∈ FT with z = Λ·w for some Λ,
    and define extendF(z) = F(w). The choice doesn't matter by
    `complex_lorentz_invariance`. For z ∉ ExtendedTube, define extendF(z) = 0. -/
def extendF (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if h : ∃ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w
    then F h.choose
    else 0

/-- `extendF` agrees with F on the forward tube. -/
theorem extendF_eq_on_forwardTube (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    extendF F z = F z := by
  simp only [extendF]
  -- The existential is satisfied: z ∈ FT, take w = z and Λ = 1.
  have hex : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ : ComplexLorentzGroup d), z = complexLorentzAction Λ w :=
    ⟨z, hz, 1, (complexLorentzAction_one z).symm⟩
  rw [dif_pos hex]
  -- The chosen w satisfies w ∈ FT and z = Λ·w for some Λ.
  -- Need: F(chosen_w) = F(z).
  have hspec := hex.choose_spec
  have hw : hex.choose ∈ ForwardTube d n := hspec.1
  obtain ⟨Λ, hzΛw⟩ := hspec.2
  -- z = Λ·w, so Λ·w ∈ FT (since z ∈ FT)
  have hΛw : complexLorentzAction Λ hex.choose ∈ ForwardTube d n := hzΛw ▸ hz
  -- By complex_lorentz_invariance: F(Λ·w) = F(w), and z = Λ·w, so F(w) = F(z).
  have key := complex_lorentz_invariance n F hF_holo hF_real_inv Λ hex.choose hw hΛw
  -- key : F(Λ·w) = F(w).  congr_arg F hzΛw.symm : F(Λ·w) = F(z).
  exact key.symm.trans (congr_arg F hzΛw.symm)

/-- Any two forward-tube preimages of the same extended-tube point give the same F-value.
    This is the key well-definedness lemma for `extendF`. -/
private theorem extendF_preimage_eq (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ} (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ w₁ = complexLorentzAction Λ₂ w₂) :
    F w₁ = F w₂ := by
  -- From Λ₁·w₁ = Λ₂·w₂, apply Λ₂⁻¹: (Λ₂⁻¹*Λ₁)·w₁ = w₂
  have hrel : complexLorentzAction (Λ₂⁻¹ * Λ₁) w₁ = w₂ := by
    have := congr_arg (complexLorentzAction Λ₂⁻¹) h
    rwa [← complexLorentzAction_mul, complexLorentzAction_inv] at this
  -- w₂ = (Λ₂⁻¹*Λ₁)·w₁ ∈ FT, so by complex_lorentz_invariance: F(w₂) = F(w₁)
  have := complex_lorentz_invariance n F hF_holo hF_real_inv (Λ₂⁻¹ * Λ₁) w₁ hw₁ (hrel ▸ hw₂)
  rw [hrel] at this; exact this.symm

/-- `extendF` is invariant under complex Lorentz transformations on the extended tube. -/
theorem extendF_complex_lorentz_invariant (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n) :
    extendF F (complexLorentzAction Λ z) = extendF F z := by
  -- z ∈ ExtendedTube: ∃ Λ₀, w₀ with z = Λ₀·w₀, w₀ ∈ FT
  obtain ⟨Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
  simp only [extendF]
  -- The existential is satisfied for z
  have hex_z : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d), z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ₀, hzw₀⟩
  -- The existential is satisfied for Λ·z (since Λ·z = (Λ*Λ₀)·w₀)
  have hex_Λz : ∃ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d),
        complexLorentzAction Λ z = complexLorentzAction Λ' w :=
    ⟨w₀, hw₀, Λ * Λ₀, by rw [hzw₀, complexLorentzAction_mul]⟩
  rw [dif_pos hex_Λz, dif_pos hex_z]
  -- hex_Λz.choose and hex_z.choose are both in FT.
  -- They are preimages of Λ·z and z respectively, related by Λ.
  obtain ⟨hw_Λz, Λ₃, hΛz_eq⟩ := hex_Λz.choose_spec
  obtain ⟨hw_z, Λ₂, hz_eq⟩ := hex_z.choose_spec
  -- Both preimages map to the same point (up to Lorentz transformations):
  -- Λ₃·hex_Λz.choose = Λ·z = Λ·(Λ₂·hex_z.choose) = (Λ*Λ₂)·hex_z.choose
  -- By extendF_preimage_eq, F values agree.
  exact extendF_preimage_eq n F hF_holo hF_real_inv hw_Λz hw_z
    (hΛz_eq.symm.trans ((congr_arg (complexLorentzAction Λ) hz_eq).trans
      (complexLorentzAction_mul Λ Λ₂ hex_z.choose).symm))

/-! ### Full BHW theorem -/

/-- **The Bargmann-Hall-Wightman Theorem.**

    Given a holomorphic function F on the forward tube that is:
    1. Invariant under the real restricted Lorentz group
    2. Continuously extends to the real boundary (`hF_bv`)
    3. Has boundary values satisfying local commutativity at spacelike pairs (`hF_local`)

    Then F extends uniquely to a holomorphic function on the permuted extended tube,
    and the extension is:
    1. Invariant under the complex Lorentz group SO⁺(1,d;ℂ)
    2. Invariant under all permutations of the arguments
    3. Unique (any other holomorphic extension agreeing with F on the forward tube
       must equal F_ext on the permuted extended tube)

    This theorem eliminates the `bargmann_hall_wightman` axiom from
    `AnalyticContinuation.lean` once the bridge to the Wightman module is established. -/
theorem bargmann_hall_wightman_theorem (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    -- F extends continuously to the real boundary of the forward tube.
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    -- Local commutativity: at spacelike-separated pairs, the boundary values
    -- of F and F∘swap agree.
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- F_ext is holomorphic on the permuted extended tube
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      -- F_ext restricts to F on the forward tube
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      -- F_ext is invariant under the complex Lorentz group
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (complexLorentzAction Λ z) = F_ext z) ∧
      -- F_ext is symmetric under permutations
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      -- Uniqueness: any holomorphic function on PermutedExtendedTube agreeing with F
      -- on ForwardTube must equal F_ext.
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  -- Use extendF for the extended tube, then extend to permuted extended tube
  sorry

end BHW

end
