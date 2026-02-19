/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import SchwartzNuclear
import GaussianField
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace

/-!
# Bridge: GaussianField → OSReconstruction

This file imports results from the `gaussian-field` library and re-exports
them for use in the OS reconstruction project.

## What we get from gaussian-field

### SchwartzNuclear (all sorry-free)
- Hermite functions: definition, orthonormality, Schwartz membership
- Schwartz-Hermite expansion: `f = ∑ₙ cₙ(f) ψₙ` in Schwartz topology
- Tensor product Hermite basis for S(ℝⁿ)
- `GaussianField.NuclearSpace (SchwartzMap D ℝ)` instance (Dynin-Mityagin)

### GaussianField (all sorry-free)
- Spectral theorem for compact self-adjoint operators
- Nuclear SVD: singular value decomposition for nuclear operators
- Gaussian measure construction on `WeakDual ℝ E`
- Characteristic functional: `∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²)`
- Moment identities: E[ω(f)] = 0, E[ω(f)ω(g)] = ⟨Tf,Tg⟩

## Two NuclearSpace definitions

This project (OSReconstruction) defines `NuclearSpace` via the Pietsch
characterization (nuclear dominance by seminorms). The gaussian-field project
defines `GaussianField.NuclearSpace` via the Dynin-Mityagin characterization
(Schauder basis with rapid decay). Both are valid characterizations of nuclear
Fréchet spaces; they coexist in different namespaces.

The gaussian-field construction uses `GaussianField.NuclearSpace` directly
for the Gaussian measure construction, so we re-export that interface here.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
- Pietsch, "Nuclear Locally Convex Spaces" (1972)
-/

noncomputable section

open GaussianField
open scoped NNReal

/-! ### Schwartz NuclearSpace instance

The `schwartz_nuclearSpace` axiom from gaussian-field provides a
`GaussianField.NuclearSpace` instance for `SchwartzMap D ℝ` whenever
`D` is a nontrivial finite-dimensional normed space with a Borel σ-algebra.

This instance is registered globally, so once this file is imported,
typeclass synthesis will automatically find it. -/

-- Verify the instance is available
example : GaussianField.NuclearSpace (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ) :=
  inferInstance

/-! ### Hermite function results

The gaussian-field library provides sorry-free proofs of the fundamental
properties of Hermite functions. These are at the top-level namespace. -/

/-- Hermite functions from gaussian-field. These are ψₙ(x) = cₙ · Hₙ(x√2) · exp(-x²/2)
    using probabilist Hermite polynomials. -/
abbrev gfHermiteFunction := hermiteFunction

/-- Hermite functions are in the Schwartz space (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_schwartz := hermiteFunction_schwartz

/-- Hermite functions are orthonormal in L²(ℝ) (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_orthonormal := hermiteFunction_orthonormal

/-- Hermite functions are complete in L² (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_complete := hermiteFunction_complete

/-- Seminorm bounds on Hermite functions (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_seminorm_bound := hermiteFunction_seminorm_bound

/-! ### Spectral theorem -/

/-- Spectral theorem for compact self-adjoint operators on a real Hilbert space.
    Sorry-free from gaussian-field.

    For a compact self-adjoint T ≠ 0, there exist eigenvectors forming a
    HilbertBasis, with eigenvalues μ and T(x) = ∑ μᵢ ⟨eᵢ, x⟩ eᵢ. -/
abbrev gfCompactSelfAdjointSpectral := @compact_selfAdjoint_spectral

/-! ### Gaussian measure construction -/

/-- The configuration space (space of distributions). -/
abbrev gfConfiguration := @Configuration

/-- The Gaussian measure on Configuration E with covariance ⟨T·, T·⟩. -/
abbrev gfMeasure := @GaussianField.measure

/-- Characteristic functional: ∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²).
    Sorry-free from gaussian-field. -/
abbrev gfCharFun := @charFun

/-! ### Moment identities -/

/-- The Gaussian measure is centered: E[ω(f)] = 0 (sorry-free). -/
abbrev gfMeasureCentered := @measure_centered

/-- Cross-moment equals covariance: E[ω(f)ω(g)] = ⟨Tf, Tg⟩ (sorry-free). -/
abbrev gfCrossMomentEqCovariance := @cross_moment_eq_covariance

/-- The pairing ω(f) is Gaussian-distributed (sorry-free). -/
abbrev gfPairingIsGaussian := @pairing_is_gaussian

/-! ### Hahn-Banach for seminorms in locally convex spaces

The key tool for the bridge: given a continuous seminorm `q` on a locally
convex TVS, there exists a continuous linear functional `φ` with `φ(f) = q(f)`
and `|φ(x)| ≤ q(x)` for all `x`. This is a standard corollary of the
Hahn-Banach extension theorem. -/

/-- **Hahn-Banach for continuous seminorms.**

For a continuous seminorm `q` and any vector `f`, there exists a continuous
linear functional `φ` attaining `q` at `f` and bounded by `q` everywhere. -/
lemma exists_CLF_le_seminorm
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (q : Seminorm ℝ E) (hq : Continuous q) (f : E) :
    ∃ φ : E →L[ℝ] ℝ, φ f = q f ∧ ∀ x, |φ x| ≤ q x := by
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf, map_zero], fun x => by simp⟩
  · -- Define linear functional on span {f} with value q(f) at f
    let f₀ := LinearPMap.mkSpanSingleton (K := ℝ) f (q f) hf
    -- Apply Hahn-Banach extension with N = q (sublinear)
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f₀ q
      (fun c hc x => by -- positive homogeneity: q(c • x) = c * q(x) for c > 0
        rw [map_smul_eq_mul]; simp [abs_of_pos hc])
      (fun x y => map_add_le_add q x y) -- subadditivity
      (fun ⟨x, hx⟩ => by -- bound: f₀(x) ≤ q(x) for x ∈ span {f}
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [LinearPMap.mkSpanSingleton'_apply]
        simp only [smul_eq_mul]
        calc c * q f ≤ |c| * q f :=
              mul_le_mul_of_nonneg_right (le_abs_self c) (apply_nonneg q f)
          _ = q (c • f) := by rw [map_smul_eq_mul]; simp)
    -- g(f) = q(f)
    have hg_f : g f = q f := by
      have h := hg_ext ⟨f, Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩⟩
      simp only [f₀, LinearPMap.mkSpanSingleton'_apply_self] at h
      exact h
    -- |g(x)| ≤ q(x) from g(x) ≤ q(x) and g(-x) ≤ q(-x) = q(x)
    have hg_abs : ∀ x, |g x| ≤ q x := by
      intro x; rw [abs_le]
      constructor
      · have h1 := hg_le (-x)
        rw [map_neg, map_neg_eq_map] at h1
        linarith
      · exact hg_le x
    -- g is continuous: bounded by continuous seminorm, hence continuous at 0
    have hg_cont : Continuous g := by
      apply continuous_of_continuousAt_zero g.toAddMonoidHom
      rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
      intro ε hε
      have hqε : {x : E | q x < ε} ∈ nhds (0 : E) :=
        (hq.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp [map_zero, hε])
      exact Filter.mem_of_superset hqε (fun x hx => by
        simp only [Real.dist_eq, sub_zero]
        exact (hg_abs x).trans_lt hx)
    exact ⟨⟨g, hg_cont⟩, hg_f, hg_abs⟩

/-! ### Bridge: Dynin-Mityagin → Pietsch

We prove that `GaussianField.NuclearSpace E` implies `NuclearSpace E` (Pietsch).
The proof uses the Hahn-Banach lemma above to establish the key seminorm bound
from the Schauder expansion. -/

/-- Auxiliary: a finset sup of seminorms applied to a sequence with polynomial
growth in each seminorm has a uniform polynomial bound.

Given `p' : ι → Seminorm ℝ E` and a finite set `s`, if each `p' i` for `i ∈ s`
satisfies `p' i (x m) ≤ Cᵢ · (1+m)^{tᵢ}`, then `(s.sup p') (x m) ≤ D · (1+m)^S`
where `S = max tᵢ` and `D = ∑ Cᵢ`. -/
private lemma finset_sup_poly_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [DecidableEq ι]
    (p' : ι → Seminorm ℝ E) (s : Finset ι) (x : ℕ → E)
    (hx : ∀ i ∈ s, ∃ C > 0, ∃ t : ℕ, ∀ m, p' i (x m) ≤ C * (1 + (m : ℝ)) ^ t) :
    ∃ D > 0, ∃ S : ℕ, ∀ m, (s.sup p') (x m) ≤ D * (1 + (m : ℝ)) ^ S := by
  induction s using Finset.cons_induction with
  | empty =>
    exact ⟨1, one_pos, 0, fun m => by simp [Finset.sup_empty, Seminorm.bot_eq_zero]⟩
  | cons a s has ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_cons.mpr (Or.inr hi)))
    obtain ⟨D₁, hD₁, S₁, hbound₁⟩ := ih'
    obtain ⟨Ca, hCa, ta, hbounda⟩ := hx a (Finset.mem_cons.mpr (Or.inl rfl))
    refine ⟨Ca + D₁, by linarith, max ta S₁, fun m => ?_⟩
    rw [Finset.sup_cons]
    have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    have h1m_le : (1 : ℝ) ≤ 1 + (m : ℝ) := by linarith
    have hpow_le_left : (1 + (m : ℝ)) ^ ta ≤ (1 + (m : ℝ)) ^ (max ta S₁) :=
      pow_le_pow_right₀ h1m_le (le_max_left ta S₁)
    have hpow_le_right : (1 + (m : ℝ)) ^ S₁ ≤ (1 + (m : ℝ)) ^ (max ta S₁) :=
      pow_le_pow_right₀ h1m_le (le_max_right ta S₁)
    have hle_sup_left : (p' a) (x m) ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) := by
      calc (p' a) (x m) ≤ Ca * (1 + (m : ℝ)) ^ ta := hbounda m
        _ ≤ Ca * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_left hpow_le_left (le_of_lt hCa)
        _ ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt h1m) _)
    have hle_sup_right : (s.sup p') (x m) ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) := by
      calc (s.sup p') (x m) ≤ D₁ * (1 + (m : ℝ)) ^ S₁ := hbound₁ m
        _ ≤ D₁ * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_left hpow_le_right (le_of_lt hD₁)
        _ ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt h1m) _)
    exact sup_le hle_sup_left hle_sup_right

/-- **Seminorm bound from Schauder expansion.**

For a continuous seminorm `q` and a Schauder basis with expansion
`f = ∑ₘ cₘ(f) · ψₘ`, the triangle inequality gives
`q(f) ≤ ∑ₘ |cₘ(f)| · q(ψₘ)`.

The proof uses Hahn-Banach to find a CLF `φ` with `φ(f) = q(f)` and `|φ| ≤ q`,
then applies the Schauder expansion to `φ` and bounds the resulting tsum. -/
lemma seminorm_le_nuclear_expansion
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : GaussianField.NuclearSpace E]
    (q : Seminorm ℝ E) (hq : Continuous q) (f : E) :
    q f ≤ ∑' m, |hN.coeff m f| * q (hN.basis m) := by
  -- Step 1: Hahn-Banach gives φ with φ(f) = q(f) and |φ| ≤ q
  obtain ⟨φ, hφf, hφq⟩ := exists_CLF_le_seminorm q hq f
  -- Step 2: Summability of the target series
  -- |coeff m f| * q(basis m) is summable from coeff_decay + basis_growth
  have hsumm : Summable (fun m => |hN.coeff m f| * q (hN.basis m)) := by
    -- Bound q by defining seminorms
    obtain ⟨s₁, C₁, hC₁ne, hqbound⟩ := Seminorm.bound_of_continuous hN.h_with q hq
    have hC₁_pos : (0 : ℝ) < C₁ := by positivity
    -- Basis growth for s₁.sup hN.p
    have hgrowth : ∀ i ∈ s₁, ∃ C > 0, ∃ t : ℕ,
        ∀ m, hN.p i (hN.basis m) ≤ C * (1 + (m : ℝ)) ^ t :=
      fun i _ => hN.basis_growth i
    classical
    obtain ⟨D, hD, S, hDbound⟩ := finset_sup_poly_bound hN.p s₁ hN.basis hgrowth
    -- Coefficient decay
    obtain ⟨C₂, hC₂, s₂, hcoeff⟩ := hN.coeff_decay (S + 2)
    -- Each term: |coeff m f| * q(basis m) ≤ const / (1+m)^2
    have h1m_pos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) := fun m => by positivity
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg q _))
    · intro m
      calc |hN.coeff m f| * q (hN.basis m)
          ≤ |hN.coeff m f| * ((C₁ : ℝ) * (s₁.sup hN.p) (hN.basis m)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have h := hqbound (hN.basis m)
            simp [NNReal.smul_def] at h; exact h
        _ ≤ |hN.coeff m f| * ((C₁ : ℝ) * (D * (1 + (m : ℝ)) ^ S)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left (hDbound m) (le_of_lt hC₁_pos)
        _ = (|hN.coeff m f| * (1 + (m : ℝ)) ^ (S + 2)) *
            ((C₁ : ℝ) * D / (1 + (m : ℝ)) ^ 2) := by
            rw [pow_add]; field_simp
        _ ≤ (C₂ * (s₂.sup hN.p) f) * ((C₁ : ℝ) * D / (1 + (m : ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_right (hcoeff f m)
            apply div_nonneg (mul_nonneg (le_of_lt hC₁_pos) (le_of_lt hD))
            positivity
        _ = C₂ * (s₂.sup hN.p) f * (C₁ : ℝ) * D * (1 / ((m : ℝ) + 1) ^ 2) := by
            field_simp; ring
    · -- Summable: const * ∑ 1/(m+1)^2
      have hsumm_shift : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
        have := (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
        exact this.congr (fun m => by push_cast; ring_nf)
      exact (hsumm_shift.const_smul (C₂ * (s₂.sup hN.p) f * (C₁ : ℝ) * D)).congr
        (fun m => by simp [smul_eq_mul])
  -- Step 3: Summability of the expansion terms (bounded by the above)
  have hsumm' : Summable (fun m => hN.coeff m f * φ (hN.basis m)) :=
    hsumm.of_norm_bounded (fun m => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hφq _) (abs_nonneg _))
  -- Step 4: Apply expansion axiom and bound the tsum
  rw [← hφf, hN.expansion φ f]
  -- Each term: coeff m f * φ(basis m) ≤ |coeff m f| * q(basis m)
  exact hsumm'.tsum_le_tsum (fun m =>
    le_trans (le_abs_self _)
      (le_trans (le_of_eq (abs_mul _ _))
        (mul_le_mul_of_nonneg_left (hφq _) (abs_nonneg _)))) hsumm

/-- **Dynin-Mityagin implies Pietsch nuclearity.**

A `GaussianField.NuclearSpace` (Schauder basis with polynomial growth/decay)
gives rise to a `NuclearSpace` (Pietsch nuclear dominance).

**Proof sketch.** Given a continuous seminorm `p`:

1. Bound `p` by the defining seminorms: `p ≤ C₁ · (s₁.sup hN.p)`
2. Get uniform polynomial growth: `(s₁.sup hN.p)(ψₘ) ≤ D · (1+m)^S`
3. Get coefficient decay with extra room: `|cₘ(f)| · (1+m)^{S+2} ≤ C₂ · (s₂.sup hN.p)(f)`
4. Define CLFs `fₘ := (1+m)^{S+2} · cₘ` and coefficients
   `aₘ := C₁ · D · (1+m)^{-(2:ℤ)}` (summable since exponent < -1)
5. The dominating seminorm is `q := C₁ · s₁.sup(p) + C₂ · s₂.sup(p)` -/
theorem GaussianField.NuclearSpace.toPietschNuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : GaussianField.NuclearSpace E] : _root_.NuclearSpace E where
  nuclear_dominance := by
    classical
    intro p hp
    -- Step 1: Bound p by the defining seminorms
    obtain ⟨s₁, C₁nn, hC₁ne, hpbound⟩ :=
      Seminorm.bound_of_continuous hN.h_with p hp
    have hC₁_pos : (0 : ℝ) < C₁nn := by positivity
    -- Step 2: Get polynomial growth bound on basis vectors
    have hgrowth : ∀ i ∈ s₁, ∃ C > 0, ∃ t : ℕ,
        ∀ m, hN.p i (hN.basis m) ≤ C * (1 + (m : ℝ)) ^ t :=
      fun i _ => hN.basis_growth i
    obtain ⟨D, hD, S, hDbound⟩ := finset_sup_poly_bound hN.p s₁ hN.basis hgrowth
    -- Step 3: Get coefficient decay with exponent S + 2
    obtain ⟨C₂, hC₂, s₂, hcoeff_decay⟩ := hN.coeff_decay (S + 2)
    -- Build the dominating seminorm q
    -- q = C₁nn • (s₁.sup hN.p) + C₂nn • (s₂.sup hN.p)
    set C₂nn : ℝ≥0 := ⟨C₂, le_of_lt hC₂⟩ with hC₂nn_def
    set q := C₁nn • s₁.sup hN.p + C₂nn • s₂.sup hN.p with hq_def
    -- Continuity of finset sups of seminorms
    -- Each p i is continuous by WithSeminorms, and finite sup of continuous seminorms is continuous
    have hsup_cont : ∀ (t : Finset hN.ι), Continuous (⇑(t.sup hN.p) : E → ℝ) := by
      intro t
      induction t using Finset.cons_induction with
      | empty =>
        show Continuous (⇑(⊥ : Seminorm ℝ E) : E → ℝ)
        simp [Seminorm.bot_eq_zero]; exact continuous_const
      | cons a t' _ ih =>
        rw [Finset.sup_cons]
        exact (hN.h_with.continuous_seminorm a).sup ih
    have hsup₁_cont : Continuous (⇑(s₁.sup hN.p) : E → ℝ) := hsup_cont s₁
    have hsup₂_cont : Continuous (⇑(s₂.sup hN.p) : E → ℝ) := hsup_cont s₂
    -- q is continuous
    have hq_cont : Continuous q := by
      show Continuous (fun x => q x)
      have : (fun x => q x) = fun x =>
          (C₁nn : ℝ) * (s₁.sup hN.p) x + (C₂nn : ℝ) * (s₂.sup hN.p) x := by
        ext x; simp [hq_def, NNReal.smul_def]
      rw [this]
      exact (continuous_const.mul hsup₁_cont).add (continuous_const.mul hsup₂_cont)
    -- q ≥ p
    have hq_ge : ∀ x, p x ≤ q x := by
      intro x
      have h1 : p x ≤ (C₁nn • s₁.sup hN.p) x := hpbound x
      have h2 : (0 : ℝ) ≤ (C₂nn • s₂.sup hN.p) x := apply_nonneg _ x
      calc p x ≤ (C₁nn • s₁.sup hN.p) x := h1
        _ ≤ (C₁nn • s₁.sup hN.p) x + (C₂nn • s₂.sup hN.p) x := le_add_of_nonneg_right h2
        _ = q x := (Seminorm.add_apply _ _ x).symm
    -- Define CLFs: f_m = (1+m)^{S+2} • coeff m
    let f : ℕ → (E →L[ℝ] ℝ) := fun m => ((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m
    -- c_m = C₁nn * sup_p(ψ_m) / (1+m)^{S+2}
    let c : ℕ → ℝ := fun m =>
      (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2)
    -- Common positivity facts
    have h1m_pos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) := fun m => by positivity
    have h1m_ne : ∀ m : ℕ, (1 + (m : ℝ)) ≠ 0 := fun m => ne_of_gt (h1m_pos m)
    -- Summability of the shifted p-series ∑ 1/(1+m)^2
    have hsumm_shift : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      exact this.congr (fun m => by push_cast; ring_nf)
    refine ⟨q, hq_cont, hq_ge, f, c, ?_, ?_, ?_, ?_⟩
    -- c ≥ 0
    · intro m
      apply div_nonneg
      · exact mul_nonneg (NNReal.coe_nonneg C₁nn) (apply_nonneg _ _)
      · positivity
    -- Summable c
    · -- c m ≤ C₁nn * D / (1+m)^2
      apply Summable.of_nonneg_of_le
      · intro m; exact div_nonneg (mul_nonneg (NNReal.coe_nonneg C₁nn) (apply_nonneg _ _))
          (pow_nonneg (h1m_pos m).le _)
      · intro m
        show (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2) ≤
          (C₁nn : ℝ) * D / (1 + (m : ℝ)) ^ 2
        -- sup_p(ψ_m) ≤ D * (1+m)^S, so after dividing by (1+m)^{S+2} we get ≤ D/(1+m)^2
        have hpow_pos : (0 : ℝ) < (1 + (m : ℝ)) ^ (S + 2) := pow_pos (h1m_pos m) _
        rw [div_le_div_iff₀ hpow_pos (pow_pos (h1m_pos m) 2)]
        calc (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) * (1 + (m : ℝ)) ^ 2
            ≤ (C₁nn : ℝ) * (D * (1 + (m : ℝ)) ^ S) * (1 + (m : ℝ)) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (h1m_pos m).le 2)
              exact mul_le_mul_of_nonneg_left (hDbound m) (NNReal.coe_nonneg C₁nn)
          _ = (C₁nn : ℝ) * D * ((1 + (m : ℝ)) ^ S * (1 + (m : ℝ)) ^ 2) := by ring
          _ = (C₁nn : ℝ) * D * (1 + (m : ℝ)) ^ (S + 2) := by rw [pow_add]
      · have : Summable (fun m : ℕ => (C₁nn : ℝ) * D * ((1 : ℝ) / ((m : ℝ) + 1) ^ 2)) :=
          hsumm_shift.const_smul ((C₁nn : ℝ) * D)
        exact this.congr (fun m => by ring_nf)
    -- ‖f m x‖ ≤ q x
    · intro m x
      show ‖((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m x‖ ≤ q x
      simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg (h1m_pos m).le _)]
      rw [mul_comm]
      calc |hN.coeff m x| * (1 + (m : ℝ)) ^ (S + 2) ≤ C₂ * (s₂.sup hN.p) x :=
              hcoeff_decay x m
        _ = (C₂nn : ℝ) * (s₂.sup hN.p) x := by simp [hC₂nn_def]
        _ = (C₂nn • s₂.sup hN.p) x := by simp [NNReal.smul_def]
        _ ≤ (C₁nn • s₁.sup hN.p) x + (C₂nn • s₂.sup hN.p) x :=
            le_add_of_nonneg_left (apply_nonneg _ x)
        _ = q x := (Seminorm.add_apply _ _ x).symm
    -- p x ≤ ∑' m, ‖f m x‖ * c m
    · intro x
      have hexpand := seminorm_le_nuclear_expansion (s₁.sup hN.p) hsup₁_cont x
      -- The key equality: ∑' ‖f_m x‖ * c_m = C₁nn * ∑' |coeff_m x| * sup_p(ψ_m)
      have hsum_eq : (C₁nn : ℝ) * ∑' m, |hN.coeff m x| * (s₁.sup hN.p) (hN.basis m) =
          ∑' m, ‖f m x‖ * c m := by
        rw [← tsum_mul_left]
        congr 1; ext m
        show (C₁nn : ℝ) * (|hN.coeff m x| * (s₁.sup hN.p) (hN.basis m)) =
          ‖((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m x‖ *
          ((C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2))
        simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (pow_nonneg (h1m_pos m).le _)]
        field_simp
      calc p x ≤ (C₁nn • s₁.sup hN.p) x := hpbound x
        _ = (C₁nn : ℝ) * (s₁.sup hN.p) x := by simp [NNReal.smul_def]
        _ ≤ (C₁nn : ℝ) * ∑' m, |hN.coeff m x| * (s₁.sup hN.p) (hN.basis m) :=
            mul_le_mul_of_nonneg_left hexpand (NNReal.coe_nonneg C₁nn)
        _ = ∑' m, ‖f m x‖ * c m := hsum_eq

end
