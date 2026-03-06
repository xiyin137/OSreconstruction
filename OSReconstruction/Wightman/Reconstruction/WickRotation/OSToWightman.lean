/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.SCV.BochnerTubeTheorem

/-!
# OS to Wightman (E'→R')

Analytic continuation from Euclidean to Minkowski: given Schwinger functions
satisfying E0'-E4 (with the linear growth condition), reconstruct Wightman
functions satisfying R0-R5.

The proof proceeds through phases:
- Phase 2: Euclidean time translation semigroup
- Phase 3: Inductive analytic continuation (OS II, Theorem 4.1-4.2)
- Phase 4: Boundary values → tempered distributions
- Phase 5: Property transfer (OS axioms → Wightman axioms)
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ### OS to Wightman (Theorem E'→R') -/

/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    This gives a contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (contraction, from E2)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    By the Hille-Yosida theorem, T(t) = e^{-tH} where H ≥ 0 is self-adjoint.
    This H is the Hamiltonian of the reconstructed QFT. -/
structure EuclideanSemigroup (OS : OsterwalderSchraderAxioms d) where
  /-- The semigroup parameter (Euclidean time) -/
  T : ℝ → (BorchersSequence d → BorchersSequence d)
  /-- Semigroup property: T(s) ∘ T(t) = T(s+t) -/
  semigroup : ∀ s t : ℝ, s > 0 → t > 0 → T s ∘ T t = T (s + t)
  /-- Contraction: ‖T(t)F‖ ≤ ‖F‖ -/
  contraction : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S (T t F) (T t F)).re ≤
    (OSInnerProduct d OS.S F F).re
  /-- Positivity: T(t) ≥ 0 as an operator -/
  positive : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S F (T t F)).re ≥ 0

/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : Im = 0, ξᵢ₀ > 0} (positive real Euclidean domain)
    C_k^(r+1) = {z ∈ ℂ^{k(d+1)} : Im(z_i,μ - z_{i-1,μ}) > 0 for all i, μ ≤ r}
      (open forward tube in the first r+1 spacetime directions; no constraint on μ > r).

    **Key property**: For r ≥ 1, C_k^(r) is an OPEN subset of ℂ^{k(d+1)}
    (strict positivity of imaginary parts ⟹ open). This ensures `DifferentiableOn ℂ`
    on C_k^(r) is genuine holomorphicity, not a vacuous condition.

    **Note**: C_k^(d+1) is the full forward tube (Im-differences positive in all
    directions). To reach the actual forward tube from C_k^(d+1), one needs:
    1. Euclidean rotation invariance (E1) to extend to SO(d+1)-rotated copies
    2. Bochner's tube theorem to extend to the convex hull = forward tube

    The regions are monotone: C_k^(r) ⊂ C_k^(r+1), and C_k^(0) is disjoint
    from C_k^(r) for r ≥ 1 (C_k^(0) has Im = 0, C_k^(r) requires Im > 0). -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- Base: positive Euclidean domain (all Im = 0, Euclidean times positive)
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- Open forward tube in first r+1 spacetime directions;
    -- no constraint on remaining directions (μ > r), giving an open set.
    { z | ∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0 }

/-- **Inductive analytic continuation (OS II, Theorem 4.1).**

    Given S holomorphic on C_k^(r) (where r spacetime coordinates are complex),
    extend it analytically to C_k^(r+1) (one more coordinate becomes complex).

    The proof at each step uses the **Paley-Wiener theorem** (one variable):
    1. Fix all variables except the (r+1)-th spacetime component of each ξ_j.
       The result is a function of k−1 real variables (the (r+1)-th components
       of the difference vectors ξ_1, ..., ξ_{k−1}).
    2. The E0' linear growth condition gives polynomial bounds on each variable.
    3. The spectral condition (from reflection positivity / positivity of the
       Hamiltonian) ensures the Fourier transform in each variable has one-sided
       support in [0, ∞). Physically: the spectral measure is supported in the
       forward cone V̄₊, so each spatial momentum component is bounded by the
       energy (|p^μ| ≤ p^0).
    4. The **Paley-Wiener theorem**: a function on ℝ with polynomial growth
       whose Fourier transform has support in [0, ∞) extends holomorphically to
       the upper half-plane {Im z > 0}, with polynomial growth.
    5. Extend one variable at a time, then apply Osgood's lemma
       (`osgood_lemma`, proved in SeparatelyAnalytic.lean) for joint holomorphicity.

    None of this is currently in Mathlib: the Paley-Wiener theorem for tempered
    distributions, the spectral representation of reflection-positive functionals,
    and the extraction of one-sided Fourier support from E0' + E2.

    Current status: this theorem is still **schematic**. The actual missing
    mathematics is not only the Osgood/joint-holomorphicity assembly, but also
    the extraction of the slice-wise Paley-Wiener hypotheses (one-sided Fourier
    support and polynomial growth for each fixed slice) from `OS` and `lgc`.
    Those slice hypotheses are not yet formalized as separate inputs, so the
    theorem remains an under-explained continuation step rather than a finished
    theorem-level interface.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 (Paley-Wiener);
    Vladimirov §26 (Fourier-Laplace representation) -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) (r : ℕ) (hr : r < d + 1)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  -- The proof uses Paley-Wiener to extend one spacetime coordinate at a time.
  -- Key mathematical inputs (extracted as atomic helpers):
  -- 1. One-sided Fourier support from E0' + E2 (spectral condition from
  --    reflection positivity + linear growth)
  -- 2. Polynomial growth in each variable from E0'
  -- Given these, the one-dimensional Paley-Wiener theorem
  -- (`paley_wiener_one_step_simple` in PaleyWiener.lean) extends each fixed
  -- slice in the new coordinate to the upper half-plane.
  -- Joint holomorphicity then follows from Osgood's lemma.
  --
  -- The remaining work is not just Osgood/plumbing. One still has to formalize
  -- the slice-wise Paley-Wiener inputs extracted from `OS` and `lgc`, then
  -- assemble those slice extensions into the region-level continuation.
  -- We decompose:
  -- Step 1: For each fixed z' in C_k^(r), the r-th coordinate slice satisfies PW
  -- Step 2: The PW extension gives holomorphicity in the new coordinate
  -- Step 3: Osgood's lemma gives joint holomorphicity on C_k^(r+1)
  -- Step 4: Agreement on C_k^(r) follows from equality of distributional boundary values
  --
  -- Each step depends on infrastructure from PaleyWiener.lean. The 1D helper
  -- `paley_wiener_one_step_simple` is now proved; the remaining blocker here is
  -- the multi-variable slice assembly together with Osgood/local boundedness.
  sorry

/-! ### Full analytic continuation from Euclidean to forward tube

After d+1 applications of `inductive_analytic_continuation`, we reach C_k^(d+1),
a tube over the positive orthant. To reach the full forward tube, we use:
1. Euclidean rotation invariance (E1) to extend to rotated copies
2. Bochner's tube theorem to extend to the convex hull = forward tube

Ref: OS II, Sections IV-V; Bochner (1938); Vladimirov Section 20.2 -/

/-- Iterate `inductive_analytic_continuation` d+1 times: from C_k^(0) to C_k^(d+1).
    Blocked by: formal iteration + composing agreement conditions.
    Ref: OS II, Theorem 4.1 -/
theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ)
    (S_base : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_base : DifferentiableOn ℂ S_base (AnalyticContinuationRegion d k 0)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k 0, S_ext z = S_base z := by
  let P : ℕ → Prop := fun r =>
    ∃ (S_r : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_r (AnalyticContinuationRegion d k r) ∧
      ∀ z ∈ AnalyticContinuationRegion d k 0, S_r z = S_base z
  have hP0 : P 0 := ⟨S_base, hS_base, fun _ _ => rfl⟩
  have hstep : ∀ r, r < d + 1 → P r → P (r + 1) := by
    intro r hr hPr
    rcases hPr with ⟨S_r, hS_r_hol, hS_r_base⟩
    obtain ⟨S_next, hS_next_hol, hS_next_agree⟩ :=
      inductive_analytic_continuation OS lgc k r hr S_r hS_r_hol
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      refine ⟨S_next, hS_next_hol, ?_⟩
      intro z hz0
      have hz_r : z ∈ AnalyticContinuationRegion d 0 r := by
        cases r <;> simp [AnalyticContinuationRegion]
      calc
        S_next z = S_r z := hS_next_agree z hz_r
        _ = S_base z := hS_r_base z hz0
    · let i0 : Fin k := ⟨0, hkpos⟩
      have hdisj : Disjoint (AnalyticContinuationRegion d k 0)
          (AnalyticContinuationRegion d k (r + 1)) := by
        rw [Set.disjoint_left]
        intro z hz0 hz1
        rcases hz0 with ⟨hz0_im, _hz0_pos⟩
        -- hz1 : ∀ i, ∀ μ, μ.val ≤ r → (let prev := ...; (z i μ - prev μ).im > 0)
        -- Apply at i0 (= ⟨0,hkpos⟩) and μ = 0:
        have hraw := hz1 i0 (0 : Fin (d + 1)) (Nat.zero_le r)
        -- i0.val = 0, so prev = fun _ => 0, prev 0 = 0; hraw : (z i0 0 - 0).im > 0
        have hpos0 : (z i0 (0 : Fin (d + 1))).im > 0 := by
          simp only [show i0.val = 0 from rfl, ↓reduceDIte, Pi.zero_apply, sub_zero] at hraw
          exact hraw
        have him0 : (z i0 (0 : Fin (d + 1))).im = 0 := hz0_im i0 (0 : Fin (d + 1))
        linarith
      let S_next' : (Fin k → Fin (d + 1) → ℂ) → ℂ :=
        fun z => if z ∈ AnalyticContinuationRegion d k 0 then S_base z else S_next z
      have hEq : Set.EqOn S_next' S_next (AnalyticContinuationRegion d k (r + 1)) := by
        intro z hz
        have hz_not_base : z ∉ AnalyticContinuationRegion d k 0 := by
          intro hz0
          exact (Set.disjoint_left.mp hdisj hz0 hz)
        simp [S_next', hz_not_base]
      refine ⟨S_next', hS_next_hol.congr hEq, ?_⟩
      intro z hz0
      simp [S_next', hz0]
  have hP_all : ∀ r, r ≤ d + 1 → P r := by
    intro r hrle
    induction r with
    | zero =>
        exact hP0
    | succ r ihr =>
        have hrlt : r < d + 1 := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hrle
        have hrle' : r ≤ d + 1 := Nat.le_trans (Nat.le_succ r) hrle
        exact hstep r hrlt (ihr hrle')
  exact hP_all (d + 1) (le_rfl)

/-- Schwinger functions on C_k^(0), recovering S_k via integration.
    Blocked by: pointwise extraction from S_k and smoothness in positive-time region.
    Ref: OS II, Section IV (base case) -/
theorem schwinger_holomorphic_on_base_region
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_base : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_base (AnalyticContinuationRegion d k 0) ∧
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_base (fun j => wickRotatePoint (x j)) * (f x)) := by
  sorry

/-- Extend from C_k^(d+1) to the forward tube via E1 + Bochner.
    Blocked by: tube domain identification and `bochner_tube_extension`.
    Ref: OS II, Section V; Bochner (1938) -/
theorem extend_to_forward_tube_via_bochner (k : ℕ)
    (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_ext : DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)))
    (h_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1),
        S_ext (fun i μ => ∑ ν, (R μ ν : ℂ) * z i ν) = S_ext z) :
    ∃ (W : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W (ForwardTube d k) ∧
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1), W z = S_ext z := by
  sorry

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : SchwartzNPoint d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f x)) := by
  -- Step 1: Base case
  obtain ⟨S_base, hS_base_hol, hS_base_euclid⟩ :=
    schwinger_holomorphic_on_base_region OS lgc k
  -- Step 2: Iterate d+1 times
  obtain ⟨S_ext, hS_ext_hol, hS_ext_agree⟩ :=
    iterated_analytic_continuation OS lgc k S_base hS_base_hol
  -- Step 3: Rotation invariance from E1 + analytic continuation uniqueness
  have h_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ z ∈ AnalyticContinuationRegion d k (d + 1),
        S_ext (fun i μ => ∑ ν, (R μ ν : ℂ) * z i ν) = S_ext z := by
    sorry
  -- Step 4: E1 + Bochner to extend to forward tube
  obtain ⟨W, hW_hol, hW_agree⟩ := extend_to_forward_tube_via_bochner k S_ext hS_ext_hol h_rot
  refine ⟨W, hW_hol, fun f => ?_⟩
  -- Step 5: Euclidean restriction chain
  -- W(wick(x)) = S_ext(wick(x)) = S_base(wick(x)) for wick(x) in C_k^(0)
  sorry

/-! ### Phase 4: Tempered boundary values

**Critical**: E0' (linear growth condition) is essential for temperedness.
Without growth control, boundary values might fail to be tempered
(the gap in OS I Lemma 8.8). E0' gives |W_n(f)| <= C_n * ||f||_{s,n}
where C_n has at most factorial growth.

Ref: OS II, Section VI -/

/-- Distributional boundary values of the forward tube analytic continuation
    exist and are tempered.

    Given F holomorphic on ForwardTube d n with polynomial growth (from E0'),
    the distributional BV ∫ F(x + iεη) f(x) dx converges as ε → 0+ for
    all Schwartz f and approach directions η ∈ V₊^n.

    Blocked by: Vladimirov's distributional boundary value theorem for tube
    domains (Theorem 26.1 in Vladimirov's "Methods of Generalized Functions"),
    which requires polynomial growth estimates from E0'.

    Ref: Vladimirov Section 26; Streater-Wightman Theorem 2-9 -/
theorem forward_tube_bv_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    ∃ (W_n : SchwartzNPoint d n → ℂ),
      Continuous W_n ∧ IsLinearMap ℂ W_n ∧
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f))) ∧
      ∃ (C : ℝ) (s : ℕ), C > 0 ∧
        ∀ f : SchwartzNPoint d n,
          ‖W_n f‖ ≤ C * lgc.alpha * lgc.beta ^ n * (n.factorial : ℝ) ^ lgc.gamma *
            SchwartzMap.seminorm ℝ s s f := by
  sorry

theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- W_n is continuous (tempered distribution)
      Continuous W_n ∧
      -- W_n is linear
      IsLinearMap ℂ W_n ∧
      -- F_analytic is holomorphic on the forward tube
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      -- Boundary values of F_analytic give W_n
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f))) ∧
      -- Euclidean restriction of F_analytic gives S_n
      (∀ (f : SchwartzNPoint d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f x)) ∧
      -- Growth estimate (linear growth condition on Wightman side, R0')
      ∃ (C : ℝ) (s : ℕ), C > 0 ∧
        ∀ f : SchwartzNPoint d n,
          ‖W_n f‖ ≤ C * lgc.alpha * lgc.beta ^ n * (n.factorial : ℝ) ^ lgc.gamma *
            SchwartzMap.seminorm ℝ s s f := by
  -- Step 1: Get the analytic continuation from full_analytic_continuation
  obtain ⟨F_analytic, hF_hol, hF_euclid⟩ := full_analytic_continuation OS lgc n
  -- Step 2: Get tempered boundary values from forward_tube_bv_tempered
  obtain ⟨W_n, hW_cont, hW_lin, hW_bv, hW_growth⟩ :=
    forward_tube_bv_tempered OS lgc n F_analytic hF_hol
  exact ⟨W_n, F_analytic, hW_cont, hW_lin, hF_hol, hW_bv, hF_euclid, hW_growth⟩

/-! ### Constructing WightmanFunctions from OS Data

Each Wightman axiom is derived from the corresponding OS axiom via analytic
continuation. The helper lemmas below capture each derivation. -/

/-- The n-point Wightman distribution `W_n` extracted from `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, Continuous W_n ∧ IsLinearMap ℂ W_n ∧ ...`.
    This definition extracts `W_n` via `.choose` (the first existential witness).

    `W_n` is the tempered distributional boundary value of the analytically continued
    function `F_analytic` on the forward tube. It is continuous (tempered) and linear,
    and satisfies factorial growth bounds from the OS linear growth condition.

    Note: `boundary_values_tempered` is proved in this file, but it depends on
    upstream deferred lemmas (`full_analytic_continuation` and
    `forward_tube_bv_tempered`), so `bvt_W` and downstream properties remain
    contingent on those obligations. -/
def bvt_W (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    SchwartzNPoint d n → ℂ :=
  (boundary_values_tempered OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, ... ∧ DifferentiableOn ℂ F_analytic
    (ForwardTube d n) ∧ ...`. This definition extracts `F_analytic` via
    `.choose_spec.choose` (the second existential witness, nested inside the first).

    `F_analytic` is holomorphic on `ForwardTube d n`, its distributional boundary values
    recover `bvt_W` (the Wightman distribution), and its Euclidean restriction
    (via Wick rotation) recovers the Schwinger functions `OS.S n`.

    Note: `boundary_values_tempered` is proved in this file, but it depends on
    upstream deferred lemmas (`full_analytic_continuation` and
    `forward_tube_bv_tempered`), so `bvt_F` and downstream properties remain
    contingent on those obligations. -/
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (boundary_values_tempered OS lgc n).choose_spec.choose

theorem bvt_W_continuous (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    Continuous (bvt_W OS lgc n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1

theorem bvt_F_holomorphic (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    DifferentiableOn ℂ (bvt_F OS lgc n) (ForwardTube d n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.1

theorem bvt_boundary_values (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n f)) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.1

theorem bvt_euclidean_restriction (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f x) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.2.1

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n

Each bvt_* property follows a three-step transfer:
1. OS axiom (E0-E4) gives a property of S_n
2. S_n = F_analytic ∘ wickRotate (Euclidean restriction) transfers to F_analytic
3. W_n = BV(F_analytic) (boundary value) transfers to W_n

The following helpers isolate the transfer steps as smaller sorry targets. -/

/-- E2R normalization: The 0-point BV is evaluation at the origin.

    For n = 0, the domain Fin 0 → Fin (d+1) → ℝ is a zero-dimensional space
    (a single point). The forward tube ForwardTube d 0 is all of the (trivial)
    domain. The analytic function F_analytic is a constant. The BV condition
    reduces to: the constant value times f(0) = W_0(f), so W_0(f) = c * f(0).
    Combining with the OS normalization (S_0 is normalized by the Euclidean
    restriction), we get c = 1, hence W_0(f) = f(0).

    This requires: (1) identifying the integral over the zero-dimensional space,
    (2) the OS normalization condition S_0(f) = f(0). -/
theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      InForwardCone d 0 η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : SchwartzNPoint d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  intro f
  let η0 : Fin 0 → Fin (d + 1) → ℝ := fun k => Fin.elim0 k
  have hη0 : InForwardCone d 0 η0 := by
    intro k
    exact Fin.elim0 k
  set I0 : ℂ := ∫ x : Fin 0 → Fin (d + 1) → ℝ,
      F_0 (fun k => wickRotatePoint (x k)) * (f x)
  have hconst :
      ∀ ε : ℝ,
        (∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) * (f x)) = I0 := by
    intro ε
    unfold I0
    congr 1
    ext x
    have hz : (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) =
        (fun k => wickRotatePoint (x k)) := by
      funext k
      exact Fin.elim0 k
    simp [hz]
  have hBV0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W_0 f)) := by
    simpa [hconst] using hBV f η0 hη0
  have hI0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I0) :=
    tendsto_const_nhds
  have hW0 : W_0 f = I0 :=
    tendsto_nhds_unique hBV0 hI0
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f := (hEuclid f).symm
    _ = f 0 := lgc.normalized_zero f

/-- E2R translation: Translation invariance transfers from S_n (via E1) through
    the analytic continuation to the BV.

    The argument: E1 says S_n is translation-invariant. The Euclidean restriction
    shows F_analytic is translation-invariant at Euclidean points. By analytic
    continuation, F_analytic is translation-invariant on the forward tube. The BV
    limit preserves translation invariance. -/
theorem bv_translation_invariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_cont : Continuous W_n)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x))
    (hE1 : ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      OS.S n f = OS.S n g) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  -- Proof sketch: From hEuclid and hE1, F_n(wick(x)) = F_n(wick(x-a)) for all x, so F_n is
  -- invariant under the Euclidean shift wick_a = (i*a_0, a_1, ..., a_d).
  -- By distributional_uniqueness_forwardTube, F_n(z) = F_n(z - wick_a) on all of FT.
  -- The BV limit W_n(g) = lim ∫ F_n(x + iεη) f(x+a) dx = lim ∫ F_n(y - a + iεη) f(y) dy,
  -- and y - a + iεη = y - wick_a + iεη (up to the i*a_0 time component cancellation) — but
  -- this identification fails because a_0 ≠ i*a_0 (real vs imaginary time shift).
  -- Full proof requires the analytic continuation infrastructure (BHW + OS II Section VI).
  sorry

/-- E2R Lorentz: Lorentz covariance transfers from E1 (Euclidean rotation
    invariance) through BHW to the BV.

    The argument: E1 gives SO(d+1)-invariance of S_n. The analytic continuation
    extends this to SO(d+1,C)-invariance of F_analytic. The restricted Lorentz
    group SO+(1,d) embeds in SO(d+1,C) (Bargmann-Hall-Wightman), giving
    real Lorentz invariance of F_analytic. The BV preserves this invariance. -/
theorem bv_lorentz_covariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x))
    (hE1_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
      OS.S n f = OS.S n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  sorry

/-- E2R locality: Local commutativity transfers from E3 (permutation symmetry)
    + edge-of-the-wedge to the BV.

    The argument: E3 says S_n is permutation-symmetric. The Euclidean restriction
    shows F_analytic is permutation-symmetric at Euclidean points. By analytic
    continuation (Jost's theorem), this extends to the permuted extended tube.
    Edge-of-the-wedge at the boundary gives local commutativity of W_n. -/
theorem bv_local_commutativity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hE3 : ∀ (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
      OS.S n f = OS.S n g) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  sorry

/-- E2R positivity: Positive definiteness transfers from E2 (reflection positivity)
    through the Wick rotation.

    The argument: The Wightman inner product sum_{n,m} W_{n+m}(f*_n x f_m) is
    related to the OS inner product sum_{n,m} S_{n+m}(theta(f*_n) x f_m) by
    analytic continuation. E2 ensures the OS inner product is non-negative,
    hence the Wightman inner product is non-negative. -/
theorem bv_positive_definiteness_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_eq : ∀ n, W n = bvt_W OS lgc n)
    (hE2 : ∀ (F : BorchersSequence d),
      (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
        x ∈ PositiveTimeRegion d n) →
      (OSInnerProduct d OS.S F F).re ≥ 0) :
    ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0 := by
  sorry

/-- E2R Hermiticity: Hermiticity of W_n from reality of Schwinger functions.

    The Schwinger functions are real-valued on real configurations. Under
    analytic continuation, this gives a Schwarz reflection principle for
    F_analytic. Taking BV, this yields the Hermiticity condition
    W_n(f~) = conj(W_n(f)). -/
theorem bv_hermiticity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : SchwartzNPoint d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  sorry

/-- S44: W_0 = 1 (normalization).
    The 0-point Schwinger function S_0 = 1 (OS normalization). Its analytic
    continuation is the constant function 1 on the (trivial) forward tube.
    The distributional BV of 1 is evaluation: W_0(f) = f(0). -/
theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

/-- S45: Translation invariance of W_n from E1. -/
theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  exact bv_translation_invariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_W_continuous OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_translation_invariant n)
    a f g hfg

/-- S46: Lorentz covariance of W_n from E1 via BHW. -/
theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_rotation_invariant n)
    Λ f g hfg

/-- S47: Local commutativity of W_n from E3 + edge-of-the-wedge. -/
theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (OS.E3_symmetric n)
    i j f g hsupp hswap

/-- S48: Positive definiteness of W_n from E2 (reflection positivity). -/
theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
  exact bv_positive_definiteness_transfer OS lgc
    (bvt_W OS lgc)
    (fun _ => rfl)
    OS.E2_reflection_positive

/-- S49: Hermiticity of W_n from reality of Schwinger functions. -/
theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  intro n f g hfg
  exact bv_hermiticity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    f g hfg

/-- The cluster property (R4) for the reconstructed Wightman functions.

    The cluster property of the boundary value distributions W_n follows from the
    cluster property E4 of the Schwinger functions via analytic continuation.

    The proof lifts E4 (distributional cluster in Euclidean space) to the Minkowski
    boundary values using the boundary value correspondence: the spatial translations
    commute with the Wick rotation, so the Euclidean factorization at large spacelike
    separation passes to the Minkowski distributional boundary values.

    Ref: OS I (1973), Section 5; OS II (1975), Section VI -/
theorem bvt_cluster (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  sorry

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc
  cluster := bvt_cluster OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    via analytic continuation of Schwinger functions.

    In the OS reconstruction (OS II, 1975), the Wightman functions are obtained
    from the Schwinger functions by analytic continuation, using the linear growth
    condition E0' to control the distribution order growth.

    The pre-Hilbert space uses the Wightman inner product:
      ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f̄_n ⊗ g_m)
    where W_n are the boundary values of the analytic continuation of S_n.

    **Requires the linear growth condition E0'**: Without it, the analytic
    continuation may fail to produce tempered boundary values (OS I, Lemma 8.8 gap).

    Ref: OS II (1975), Sections IV-VI -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :=
  PreHilbertSpace (constructWightmanFunctions OS lgc)

/-! ### The Bridge Theorems -/

-- `IsWickRotationPair` is defined in Reconstruction.lean (available via import).

/-- **Theorem R→E**: Wightman functions produce Schwinger functions satisfying E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation). -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      -- The Schwinger functions are the Wick rotation of the Wightman functions
      IsWickRotationPair OS.S Wfn.W := by
  -- Construct OS axioms from Wightman functions
  refine ⟨⟨constructSchwingerFunctions Wfn,
    constructedSchwinger_tempered Wfn,
    constructedSchwinger_translation_invariant Wfn,
    constructedSchwinger_rotation_invariant Wfn,
    constructedSchwinger_reflection_positive Wfn,
    constructedSchwinger_symmetric Wfn,
    constructedSchwinger_cluster Wfn⟩, ?_⟩
  -- Prove the Wick rotation pair property
  intro n
  -- Use the BHW extension F_ext as the IsWickRotationPair witness.
  -- F_ext = BHW extension, holomorphic on PET (hence on the forward tube).
  -- Its boundary values agree with W_n since F_ext = W_analytic on the forward tube.
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · -- Boundary values: use bhw_distributional_boundary_values directly.
    -- The previous approach tried to show x + iεη ∈ ForwardTube, which is false
    -- due to coordinate convention mismatch (absolute vs difference coordinates).
    intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

/-- **Theorem E'→R'**: OS axioms with linear growth condition produce Wightman functions.

    The Wightman functions are the boundary values of the analytic continuation
    of the Schwinger functions to the forward tube. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the Schwinger functions
      IsWickRotationPair OS.S Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  -- The analytic continuation, boundary values, and euclidean restriction are
  -- exactly the fields constructed inside `boundary_values_tempered`.
  have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
  exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ### Wired Corollaries

The theorem wiring to canonical names now lives in
`Wightman/Reconstruction/Main.lean`. The `_full` theorems above remain the
implementation-level results used by that wiring layer. -/

end
