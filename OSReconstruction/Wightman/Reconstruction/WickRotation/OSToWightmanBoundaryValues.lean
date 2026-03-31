/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

/-!
# OS to Wightman Boundary Values and Transfers

This file continues the `E'→R'` reconstruction chain after
`full_analytic_continuation`:

- tempered boundary values on the forward tube
- transfer of the Wightman axioms from the OS side
- the bridge theorems `wightman_to_os_full` and `os_to_wightman_full`

The semigroup and analytic-continuation stack now lives across
`OSToWightmanSemigroup.lean`, `OSToWightmanBase.lean`, and
`OSToWightman.lean`.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem boundary_values_from_flatBoundaryData {d : ℕ} [NeZero d]
    (n : ℕ)
    {F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hBVflat : ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
        (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ x : Fin (n * (d + 1)) → ℝ,
              (F_analytic ∘ (flattenCLEquiv n (d + 1)).symm)
                (fun i => ↑(x i) + ε * ↑(η i) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Tflat f))) :
    ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F_analytic ∘ e.symm
  let pushforward : SchwartzNPoint d n →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm
  let W : SchwartzNPoint d n →L[ℂ] ℂ := Tflat.comp pushforward
  refine ⟨W, ?_⟩
  intro f η hη
  have hηflat : eR η ∈ ForwardConeFlat d n :=
    ⟨η, (inForwardCone_iff_mem_forwardConeAbs η).mp hη, rfl⟩
  have hflat :
      Filter.Tendsto
        (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Tflat (pushforward f))) :=
    by simpa [G] using hBVflat (pushforward f) (eR η) hηflat
  have hEq :
      (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
      =
      (fun ε : ℝ =>
        ∫ y : NPointDomain d n,
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (f y)) := by
    funext ε
    rw [integral_flatten_change_of_variables n (d + 1)
      (fun x : Fin (n * (d + 1)) → ℝ =>
        G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))]
    congr 1
    ext y
    have hFarg :
        G (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) =
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) := by
      change F_analytic (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) =
        F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I)
      congr 1
      ext k μ
      have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
        simp [eR, flattenCLEquivReal_apply]
      have hηk : eR η (finProdFinEquiv (k, μ)) = η k μ := by
        simp [eR, flattenCLEquivReal_apply]
      rw [show (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) k μ =
          (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) (finProdFinEquiv (k, μ)) by
            simp [e, flattenCLEquiv_symm_apply]]
      simp [hyk, hηk]
    have hfarg : pushforward f (eR y) = f y := by
      simp [pushforward, eR]
    rw [hFarg, hfarg]
  rw [hEq] at hflat
  simpa [W, G, pushforward] using hflat

/-! ### Phase 4: Tempered boundary values

**Critical**: E0' (linear growth condition) is essential for temperedness.
Without growth control, boundary values might fail to be tempered
(the gap in OS I Lemma 8.8). E0' gives |W_n(f)| <= C_n * ||f||_{s,n}
where C_n has at most factorial growth.

Ref: OS II, Section VI -/

/-- The remaining analytic work behind `boundary_values_tempered` is to package
the flattened continuation `G` into an honest tempered Fourier-Laplace
boundary-value datum on `ForwardConeFlat`.

This isolates the missing flat-tempered package from the already-formalized
transport back to `SchwartzNPoint d n` in
`boundary_values_tempered_of_flatTempered`.

Unlike the generic transport theorem below, this phase-4 surface is only about
the specific analytic continuation produced by `full_analytic_continuation OS lgc n`.
Tempered boundary values are not claimed for an arbitrary holomorphic forward-tube
function. -/
private theorem full_analytic_continuation_flat_boundaryValueData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    let F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
      (full_analytic_continuation OS lgc n).choose
    let G : (Fin (n * (d + 1)) → ℂ) → ℂ :=
      F_analytic ∘ (flattenCLEquiv n (d + 1)).symm
    ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
          (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin (n * (d + 1)) → ℝ,
              G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Tflat f)) := by
  sorry

/--
The continuous-linear boundary-value witness is the only remaining Phase-4 input
needed by the OS-specific reconstruction theorem. Once the flattened continuation
carries an honest boundary-value functional on Schwartz tests, it transports back
to `NPointDomain` and constructs the required continuous linear functional.

So the remaining content here is exactly the theorem producing that honest
flattened boundary-value datum for the specific `F_analytic` supplied by
`full_analytic_continuation`.
-/
theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      Continuous W_n ∧
      IsLinearMap ℂ W_n ∧
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f))) ∧
      (∀ (f : ZeroDiagonalSchwartz d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x)) := by
  let hcont := full_analytic_continuation OS lgc n
  let F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ := hcont.choose
  have hF_hol : DifferentiableOn ℂ F_analytic (ForwardTube d n) := hcont.choose_spec.1
  have hF_euclid :
      ∀ (f : ZeroDiagonalSchwartz d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x) := hcont.choose_spec.2
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F_analytic ∘ (flattenCLEquiv n (d + 1)).symm
  obtain ⟨Tflat, hBVflat⟩ :
      ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
        ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
            (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
            Filter.Tendsto (fun ε : ℝ =>
              ∫ x : Fin (n * (d + 1)) → ℝ,
                G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Tflat f)) := by
    simpa [G] using
      full_analytic_continuation_flat_boundaryValueData (d := d) OS lgc n
  obtain ⟨W, hW_bv⟩ :=
    boundary_values_from_flatBoundaryData (d := d) n Tflat hBVflat
  refine ⟨W, F_analytic, W.continuous, ?_, hF_hol, hW_bv, fun f => hF_euclid f⟩
  constructor
  · intro f g
    exact map_add W f g
  · intro c f
    exact map_smul W c f

/-! ### Constructing WightmanFunctions from OS Data

Each Wightman axiom is derived from the corresponding OS axiom via analytic
continuation. The helper lemmas below capture each derivation. -/

/-- The n-point Wightman distribution `W_n` extracted from `boundary_values_tempered`. -/
def bvt_W (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    SchwartzNPoint d n → ℂ :=
  (boundary_values_tempered OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`. -/
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
    ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f.1 x) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.2

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n -/

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
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f.1 x)) :
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
  let f0 : ZeroDiagonalSchwartz d 0 := ⟨f, by
    intro k x hx
    rcases hx with ⟨i, _, _, _⟩
    exact Fin.elim0 i⟩
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f0 := by simpa [I0, f0] using (hEuclid f0).symm
    _ = f 0 := lgc.normalized_zero f0

private theorem boundary_ray_translation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x i + a) =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  let aN : NPointDomain d n := fun _ => a
  let gfun : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f x
  have hga :
      (fun x : NPointDomain d n => gfun (x + aN)) =
        fun x : NPointDomain d n =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
    ext x
    calc
      gfun (x + aN)
          = F_n (fun k μ => ↑((x + aN) k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
              rfl
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
            congr
            ext k μ
            simp [aN, Pi.add_apply, add_sub_cancel_right]
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
            rfl
  rw [← hga, MeasureTheory.integral_add_right_eq_self gfun aN]
  simp only [gfun]
  congr 1
  ext x
  exact congrArg (fun z : ℂ => z * f x) (hF_inv a x η ε)

private theorem bv_translation_invariance_transfer_of_F_invariant
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  intro a f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    refine Filter.Eventually.of_forall ?_
    intro ε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun i => x i + a) := by
      congr 1
      ext x
      have hxg : g x = f (fun i => x i + a) := by
        simpa using hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => x i + a) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_translation_invariant_of_F_invariant (d := d) n F_n hF_inv a f η ε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

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
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1 : ∀ (a : SpacetimeDim d) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x i + a)) →
      OS.S n f = OS.S n g) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  have hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
        F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
    sorry
  exact bv_translation_invariance_transfer_of_F_invariant (d := d) n W_n F_n hBV hF_inv

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
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
      OS.S n f = OS.S n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  sorry

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
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE3 : ∀ (σ : Equiv.Perm (Fin n)) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
      OS.S n f = OS.S n g) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  sorry

theorem bv_positive_definiteness_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_eq : ∀ n, W n = bvt_W OS lgc n)
    (hE2 : ∀ (F : BorchersSequence d),
      (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) →
      (OSInnerProduct d OS.S F F).re ≥ 0) :
    ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0 := by
  sorry

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
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE0_real : ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
      starRingEnd ℂ (OS.S n f) = OS.S n g) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  sorry

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

theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E3_symmetric n)
    i j f g hsupp hswap

theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
  exact bv_positive_definiteness_transfer OS lgc
    (bvt_W OS lgc)
    (fun _ => rfl)
    OS.E2_reflection_positive

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
    (OS.E0_reality n)
    f g hfg

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
    data. -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
  OSPreHilbertSpace OS

/-! ### The Bridge Theorems -/

theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  intro n
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.schwinger Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
  exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
    h.2.2.1, h.2.2.2.1, fun f => by
      simpa [OsterwalderSchraderAxioms.schwinger] using h.2.2.2.2 f⟩

end
