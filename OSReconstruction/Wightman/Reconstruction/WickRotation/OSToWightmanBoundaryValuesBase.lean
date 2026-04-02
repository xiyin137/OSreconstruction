/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.SCV.TubeBoundaryValues

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

/-- Pure boundary-value existence on the forward tube from holomorphy plus a
global polynomial-growth bound.

This is the honest remaining SCV-shaped ingredient on the active OS route: once
the chosen continuation is known to be holomorphic on `ForwardTube d n` and to
satisfy a global real-direction growth estimate there, the rest of the
boundary-value packaging is formal. -/
private theorem forwardTube_boundaryValueData_of_polyGrowth
    (n : ℕ)
    {F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F_analytic (ForwardTube d n))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ ForwardTube d n,
      ‖F_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)) := by
  simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using
    SCV.tube_boundaryValueData_of_polyGrowth
      (C := ForwardConeAbs d n)
      (hC_open := forwardConeAbs_isOpen d n)
      (hC_conv := forwardConeAbs_convex d n)
      (hC_cone := by
        intro y hy t ht
        exact forwardConeAbs_smul d n t ht y hy)
      (hC_salient := forwardConeAbs_salient d n)
      (hF_hol := by
        simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF_hol)
      C_bd N hC
      (hF_growth := by
        intro z hz
        exact hF_growth z ((by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz)))

/-- The remaining analytic work behind `boundary_values_tempered` is to produce
an honest boundary-value functional for the specific continuation extracted from
`full_analytic_continuation_with_growth OS lgc n`.

This is the exact OS-side phase-4 datum the active reconstruction path uses:
a continuous linear functional on `SchwartzNPoint d n` together with the raywise
boundary-value convergence statement. No flattened witness or generic tempered
Fourier-Laplace package is needed at this stage. -/
private theorem full_analytic_continuation_boundaryValueData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
              (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)) := by
  let F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
  have hF_hol : DifferentiableOn ℂ F_analytic (ForwardTube d n) :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.1
  have hGrowthPkg :
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d n,
          ‖F_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    rcases (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec with
      ⟨_hhol, hrest⟩
    rcases hrest with ⟨_hF_euclid, hrest⟩
    rcases hrest with ⟨_hF_perm, hrest⟩
    rcases hrest with ⟨_hF_trans, hrest⟩
    exact hrest.2
  obtain ⟨C_bd, N, hC, hgrowth⟩ :=
    hGrowthPkg
  obtain ⟨W, hW⟩ :=
    forwardTube_boundaryValueData_of_polyGrowth
      (d := d) (n := n)
      (F_analytic := F_analytic)
      hF_hol
      C_bd N hC hgrowth
  refine ⟨W, ?_⟩
  intro f η hη
  exact hW f η hη

/--
The continuous boundary-value witness is the only remaining Phase-4 input needed
by the OS-specific reconstruction theorem. Once the chosen continuation carries
an honest boundary-value functional on `SchwartzNPoint d n`, the rest of the
Wightman packaging is formal.
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
          F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        F_analytic (fun j => z (σ j)) = F_analytic z) ∧
      (∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        F_analytic (fun j => z j + a) = F_analytic z) := by
  obtain ⟨W, hW_bv⟩ :
      ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
        ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (W f)) :=
    full_analytic_continuation_boundaryValueData (d := d) OS lgc n
  have hF_hol :
      DifferentiableOn ℂ
        ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose)
        (ForwardTube d n) :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.1
  have hF_euclid :
      ∀ (f : ZeroDiagonalSchwartz d n),
        OS.S n f = ∫ x : NPointDomain d n,
          (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
            (fun k => wickRotatePoint (x k)) * (f.1 x) :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.1
  have hF_perm :
      ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
          (fun j => z (σ j)) =
        (full_analytic_continuation_with_symmetry_growth OS lgc n).choose z :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.1
  have hF_trans :
      ∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
          (fun j => z j + a) =
        (full_analytic_continuation_with_symmetry_growth OS lgc n).choose z :=
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.1
  refine ⟨W, (full_analytic_continuation_with_symmetry_growth OS lgc n).choose, W.continuous,
    ?_, hF_hol, hW_bv, (fun f => hF_euclid f), hF_perm, hF_trans⟩
  · constructor
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
  (full_analytic_continuation_boundaryValueData (d := d) OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`. -/
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (full_analytic_continuation_with_symmetry_growth OS lgc n).choose

theorem bvt_W_continuous (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    Continuous (bvt_W OS lgc n) :=
  (full_analytic_continuation_boundaryValueData (d := d) OS lgc n).choose.continuous

theorem bvt_W_linear (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    IsLinearMap ℂ (bvt_W OS lgc n) := by
  constructor
  · intro f g
    exact map_add (full_analytic_continuation_boundaryValueData (d := d) OS lgc n).choose f g
  · intro c f
    exact map_smul (full_analytic_continuation_boundaryValueData (d := d) OS lgc n).choose c f

theorem bvt_F_holomorphic (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    DifferentiableOn ℂ (bvt_F OS lgc n) (ForwardTube d n) :=
  (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.1

theorem bvt_boundary_values (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n f)) :=
  (full_analytic_continuation_boundaryValueData (d := d) OS lgc n).choose_spec

theorem bvt_euclidean_restriction (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f.1 x) :=
  (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.1

/-- The generic OS one-variable holomorphic bridge specialized to the chosen
boundary-value witness `bvt_F`. This is the direct BV-side connection between
positive-time OS test pairs and the reconstructed `ξ`-shifted witness integrals. -/
theorem bvt_exists_singleSplit_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y := by
  simpa using
    exists_singleSplit_xiShift_holomorphicValue
      (d := d) (OS := OS) (lgc := lgc)
      (hm := hm) (Ψ := bvt_F OS lgc (n + m))
      (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
      (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)

/-- Two-point specialization of `bvt_exists_singleSplit_xiShift_holomorphicValue`.
This is the concrete BV-side holomorphic shell behind the later one-point
spectral comparisons. -/
theorem bvt_exists_twoPoint_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            bvt_F OS lgc 2
                (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
  simpa using
    exists_twoPoint_xiShift_holomorphicValue
      (d := d) (OS := OS) (lgc := lgc)
      (Ψ := bvt_F OS lgc 2)
      (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc 2)
      (χ := χ) (h := h)
      (hχ_pos := hχ_pos) (hh_pos := hh_pos) (hh_compact := hh_compact)

/-- The concrete one-point spectral Laplace shell specialized to `bvt_F`. This
is the direct BV-side bridge from the reconstructed witness to the OS Hilbert
semigroup data on positive real times. -/
theorem bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      ∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
            (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (χ (y 0) * g (y 1)) := by
  simpa using
    selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc)
      (Ψ := bvt_F OS lgc 2)
      (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc 2)
      (χ := χ) (g := g)
      (hχ_pos := hχ_pos) (hg_pos := hg_pos)
      (hg_compact := hg_compact) (t := t) ht

private theorem onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (a : SpacetimeDim d) (ha0 : a 0 = 0) :
    tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-a) g) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  have hsup :
      (((onePointToFin1CLM d (SCV.translateSchwartz (-a) g) : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) =
        (((translateSchwartzNPoint (d := d) a
            (onePointToFin1CLM d g : SchwartzNPoint d 1)) :
            NPointDomain d 1 → ℂ)) := by
    ext x
    simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
  rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-a) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    tsupport (((translateSchwartzNPoint (d := d) a
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) :
      NPointDomain d 1 → ℂ)) from congr_arg tsupport hsup]
  exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (d := d) a ha0 (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos

private theorem onePointToFin1_translate_spatial_hasCompactSupport_local
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (a : SpacetimeDim d) :
    HasCompactSupport (((onePointToFin1CLM d (SCV.translateSchwartz (-a) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
  have hspace : HasCompactSupport ((SCV.translateSchwartz (-a) g : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) := by
    simpa [SCV.translateSchwartz_apply, sub_eq_add_neg] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-a))
  simpa [onePointToFin1CLM] using
    (hspace.comp_homeomorph
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))

private def timeReflectionNHomeomorph_local {n : ℕ} :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := timeReflectionN d
  invFun := timeReflectionN d
  left_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  right_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)

private def translateNPointDomainHomeomorph_local {n : ℕ}
    (a : SpacetimeDim d) :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := fun x i => x i - a
  invFun := fun x i => x i + a
  left_inv x := by
    ext i μ
    simp
  right_inv x := by
    ext i μ
    simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub continuous_const
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).add continuous_const

private theorem onePointToFin1_hasCompactSupport_local
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    HasCompactSupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) := by
  simpa [onePointToFin1CLM] using
    (hg_compact.comp_homeomorph
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))

private theorem osConj_onePointToFin1_hasCompactSupport_local
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    HasCompactSupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d g : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) := by
  have hbase :
      HasCompactSupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) :=
    onePointToFin1_hasCompactSupport_local (d := d) g hg_compact
  have hreflect :
      HasCompactSupport (fun x : NPointDomain d 1 =>
        ((onePointToFin1CLM d g : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)
          (timeReflectionN d x)) := by
    simpa using hbase.comp_homeomorph (timeReflectionNHomeomorph_local (d := d) (n := 1))
  simpa [SchwartzNPoint.osConj_apply] using
    hreflect.comp_left (g := starRingEnd ℂ) (map_zero _)

private theorem onePointToFin1_tsupport_positive_of_ordered_local
    (g : SchwartzSpacetime d)
    (hg_ord : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  let u : SpacetimeDim d → NPointDomain d 1 :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).symm
  have hu : Continuous u :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).symm.continuous
  have hx1 : u x ∈ tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) := by
    by_contra hx1
    have hzero : x ∉ tsupport (g : SpacetimeDim d → ℂ) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx1 ⊢
      simpa [u, onePointToFin1CLM_apply] using
        hx1.comp_tendsto (hu.continuousAt.tendsto : Filter.Tendsto u (nhds x) (nhds (u x)))
    exact hzero hx
  have hpos0 : 0 < (u x 0) 0 := (hg_ord hx1 0).1
  simpa [u] using hpos0

private theorem osSpatialTranslateHilbert_single_onePoint_eq_of_ordered_local
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_ord : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (a : Fin d → ℝ) :
    let a0 : SpacetimeDim d := Fin.cons 0 a
    let g_translated := SCV.translateSchwartz (-a0) g
    let hg_translated_ord :
        tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
      onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
        (d := d) g hg_ord a0 (by simp [a0])
    (osSpatialTranslateHilbert OS a)
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              hg_ord⟧) : OSHilbertSpace OS)) =
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
              hg_translated_ord⟧) : OSHilbertSpace OS)) := by
  dsimp
  let hg_pos :
      tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} :=
    onePointToFin1_tsupport_positive_of_ordered_local (d := d) g hg_ord
  simpa [hg_pos] using
    osSpatialTranslateHilbert_single_onePoint_eq
      (d := d) OS g hg_pos a

private theorem osSpatialTranslateHilbert_single_eq_of_ordered_local
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (a : Fin d → ℝ) :
    let a0 : SpacetimeDim d := Fin.cons 0 a
    let f_translated := translateSchwartzNPoint (d := d) a0 f
    let hf_translated_ord :
        tsupport (((f_translated : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n :=
      translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a0 (by simp [a0]) f hf_ord
    (osSpatialTranslateHilbert OS a)
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS)) =
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single n f_translated hf_translated_ord⟧) :
            OSHilbertSpace OS)) := by
  simpa using
    osSpatialTranslateHilbert_single_eq
      (d := d) OS f hf_ord a

/-- The translated single-split OS Hilbert matrix element is exactly the
corresponding Euclidean Schwinger tensor term. This is the literal `t = 0`
large-spatial quantity that appears in the current BV cluster support route. -/
private theorem osInner_single_translate_spatial_right_eq_schwinger_local
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (a : Fin d → ℝ) :
    @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
      ((osSpatialTranslateHilbert OS a)
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))) := by
  rw [osSpatialTranslateHilbert_single_eq_of_ordered_local
    (d := d) OS g hg_ord a]
  rw [UniformSpace.Completion.inner_coe]
  change OSInnerProduct d OS.S
      (BorchersSequence.single n f)
      (BorchersSequence.single m
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)))
  simpa using
    (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
      (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))

/-- Ordered positive-time support forces the OS-conjugated left factor onto the
strict ordered negative-time region, hence away from the coincidence locus. -/
private theorem VanishesToInfiniteOrderOnCoincidence_osConj_of_tsupport_subset_orderedPositiveTimeRegion_local
    {n : ℕ} (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    VanishesToInfiniteOrderOnCoincidence (f.osConj) := by
  have hosConj :
      tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n := by
    intro x hx i
    have hxpre_conj :
        x ∈ tsupport (fun y : NPointDomain d n =>
          starRingEnd ℂ (f (timeReflectionN d y))) := by
      simpa [SchwartzNPoint.osConj_apply] using hx
    have hxpre :
        timeReflectionN d x ∈ tsupport (f : NPointDomain d n → ℂ) := by
      exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
        (f := timeReflectionN d)
        (timeReflectionNHomeomorph_local (d := d) (n := n)).continuous_toFun
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _)
          (fun y : NPointDomain d n => f (timeReflectionN d y))) hxpre_conj)
    have hpos := hf hxpre
    constructor
    · have : 0 < timeReflectionN d x i 0 := (hpos i).1
      simpa [timeReflectionN, timeReflection] using this
    · intro j hij
      have : timeReflectionN d x i 0 < timeReflectionN d x j 0 := (hpos i).2 j hij
      simpa [timeReflectionN, timeReflection] using this
  have hdisj :
      Disjoint
        (tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        (CoincidenceLocus d n) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxsupport hxcoin
    exact
      (not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion
        (hosConj hxsupport)) hxcoin
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint (f := f.osConj) hdisj

/-- BV-side holomorphic shell for a spatially translated right one-point test.
This matches the geometry that later appears in the cluster discussion: the
complex time shift stays in the witness, while the real spatial separation is
carried by translating only the right test function. -/
theorem bvt_exists_twoPoint_xiShift_holomorphicValue_translate_spatial_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (a : SpacetimeDim d) (ha0 : a 0 = 0) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            bvt_F OS lgc 2
                (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * (SCV.translateSchwartz (-a) g) (y 1)) := by
  simpa using
    bvt_exists_twoPoint_xiShift_holomorphicValue
      (d := d) (OS := OS) (lgc := lgc)
      (χ := χ) (h := SCV.translateSchwartz (-a) g)
      (hχ_pos := hχ_pos)
      (hh_pos := onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
        (d := d) g hg_pos a ha0)
      (hh_compact := by
        simpa [SCV.translateSchwartz_apply, sub_eq_add_neg] using
          hg_compact.comp_homeomorph (Homeomorph.addRight (-a)))

/-- Real-axis specialization of
`bvt_exists_twoPoint_xiShift_holomorphicValue_translate_spatial_right`. This
packages the semigroup-side spectral Laplace value against a spatially
translated right one-point test in the exact BV witness form used later by the
cluster route. -/
theorem bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_translate_spatial_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d (SCV.translateSchwartz (-a) g) : SchwartzNPoint d 1)
                (onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
                  (d := d) g hg_pos a ha0)⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      ∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
            (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (χ (y 0) * (SCV.translateSchwartz (-a) g) (y 1)) := by
  simpa using
    bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc)
      (χ := χ) (g := SCV.translateSchwartz (-a) g)
      (hχ_pos := hχ_pos)
      (hg_pos := onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
        (d := d) g hg_pos a ha0)
      (hg_compact := by
        simpa [SCV.translateSchwartz_apply, sub_eq_add_neg]
          using hg_compact.comp_homeomorph (Homeomorph.addRight (-a)))
      (t := t) ht

/-- General translated-right real-axis `xiShift` bridge for single positive-time
factors. This is the arbitrary `(n,m)` analogue of the specialized one-point
shell theorem above. -/
theorem bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m (translateSchwartzNPoint (d := d) a g)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 g hg_ord))
        (t : ℂ) =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct (translateSchwartzNPoint (d := d) a g)) y := by
  calc
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m (translateSchwartzNPoint (d := d) a g)
          (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) a ha0 g hg_ord))
        (t : ℂ)
      =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              (translateSchwartzNPoint (d := d) a g)))) := by
            exact OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := f) (hf_ord := hf_ord)
              (g := translateSchwartzNPoint (d := d) a g)
              (hg_ord := translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
                (d := d) a ha0 g hg_ord)
              (hg_compact := by
                simpa [translateSchwartzNPoint_apply] using
                  hg_compact.comp_homeomorph
                    (translateNPointDomainHomeomorph_local (d := d) (n := m) a))
              (t := t) ht
    _ =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct (translateSchwartzNPoint (d := d) a g)) y := by
            simpa [translateSchwartzNPoint_timeShiftSchwartzNPoint]
              using schwinger_simpleTensor_timeShift_eq_xiShift
                (d := d) (OS := OS) (hm := hm) (Ψ := bvt_F OS lgc (n + m))
                (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
                (f := f) (hf_ord := hf_ord)
                (g := translateSchwartzNPoint (d := d) a g)
                (hg_ord := translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
                  (d := d) a ha0 g hg_ord)
                (t := t) ht

/-- BV-side polarized semigroup-group Bochner package for arbitrary compact-support
single positive-time tensors in the translated-right geometry. This upgrades the
earlier one-point specialization to the general single-split `(n,m)` shell that
the private cluster frontier actually wants. -/
theorem bvt_exists_polarized_measure_singleSplit_xiShift_translate_spatial_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ)) :
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
    ∃ (ν₁ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₁fin : MeasureTheory.IsFiniteMeasure ν₁)
      (ν₂ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₂fin : MeasureTheory.IsFiniteMeasure ν₂)
      (ν₃ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₃fin : MeasureTheory.IsFiniteMeasure ν₃)
      (ν₄ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₄fin : MeasureTheory.IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (if ht : 0 < t then
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
        else
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG)) =
          (1 / 4 : ℂ) *
            ((∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
  let Ff : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let Gg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m g hg_ord
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦Ff⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦Gg⟧)) : OSHilbertSpace OS))
  have hFf_compact :
      ∀ k,
        HasCompactSupport ((((Ff : BorchersSequence d).funcs k : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) := by
    intro k
    by_cases hk : k = n
    · subst hk
      simpa [Ff, PositiveTimeBorchersSequence.single_toBorchersSequence]
        using hf_compact
    · have hzero :
        ((((Ff : BorchersSequence d).funcs k : SchwartzNPoint d k) :
            NPointDomain d k → ℂ)) = 0 := by
          simp [Ff, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hk]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d k → ℂ))
  have hGg_compact :
      ∀ k,
        HasCompactSupport ((((Gg : BorchersSequence d).funcs k : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) := by
    intro k
    by_cases hk : k = m
    · subst hk
      simpa [Gg, PositiveTimeBorchersSequence.single_toBorchersSequence]
        using hg_compact
    · have hzero :
        ((((Gg : BorchersSequence d).funcs k : SchwartzNPoint d k) :
            NPointDomain d k → ℂ)) = 0 := by
          simp [Gg, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hk]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d k → ℂ))
  obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, hrepr⟩ :=
      exists_polarized_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc Ff Gg hFf_compact hGg_compact
  refine ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, ?_⟩
  intro t a ht_nonneg
  by_cases ht : 0 < t
  · let a0 : SpacetimeDim d := Fin.cons 0 a
    let g_translated := translateSchwartzNPoint (d := d) a0 g
    let hg_translated_ord :
        tsupport (((g_translated : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)) ⊆ OrderedPositiveTimeRegion d m :=
      translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a0 (by simp [a0]) g hg_ord
    let xGa : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g_translated hg_translated_ord⟧)) :
        OSHilbertSpace OS))
    have hshift :
        (osSpatialTranslateHilbert (d := d) OS a) xG = xGa := by
      simpa [xG, xGa, Gg, a0, g_translated, hg_translated_ord] using
        osSpatialTranslateHilbert_single_eq_of_ordered_local
          (d := d) OS g hg_ord a
    have hint :
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
        =
        @inner ℂ (OSHilbertSpace OS) _ xF
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS a) xG)) := by
      calc
        ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
          =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g_translated hg_translated_ord)
              (t : ℂ) := by
                symm
                exact bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right
                  (d := d) (OS := OS) (lgc := lgc)
                  (hm := hm) (f := f) (hf_ord := hf_ord)
                  (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
                  (a := a0) (ha0 := by simp [a0]) (t := t) ht
        _ =
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xGa (t : ℂ) := by
              rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
                (d := d) (OS := OS) (lgc := lgc)
                (F := PositiveTimeBorchersSequence.single n f hf_ord)
                (G := PositiveTimeBorchersSequence.single m g_translated hg_translated_ord)
                (z := (t : ℂ)) (hz := by simpa using ht)]
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xGa) := by
              symm
              exact osTimeShiftHilbertComplex_inner_eq
                (d := d) OS lgc xF xGa (t : ℂ) (by simpa using ht)
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) xG)) := by
                rw [← hshift]
    calc
      (if ht' : 0 < t then
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
      else
        @inner ℂ (OSHilbertSpace OS) _ xF
          ((osSpatialTranslateHilbert (d := d) OS a) xG))
        =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y) := by
              simp [ht]
      _ =
        @inner ℂ (OSHilbertSpace OS) _ xF
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS a) xG)) := hint
      _ =
        (1 / 4 : ℂ) *
          ((∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
            (∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
              simpa [xF, xG, ht] using hrepr t a ht_nonneg
  · simpa [xF, xG, ht] using hrepr t a ht_nonneg

/-- The translated-right canonical `xiShift` shell is right-continuous at
`t = 0` in the exact BV form used by the cluster route. This pays the
small-positive-time part of the eventual-cluster comparison; the remaining
cluster seam is then the large-spatial-translation factorization input. -/
theorem bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (a : Fin d → ℝ) :
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
        else
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (@inner ℂ (OSHilbertSpace OS) _ xF
        ((osSpatialTranslateHilbert OS a) xG))) := by
  let Ff : PositiveTimeBorchersSequence d := PositiveTimeBorchersSequence.single n f hf_ord
  let a0 : SpacetimeDim d := Fin.cons 0 a
  let g_translated : SchwartzNPoint d m := translateSchwartzNPoint (d := d) a0 g
  let hg_translated_ord :
      tsupport (((g_translated : SchwartzNPoint d m) :
        NPointDomain d m → ℂ)) ⊆ OrderedPositiveTimeRegion d m :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a0 (by simp [a0]) g hg_ord
  let Gga : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m g_translated hg_translated_ord
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦Ff⟧) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
  let xGa : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦Gga⟧) : OSHilbertSpace OS))
  have hGga_compact :
      ∀ k,
        HasCompactSupport ((((Gga : BorchersSequence d).funcs k : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) := by
    intro k
    by_cases hk : k = m
    · subst hk
      have htrans_compact :
          HasCompactSupport (((g_translated : SchwartzNPoint d k) :
            NPointDomain d k → ℂ)) := by
        simpa [g_translated, translateSchwartzNPoint_apply, sub_eq_add_neg] using
          hg_compact.comp_homeomorph
            (translateNPointDomainHomeomorph_local (d := d) (n := k) a0)
      simpa [Gga, PositiveTimeBorchersSequence.single_toBorchersSequence] using htrans_compact
    · have hzero :
        ((((Gga : BorchersSequence d).funcs k : SchwartzNPoint d k) :
            NPointDomain d k → ℂ)) = 0 := by
          simp [Gga, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hk]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d k → ℂ))
  have hshift :
      (osSpatialTranslateHilbert OS a) xG = xGa := by
    simpa [xG, xGa, Gga, a0, g_translated, hg_translated_ord] using
      osSpatialTranslateHilbert_single_eq_of_ordered_local
        (d := d) OS g hg_ord a
  have hshift_tendsto :
      Filter.Tendsto
        (fun t : ℝ =>
          if ht : 0 < t then
            osTimeShiftHilbert (d := d) OS lgc t ht xGa
          else
            xGa)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds xGa) := by
    simpa [xGa, Gga] using
      tendsto_osTimeShiftHilbert_nhdsWithin_zero_of_isCompactSupport
        (d := d) OS lgc Gga hGga_compact
  have hinner_tendsto :
      Filter.Tendsto
        (fun t : ℝ =>
          @inner ℂ (OSHilbertSpace OS) _ xF
            (if ht : 0 < t then
              osTimeShiftHilbert (d := d) OS lgc t ht xGa
            else
              xGa))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (@inner ℂ (OSHilbertSpace OS) _ xF xGa)) := by
    have hinner_cont : Continuous fun y : OSHilbertSpace OS =>
        @inner ℂ (OSHilbertSpace OS) _ xF y :=
      continuous_const.inner continuous_id
    exact (hinner_cont.tendsto xGa).comp hshift_tendsto
  have hEq :
      (fun t : ℝ =>
        if ht : 0 < t then
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
        else
          @inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        @inner ℂ (OSHilbertSpace OS) _ xF
          (if ht : 0 < t then
            osTimeShiftHilbert (d := d) OS lgc t ht xGa
          else
            xGa)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    have hIntegral :
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
        =
        @inner ℂ (OSHilbertSpace OS) _ xF
          (osTimeShiftHilbert (d := d) OS lgc t ht_pos xGa) := by
      calc
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
          =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              Ff Gga (t : ℂ) := by
                symm
                simpa [Ff, Gga, a0, g_translated, hg_translated_ord] using
                  bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right
                    (d := d) (OS := OS) (lgc := lgc)
                    (hm := hm) (f := f) (hf_ord := hf_ord) (g := g)
                    (hg_ord := hg_ord) (hg_compact := hg_compact)
                    (a := a0) (ha0 := by simp [a0]) (t := t) ht_pos
        _ =
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xGa (t : ℂ) := by
              simpa [xF, xGa, Ff, Gga] using
                OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
                  (d := d) OS lgc Ff Gga (t : ℂ) (by simpa using ht_pos)
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xF
            (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) xGa) := by
              symm
              exact osTimeShiftHilbertComplex_inner_eq
                (d := d) OS lgc xF xGa (t : ℂ) (by simpa using ht_pos)
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xF
            (osTimeShiftHilbert (d := d) OS lgc t ht_pos xGa) := by
              rw [show osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ) xGa =
                  osTimeShiftHilbert (d := d) OS lgc t ht_pos xGa by
                    simpa [xGa, Gga] using
                      osTimeShiftHilbertComplex_ofReal_eq_of_isCompactSupport
                        (d := d) OS lgc Gga hGga_compact t ht_pos]
    simp [ht_pos, hIntegral]
  have hfinal :
      Filter.Tendsto
        (fun t : ℝ =>
          if ht : 0 < t then
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
          else
            @inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (@inner ℂ (OSHilbertSpace OS) _ xF xGa)) :=
    Filter.Tendsto.congr' hEq.symm hinner_tendsto
  simpa [xF, xG, xGa, Ff, Gga, a0, g_translated, hg_translated_ord, hshift] using hfinal

/-- The translated-right canonical `xiShift` cluster estimate is already formal
once the large-spatial translated OS Hilbert matrix element is controlled. The
small-`t` continuity leg has been fully paid by
`bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`, so
the remaining content is only the large-spatial factorization input. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (hlarge :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
          ‖@inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
  have hlarge' :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
          ‖@inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
    simpa [xF, xG] using hlarge
  intro ε hε
  obtain ⟨R, hR, hlargeR⟩ := hlarge' (ε / 2) (by positivity)
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  have hnear_zero :=
    bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero
      (d := d) OS lgc n m hm f hf_ord hf_compact g hg_ord hg_compact a
  have hnear_inner :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
          (@inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG)) < ε / 2 := by
    have hmetric :=
      Metric.tendsto_nhds.1 hnear_zero (ε / 2) (by positivity)
    filter_upwards [hmetric, self_mem_nhdsWithin] with t ht htt
    have ht_pos : 0 < t := htt
    have ht' :
        dist
          (if ht0 : 0 < t then
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)
          else
            @inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG))
          (@inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG)) < ε / 2 := by
      simpa [xF, xG] using ht
    simpa [ht_pos] using ht'
  filter_upwards [hnear_inner] with t ht
  have hlarge_a :
      dist
        (@inner ℂ (OSHilbertSpace OS) _ xF
          ((osSpatialTranslateHilbert OS a) xG))
        (bvt_W OS lgc n f * bvt_W OS lgc m g) < ε / 2 := by
    simpa [dist_eq_norm] using hlargeR a ha_large
  have hdist :
      dist
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
        (bvt_W OS lgc n f * bvt_W OS lgc m g) < ε := by
    calc
      dist
          (∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
          (bvt_W OS lgc n f * bvt_W OS lgc m g)
        ≤ dist
            (∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
            (@inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG)) +
          dist
            (@inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG))
            (bvt_W OS lgc n f * bvt_W OS lgc m g) := by
              simpa [dist_comm, add_comm] using
                (dist_triangle_right
                  (∫ y : NPointDomain d (n + m),
                    bvt_F OS lgc (n + m)
                        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                      ((f.osConjTensorProduct
                        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
                  (bvt_W OS lgc n f * bvt_W OS lgc m g)
                  (@inner ℂ (OSHilbertSpace OS) _ xF
                    ((osSpatialTranslateHilbert OS a) xG)))
      _ < ε / 2 + ε / 2 := add_lt_add ht hlarge_a
      _ = ε := by ring
  simpa [dist_eq_norm] using hdist

/-- The single-split BV cluster support theorem can equivalently take its
large-spatial input directly in Euclidean Schwinger form, rather than through
the intermediate OS Hilbert matrix element. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (hlarge :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
          ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
  have hlarge' :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
          ‖@inner ℂ (OSHilbertSpace OS) _ xF
              ((osSpatialTranslateHilbert OS a) xG) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
    intro ε hε
    obtain ⟨R, hR, hRbound⟩ := hlarge ε hε
    refine ⟨R, hR, ?_⟩
    intro a ha_large
    simpa [xF, xG, osInner_single_translate_spatial_right_eq_schwinger_local
      (d := d) OS f hf_ord g hg_ord a] using hRbound a ha_large
  exact bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial
    (d := d) (OS := OS) (lgc := lgc) n m hm
    f hf_ord hf_compact g hg_ord hg_compact (by
      simpa [xF, xG] using hlarge')

/-- Euclidean cluster property specialized to the exact translated single-split
shell appearing in the BV cluster route. This isolates the genuine OS-I
large-spatial input before any boundary-value comparison is applied. -/
theorem schwinger_cluster_osConjTensorProduct_translate_spatial_right_local
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ‖OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))) -
          OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)) *
            OS.S m (ZeroDiagonalSchwartz.ofClassical g)‖ < ε := by
  let f0 : ZeroDiagonalSchwartz d n := ZeroDiagonalSchwartz.ofClassical (f.osConj)
  let g0 : ZeroDiagonalSchwartz d m := ZeroDiagonalSchwartz.ofClassical g
  intro ε hε
  obtain ⟨R, hR, hcluster⟩ := OS.E4_cluster n m f0 g0 ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  let a0 : SpacetimeDim d := Fin.cons 0 a
  have ha0 : a0 0 = 0 := by simp [a0]
  let g_translated : SchwartzNPoint d m := translateSchwartzNPoint (d := d) a0 g
  have hg_translated_ord :
      tsupport ((g_translated : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a0 ha0 g hg_ord
  have hf0_vanish :
      VanishesToInfiniteOrderOnCoincidence (f.osConj) :=
    VanishesToInfiniteOrderOnCoincidence_osConj_of_tsupport_subset_orderedPositiveTimeRegion_local
      (d := d) f hf_ord
  have hg0_vanish :
      VanishesToInfiniteOrderOnCoincidence g :=
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
      g hg_ord
  have hga_vanish :
      VanishesToInfiniteOrderOnCoincidence g_translated :=
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
      g_translated hg_translated_ord
  let g_a : ZeroDiagonalSchwartz d m := ZeroDiagonalSchwartz.ofClassical g_translated
  have hg_a :
      ∀ x : NPointDomain d m, g_a.1 x = g0.1 (fun i => x i - a0) := by
    intro x
    simp [g_a, g0, g_translated, a0, translateSchwartzNPoint_apply,
      ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes, hg0_vanish, hga_vanish]
  let fg_a : ZeroDiagonalSchwartz d (n + m) := ZeroDiagonalSchwartz.ofClassical
    (f.osConjTensorProduct g_translated)
  have hfg_vanish :
      VanishesToInfiniteOrderOnCoincidence (f.osConjTensorProduct g_translated) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f) (g := g_translated) hf_ord hg_translated_ord
  have hfg_a :
      ∀ x : NPointDomain d (n + m),
        fg_a.1 x = f0.1 (splitFirst n m x) * g_a.1 (splitLast n m x) := by
    intro x
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConjTensorProduct g_translated) hfg_vanish]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := f.osConj) hf0_vanish]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := g_translated) hga_vanish]
    simp [g_translated, translateSchwartzNPoint_apply, SchwartzNPoint.osConjTensorProduct]
  simpa [f0, g0, a0] using hcluster a0 ha0 (by simpa [a0] using ha_large) g_a hg_a fg_a hfg_a

/-- The translated single-split OS Hilbert matrix element has the exact
large-spatial factorization dictated by the Euclidean cluster axiom. The only
remaining mismatch with the BV cluster target is therefore the comparison of the
single-factor limits. -/
theorem osInner_single_translate_spatial_right_cluster_local
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ‖@inner ℂ (OSHilbertSpace OS) _
            (((show OSPreHilbertSpace OS from
              ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
            ((osSpatialTranslateHilbert OS a)
              (((show OSPreHilbertSpace OS from
                ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))) -
          OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)) *
            OS.S m (ZeroDiagonalSchwartz.ofClassical g)‖ < ε := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
  intro ε hε
  obtain ⟨R, hR, hcluster⟩ :=
    schwinger_cluster_osConjTensorProduct_translate_spatial_right_local
      (d := d) OS n m f hf_ord g hg_ord ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  simpa [xF, xG, osInner_single_translate_spatial_right_eq_schwinger_local
    (d := d) OS f hf_ord g hg_ord a] using hcluster a ha_large

/-- The translated single-split BV cluster estimate follows formally from the
Euclidean OS-I cluster theorem once the two one-factor limits are identified
with the corresponding reconstructed boundary-value functionals. This isolates
the genuine remaining mismatch on the cluster route to those single-factor
comparison statements. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (hleft :
      bvt_W OS lgc n f =
        OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)))
    (hright :
      bvt_W OS lgc m g =
        OS.S m (ZeroDiagonalSchwartz.ofClassical g)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  refine
    bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact ?_
  intro ε hε
  obtain ⟨R, hR, hcluster⟩ :=
    schwinger_cluster_osConjTensorProduct_translate_spatial_right_local
      (d := d) OS n m f hf_ord g hg_ord ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  simpa [hleft, hright] using hcluster a ha_large

private theorem translateSchwartzNPoint_onePointToFin1_eq_translate_local
    (g : SchwartzSpacetime d) (a : SpacetimeDim d) :
    translateSchwartzNPoint (d := d) a (onePointToFin1CLM d g) =
      onePointToFin1CLM d (SCV.translateSchwartz (-a) g) := by
  ext x
  simp [translateSchwartzNPoint_apply, onePointToFin1CLM_apply,
    SCV.translateSchwartz_apply, sub_eq_add_neg]

private theorem onePoint_osConjTensorProduct_translate_spatial_apply_local
    (χ g : SchwartzSpacetime d) (a : Fin d → ℝ) (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a)
          (onePointToFin1CLM d g))) y) =
      χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1) := by
  simpa [translateSchwartzNPoint_onePointToFin1_eq_translate_local]
    using onePoint_osConjTensorProduct_apply
      (d := d) χ (SCV.translateSchwartz (-Fin.cons 0 a) g) y

/-- BV-side polarized semigroup-group Bochner package in the actual translated-right
cluster geometry. This packages one fixed two-point `xiShift` pairing against a
spatially translated right test into a finite polarized measure representation
uniform in the spatial translation parameter. -/
theorem bvt_exists_polarized_measure_twoPoint_xiShift_translate_spatial_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xχ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
          hχ_pos⟧) : OSHilbertSpace OS))
    let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      ⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d g : SchwartzNPoint d 1)
          hg_pos⟧) : OSHilbertSpace OS))
    ∃ (ν₁ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₁fin : MeasureTheory.IsFiniteMeasure ν₁)
      (ν₂ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₂fin : MeasureTheory.IsFiniteMeasure ν₂)
      (ν₃ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₃fin : MeasureTheory.IsFiniteMeasure ν₃)
      (ν₄ : MeasureTheory.Measure (ℝ × (Fin d → ℝ)))
      (_hν₄fin : MeasureTheory.IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (if ht : 0 < t then
          ∫ y : NPointDomain d 2,
            bvt_F OS lgc 2
                (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))
        else
          @inner ℂ (OSHilbertSpace OS) _ xχ
            ((osSpatialTranslateHilbert OS a) xg)) =
          (1 / 4 : ℂ) *
            ((∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
  let χ0 : SchwartzNPoint d 1 :=
    SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ : SchwartzNPoint d 1)
  let g0 : SchwartzNPoint d 1 := onePointToFin1CLM d g
  let Fχ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1 χ0 hχ_pos
  let Gg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1 g0 hg_pos
  let xχ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦Fχ⟧)) : OSHilbertSpace OS))
  let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦Gg⟧)) : OSHilbertSpace OS))
  have hFχ_compact :
      ∀ n,
        HasCompactSupport ((((Fχ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      simpa [Fχ, χ0, PositiveTimeBorchersSequence.single_toBorchersSequence]
        using osConj_onePointToFin1_hasCompactSupport_local (d := d) χ hχ_compact
    · have hzero :
        ((((Fχ : BorchersSequence d).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)) = 0 := by
          simp [Fχ, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hn]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d n → ℂ))
  have hGg_compact :
      ∀ n,
        HasCompactSupport ((((Gg : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      simpa [Gg, g0, PositiveTimeBorchersSequence.single_toBorchersSequence]
        using onePointToFin1_hasCompactSupport_local (d := d) g hg_compact
    · have hzero :
        ((((Gg : BorchersSequence d).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)) = 0 := by
          simp [Gg, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hn]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d n → ℂ))
  obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, hrepr⟩ :=
      exists_polarized_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc Fχ Gg hFχ_compact hGg_compact
  refine ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, ?_⟩
  intro t a ht_nonneg
  by_cases ht : 0 < t
  · let a0 : SpacetimeDim d := Fin.cons 0 a
    let g_translated := SCV.translateSchwartz (-a0) g
    let hg_translated_ord :
        tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
      onePointToFin1_translate_spatial_tsupport_subset_orderedPositiveTime_local
        (d := d) g hg_pos a0 (by simp [a0])
    let xga : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_ord⟧)) : OSHilbertSpace OS))
    have hshift :
        (osSpatialTranslateHilbert (d := d) OS a) xg = xga := by
      simpa [xg, xga, Gg, g0, a0, g_translated, hg_translated_ord] using
        osSpatialTranslateHilbert_single_onePoint_eq_of_ordered_local
          (d := d) OS g hg_pos a
    have hint :
        ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1)) =
          @inner ℂ (OSHilbertSpace OS) _ xχ
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) xg)) := by
      calc
        ∫ y : NPointDomain d 2,
            bvt_F OS lgc 2
                (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))
            =
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              xχ xga (t : ℂ) := by
                symm
                simpa [xχ, xga, χ0, a0, g_translated, hg_translated_ord] using
                  bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_translate_spatial_right
                    (d := d) (OS := OS) (lgc := lgc)
                    (χ := χ) (g := g)
                    (hχ_pos := hχ_pos) (hg_pos := hg_pos) (hg_compact := hg_compact)
                    (a := a0) (ha0 := by simp [a0]) (t := t) ht
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xχ
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xga) := by
              symm
              exact osTimeShiftHilbertComplex_inner_eq
                (d := d) OS lgc xχ xga (t : ℂ) (by simpa using ht)
        _ =
          @inner ℂ (OSHilbertSpace OS) _ xχ
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) xg)) := by
                rw [← hshift]
    calc
      (if ht' : 0 < t then
        ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))
      else
        @inner ℂ (OSHilbertSpace OS) _ xχ
          ((osSpatialTranslateHilbert (d := d) OS a) xg))
          =
        ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1)) := by
              simp [ht]
      _ =
        @inner ℂ (OSHilbertSpace OS) _ xχ
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS a) xg)) := hint
      _ =
        (1 / 4 : ℂ) *
          ((∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
            (∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
              simpa [xχ, xg, ht] using hrepr t a ht_nonneg
  · simpa [xχ, xg, ht] using hrepr t a ht_nonneg

theorem bvt_F_perm (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      bvt_F OS lgc n (fun j => z (σ j)) = bvt_F OS lgc n z :=
  (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.1

theorem bvt_F_translationInvariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
      bvt_F OS lgc n (fun j => z j + a) = bvt_F OS lgc n z :=
  (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.1

def canonicalForwardConeDirection (n : ℕ) : Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ = 0 then (↑(k : ℕ) + 1 : ℝ) else 0

theorem canonicalForwardConeDirection_mem (n : ℕ) :
    InForwardCone d n (canonicalForwardConeDirection (d := d) n) := by
  let η₀ : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i
        split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  rw [inForwardCone_iff_mem_forwardConeAbs]
  intro k
  simp only []
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [canonicalForwardConeDirection, η₀, h]
  · by_cases hμ : μ = 0
    · simp [canonicalForwardConeDirection, η₀, hμ]
      have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hk_pos]
        simp
      rw [this]
      ring
    · simp [canonicalForwardConeDirection, η₀, hμ]

theorem bvt_F_negCanonical (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) -
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
  by
    intro x ε hε
    have hF_negCanonical :
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          starRingEnd ℂ
            ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
              (fun j μ =>
                ↑(x j μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
          (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
            (fun j μ =>
              ↑(x j μ) -
                ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I) := by
      rcases (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec with
        ⟨_hhol, hrest⟩
      rcases hrest with ⟨_hF_euclid, hrest⟩
      rcases hrest with ⟨_hF_perm, hrest⟩
      rcases hrest with ⟨_hF_trans, hrest⟩
      exact hrest.1
    change
      starRingEnd ℂ
        ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
          (fun j μ =>
            ↑(x j μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
      (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
        (fun j μ =>
          ↑(x j μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)
    simpa [bvt_F, canonicalForwardConeDirection] using
      hF_negCanonical x ε hε

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

private theorem bvt_F_one_eq_zero_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (z : Fin 1 → Fin (d + 1) → ℂ) :
    bvt_F OS lgc 1 z = bvt_F OS lgc 1 (fun _ _ => 0) := by
  let a : Fin (d + 1) → ℂ := fun μ => - z 0 μ
  have htrans := bvt_F_translationInvariant (d := d) OS lgc 1 z a
  have hzero : (fun j => z j + a) = (fun _ _ => 0) := by
    funext j μ
    fin_cases j
    simp [a]
  have hzero' : bvt_F OS lgc 1 (fun _ _ => 0) = bvt_F OS lgc 1 z := by
    simpa [hzero] using htrans
  exact hzero'.symm

private theorem bvt_W_one_eq_const_integral_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    bvt_W OS lgc 1 f =
      bvt_F OS lgc 1 (fun _ _ => 0) *
        ∫ x : NPointDomain d 1, f x := by
  let c : ℂ := bvt_F OS lgc 1 (fun _ _ => 0)
  have hBV :=
    bvt_boundary_values (d := d) OS lgc 1 f
      (canonicalForwardConeDirection (d := d) 1)
      (canonicalForwardConeDirection_mem (d := d) 1)
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d 1,
          bvt_F OS lgc 1 (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I) * f x)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc
      ∫ x : NPointDomain d 1,
          bvt_F OS lgc 1 (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I) * f x
          =
        ∫ x : NPointDomain d 1, c * f x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [bvt_F_one_eq_zero_local (d := d) (OS := OS) (lgc := lgc)
            (z := fun k μ =>
              ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I)]
      _ = c * ∫ x : NPointDomain d 1, f x := by
          rw [MeasureTheory.integral_const_mul]
  have hconst :
      Filter.Tendsto
        (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c * ∫ x : NPointDomain d 1, f x)) :=
    tendsto_const_nhds
  have hBV' :
      Filter.Tendsto
        (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc 1 f)) :=
    Filter.Tendsto.congr' hEq hBV
  exact tendsto_nhds_unique hBV' hconst

private theorem schwinger_one_eq_const_integral_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical f) =
      bvt_F OS lgc 1 (fun _ _ => 0) *
        ∫ x : NPointDomain d 1, f x := by
  let c : ℂ := bvt_F OS lgc 1 (fun _ _ => 0)
  calc
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical f)
        =
      ∫ x : NPointDomain d 1,
        bvt_F OS lgc 1 (fun k => wickRotatePoint (x k)) *
          (ZeroDiagonalSchwartz.ofClassical f).1 x := by
          simpa using
            bvt_euclidean_restriction (d := d) OS lgc 1
              (ZeroDiagonalSchwartz.ofClassical f)
    _ =
      ∫ x : NPointDomain d 1,
        bvt_F OS lgc 1 (fun k => wickRotatePoint (x k)) * f x := by
          have hvan : VanishesToInfiniteOrderOnCoincidence f :=
            VanishesToInfiniteOrderOnCoincidence.one (d := d) f
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes (f := f) hvan]
    _ = ∫ x : NPointDomain d 1, c * f x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [bvt_F_one_eq_zero_local (d := d) (OS := OS) (lgc := lgc)
            (z := fun k => wickRotatePoint (x k))]
    _ = c * ∫ x : NPointDomain d 1, f x := by
          rw [MeasureTheory.integral_const_mul]

/-- In one variable, translation invariance forces the reconstructed boundary
value functional to agree with the Euclidean Schwinger functional on all
Schwartz tests. This is the first exact one-factor comparison theorem on the BV
cluster lane. -/
theorem bvt_W_one_eq_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    bvt_W OS lgc 1 f =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical f) := by
  rw [bvt_W_one_eq_const_integral_local (d := d) (OS := OS) (lgc := lgc) f,
    schwinger_one_eq_const_integral_local (d := d) (OS := OS) (lgc := lgc) f]

/-- Spacetime one-point tests therefore agree with their Euclidean Schwinger
values after boundary-value reconstruction, without additional support
hypotheses. -/
theorem bvt_W_onePointToFin1_eq_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d) :
    bvt_W OS lgc 1 (onePointToFin1CLM d g) =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d g)) := by
  simpa using bvt_W_one_eq_schwinger (d := d) OS lgc (onePointToFin1CLM d g)

private theorem schwinger_onePointToFin1_osConj_eq_star_local
    (OS : OsterwalderSchraderAxioms d) (χ : SchwartzSpacetime d) :
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))) =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
  let f : ZeroDiagonalSchwartz d 1 :=
    ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)
  let g : ZeroDiagonalSchwartz d 1 :=
    ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
  have hreal :
      starRingEnd ℂ (OS.S 1 f) = OS.S 1 g := by
    refine OS.E0_reality (n := 1) (f := f) (g := g) ?_
    intro x
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := onePointToFin1CLM d χ)
      (VanishesToInfiniteOrderOnCoincidence.one (d := d) _)]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (VanishesToInfiniteOrderOnCoincidence.one (d := d) _)]
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply, timeReflectionN]
  simpa [f, g] using hreal.symm

/-- The BV reconstruction already identifies the left one-point `osConj` factor
with the conjugate of the ordinary one-point Schwinger value. This is the exact
mixed one-point comparison used later on the translated two-point cluster lane. -/
theorem bvt_W_onePointToFin1_osConj_eq_star_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ : SchwartzSpacetime d) :
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    starRingEnd ℂ
      (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
  calc
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))) := by
          simpa using
            bvt_W_one_eq_schwinger (d := d) OS lgc
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
    _ =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
          exact schwinger_onePointToFin1_osConj_eq_star_local (d := d) OS χ

/-- On the actual two-point translated-right cluster lane, the right one-point
factor comparison is now automatic. The only remaining mismatch is the left
one-point `osConj` comparison. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  let χ0 : SchwartzNPoint d 1 :=
    SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ : SchwartzNPoint d 1)
  let g0 : SchwartzNPoint d 1 := onePointToFin1CLM d g
  have hcluster :=
    bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison
      (d := d) (OS := OS) (lgc := lgc) 1 1 (by omega)
      χ0 hχ_pos
      (osConj_onePointToFin1_hasCompactSupport_local (d := d) χ hχ_compact)
      g0 hg_pos
      (onePointToFin1_hasCompactSupport_local (d := d) g hg_compact)
      (by simpa [χ0, SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
            timeReflectionN, timeReflection_timeReflection] using hleft)
      (bvt_W_onePointToFin1_eq_schwinger (d := d) OS lgc g)
  intro ε hε
  obtain ⟨R, hR, hclusterR⟩ := hcluster ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  filter_upwards [hclusterR a ha_large] with t ht
  have hIntEq :
      ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((χ0.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g0)) y)
        =
      ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [onePoint_osConjTensorProduct_translate_spatial_apply_local
      (d := d) χ g a y]
  rw [← hIntEq]
  simpa [χ0, g0] using ht

/-- On the actual two-point translated-right cluster lane, it is enough that
the ordinary one-point Schwinger value of the left factor is real. The mixed
BV-vs-Schwinger comparison for the `osConj` left factor is already paid by
`bvt_W_onePointToFin1_osConj_eq_star_schwinger`. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorReality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ_real :
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) =
          OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  have hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
    calc
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
            exact bvt_W_onePointToFin1_osConj_eq_star_schwinger (d := d) OS lgc χ
      _ = OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := hχ_real
  exact bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (d := d) (OS := OS) (lgc := lgc) χ g hχ_pos hg_pos hχ_compact hg_compact hleft

/-- For a real-valued time-reflection-invariant one-point test, the mixed
`osConj` one-point BV factor already agrees with the ordinary one-point
Schwinger value. This makes the two-point translated cluster lane theorem-based
on the natural self-adjoint one-point shell. -/
theorem bvt_W_onePointToFin1_osConj_eq_schwinger_of_real_reflectionInvariant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ : SchwartzSpacetime d)
    (hχ_real : ∀ x, (χ x).im = 0)
    (hχ_reflect : ∀ x, χ (timeReflection d x) = χ x) :
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
  have hosConj_eq :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)
        =
      (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    have him : (χ (timeReflection d (x 0))).im = 0 :=
      hχ_real (timeReflection d (x 0))
    have hstar :
        starRingEnd ℂ (χ (timeReflection d (x 0))) =
          χ (timeReflection d (x 0)) := by
      apply Complex.ext <;> simp [him]
    calc
      (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)) x
        = starRingEnd ℂ (χ (timeReflection d (x 0))) := by
            simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply, timeReflectionN]
      _ = χ (timeReflection d (x 0)) := hstar
      _ = χ (x 0) := hχ_reflect (x 0)
      _ = (onePointToFin1CLM d χ : SchwartzNPoint d 1) x := by
            simp [onePointToFin1CLM_apply]
  simpa [hosConj_eq] using bvt_W_onePointToFin1_eq_schwinger (d := d) OS lgc χ

/-- On the actual two-point translated-right cluster lane, it is enough that
the left one-point cutoff is self-adjoint in the explicit test-function sense:
real-valued and invariant under Euclidean time reflection. This removes the
remaining abstract scalar reality hypothesis from the natural reflected-real
one-point shell. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorSelfAdjoint
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ_real : ∀ x, (χ x).im = 0)
    (hχ_reflect : ∀ x, χ (timeReflection d x) = χ x) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  have hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
    exact bvt_W_onePointToFin1_osConj_eq_schwinger_of_real_reflectionInvariant
      (d := d) OS lgc χ hχ_real hχ_reflect
  exact bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (d := d) (OS := OS) (lgc := lgc) χ g hχ_pos hg_pos hχ_compact hg_compact hleft

private theorem boundary_ray_translation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
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
  exact congrArg (fun z : ℂ => z * f x) (hF_inv a x η ε hε)

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
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
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
        boundary_ray_translation_invariant_of_F_invariant (d := d) n F_n hF_inv a f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_translation_invariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  exact bv_translation_invariance_transfer_of_F_invariant (d := d) n W_n F_n hBV hF_inv

theorem integral_lorentz_eq_self_full {n : ℕ}
    (Λ : LorentzGroup d)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have habs : |Λ.val.det| = 1 := by
    rcases LorentzGroup.det_eq_pm_one Λ with hdet | hdet
    · rw [hdet]
      simp
    · rw [hdet]
      simp
  have hdet_ne : Λ.val.det ≠ 0 := by
    intro hzero
    rw [hzero] at habs
    norm_num at habs
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmv : (fun v => Λ.val.mulVec v) = Matrix.toLin' Λ.val := by
    ext v
    simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d + 1) → ℝ => Λ.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]
    constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [habs]
  let e : (Fin n → Fin (d + 1) → ℝ) ≃ᵐ (Fin n → Fin (d + 1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.mulVec (a i)
        invFun := fun a i => Λ⁻¹.val.mulVec (a i)
        left_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛinv_mul]
        right_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛ_mul_inv] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_Λ.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Λinv.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

private noncomputable def lorentzInvCLEquivFull
    (Λ : LorentzGroup d) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' (Λ⁻¹).val
          invFun := Matrix.toLin' Λ.val
          left_inv := fun v => by
            show (Matrix.toLin' Λ.val) ((Matrix.toLin' (Λ⁻¹).val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛ_mul_inv, Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' (Λ⁻¹).val) ((Matrix.toLin' Λ.val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛinv_mul, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

private noncomputable def lorentzCompSchwartzFull {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight
      (fun (_ : Fin n) => lorentzInvCLEquivFull (d := d) Λ)) f

private theorem lorentzCompSchwartzFull_apply {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartzFull (d := d) Λ f).toFun x =
      f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartzFull, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquivFull]
  rfl

private theorem boundary_ray_lorentz_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I))
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hΛinv_mul] using
      (integral_lorentz_eq_self_full (d := d) (n := n) Λ
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x ε hε] with x hx
    simp [hx]
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x := hcov.symm
    _ =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := hrewrite

theorem bv_lorentz_covariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hcanonical_pairing :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
    intro Λ f g ε hε hfg
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          simpa using
            boundary_ray_lorentz_invariant_of_F_invariant (d := d) n F_n
              hF_lorentz
              Λ f ε hε
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hcanonical_pairing Λ f g ε hε hfg
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_lorentz_covariance_transfer_of_fixed_tube_covariance
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
    (Λ : LorentzGroup d)
    (hF_lorentz_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_orthochronous
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
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ =>
            ↑((Matrix.mulVec Λ.val (x k)) μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ f g hfg
  have hF_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
    hF_lorentz Λ hΛ
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_restricted_of_tube_covariance
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
    (hF_lorentz :
      ∀ (Λ : LorentzGroup.Restricted (d := d))
        (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup.Restricted (d := d)) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ.val⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := restricted_preserves_forward_cone Λ diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ.val⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ.val⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, lorentz_inv_mul_eq_one (d := d) Λ] using
        (integral_lorentz_eq_self (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ.val⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x η ε hε] with x hx
      simp [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

theorem bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance
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
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d),
        LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
          F_n (fun k μ => ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ_ortho f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := orthochronous_preserves_forward_cone (d := d) Λ hΛ_ortho diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
      have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
      rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
      rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
      exact h1
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, hΛinv_mul] using
        (integral_lorentz_eq_self_full (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ hΛ_ortho x ε hε] with x hx
      rw [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

theorem lorentz_covariance_of_orthochronous_and_timeReversal
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_ortho :
      ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
        ∀ (f g : SchwartzNPoint d n),
          (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
          W_n f = W_n g)
    (hW_timeReversal :
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x =
          f.toFun (fun i =>
            Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))) →
        W_n f = W_n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  rcases LorentzGroup.orthochronous_or_timeReversal_mul_orthochronous (d := d) Λ with
    hΛ_ortho | hTΛ_ortho
  · exact hW_ortho Λ hΛ_ortho f g hfg
  · let Λo : LorentzGroup d := LorentzGroup.timeReversal (d := d) * Λ
    let h : SchwartzNPoint d n := lorentzCompSchwartzFull (d := d) Λo f
    have hf_h : W_n f = W_n h := by
      apply hW_ortho Λo hTΛ_ortho f h
      intro x
      simpa [Λo] using lorentzCompSchwartzFull_apply (d := d) Λo f x
    have hg_rel :
        ∀ x, g.toFun x =
          h.toFun (fun i =>
            Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i)) := by
      intro x
      rw [hfg x, lorentzCompSchwartzFull_apply]
      congr 1
      ext i j
      have hmul :
          Λo⁻¹.val * (LorentzGroup.timeReversal (d := d)).val = Λ⁻¹.val := by
        have hgrp : Λo⁻¹ * LorentzGroup.timeReversal (d := d) = Λ⁻¹ := by
          dsimp [Λo]
          rw [mul_inv_rev]
          simp [mul_assoc]
        change ((Λo⁻¹ * LorentzGroup.timeReversal (d := d)).val : Matrix _ _ ℝ) = Λ⁻¹.val
        simpa using congrArg (fun Γ : LorentzGroup d => Γ.val) hgrp
      simpa [Matrix.mulVec_mulVec, hmul]
    have hh_g : W_n h = W_n g := hW_timeReversal h g hg_rel
    exact hf_h.trans hh_g

private theorem boundary_ray_permutation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x (σ i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x (σ i))
        =
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) *
          f (fun i => x (σ i)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_perm σ x η ε hε] with x hx
            simp [hx]
  _ =
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
          simpa using
            (MeasureTheory.volume_measurePreserving_piCongrLeft
              (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp'
                (fun x : NPointDomain d n =>
                  F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x)

private theorem bv_local_commutativity_transfer_of_F_invariant
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
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun k => x (σ k))) →
      W_n f = W_n g := by
  intro σ f g hfg
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (σ k)) := by
      congr 1
      ext x
      have hxg : g x = f (fun k => x (σ k)) := by
        simpa using hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (σ k)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_permutation_invariant_of_F_invariant (d := d) n F_n hF_perm σ f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_local_commutativity_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_swapCanonical :
      ∀ (i j : Fin n) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
        F_n (fun k μ =>
          ↑(x (Equiv.swap i j k) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)
          =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  intro i j f g hsupp hswap
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hswap x)
    have hswap_integral :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k))
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      let e : NPointDomain d n ≃ᵐ NPointDomain d n :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) (Equiv.swap i j)
      have hmp :
          MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.volume_measurePreserving_piCongrLeft
          (fun _ : Fin n => Fin (d + 1) → ℝ) (Equiv.swap i j)
      let h :
          NPointDomain d n → ℂ := fun x =>
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * f x
      have hleft :
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun k => x (Equiv.swap i j k))
            =
          ∫ x : NPointDomain d n, h (e.symm x) := by
        congr 1
        ext x
        have he_symm :
            e.symm x = fun k => x (Equiv.swap i j k) := by
          ext k μ
          change
            ((Equiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ)
              (Equiv.swap i j)).symm x k) μ
              =
            x (Equiv.swap i j k) μ
          simp
        rw [he_symm]
        simp [h]
      calc
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k))
            =
          ∫ x : NPointDomain d n, h (e.symm x) := hleft
        _ = ∫ x : NPointDomain d n, h x := hmp.symm.integral_comp' h
        _ =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
              rfl
    have hcanonical :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : f x = 0
      · simp [hx]
      · have hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) := hsupp x hx
        have hswapx :
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I)
              =
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
          simpa [η] using hF_swapCanonical i j x ε hε hsp
        simpa [hx] using congrArg (fun z : ℂ => z * f x) hswapx
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        hswap_integral
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := hcanonical
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_local_commutativity_transfer_of_swap_pairing (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_swapCanonical_pairing :
      ∀ (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, f.toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
        (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  intro i j f g hsupp hswap
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_swapCanonical_pairing i j f g ε hε hsupp hswap
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_hermitian_pairing_of_F_negCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      F_n (fun j => z (σ j)) = F_n z)
    (hF_trans : ∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
      F_n (fun j => z j + a) = F_n z)
    (hF_neg :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
        F_n (fun k μ =>
          ↑(x k μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
  let η := canonicalForwardConeDirection (d := d) n
  intro f g ε hε hfg
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := by
            intro x
            ext i μ
            simp [Ψfun]
          right_inv := by
            intro x
            ext i μ
            simp [Ψfun] }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hreflect :
      ∀ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
    intro x
    let a : Fin (d + 1) → ℂ := fun μ =>
      if μ = 0 then (((n : ℝ) + 1) * ε : ℂ) * Complex.I else 0
    let zrev : Fin n → Fin (d + 1) → ℂ := fun k μ =>
      ↑(x k μ) + ε * ↑(η (Fin.rev k) μ) * Complex.I
    have hshift :
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) =
          F_n zrev := by
      have hzrev :
          (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) = zrev := by
        funext k
        funext μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [a, zrev, η, canonicalForwardConeDirection, Fin.val_rev]
          ring_nf
        · simp [a, zrev, η, canonicalForwardConeDirection, hμ]
      calc
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I)
            =
          F_n (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) := by
              symm
              exact hF_trans _ a
        _ = F_n zrev := by rw [hzrev]
    have hperm :
        F_n zrev =
          F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
      simpa [zrev] using (hF_perm Fin.revPerm zrev).symm
    calc
      starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) := hF_neg x ε hε
      _ = F_n zrev := hshift
      _ = F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := hperm
  let h : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑((Ψfun x) k μ) + ε * ↑(η k μ) * Complex.I) * starRingEnd ℂ (f x)
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n, h x := by
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n, h (Ψ x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall hfg] with x _hxg
          have hxg : g x = starRingEnd ℂ (f (fun i => x (Fin.rev i))) := by
            simpa using hfg x
          rw [hxg]
          simp [h, Ψ, Ψfun]
      _ = ∫ x : NPointDomain d n, h x := by
        simpa [h, Ψ, Ψfun] using
          ((reverseNPoint_measurePreserving (d := d) (n := n)).integral_comp'
            (f := Ψ) (g := h))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
            rw [hrewrite]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall hreflect] with x hx
            have hx' :
                F_n (fun k μ => ↑(Ψfun x k μ) + ε * ↑(η k μ) * Complex.I) =
                  starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
              simpa [Ψfun] using hx.symm
            calc
              h x =
                starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
                  starRingEnd ℂ (f x) := by
                    simp [h, Ψfun, hx']
              _ =
                starRingEnd ℂ
                  ((F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * f x) := by
                    simp [map_mul, mul_comm]
    _ =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
            rw [← _root_.integral_conj]

private theorem bv_hermiticity_transfer_of_F_reflect
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
    (hF_reflect : ∀ (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
      0 < ε →
      starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  intro f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            starRingEnd ℂ (f (Ψ x)) := by
      congr 1
      ext x
      have hxg : g x = starRingEnd ℂ (f (Ψ x)) := by
        simpa [Ψ, Ψfun] using hfg x
      rw [hxg]
    have hpattern :
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              starRingEnd ℂ (f (Ψ x)) := by
      simpa [Ψ, Ψfun] using
          (SCV.bv_reality_pattern (μ := MeasureTheory.volume)
          (F := fun x : NPointDomain d n =>
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          (f := f) (Ψ := Ψ)
          (by simpa [Ψ, Ψfun] using reverseNPoint_measurePreserving (d := d) (n := n))
          (fun x => by simpa [Ψ] using hΨ_invol x)
          (Filter.Eventually.of_forall <| by
            intro x
            simpa [Ψ, Ψfun] using hF_reflect x η ε hε))
    exact hrewrite.trans hpattern.symm
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm

theorem bv_timeReversal_transfer
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
    (hF_timeReflect_pairing :
      ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (timeReflectionN d x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (timeReflectionN d x)) →
      W_n f = W_n g := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
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
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          simpa [η] using hF_timeReflect_pairing f ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_timeReversal :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  intro f ε hε
  have hTT_mul :
      (LorentzGroup.timeReversal (d := d)).val *
          (LorentzGroup.timeReversal (d := d)).val
        = 1 := by
    have h1 := LorentzGroup.ext_iff.mp
      (LorentzGroup.timeReversal_mul_timeReversal (d := d))
    rw [show ((LorentzGroup.timeReversal (d := d)) *
        LorentzGroup.timeReversal (d := d)).val =
          (LorentzGroup.timeReversal (d := d)).val *
            (LorentzGroup.timeReversal (d := d)).val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hTT_mul] using
      (integral_lorentz_eq_self_full (d := d) (n := n)
        (LorentzGroup.timeReversal (d := d))
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (y i))))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          exact hcov.symm
    _ =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards
            [Filter.Eventually.of_forall fun x =>
              hF_timeReversal x ε hε] with x hx
          rw [hx]

theorem bv_hermiticity_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_reflect_pairing :
      ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x))) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_reflect_pairing f g ε hε hfg
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm
