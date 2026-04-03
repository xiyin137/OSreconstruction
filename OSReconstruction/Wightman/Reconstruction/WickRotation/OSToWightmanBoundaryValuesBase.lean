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
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAXiShift
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

/-! ### Positive-time inner-product reductions

These lemmas isolate the purely algebraic part of the BV positivity lane.
If a candidate Wightman family agrees termwise with the Euclidean OS tensor
terms on ordered positive-time pairs, then positivity on the honest
positive-time Borchers algebra is formal from reflection positivity. The
remaining content is therefore the termwise comparison itself, plus any later
reduction from arbitrary Borchers data to the positive-time sector. -/

/-- If a candidate Wightman family agrees termwise with the Euclidean OS tensor
terms on ordered positive-time test pairs, then its Borchers inner product
agrees with the honest OS inner product on the positive-time Borchers algebra. -/
theorem wightmanInner_eq_osInner_of_orderedPositive_termwise
    (OS : OsterwalderSchraderAxioms d)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hterm :
      ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
          OrderedPositiveTimeRegion d n →
        tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
          OrderedPositiveTimeRegion d m →
        W (n + m) (f.conjTensorProduct g) =
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))
    (F G : PositiveTimeBorchersSequence d) :
    WightmanInnerProduct d W (F : BorchersSequence d) (G : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  unfold WightmanInnerProduct PositiveTimeBorchersSequence.osInner OSInnerProduct
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm
  simpa using
    hterm n m
      (((F : BorchersSequence d).funcs n) : SchwartzNPoint d n)
      (((G : BorchersSequence d).funcs m) : SchwartzNPoint d m)
      (F.ordered_tsupport n)
      (G.ordered_tsupport m)

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

/-- On the exact compact ordered positive-time shell where the BV `xiShift`
comparison theorem applies, the reconstructed Wightman inner product of two
concentrated Borchers vectors already agrees with the honest OS inner product. -/
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

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_twoPointDifferenceLift_eq_local
    (χ h : SchwartzSpacetime d) (t : ℝ) :
    timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h) =
      twoPointDifferenceLift (SCV.translateSchwartz (- timeShiftVec d t) χ) h := by
  ext x
  have hdiff :
      (x 1 - timeShiftVec d t) - (x 0 - timeShiftVec d t) = x 1 - x 0 := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  rw [timeShiftSchwartzNPoint_apply, twoPointDifferenceLift_apply,
    twoPointDifferenceLift_apply, SCV.translateSchwartz_apply]
  congr 1
  rw [hdiff]

omit [NeZero d] in
private theorem tsupport_precomp_subset_proj0_local
    (χ : SchwartzSpacetime d) :
    tsupport (fun x : NPointDomain d 2 => χ (x 0)) ⊆
      (fun x : NPointDomain d 2 => x 0) ⁻¹' tsupport (χ : SpacetimeDim d → ℂ) := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage (continuous_apply 0))
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem tsupport_twoPointDifferenceLift_subset_proj0_preimage_local
    (χ h : SchwartzSpacetime d) :
    tsupport ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) ⊆
      (fun x : NPointDomain d 2 => x 0) ⁻¹' tsupport (χ : SpacetimeDim d → ℂ) := by
  refine (tsupport_mul_subset_left
    (f := fun x : NPointDomain d 2 => χ (x 0))
    (g := fun x : NPointDomain d 2 => h (x 1 - x 0))).trans ?_
  exact tsupport_precomp_subset_proj0_local (d := d) χ

omit [NeZero d] in
private theorem tsupport_twoPointDifferenceLift_subset_orderedPositiveTimeRegion_local
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) ⊆ OrderedPositiveTimeRegion d 2 := by
  intro x hx
  have hx0 : x 0 ∈ tsupport (χ : SpacetimeDim d → ℂ) := by
    exact (tsupport_twoPointDifferenceLift_subset_proj0_preimage_local (d := d) χ h hx)
  have hdiff : x 1 - x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact (tsupport_twoPointDifferenceLift_subset_diff_preimage χ h hx)
  have hx0_pos : 0 < (x 0) 0 := hχ_pos hx0
  have hdiff_pos : 0 < (x 1 - x 0) 0 := hh_pos hdiff
  intro i
  fin_cases i
  · refine ⟨hx0_pos, ?_⟩
    intro j hij
    fin_cases j
    · exact (lt_irrefl _ hij).elim
    · simpa [sub_eq_add_neg] using hdiff_pos
  · refine ⟨?_, ?_⟩
    · have hcoord : (x 1 - x 0) 0 = x 1 0 - x 0 0 := by
        simp
      have hx1_eq : x 1 0 = x 0 0 + (x 1 - x 0) 0 := by
        linarith
      have hx1_pos : 0 < x 1 0 := by
        nlinarith [hx1_eq, hx0_pos, hdiff_pos]
      simpa using hx1_pos
    · intro j hij
      fin_cases j
      · exact (Fin.not_lt_zero _ hij).elim
      · exact (lt_irrefl _ hij).elim

/-- On the admissible two-point center/difference shell with positive-time
center and positive-time difference support, the base-time `xiShift 0 0`
variable is already trivial: every positive real slice equals the same
Schwinger value. This isolates the remaining two-point comparison content to
the genuine difference-time direction rather than the common center-time
direction. -/
theorem bvt_twoPointDifferenceLift_baseTime_eq_constant_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∫ y : NPointDomain d 2,
      bvt_F OS lgc 2
        (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (twoPointDifferenceLift χ h) y =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  let f0fun : NPointDomain d 0 → ℂ := fun _ => 1
  have hf0_compact : HasCompactSupport f0fun := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (Set.univ : Set (NPointDomain d 0))) ?_ ?_
    · exact Set.Subsingleton.isCompact Set.subsingleton_univ
    · intro x hx
      simp
  have hf0_smooth : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) f0fun := by
    simpa [f0fun] using
      (contDiff_const :
        ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun _ : NPointDomain d 0 => (1 : ℂ)))
  let f0 : SchwartzNPoint d 0 := hf0_compact.toSchwartzMap hf0_smooth
  have hf0_apply : ∀ x : NPointDomain d 0, f0 x = 1 := by
    intro x
    rfl
  have hf0_ord :
      tsupport (f0 : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0 := by
    intro x hx
    simp [OrderedPositiveTimeRegion]
  have hg_ord :
      tsupport (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ)) ⊆ OrderedPositiveTimeRegion d 2 :=
    tsupport_twoPointDifferenceLift_subset_orderedPositiveTimeRegion_local
      (d := d) χ h hχ_pos hh_pos
  have h0 :
      (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro h0mem
    have hnot : ¬ 0 < ((0 : SpacetimeDim d) 0) := by simp
    exact hnot (hh_pos h0mem)
  have hshift :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
    rw [timeShiftSchwartzNPoint_twoPointDifferenceLift_eq_local (d := d) χ h t]
    exact (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
      (d := d) (OS := OS) (a := -timeShiftVec d t) (χ := χ) (h := h) h0).symm
  calc
    ∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (twoPointDifferenceLift χ h) y
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (f0.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)))) := by
          symm
          have hosconj0 : SchwartzNPoint.osConj (d := d) (n := 0) f0 = f0 := by
            ext x
            simp [SchwartzNPoint.osConj_apply, hf0_apply]
          have htensor :
              f0.osConjTensorProduct (twoPointDifferenceLift χ h) =
                twoPointDifferenceLift χ h := by
            ext y
            have hsplit : splitLast 0 2 y = y := by
              ext i
              simp [splitLast]
            calc
              (f0.osConjTensorProduct (twoPointDifferenceLift χ h)) y
                  = ((f0.tensorProduct (twoPointDifferenceLift χ h)) y) := by
                      simp [SchwartzNPoint.osConjTensorProduct, hosconj0]
              _ = f0 (splitFirst 0 2 y) * (twoPointDifferenceLift χ h) (splitLast 0 2 y) := by
                    rw [SchwartzMap.tensorProduct_apply]
              _ = 1 * (twoPointDifferenceLift χ h) y := by
                    simp [hf0_apply, hsplit]
              _ = (twoPointDifferenceLift χ h) y := by simp
          simpa [htensor] using
            (schwinger_simpleTensor_timeShift_eq_xiShift
              (d := d) (OS := OS) (n := 0) (m := 2) (hm := by omega)
              (Ψ := bvt_F OS lgc 2)
              (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc 2)
              (f := f0) (hf_ord := hf0_ord)
              (g := twoPointDifferenceLift χ h) (hg_ord := hg_ord)
              (t := t) ht)
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))) := by
          have htensor_shift :
              f0.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t
                (twoPointDifferenceLift χ h)) =
                timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h) := by
            ext y
            have hosconj0 : SchwartzNPoint.osConj (d := d) (n := 0) f0 = f0 := by
              ext x
              simp [SchwartzNPoint.osConj_apply, hf0_apply]
            have hsplit : splitLast 0 2 y = y := by
              ext i
              simp [splitLast]
            calc
              (f0.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t
                  (twoPointDifferenceLift χ h))) y
                  = ((f0.tensorProduct (timeShiftSchwartzNPoint (d := d) t
                      (twoPointDifferenceLift χ h))) y) := by
                        simp [SchwartzNPoint.osConjTensorProduct, hosconj0]
              _ = f0 (splitFirst 0 2 y) *
                    (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))
                      (splitLast 0 2 y) := by
                    rw [SchwartzMap.tensorProduct_apply]
              _ = 1 *
                    (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)) y := by
                    simp [hf0_apply, hsplit]
              _ = (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)) y := by
                    simp
          simp [htensor_shift]
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := hshift

/-- Fixed-time two-point `xiShift` pairings for the actual BV witness already
depend on the center test only through its integral. This is the concrete
`k = 2` fixed-time shell-collapse statement on the production witness `bvt_F`,
obtained by specializing the K2 Input A theorem rather than introducing a new
auxiliary kernel. -/
theorem bvt_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    ∫ y : NPointDomain d 2,
      bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
        (χ (y 0) * h (y 1))
      =
    (∫ y : NPointDomain d 2,
      bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
        (χ₀ (y 0) * h (y 1))) *
      ∫ u : SpacetimeDim d, χ u := by
  simpa using
    OSReconstruction.schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
      (d := d) (OS := OS) (Ψ := bvt_F OS lgc 2)
      (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc 2)
      (h := h) (hh_pos := hh_pos) (t := t) ht
      (χ₀ := χ₀) (hχ₀ := hχ₀) (χ := χ)

/-- Production-witness center-collapse on the actual shifted Schwinger shell:
once one normalized center cutoff is fixed, every other two-point
`twoPointDifferenceLift χ (translate (-timeShiftVec t) h)` value is obtained by
scaling with `∫ χ`. This is the exact production specialization of the K2
fixed-time shell reduction, and it shrinks the live comparison problem to one
normalized center cutoff. -/
theorem bvt_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      (∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
  calc
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      ∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1)) := by
            exact OSReconstruction.schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport_local
              (d := d) (OS := OS) (Ψ := bvt_F OS lgc 2)
              (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc 2)
              χ h hh_pos t ht
    _ =
      (∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
            exact bvt_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
              (d := d) (OS := OS) (lgc := lgc)
              h hh_pos t ht χ₀ hχ₀ χ

/-- The shifted two-point Schwinger shell on a positive-support difference test
already has a concrete fixed-time center/difference kernel representation
coming from the `k = 2` base-step witness. This is the correct K2-facing
replacement for the discarded direct-holomorphic-family claim: it exposes the
actual fixed-time kernel on the live two-point route without conflating the
center/difference witness with the direct product-shell `xiShift` family. -/
theorem bvt_exists_twoPointDifferenceLift_timeShift_fixedTimeCenterDiffKernel_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((t : ℂ) * Complex.I) z *
            (χ (z 0) * h (z 1)) := by
  obtain ⟨G, hG_holo, hG_euclid⟩ := schwinger_continuation_base_step (d := d) OS lgc 2
  refine ⟨G, hG_holo, hG_euclid, ?_⟩
  exact
    OSReconstruction.schwinger_twoPointDifferenceLift_timeShift_eq_fixedTimeCenterDiffKernel_of_positiveSupport_local
      (d := d) OS G hG_euclid χ h hh_pos t ht

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

/-- The one-point OS time-shift matrix element can already be written directly
on the two-point center/difference shell. This exposes the semigroup side on
the same geometric coordinates as the live `k = 2` two-point route, without
claiming it is yet the shifted admissible difference shell. -/
theorem bvt_OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
            hχ_pos))
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d g : SchwartzNPoint d 1)
            hg_pos))
        (t : ℂ) =
      ∫ z : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
  rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
    (d := d) (OS := OS) (lgc := lgc)
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        hχ_pos))
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d g : SchwartzNPoint d 1)
        hg_pos))
    (t : ℂ) (by simpa using ht)]
  calc
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
        (t : ℂ)
      =
        ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i))
                ((t : ℂ) * Complex.I)) *
              (χ (y 0) * g (y 1)) := by
          exact bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
            (d := d) (OS := OS) (lgc := lgc)
            χ g hχ_pos hg_pos hg_compact t ht
    _ =
        ∫ z : NPointDomain d 2,
          bvt_F OS lgc 2
            (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
            (χ (z 0) * g (z 0 + z 1)) := by
          simpa [twoPointProductLift_apply] using
            (integral_mul_twoPointProductLift_eq_centerShear
              (d := d)
              (Ψ := fun y : NPointDomain d 2 =>
                bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i))
                    ((t : ℂ) * Complex.I)))
              χ g)

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

theorem onePointToFin1_hasCompactSupport_local
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    HasCompactSupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) := by
  simpa [onePointToFin1CLM] using
    (hg_compact.comp_homeomorph
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))

theorem osConj_onePointToFin1_hasCompactSupport_local
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

/-- The translated-right canonical `xiShift` shell therefore converges at
`t = 0⁺` to the corresponding Euclidean Schwinger tensor term. This packages
the OS-semigroup continuity theorem above into the exact Schwinger-form limit
that the ordered positive-time comparison route wants. -/
theorem bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger
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
    Filter.Tendsto
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))))) := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single n f hf_ord⟧) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single m g hg_ord⟧) : OSHilbertSpace OS))
  have hbase :=
    bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero
      (d := d) OS lgc n m hm f hf_ord hf_compact g hg_ord hg_compact a
  have hEq :
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((f.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
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
            ((osSpatialTranslateHilbert OS a) xG)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    simp [ht_pos]
  have hbase' :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (@inner ℂ (OSHilbertSpace OS) _ xF
            ((osSpatialTranslateHilbert OS a) xG))) :=
    Filter.Tendsto.congr' hEq.symm hbase
  simpa [xF, xG, osInner_single_translate_spatial_right_eq_schwinger_local
    (d := d) OS f hf_ord g hg_ord a] using hbase'

/-- If the same translated-right single-split `xiShift` shell also tends to the
corresponding reconstructed boundary-value functional, then the ordered
positive-time BV-vs-Schwinger comparison follows immediately by uniqueness of
the limit. This isolates the remaining comparison content to the BV-side
small-`t` limit alone. -/
theorem bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero
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
    (a : Fin d → ℝ)
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (f.conjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))))) :
    bvt_W OS lgc (n + m)
      (f.conjTensorProduct
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))
    =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g))) := by
  have hSlimit :=
    bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact a
  exact tendsto_nhds_unique hWlimit hSlimit

/-- Zero-translation specialization of
`bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`.
This is the exact ordered positive-time comparison shape needed by the
positivity lane: once the BV-side `xiShift` shell is shown to converge to the
reconstructed `bvt_W` term, the Euclidean Schwinger identity follows
formally. -/
theorem bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
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
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct g) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g)))) :
    bvt_W OS lgc (n + m) (f.conjTensorProduct g)
      =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct g)) := by
  have ha0_zero : (Fin.cons 0 (0 : Fin d → ℝ) : SpacetimeDim d) = 0 := by
    funext μ
    refine Fin.cases ?_ ?_ μ
    · simp
    · intro i
      simp
  have htranslate_zero :
      translateSchwartzNPoint (d := d) (Fin.cons 0 (0 : Fin d → ℝ)) g = g := by
    ext x
    simp [translateSchwartzNPoint_apply, ha0_zero]
  have hWlimit' :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct
                (translateSchwartzNPoint (d := d) (Fin.cons 0 (0 : Fin d → ℝ)) g)) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (f.conjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 (0 : Fin d → ℝ)) g)))) := by
    simpa [htranslate_zero] using hWlimit
  simpa [htranslate_zero] using
    bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact (0 : Fin d → ℝ) hWlimit'

/-- On the exact compact ordered positive-time shell where the BV `xiShift`
comparison theorem applies, the reconstructed Wightman inner product of two
concentrated Borchers vectors already agrees with the honest OS inner product. -/
theorem bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
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
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct g) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + m) (f.conjTensorProduct g)))) :
    WightmanInnerProduct d (bvt_W OS lgc)
        (BorchersSequence.single n f) (BorchersSequence.single m g) =
      PositiveTimeBorchersSequence.osInner OS
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) := by
  calc
    WightmanInnerProduct d (bvt_W OS lgc)
        (BorchersSequence.single n f) (BorchersSequence.single m g)
      =
        bvt_W OS lgc (n + m) (f.conjTensorProduct g) := by
          simpa using
            WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
              (bvt_W_linear (d := d) OS lgc) n m f g
    _ =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct g)) := by
            exact
              bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
                (d := d) (OS := OS) (lgc := lgc) n m hm
                f hf_ord hf_compact g hg_ord hg_compact hWlimit
    _ =
        OSInnerProduct d OS.S
          (BorchersSequence.single n f) (BorchersSequence.single m g) := by
            symm
            simpa using
              OSInnerProduct_single_single (d := d) OS.S OS.E0_linear n m f g
    _ =
        PositiveTimeBorchersSequence.osInner OS
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) := by
            simp [PositiveTimeBorchersSequence.osInner]

/-- In the self-pair case, the same compact ordered positive-time shell
comparison already yields nonnegativity of the reconstructed singleton
Wightman norm from OS reflection positivity. -/
theorem bvt_wightmanInner_single_self_nonneg_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (hn : 0 < n)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (n + n),
            bvt_F OS lgc (n + n)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hn⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((f.osConjTensorProduct f) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + n) (f.conjTensorProduct f)))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (BorchersSequence.single n f) (BorchersSequence.single n f)).re := by
  rw [bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (d := d) (OS := OS) (lgc := lgc) n n hn
    f hf_ord hf_compact f hf_ord hf_compact hWlimit]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS
    (PositiveTimeBorchersSequence.single n f hf_ord)

/-- If each compact ordered positive-time component of a left Borchers vector
admits the same `xiShift` boundary-value comparison against a compact ordered
positive-time right singleton, then the full reconstructed Wightman inner
product against that singleton already agrees with the honest OS inner
product. -/
theorem bvt_wightmanInner_right_single_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (m : ℕ) (hm : 0 < m)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ))
    (hWlimit :
      ∀ n,
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct g) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct g))))) :
    WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d)
        (BorchersSequence.single m g) =
      PositiveTimeBorchersSequence.osInner OS F
        (PositiveTimeBorchersSequence.single m g hg_ord) := by
  unfold WightmanInnerProduct
  rw [PositiveTimeBorchersSequence.osInner]
  calc
    ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∑ m_1 ∈ Finset.range ((BorchersSequence.single m g).bound + 1),
          bvt_W OS lgc (n + m_1)
            (((F : BorchersSequence d).funcs n).conjTensorProduct
              ((BorchersSequence.single m g).funcs m_1))
      =
        ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (((F : BorchersSequence d).funcs n).osConjTensorProduct g)) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [BorchersSequence.single_bound, Finset.sum_range_succ]
              have hrightW :
                  ∑ j ∈ Finset.range m,
                    bvt_W OS lgc (n + j)
                      (((F : BorchersSequence d).funcs n).conjTensorProduct
                        ((BorchersSequence.single m g).funcs j)) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro j hj
                have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
                rw [BorchersSequence.single_funcs_ne hj_ne,
                  SchwartzMap.conjTensorProduct_zero_right,
                  (bvt_W_linear (d := d) OS lgc _).map_zero]
              rw [hrightW, zero_add, BorchersSequence.single_funcs_eq]
              exact bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
                (d := d) (OS := OS) (lgc := lgc) n m hm
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n) (hF_compact n)
                g hg_ord hg_compact (hWlimit n)
    _ = OSInnerProduct d OS.S (F : BorchersSequence d)
          (BorchersSequence.single m g) := by
            symm
            exact OSInnerProduct_right_single (d := d) OS.S OS.E0_linear
              (F := (F : BorchersSequence d)) (g := g)
    _ = OSInnerProduct d OS.S (F : BorchersSequence d)
          ((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
            BorchersSequence d) := by
            rfl

/-- Summing the right-single comparison over all positive-degree right
components reduces the full compact ordered positive-time inner-product
comparison to a single remaining `m = 0` term. The active `xiShift` shell
machinery therefore already pays for every positive-degree right component. -/
theorem bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((G : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((G : BorchersSequence d).funcs 0)))))
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((G : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((G : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d) (G : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  rw [WightmanInnerProduct_eq_sum_right_singles (d := d) (W := bvt_W OS lgc)
    (bvt_W_linear (d := d) OS lgc) (F := (F : BorchersSequence d))
    (G := (G : BorchersSequence d))]
  rw [PositiveTimeBorchersSequence.osInner_eq_sum_right_singles (d := d) OS F G]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    calc
      WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d)
          (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0))
        =
          ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            bvt_W OS lgc n
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((G : BorchersSequence d).funcs 0))) := by
              simpa using
                WightmanInnerProduct_right_single (d := d) (W := bvt_W OS lgc)
                  (bvt_W_linear (d := d) OS lgc) (F := (F : BorchersSequence d))
                  (g := ((G : BorchersSequence d).funcs 0))
      _ =
          ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
            OS.S n (ZeroDiagonalSchwartz.ofClassical
              ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                ((G : BorchersSequence d).funcs 0)))) := by
              apply Finset.sum_congr rfl
              intro n hn
              simpa using hzero n
      _ =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0)) := by
              symm
              simpa using
                OSInnerProduct_right_single (d := d) OS.S OS.E0_linear
                  (F := (F : BorchersSequence d))
                  (g := ((G : BorchersSequence d).funcs 0))
      _ =
          PositiveTimeBorchersSequence.osInner OS F
            (PositiveTimeBorchersSequence.single 0 (((G : BorchersSequence d).funcs 0))
              (G.ordered_tsupport 0)) := by
              rfl
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    simpa using
      bvt_wightmanInner_right_single_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
        (d := d) (OS := OS) (lgc := lgc) F hF_compact m hm_pos
        (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m) (hG_compact m) (fun n => hWlimit n m hm_pos)

/-- If the right positive-time Borchers vector has vanishing degree-zero
component, the positive-degree `xiShift` shell comparisons already determine
the full compact ordered positive-time Wightman inner product. -/
theorem bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hG0 : ((G : BorchersSequence d).funcs 0) = 0)
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((G : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((G : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc) (F : BorchersSequence d) (G : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  apply
    bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) F G hF_compact hG_compact
  · intro n
    rw [hG0, SchwartzMap.conjTensorProduct_zero_right,
      SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_zero,
      (bvt_W_linear (d := d) OS lgc _).map_zero, (OS.E0_linear _).map_zero]
  · exact hWlimit

/-- In the self-pair case, the same hypotheses yield positivity for compact
ordered positive-time Borchers vectors with vanishing degree-zero component. -/
theorem bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hF0 : ((F : BorchersSequence d).funcs 0) = 0)
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((F : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  rw [bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right
    (d := d) (OS := OS) (lgc := lgc) F F hF_compact hF_compact hF0 hWlimit]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

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

theorem onePoint_osConjTensorProduct_translate_spatial_apply_local
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
