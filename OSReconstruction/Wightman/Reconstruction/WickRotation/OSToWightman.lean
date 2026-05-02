/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.DenseCLM

/-!
# OS to Wightman Analytic Continuation Core

This file contains the continuation chain and general-k base step.
Base definitions (tube domains, coordinate helpers) are in
`OSToWightmanBase.lean`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

/-- First general-`k` ACR(1) subproblem: construct a scalar holomorphic witness on
admissible factorized tests.

This is the honest OS II one-slice/Osgood problem above the `k = 2` Bochner core:
produce a single scalar function on `C_k^(1)` whose Euclidean pairing already
reproduces the Schwinger functional on zero-diagonal product tensors. -/
private theorem exists_acrOne_productTensor_witness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1) ∧
      (∀ (fs : Fin k → SchwartzSpacetime d)
          (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S k ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d k,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S_prod (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S_prod (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  sorry

/- The formal dense-extension step above factors through two separate analytic
inputs:
1. continuity of the Euclidean kernel functional on `SchwartzNPoint d k`,
2. density of the admissible product-tensor subset inside `ZeroDiagonalSchwartz`.

This helper packages the purely topological last mile once those two pieces are
available. -/
private theorem zeroDiagonal_eq_schwinger_of_eq_on_dense
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (K : NPointDomain d k → ℂ)
    (L : ZeroDiagonalSchwartz d k →L[ℂ] ℂ)
    (hL_apply : ∀ f : ZeroDiagonalSchwartz d k,
      L f = ∫ x : NPointDomain d k, K x * (f.1 x))
    {S : Set (ZeroDiagonalSchwartz d k)}
    (hDense : Dense S)
    (hEq : ∀ f ∈ S, OS.S k f = ∫ x : NPointDomain d k, K x * (f.1 x)) :
    ∀ f : ZeroDiagonalSchwartz d k,
      OS.S k f = ∫ x : NPointDomain d k, K x * (f.1 x) := by
  have hL_eq :
      L = OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k := by
    apply ContinuousLinearMap.eq_of_eq_on_dense L
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k) hDense
    intro f hf
    rw [hL_apply]
    exact (hEq f hf).symm
  intro f
  have := congrArg (fun T : ZeroDiagonalSchwartz d k →L[ℂ] ℂ => T f) hL_eq
  simpa [hL_apply f] using this.symm

/-- The admissible product-tensor subset of `ZeroDiagonalSchwartz`: those
product tensors for which the zero-diagonal witness is genuine rather than the
`ofClassical` junk branch. This is the exact dense set needed by the upstream
ACR(1) closure problem. -/
private def admissibleProductTensorSet {d : ℕ} (k : ℕ) :
    Set (ZeroDiagonalSchwartz d k) :=
  {f : ZeroDiagonalSchwartz d k |
    ∃ (fs : Fin k → SchwartzSpacetime d)
      (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
      f = ⟨SchwartzMap.productTensor fs, hvanish⟩}

/-- Once the Euclidean section of `S_prod` is already packaged as a polynomially
bounded measurable kernel and the admissible product tensors are dense in
`ZeroDiagonalSchwartz`, the Schwinger reproduction identity extends formally
from the admissible product tensors to all zero-diagonal tests. -/
private theorem acrOne_productTensor_witness_extends_zeroDiagonal_of_kernelPackage_and_dense
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_prod :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S k ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d k,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x)
    (hK_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : NPointDomain d k => S_prod (fun j => wickRotatePoint (x j)))
        MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume,
      ‖S_prod (fun j => wickRotatePoint (x j))‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hDense : Dense (admissibleProductTensorSet (d := d) k)) :
    ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        S_prod (fun j => wickRotatePoint (x j)) * (f.1 x) := by
  let K : NPointDomain d k → ℂ := fun x => S_prod (fun j => wickRotatePoint (x j))
  have hK_cont :
      Continuous (fun f : SchwartzNPoint d k => ∫ x, K x * f x) :=
    schwartz_continuous_of_polynomial_bound K hK_meas C_bd N hC hK_bound
  let Llin : ZeroDiagonalSchwartz d k →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x : NPointDomain d k, K x * (f.1 x)
      map_add' := by
        intro f g
        have hIntf :
            MeasureTheory.Integrable (fun x : NPointDomain d k => K x * (f.1 x))
              MeasureTheory.volume :=
          schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound f.1
        have hIntg :
            MeasureTheory.Integrable (fun x : NPointDomain d k => K x * (g.1 x))
              MeasureTheory.volume :=
          schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound g.1
        have hadd :
            (fun x : NPointDomain d k => K x * ((f + g : ZeroDiagonalSchwartz d k).1 x)) =
              (fun x : NPointDomain d k => K x * (f.1 x)) +
                (fun x : NPointDomain d k => K x * (g.1 x)) := by
          funext x
          rw [Submodule.coe_add]
          simpa [Pi.add_apply] using mul_add (K x) (f.1 x) (g.1 x)
        rw [hadd]
        exact MeasureTheory.integral_add hIntf hIntg
      map_smul' := by
        intro c f
        change
          ∫ x : NPointDomain d k, K x * ((c • f : ZeroDiagonalSchwartz d k).1 x) =
            c * ∫ x : NPointDomain d k, K x * (f.1 x)
        have hmul :
            (fun x : NPointDomain d k => K x * ((c • f : ZeroDiagonalSchwartz d k).1 x)) =
              fun x : NPointDomain d k => c * (K x * (f.1 x)) := by
          funext x
          rw [Submodule.coe_smul_of_tower]
          simp [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
        rw [hmul]
        exact MeasureTheory.integral_const_mul c _ }
  let L : ZeroDiagonalSchwartz d k →L[ℂ] ℂ :=
    ContinuousLinearMap.mk Llin (hK_cont.comp continuous_subtype_val)
  apply zeroDiagonal_eq_schwinger_of_eq_on_dense (d := d) OS k K L
    (fun f => rfl) hDense
  intro f hf
  rcases hf with ⟨fs, hvanish, rfl⟩
  simpa [K] using hS_prod_prod fs hvanish

/-- First honest subproblem inside theorem 2: package the Euclidean section of
the `ACR(1)` witness as a measurable polynomially bounded kernel on real
configurations. -/
private theorem acrOne_productTensor_witness_euclidKernelPackage
    {d : ℕ} [NeZero d]
    (k : ℕ)
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_holo : DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1))
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z)
    (hS_prod_growth :
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      MeasureTheory.AEStronglyMeasurable
        (fun x : NPointDomain d k => S_prod (fun j => wickRotatePoint (x j)))
        MeasureTheory.volume ∧
      (∀ᵐ x : NPointDomain d k ∂MeasureTheory.volume,
        ‖S_prod (fun j => wickRotatePoint (x j))‖ ≤ C_bd * (1 + ‖x‖) ^ N) := by
  sorry

/-- Second honest subproblem inside theorem 2: the admissible product tensors
are dense in `ZeroDiagonalSchwartz`. -/
private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
    {d : ℕ} [NeZero d] {n : ℕ} {ψ f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply
        (g := ((ψ : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        ψ.hasTemperateGrowth f y)
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (ψ.smooth ⊤) (f.smooth ⊤) x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψ : NPointDomain d n → ℂ) x‖ *
          ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x = 0 := hf (k - i) x hx
    simp [hfi]
  have hnonneg :
      0 ≤ ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ := norm_nonneg _
  have hzero_norm :
      ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      calc
        ‖iteratedFDeriv ℝ k (fun y : NPointDomain d n => ψ y * f y) x‖
            ≤
          ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψ : NPointDomain d n → ℂ) x‖ *
              ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ := hle
        _ = 0 := hsum_zero
    · exact hnonneg
  exact norm_eq_zero.mp hzero_norm

private noncomputable def unitBallBumpSchwartzNPointRadius
    {d : ℕ} [NeZero d] (n : ℕ) (R : ℝ) (hR : 0 < R) : SchwartzNPoint d n :=
  OSReconstruction.unflattenSchwartzNPoint (d := d)
    (OSReconstruction.unitBallBumpSchwartzPiRadius (n * (d + 1)) R hR)

private theorem unflatten_flattenSchwartzNPoint_local
    {d : ℕ} [NeZero d] {n : ℕ} (f : SchwartzNPoint d n) :
    OSReconstruction.unflattenSchwartzNPoint (d := d)
      (OSReconstruction.flattenSchwartzNPoint (d := d) f) = f := by
  ext x
  simp [OSReconstruction.flattenSchwartzNPoint_apply,
    OSReconstruction.unflattenSchwartzNPoint_apply]

private noncomputable def bumpTruncationRadiusNPoint
    {d : ℕ} [NeZero d] {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) : SchwartzNPoint d n :=
  SchwartzMap.smulLeftCLM ℂ
    (unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)) f

private theorem bumpTruncationRadiusNPoint_eq_unflatten
    {d : ℕ} [NeZero d] {n : ℕ}
    (f : SchwartzNPoint d n) (N : ℕ) :
    bumpTruncationRadiusNPoint (d := d) f N =
      OSReconstruction.unflattenSchwartzNPoint (d := d)
        (OSReconstruction.bumpTruncationRadius
          (OSReconstruction.flattenSchwartzNPoint (d := d) f) N) := by
  ext x
  rw [bumpTruncationRadiusNPoint]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N) : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (unitBallBumpSchwartzNPointRadius (d := d) n
      (OSReconstruction.bumpTruncationRadiusValue N)
      (OSReconstruction.bumpTruncationRadiusValue_pos N)).hasTemperateGrowth
    f x]
  rw [unitBallBumpSchwartzNPointRadius, OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.unflattenSchwartzNPoint_apply]
  rw [OSReconstruction.bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [OSReconstruction.flattenSchwartzNPoint_apply, smul_eq_mul]

private theorem dense_hasCompactSupport_zeroDiagonal
    {d : ℕ} [NeZero d] (k : ℕ) :
    Dense {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} := by
  intro F
  let v : ℕ → SchwartzNPoint d k := fun n =>
    bumpTruncationRadiusNPoint (d := d) F.1 n
  have hv_vanish :
      ∀ n, VanishesToInfiniteOrderOnCoincidence (v n) := by
    intro n
    simpa [v, bumpTruncationRadiusNPoint] using
      (VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (d := d) F.2
          (ψ := unitBallBumpSchwartzNPointRadius (d := d) k
            (OSReconstruction.bumpTruncationRadiusValue n)
            (OSReconstruction.bumpTruncationRadiusValue_pos n)))
  let u : ℕ → ZeroDiagonalSchwartz d k := fun n => ⟨v n, hv_vanish n⟩
  have hu_mem :
      ∀ n, u n ∈ {F : ZeroDiagonalSchwartz d k |
        HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} := by
    intro n
    have hflat_compact :
        HasCompactSupport
          (((OSReconstruction.bumpTruncationRadius
            (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n :
              SchwartzMap (Fin (k * (d + 1)) → ℝ) ℂ)) :
            (Fin (k * (d + 1)) → ℝ) → ℂ) := by
      simpa [OSReconstruction.bumpTruncationRadius, OSReconstruction.bumpTruncationRadiusValue] using
        OSReconstruction.hasCompactSupport_cutoff_mul_radius
          (m := k * (d + 1)) (R := OSReconstruction.bumpTruncationRadiusValue n)
          (OSReconstruction.bumpTruncationRadiusValue_pos n)
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)
    have hv_compact :
        HasCompactSupport ((v n : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
      simpa [v] using
        (show HasCompactSupport ((bumpTruncationRadiusNPoint (d := d) F.1 n :
            SchwartzNPoint d k) : NPointDomain d k → ℂ) from by
          rw [bumpTruncationRadiusNPoint_eq_unflatten (d := d)]
          simpa [OSReconstruction.unflattenSchwartzNPoint_apply] using
            hflat_compact.comp_homeomorph (flattenCLEquivReal k (d + 1)).toHomeomorph)
    simpa [u] using hv_compact
  have hu_tendsto :
      Filter.Tendsto u Filter.atTop (nhds F) := by
    rw [tendsto_subtype_rng]
    have hv_tendsto :
        Filter.Tendsto v Filter.atTop (nhds F.1) := by
      have hunflat :=
        ((OSReconstruction.unflattenSchwartzNPoint (d := d)).continuous.tendsto
          (OSReconstruction.flattenSchwartzNPoint (d := d) F.1)).comp
            (SchwartzMap.tendsto_bump_truncation_nhds
              (OSReconstruction.flattenSchwartzNPoint (d := d) F.1))
      have hrew :
          v =
            fun n : ℕ =>
              OSReconstruction.unflattenSchwartzNPoint (d := d)
                (OSReconstruction.bumpTruncationRadius
                  (OSReconstruction.flattenSchwartzNPoint (d := d) F.1) n) := by
        funext n
        simpa [v] using bumpTruncationRadiusNPoint_eq_unflatten (d := d) F.1 n
      rw [hrew]
      simpa [Function.comp, unflatten_flattenSchwartzNPoint_local (d := d) F.1] using
        hunflat
    simpa [u] using hv_tendsto
  exact isClosed_closure.mem_of_tendsto hu_tendsto
    (Filter.Eventually.of_forall fun n => subset_closure (hu_mem n))

private theorem compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSet
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} ⊆
      closure (admissibleProductTensorSet (d := d) k) := by
  sorry

private theorem admissibleProductTensorSet_dense_zeroDiagonal
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    Dense (admissibleProductTensorSet (d := d) k) := by
  let C : Set (ZeroDiagonalSchwartz d k) :=
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)}
  have hC_dense : Dense C := dense_hasCompactSupport_zeroDiagonal (d := d) k
  have hC_subset :
      C ⊆ closure (admissibleProductTensorSet (d := d) k) :=
    compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSet (d := d) k
  have hclosure_subset :
      closure C ⊆ closure (admissibleProductTensorSet (d := d) k) := by
    exact closure_minimal hC_subset isClosed_closure
  intro F
  exact hclosure_subset (hC_dense F)

/-- Second general-`k` ACR(1) subproblem: upgrade the product-tensor witness to
the full zero-diagonal Schwartz space.

This is the density / nuclear-extension step: once a scalar witness reproduces
the Schwinger functional on admissible factorized tests, the remaining honest
inputs are:
- a Euclidean kernel package for the real section of `S_prod`,
- density of the admissible product-tensor subset of `ZeroDiagonalSchwartz`. -/
private theorem acrOne_productTensor_witness_extends_zeroDiagonal {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prod_holo : DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1))
    (hS_prod_prod :
      ∀ (fs : Fin k → SchwartzSpacetime d)
        (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S k ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d k,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x)
    (hS_prod_perm :
      ∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z)
    (hS_prod_trans :
      ∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z)
    (hS_prod_growth :
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        S_prod (fun j => wickRotatePoint (x j)) * (f.1 x) := by
  obtain ⟨C_bd, N, hC, hK_meas, hK_bound⟩ :=
    acrOne_productTensor_witness_euclidKernelPackage
      (d := d) k S_prod hS_prod_holo hS_prod_perm hS_prod_trans hS_prod_growth
  have hDense :
      Dense (admissibleProductTensorSet (d := d) k) :=
    admissibleProductTensorSet_dense_zeroDiagonal (d := d) k
  exact
    acrOne_productTensor_witness_extends_zeroDiagonal_of_kernelPackage_and_dense
      (d := d) OS k S_prod hS_prod_prod hK_meas C_bd N hC hK_bound hDense

/-- General-`k` OS-II first-step assembly on `ACR(1)`.

This is the honest several-complex-variables gap above the `k = 2` Bochner core:
assemble the one-slice semigroup continuation data into a jointly holomorphic
function on the first continuation region `C_k^(1)` with the Euclidean
reproduction identity. The intended proof route is the OS II equation `(5.4)`
slice theorem plus nuclear extension and Osgood/Hartogs assembly. -/
private theorem schwinger_continuation_base_step_acrOne_assembly {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S_prod, hS_prod_holo, hS_prod_prod, hS_prod_perm, hS_prod_trans,
    _hS_prod_negCanonical, hS_prod_growth⟩ :=
    exists_acrOne_productTensor_witness (d := d) OS lgc k
  refine ⟨S_prod, hS_prod_holo, ?_⟩
  exact
    acrOne_productTensor_witness_extends_zeroDiagonal
      (d := d) OS k S_prod hS_prod_holo hS_prod_prod hS_prod_perm hS_prod_trans hS_prod_growth

/-- `ACR(1)` assembly together with the common complex translation invariance
of the chosen witness.

This is the strengthened upstream surface needed by the `k = 2` diff-block
route: once `S₁` is chosen as a globally translation-invariant analytic
continuation witness, the flattened witness `G := S₁ ∘ fromDiffFlat` becomes
diff-block-dependent automatically. -/
theorem schwinger_continuation_base_step_acrOne_productTensor_assembly_with_translationInvariant
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_prod : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d k 1) ∧
      (∀ (fs : Fin k → SchwartzSpacetime d)
          (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S k ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d k,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S_prod (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S_prod (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  exact exists_acrOne_productTensor_witness (d := d) OS lgc k

/-- `ACR(1)` assembly together with the common complex translation invariance
of the chosen witness.

This is the strengthened upstream surface needed by the `k = 2` diff-block
route: once `S₁` is chosen as a globally translation-invariant analytic
continuation witness, the flattened witness `G := S₁ ∘ fromDiffFlat` becomes
diff-block-dependent automatically. -/
theorem schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        S_ext (fun j => z (σ j)) = S_ext z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_ext (fun j => z j + a) = S_ext z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S_ext (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S_ext (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d k 1,
          ‖S_ext z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨S_prod, hS_prod_holo, hS_prod_prod, hS_prod_perm, hS_prod_trans,
    hS_prod_negCanonical, hS_prod_growth⟩ :=
    exists_acrOne_productTensor_witness (d := d) OS lgc k
  refine ⟨S_prod, hS_prod_holo, ?_, hS_prod_perm, hS_prod_trans,
    hS_prod_negCanonical, hS_prod_growth⟩
  exact
    acrOne_productTensor_witness_extends_zeroDiagonal
      (d := d) OS k S_prod hS_prod_holo hS_prod_prod hS_prod_perm hS_prod_trans hS_prod_growth

/-- OS-II-faithful first-stage base-step theorem: construct a witness on the flattened
positive-time-difference tube that is holomorphic in the time-difference variables
and continuous in the remaining variables, together with the Euclidean
reproduction identity.

This matches the corrected reading of OS II more closely than the older single-step
formulation asking immediately for full holomorphicity on all complex coordinates. -/
theorem schwinger_continuation_base_step_timeParametric {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid⟩ :=
    schwinger_continuation_base_step_acrOne_assembly (d := d) OS lgc k
  let G : (Fin (k * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat k d u)
  refine ⟨G, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro u hu
      have hfrom_maps :
          Set.MapsTo (BHW.fromDiffFlat k d)
            (SCV.TubeDomain (FlatPositiveTimeDiffReal k d))
            (AnalyticContinuationRegion d k 1) := by
        intro v hv
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        simpa [BHW.toDiffFlat_fromDiffFlat] using hv
      have hS₁_cont : ContinuousOn S₁ (AnalyticContinuationRegion d k 1) := hS₁_hol.continuousOn
      have hG_cont : ContinuousOn G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) :=
        hS₁_cont.comp (differentiable_fromDiffFlat_local k d).continuous.continuousOn hfrom_maps
      exact hG_cont u hu
    · intro z hz i
      let idx : Fin (k * (d + 1)) := finProdFinEquiv (i, (0 : Fin (d + 1)))
      let φ : ℂ → (Fin k → Fin (d + 1) → ℂ) := fun w =>
        BHW.fromDiffFlat k d (Function.update z idx w)
      have hupdate_diff : Differentiable ℂ (fun w : ℂ => Function.update z idx w) := by
        rw [differentiable_pi]
        intro j
        by_cases hj : j = idx
        · subst hj
          simpa using differentiable_id
        · simpa [Function.update, hj] using differentiable_const (z j)
      have hφ_maps :
          Set.MapsTo φ {w : ℂ | 0 < w.im} (AnalyticContinuationRegion d k 1) := by
        intro w hw
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        rw [BHW.toDiffFlat_fromDiffFlat]
        rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [φ, idx]
        · have hzj :=
            (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := z)).mp hz j
          simpa [φ, idx, Function.update, hj] using hzj
      simpa [G, φ, idx] using
        (hS₁_hol.comp
          ((differentiable_fromDiffFlat_local k d).comp hupdate_diff).differentiableOn
          hφ_maps)
  · intro f
    simpa [G, BHW.fromDiffFlat_toDiffFlat] using hS₁_euclid f

/-- Public OS-II-faithful base-step theorem: produce a witness on the flattened
positive-time-difference tube that is holomorphic in the time-difference variables
and continuous in the remaining variables, together with the Euclidean
reproduction identity. -/
theorem schwinger_continuation_base_step {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  exact schwinger_continuation_base_step_timeParametric (d := d) OS lgc k

/-- Legacy full-holomorphic `ACR(1)` version of the base step.

This is the theorem currently consumed by the downstream restriction chain.
Mathematically, it should now be read as the explicit `ACR(1)` assembly theorem
underlying the public flattened time-parametric surface. -/
private theorem schwinger_continuation_base_step_full {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  exact schwinger_continuation_base_step_acrOne_assembly (d := d) OS lgc k


/-- **ξ-shift: the correct one-variable perturbation in the cumulative-sum structure.**

    In the cumulative-sum parametrization, the j-th new variable at level r is
      ξ[j] = z[j][r] - (if j = 0 then 0 else z[j-1][r])
    These k variables ξ[0], ..., ξ[k-1] are INDEPENDENT:
      C_k^(r+1) = C_k^(r) × UHP^k  (in the (z_base, ξ) parametrization).

    Moving ξ[j] by t (holding ξ[i] fixed for i ≠ j) requires shifting ALL z[i][r]
    for i ≥ j by +t simultaneously, since z[i][r] = ξ[0] + ... + ξ[i] (cumulative sum).

    WARNING: Updating only z[j][r] while keeping z[j+1][r],...,z[k-1][r] fixed changes
    BOTH ξ[j] (by +t) AND ξ[j+1] (by -t), which is NOT a single-variable extension.
    The test case in `test/acr_next_steps_test.lean` (d=1, k=2, r=1) confirms that a
    single-coordinate update can FAIL to land in ACR(r+1). -/
def xiShift {k d : ℕ} (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) : Fin k → Fin (d + 1) → ℂ :=
  fun i μ => if j.val ≤ i.val ∧ μ = r then z i μ + t else z i μ

/-- Shifting a cumulative-difference slice by zero does nothing. -/
private theorem xiShift_zero {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) :
    xiShift j r z 0 = z := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h]
  · simp [xiShift, h]

/-- Successive ξ-shifts in the same cumulative-difference coordinate add. -/
private theorem xiShift_add_same {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (s t : ℂ) :
    xiShift j r (xiShift j r z s) t = xiShift j r z (s + t) := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h, add_assoc]
  · simp [xiShift, h]

/-- In flattened difference coordinates, `xiShift` changes exactly one coordinate:
the `(j,r)` difference variable is translated by `t`, and all other difference
coordinates stay fixed. This is the concrete bookkeeping fact behind the
one-variable slice picture used in analytic continuation. -/
private theorem toDiffFlat_xiShift_eq_update {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.toDiffFlat k d (xiShift j r z t) =
      Function.update (BHW.toDiffFlat k d z) (finProdFinEquiv (j, r))
        (BHW.toDiffFlat k d z (finProdFinEquiv (j, r)) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  simp only [BHW.toDiffFlat, BHW.flattenCfg]
  simp only [finProdFinEquiv.symm_apply_apply]
  have hflat :
      BHW.flattenCfg k d (BHW.diffCoordEquiv k d z) (finProdFinEquiv (i, μ)) =
        BHW.diffCoordEquiv k d z i μ := by
    simp [BHW.flattenCfg]
  by_cases hμ : μ = r
  · subst hμ
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i.val = 0
      · simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0]
      · have hpred_not : ¬ i.val ≤ i.val - 1 := by omega
        simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0, hpred_not]
        ring
    · by_cases hij_lt : i.val < j.val
      · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
          intro h
          apply hij
          exact congrArg Prod.fst (finProdFinEquiv.injective h)
        have hj_not_le : ¬ j.val ≤ i.val := not_le.mpr hij_lt
        by_cases hi0 : i.val = 0
        · have hj0 : j.val ≠ 0 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj0]
        · have hpred_not : ¬ j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_not_le, hpred_not]
      · have hj_le : j.val ≤ i.val := le_of_not_gt hij_lt
        by_cases hi0 : i.val = 0
        · have : False := by
            apply hij
            exact Fin.ext (by omega)
          exact False.elim this
        · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
            intro h
            apply hij
            exact congrArg Prod.fst (finProdFinEquiv.injective h)
          have hpred : j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hpred]
  · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, r) := by
      intro h
      apply hμ
      exact congrArg Prod.snd (finProdFinEquiv.injective h)
    by_cases hi0 : i.val = 0
    · simp [Function.update, hneq]
      rw [hflat]
      simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
    · by_cases hj_le : j.val ≤ i.val
      · by_cases hpred : j.val ≤ i.val - 1
        · simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ, hj_le, hpred]
        · have hji : j = i := by
            apply Fin.ext
            omega
          subst hji
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
      · simp [Function.update, hneq]
        rw [hflat]
        simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hμ]

/-- Inverse-chart form of `toDiffFlat_xiShift_eq_update`: updating exactly the
flattened difference coordinate `(j,r)` by `+ t` reconstructs the configuration
obtained from `xiShift j r` by the same increment. -/
private theorem fromDiffFlat_update_eq_xiShift {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (u : Fin (k * (d + 1)) → ℂ) (t : ℂ) :
    BHW.fromDiffFlat k d
        (Function.update u (finProdFinEquiv (j, r))
          (u (finProdFinEquiv (j, r)) + t)) =
      xiShift j r (BHW.fromDiffFlat k d u) t := by
  have hinj : Function.Injective (BHW.toDiffFlat k d) := by
    intro z₁ z₂ h
    simpa [BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₁,
      BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₂] using
      congrArg (BHW.fromDiffFlat k d) h
  apply hinj
  rw [BHW.toDiffFlat_fromDiffFlat]
  rw [toDiffFlat_xiShift_eq_update]
  simp [BHW.toDiffFlat_fromDiffFlat]

/-- Affine version of `fromDiffFlat_update_eq_xiShift`: replacing the flattened
coordinate `(j,r)` by an arbitrary value `w` corresponds to `xiShift` by the
increment `w - u(j,r)`. This is the form used by one-variable slice maps
written with `Function.update`. -/
theorem fromDiffFlat_update_eq_xiShift_sub {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (u : Fin (k * (d + 1)) → ℂ) (w : ℂ) :
    BHW.fromDiffFlat k d
        (Function.update u (finProdFinEquiv (j, r)) w) =
      xiShift j r (BHW.fromDiffFlat k d u)
        (w - u (finProdFinEquiv (j, r))) := by
  rw [← fromDiffFlat_update_eq_xiShift (j := j) (r := r) (u := u)
    (t := w - u (finProdFinEquiv (j, r)))]
  congr 1
  ext q
  by_cases hq : q = finProdFinEquiv (j, r)
  · subst hq
    simp [Function.update]
  · simp [Function.update, hq]

/-- Tail Euclidean time shift starting at index `j`: points with index `i ≥ j`
are shifted by the real time vector `timeShiftVec d t`, earlier points are fixed. -/
private def tailTimeShiftConfig {d k : ℕ} (j : Fin k) (t : ℝ)
    (x : NPointDomain d k) : NPointDomain d k :=
  fun i => if j.val ≤ i.val then x i + timeShiftVec d t else x i

/-- Sign-correct inverse form of `osConjTensorProduct_timeShift_eq_tailShift`.
A positive tail shift of the right block corresponds to a negative time shift on
the right Schwartz factor. This fixes the sign convention needed when a flat
coordinate update by `+ t * I` is converted back to the OS semigroup picture. -/
private theorem osConjTensorProduct_tailTimeShift_eq_timeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x) =
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (-t) g)) x := by
  have htail :=
    osConjTensorProduct_timeShift_eq_tailShift (d := d) f g (-t) x
  have hneg_shift : -timeShiftVec d (-t) = timeShiftVec d t := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  have hcfg :
      (fun i => if h : n ≤ i.val then x i - timeShiftVec d (-t) else x i) =
        tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x := by
    funext i
    by_cases hi : n ≤ i.val
    · simp [tailTimeShiftConfig, hi, sub_eq_add_neg, hneg_shift]
    · simp [tailTimeShiftConfig, hi]
  rw [hcfg] at htail
  exact htail.symm

/-- Forward form of `osConjTensorProduct_tailTimeShift_eq_timeShift`: a positive
time shift on the right Schwartz factor is evaluation of the unshifted tensor
product on the configuration with the right block shifted by `- timeShiftVec d t`.
Written with `tailTimeShiftConfig`, this is the form that matches a flat update
by `- t * I`. -/
private theorem osConjTensorProduct_timeShift_eq_tailTimeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ (-t) x) := by
  simpa using
    (osConjTensorProduct_tailTimeShift_eq_timeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := -t) (x := x)).symm

/-- Wightman-side analogue of `osConjTensorProduct_timeShift_eq_tailTimeShift`:
the right-factor positive time shift can be moved from the test function to the
configuration by the same tail block translation. This is the exact
configuration-space bookkeeping later used in the transformed-image matrix
element comparison. -/
private theorem conjTensorProduct_timeShift_eq_tailTimeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      (f.conjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ (-t) x) := by
  let y : NPointDomain d (n + m) :=
    tailTimeShiftConfig (d := d) ⟨n, by omega⟩ (-t) x
  have hsplitFirst : splitFirst n m y = splitFirst n m x := by
    ext i μ
    have hi : ¬ n ≤ (Fin.castAdd m i).val := by
      simpa using (not_le_of_gt i.isLt)
    change (if n ≤ (Fin.castAdd m i).val then
        x (Fin.castAdd m i) + timeShiftVec d (-t) else
        x (Fin.castAdd m i)) μ = x (Fin.castAdd m i) μ
    rw [if_neg hi]
  have hsplitLast :
      splitLast n m y = fun i => x (Fin.natAdd n i) + timeShiftVec d (-t) := by
    ext i μ
    have hi : n ≤ (Fin.natAdd n i).val := by
      simp [Fin.natAdd]
    change (if n ≤ (Fin.natAdd n i).val then
        x (Fin.natAdd n i) + timeShiftVec d (-t) else
        x (Fin.natAdd n i)) μ =
      (x (Fin.natAdd n i) + timeShiftVec d (-t)) μ
    rw [if_pos hi]
  have hshift :
      (fun i => splitLast n m x i - timeShiftVec d t) =
        fun i => x (Fin.natAdd n i) + timeShiftVec d (-t) := by
    ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitLast, timeShiftVec]
      ring
    · simp [splitLast, timeShiftVec, hμ]
  simp only [SchwartzMap.conjTensorProduct_apply, timeShiftSchwartzNPoint_apply]
  rw [hsplitFirst, hsplitLast, hshift]

/-- Tail translation of the right block preserves Lebesgue measure on configuration
space. This is the change-of-variables ingredient for converting the sign-correct
flat-update slice picture back to the Euclidean integral. -/
private theorem rightBlockTailShift_measurePreserving {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t)
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t =
      (fun (x : NPointDomain d (n + m)) (i : Fin (n + m)) =>
        (if h : n ≤ i.val then fun y : SpacetimeDim d => y + timeShiftVec d t else id) (x i)) by
      funext x i
      by_cases h : n ≤ i.val <;> simp [tailTimeShiftConfig, h]]
  exact MeasureTheory.volume_preserving_pi
    (fun i : Fin (n + m) => by
      by_cases h : n ≤ i.val
      · simpa [h] using
          (MeasureTheory.measurePreserving_add_right
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))
            (timeShiftVec d t))
      · simpa [h] using
          (MeasureTheory.MeasurePreserving.id
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))

/-- The right-block tail shift is a measurable equivalence, with inverse given by
shifting the same tail by `-t`. This packages the change of variables needed in
the Euclidean integral form of the slice identity. -/
private def rightBlockTailShiftMeasurableEquiv {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    NPointDomain d (n + m) ≃ᵐ NPointDomain d (n + m) where
  toEquiv :=
    { toFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t
      invFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ (-t)
      left_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi]
      right_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi] }
  measurable_toFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))
  measurable_invFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))

/-- Change of variables under the right-block tail shift. Combined with the
sign-correct pointwise bridge lemmas above, this is the generic integral shell
needed for the remaining `schwinger_continuation_base_step` slice theorem. -/
private theorem integral_comp_rightBlockTailShift {n m : ℕ}
    (hm : 0 < m) (t : ℝ)
    {e : NPointDomain d (n + m) → ℂ} :
    ∫ x, e (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t x) =
      ∫ x, e x := by
  let Ψ := rightBlockTailShiftMeasurableEquiv (d := d) (n := n) (m := m) hm t
  have hmp : MeasureTheory.MeasurePreserving
      (Ψ : NPointDomain d (n + m) → NPointDomain d (n + m))
      MeasureTheory.volume MeasureTheory.volume := by
    simpa [Ψ] using rightBlockTailShift_measurePreserving (d := d) (n := n) (m := m) hm t
  exact hmp.integral_comp' (f := Ψ) e

/-- On Wick-rotated Euclidean configurations, the complex ξ-shift in the time
difference coordinate `(j,0)` is exactly the Wick rotation of a real tail time
shift on the underlying Euclidean configuration. -/
private theorem xiShift_wickRotate_eq_tailTimeShift {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    xiShift j 0 (fun i => wickRotatePoint (x i)) ((t : ℂ) * Complex.I) =
      fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i) := by
  ext i μ
  by_cases hji : j.val ≤ i.val
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec]
      ring
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec, hμ]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint]
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, hμ]

/-- Flattened-difference form of `xiShift_wickRotate_eq_tailTimeShift`: a flat
update by `+ t I` in the `(j,0)` coordinate is exactly the Wick-rotated tail
time shift on Euclidean configurations. This is the coordinate bridge from flat
slice updates back to the OS semigroup picture. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) + (t : ℂ) * Complex.I) := by
  rw [← xiShift_wickRotate_eq_tailTimeShift (d := d) (j := j) (x := x) (t := t)]
  simpa using
    toDiffFlat_xiShift_eq_update (j := j) (r := (0 : Fin (d + 1)))
      (z := fun i => wickRotatePoint (x i)) (t := (t : ℂ) * Complex.I)

/-- Sign-correct specialization of `toDiffFlat_wickRotate_tailTimeShift_eq_update`:
shifting the Euclidean tail by `-t` corresponds to updating the flattened time
difference coordinate by `- t * I`. This is the form aligned with the positive
OS semigroup parameter in `timeShiftSchwartzNPoint t`. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update_sub {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j (-t) x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    toDiffFlat_wickRotate_tailTimeShift_eq_update (d := d) (j := j) (x := x) (-t)

/-- Generic simple-tensor slice identity under the Euclidean integral. A positive
time shift on the right Schwartz factor is converted into a flat update by
`- t * I` in the split time-difference coordinate, with the intervening tail
translation absorbed by `integral_comp_rightBlockTailShift`. This is the core
integral shell for the remaining `schwinger_continuation_base_step` assembly. -/
private theorem simpleTensor_flatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Φ : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Φ (Function.update
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
          (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y *
          Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let e : NPointDomain d (n + m) → ℂ := fun y =>
    (f.osConjTensorProduct g) y *
      Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i)))
  have hshell :
      ∀ x : NPointDomain d (n + m),
        e (tailTimeShiftConfig (d := d) j (-t) x) =
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
            Φ (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) := by
    intro x
    unfold e
    rw [toDiffFlat_wickRotate_tailTimeShift_eq_update_sub (d := d) (j := j) (x := x) (t := t)]
    rw [osConjTensorProduct_timeShift_eq_tailTimeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := t) (x := x)]
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Φ (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m), e (tailTimeShiftConfig (d := d) j (-t) x) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simpa [j] using (hshell x).symm
    _ = ∫ x : NPointDomain d (n + m), e x := by
        simpa [j] using
          (integral_comp_rightBlockTailShift (d := d) (n := n) (m := m) (hm := hm)
            (t := -t) (e := e))
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
        rfl

/-- Configuration-space form of `simpleTensor_flatUpdate_integral_eq`: composing
the flat update with `fromDiffFlat` yields the same Euclidean slice identity. -/
private theorem simpleTensor_fromDiffFlatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I))) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  simpa [Function.comp_apply, BHW.fromDiffFlat_toDiffFlat] using
    (simpleTensor_flatUpdate_integral_eq (d := d) (n := n) (m := m)
      (hm := hm) (f := f) (g := g) (t := t)
      (Φ := Ψ ∘ BHW.fromDiffFlat (n + m) d))

/-- Integrated ξ-shift form of the simple-tensor slice identity. A flat update by
`- t * I` in the split time-difference coordinate is exactly the same Euclidean
integral as the positive right-factor time shift. -/
private theorem simpleTensor_xiShift_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hslice :
      ∀ x : NPointDomain d (n + m),
        BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (j, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) =
          xiShift j 0 (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I) := by
    intro x
    let u : Fin ((n + m) * (d + 1)) → ℂ :=
      BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
    simpa [u, sub_eq_add_neg, BHW.fromDiffFlat_toDiffFlat] using
      (fromDiffFlat_update_eq_xiShift (j := j) (r := (0 : Fin (d + 1)))
        (u := u) (t := -(t : ℂ) * Complex.I))
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (BHW.fromDiffFlat (n + m) d
            (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I))) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [hslice x]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
        simpa [j] using
          (simpleTensor_fromDiffFlatUpdate_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ))

/-- Witness-side version of `simpleTensor_xiShift_integral_eq`: moving the positive
right-factor time shift from the Schwartz tensor term to the Euclidean witness
changes the witness by `+ t * I` in the split time-difference coordinate. -/
theorem simpleTensor_timeShift_integral_eq_xiShift {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      Ψ (fun i => wickRotatePoint (x i)) *
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hcancel : (-(t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
    ring
  calc
    ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (fun i => wickRotatePoint (x i)) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simp [mul_comm]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
        simpa [j, xiShift_add_same, xiShift_zero, hcancel] using
          (simpleTensor_xiShift_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t)
            (Ψ := fun z =>
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z
                ((t : ℂ) * Complex.I))))
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        simp [mul_comm]

/-- Wightman-side analogue of `simpleTensor_timeShift_integral_eq_xiShift`:
moving the positive time shift from the right tensor factor to the Euclidean
configuration produces the same `ξ`-shift shell, but now against the Borchers
`conjTensorProduct`. This is the spatial bookkeeping input for the later
Section-4.3 / Lemma-4.2 matrix-element adapter. -/
theorem simpleTensor_timeShift_integral_eq_xiShift_conj {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      Ψ (fun i => wickRotatePoint (x i)) *
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.conjTensorProduct g) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let e : NPointDomain d (n + m) → ℂ := fun y =>
    Ψ (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t y i)) *
      (f.conjTensorProduct g) y
  have htail_cancel :
      ∀ x : NPointDomain d (n + m),
        tailTimeShiftConfig (d := d) j t
            (tailTimeShiftConfig (d := d) j (-t) x) = x := by
    intro x
    ext i μ
    by_cases hi : n ≤ i.val
    · by_cases hμ : μ = 0
      · subst hμ
        simp [j, tailTimeShiftConfig, hi, timeShiftVec]
      · simp [j, tailTimeShiftConfig, hi, timeShiftVec, hμ]
    · simp [j, tailTimeShiftConfig, hi]
  calc
    ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.conjTensorProduct g)
            (tailTimeShiftConfig (d := d) j (-t) x) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [conjTensorProduct_timeShift_eq_tailTimeShift
          (d := d) (f := f) (g := g) (hm := hm) (t := t) (x := x)]
    _ = ∫ x : NPointDomain d (n + m),
          e (tailTimeShiftConfig (d := d) j (-t) x) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        change (Ψ (fun i => wickRotatePoint (x i)) *
            (f.conjTensorProduct g) (tailTimeShiftConfig (d := d) j (-t) x)) =
          Ψ (fun i =>
              wickRotatePoint
                (tailTimeShiftConfig (d := d) j t
                  (tailTimeShiftConfig (d := d) j (-t) x) i)) *
            (f.conjTensorProduct g) (tailTimeShiftConfig (d := d) j (-t) x)
        rw [htail_cancel x]
    _ = ∫ x : NPointDomain d (n + m), e x := by
        simpa [j] using
          (integral_comp_rightBlockTailShift (d := d) (n := n) (m := m) (hm := hm)
            (t := -t) (e := e))
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.conjTensorProduct g) y := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        have hPsi :
            Ψ (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t y i)) =
              Ψ (xiShift j 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
          simpa [j] using congrArg Ψ
            (xiShift_wickRotate_eq_tailTimeShift (d := d) (j := j) (x := y) (t := t)).symm
        change
          Ψ (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t y i)) *
              (f.conjTensorProduct g) y =
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.conjTensorProduct g) y
        rw [hPsi]

/-- If a Euclidean witness `Ψ` recovers `OS.S (n+m)` on zero-diagonal tests, then
the positive right-factor time shift of a simple tensor is recovered by the same
witness evaluated on the `+ t * I` ξ-shifted Euclidean configuration. This is the
direct `OS.S`-level slice identity needed before the finite-sum `ExpandBoth`
assembly in `schwinger_continuation_base_step`. -/
theorem schwinger_simpleTensor_timeShift_eq_xiShift {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  have hg_shift_ord :
      tsupport ((timeShiftSchwartzNPoint (d := d) t g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m := by
    exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  have hvanish_shift :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f) (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  calc
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          ((ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))).1 x) := by
        exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
        simp [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes, hvanish_shift]
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y := by
        exact simpleTensor_timeShift_integral_eq_xiShift
          (d := d) (n := n) (m := m) (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ)

/-- Concentrated-right-factor finite-sum Euclidean recovery. For a fixed split point
`m > 0`, the positive-real restriction of the one-variable OS holomorphic matrix
element against a concentrated right factor is the finite sum of the corresponding
`ξ`-shifted Euclidean witnesses over the left Borchers components. This is the first
genuine finite-sum upgrade of `schwinger_simpleTensor_timeShift_eq_xiShift`. -/
theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single_xiShift_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (N : ℕ) → (Fin N → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (N : ℕ) (h : ZeroDiagonalSchwartz d N),
      OS.S N h = ∫ x : NPointDomain d N,
        Ψ N (fun i => wickRotatePoint (x i)) * (h.1 x))
    (F : PositiveTimeBorchersSequence d)
    {m : ℕ} (hm : 0 < m)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∫ y : NPointDomain d (n + m),
          Ψ (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (((F : BorchersSequence d).funcs n).osConjTensorProduct g) y := by
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
    (d := d) (OS := OS) (lgc := lgc) (F := F)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht]
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact schwinger_simpleTensor_timeShift_eq_xiShift
    (d := d) (OS := OS) (hm := hm) (Ψ := Ψ (n + m))
    (hΨ_euclid := hΨ_euclid (n + m))
    (f := ((F : BorchersSequence d).funcs n))
    (hf_ord := F.ordered_tsupport n)
    (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Single-split Euclidean recovery before the `ξ`-shift rewrite. On positive real
points, the concentrated `ExpandBoth` term agrees with the direct Euclidean integral
against the time-shifted simple tensor. This branch is needed in the `m = 0` case,
where there is no split time-difference variable to shift. -/
private theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_euclid
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
  have hreal :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    rw [OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence]
    have hshift_single :
        ∀ k,
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
            (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
      intro k
      by_cases hk : k = m
      · subst hk
        simp [BorchersSequence.single]
      · simp [BorchersSequence.single, hk]
    calc
      OSInnerProduct d OS.S (BorchersSequence.single n f)
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
        OSInnerProduct d OS.S (BorchersSequence.single n f)
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)) := by
            exact OSInnerProduct_congr_right d OS.S OS.E0_linear
              (BorchersSequence.single n f)
              (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
              (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
              hshift_single
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
            simpa using
              (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
                (timeShiftSchwartzNPoint (d := d) t g))
  have hg_shift_ord :
      tsupport ((timeShiftSchwartzNPoint (d := d) t g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m := by
    exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  have hvanish_shift :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f) (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  calc
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := hreal
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            ((ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))).1 x) := by
        exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
        simp [hvanish_shift]

/-- Single-split bridge from the semigroup-side holomorphic term to the Euclidean
ξ-shift witness. On positive real points, the public `ExpandBoth` value for
concentrated left/right Borchers sequences matches the corresponding shifted
simple-tensor Schwinger term, which is then rewritten by
`schwinger_simpleTensor_timeShift_eq_xiShift`. This is the first production theorem
that directly connects the one-variable OS holomorphic family to the Euclidean
slice witness used in `schwinger_continuation_base_step`. -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  have hreal :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    rw [OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence]
    have hshift_single :
        ∀ k,
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
            (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
      intro k
      by_cases hk : k = m
      · subst hk
        simp [BorchersSequence.single]
      · simp [BorchersSequence.single, hk]
    calc
      OSInnerProduct d OS.S (BorchersSequence.single n f)
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
        OSInnerProduct d OS.S (BorchersSequence.single n f)
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)) := by
            exact OSInnerProduct_congr_right d OS.S OS.E0_linear
              (BorchersSequence.single n f)
              (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
              (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
              hshift_single
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
            simpa using
              (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
                (timeShiftSchwartzNPoint (d := d) t g))
  exact hreal.trans <|
    schwinger_simpleTensor_timeShift_eq_xiShift (d := d) (OS := OS)
      (hm := hm) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Finite double-sum Euclidean recovery for `ExpandBoth` on positive real points.
Each summand is rewritten honestly according to whether the right block contributes
a genuine time-difference variable (`m > 0`) or is the vacuum branch (`m = 0`). -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (N : ℕ) → (Fin N → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (N : ℕ) (h : ZeroDiagonalSchwartz d N),
      OS.S N h = ∫ x : NPointDomain d N,
        Ψ N (fun i => wickRotatePoint (x i)) * (h.1 x))
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G (t : ℂ) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          if hm : 0 < m then
            ∫ y : NPointDomain d (n + m),
              Ψ (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((G : BorchersSequence d).funcs m)) y
          else
            ∫ y : NPointDomain d (n + m),
              Ψ (n + m) (fun i => wickRotatePoint (y i)) *
                (((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))) y := by
  unfold OSInnerProductTimeShiftHolomorphicValueExpandBoth
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm_range
  by_cases hm : 0 < m
  · simp [hm]
    calc
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m)) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))) := by
            exact OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs m))
              (hg_ord := G.ordered_tsupport m)
              (hg_compact := hG_compact m)
              (t := t) ht
      _ = ∫ y : NPointDomain d (n + m),
            Ψ (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (((F : BorchersSequence d).funcs n).osConjTensorProduct
                ((G : BorchersSequence d).funcs m)) y := by
            exact schwinger_simpleTensor_timeShift_eq_xiShift
              (d := d) (OS := OS) (hm := hm) (Ψ := Ψ (n + m))
              (hΨ_euclid := hΨ_euclid (n + m))
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs m))
              (hg_ord := G.ordered_tsupport m)
              (t := t) ht
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    simp
    have hg_shift_ord :
        tsupport
            ((timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0) :
                SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) ⊆
          OrderedPositiveTimeRegion d 0 := by
      exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) t ht ((G : BorchersSequence d).funcs 0) (G.ordered_tsupport 0)
    have hvanish_shift :
        VanishesToInfiniteOrderOnCoincidence
          (((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))) := by
      exact
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (f := ((F : BorchersSequence d).funcs n))
          (g := timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))
          (F.ordered_tsupport n) hg_shift_ord
    calc
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single 0 (((G : BorchersSequence d).funcs 0))
            (G.ordered_tsupport 0)) (t : ℂ) =
        OS.S n (ZeroDiagonalSchwartz.ofClassical
          ((((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))))) := by
            simpa using OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs 0))
              (hg_ord := G.ordered_tsupport 0)
              (hg_compact := hG_compact 0)
              (t := t) ht
      _ = ∫ y : NPointDomain d n,
            Ψ n (fun i => wickRotatePoint (y i)) *
              ((ZeroDiagonalSchwartz.ofClassical
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))))).1 y) := by
            exact hΨ_euclid n
              (ZeroDiagonalSchwartz.ofClassical
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0)))))
      _ = ∫ y : NPointDomain d n,
            Ψ n (fun i => wickRotatePoint (y i)) *
              ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))) y) := by
            simp [hvanish_shift]

theorem hasCompactSupport_onePointToFin1
    (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    HasCompactSupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) := by
  simpa [onePointToFin1CLM] using
    hh_compact.comp_homeomorph
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph)

theorem onePoint_osConjTensorProduct_apply
    (χ h : SchwartzSpacetime d)
    (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) =
      χ (y 0) * h (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h : SchwartzNPoint d 1)) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast]

/-- The two-point Schwinger product shell is exactly the OS Hilbert inner
product of the corresponding one-point vectors. This is the canonical bilinear
bridge behind the nuclear-extension route for `k = 2`. -/
theorem schwinger_twoPointProductLift_eq_onePointInner
    (OS : OsterwalderSchraderAxioms d)
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift χ h)) =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ))
            hχ_pos⟧) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d h)
            hh_pos⟧) : OSHilbertSpace OS)) := by
  have hleft_vanish :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ)).osConjTensorProduct
          (onePointToFin1CLM d h)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (g := onePointToFin1CLM d h)
      hχ_pos hh_pos
  have hright_vanish :
      VanishesToInfiniteOrderOnCoincidence (twoPointProductLift χ h) := by
    have hprod_eq :
        (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ)).osConjTensorProduct
          (onePointToFin1CLM d h) =
        twoPointProductLift χ h := by
      ext x
      exact onePoint_osConjTensorProduct_apply (d := d) χ h x
    simpa [hprod_eq] using hleft_vanish
  have hzeroeq :
      ZeroDiagonalSchwartz.ofClassical (twoPointProductLift χ h) =
        ZeroDiagonalSchwartz.ofClassical
          ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ)).osConjTensorProduct
            (onePointToFin1CLM d h)) := by
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointProductLift χ h) hright_vanish]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ)).osConjTensorProduct
        (onePointToFin1CLM d h))) hleft_vanish]
    apply Subtype.ext
    ext x
    symm
    exact onePoint_osConjTensorProduct_apply (d := d) χ h x
  have hos :
      OSInnerProduct d OS.S
        (BorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
        (BorchersSequence.single 1 (onePointToFin1CLM d h : SchwartzNPoint d 1)) =
      OS.S 2
        ⟨((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ)).osConjTensorProduct
            (onePointToFin1CLM d h)), hleft_vanish⟩ := by
    rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
      (n := 1) (m := 1)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (g := onePointToFin1CLM d h)]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ)).osConjTensorProduct
        (onePointToFin1CLM d h))) hleft_vanish]
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift χ h))
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ)).osConjTensorProduct
            (onePointToFin1CLM d h))) := by rw [hzeroeq]
    _ = @inner ℂ (OSHilbertSpace OS) _
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ))
              hχ_pos⟧) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d h)
              hh_pos⟧) : OSHilbertSpace OS)) := by
          rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
            (f := ((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ)).osConjTensorProduct
              (onePointToFin1CLM d h))) hleft_vanish]
          rw [UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
          rw [PositiveTimeBorchersSequence.osInner]
          simpa using hos.symm

/-- For a fixed admissible left factor `χ`, the two-point Schwinger product-shell
pairing is continuous in the honest positive-time compact-support right factor. -/
theorem schwinger_twoPointProductLift_continuous_right_on_positive
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    Continuous (fun h : positiveTimeCompactSupportSubmodule d =>
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d)))) := by
  let raw :
      positiveTimeCompactSupportSubmodule d →L[ℂ] SchwartzNPoint d 2 :=
    (SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
      ((onePointToFin1CLM d).comp (positiveTimeCompactSupportValCLM d))
  have hraw :
      ∀ h : positiveTimeCompactSupportSubmodule d,
        raw h = twoPointProductLift χ (h : SchwartzSpacetime d) := by
    intro h
    rfl
  have hvanish :
      ∀ h : positiveTimeCompactSupportSubmodule d,
        VanishesToInfiniteOrderOnCoincidence
          (twoPointProductLift χ (h : SchwartzSpacetime d)) := by
    intro h
    have hh_pos :
        tsupport (((onePointToFin1CLM d (h : SchwartzSpacetime d) :
            SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆
          OrderedPositiveTimeRegion d 1 := by
      intro x hx
      have hx0 : x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
        by_contra hx0
        have hzero :
            (x : NPointDomain d 1) ∉ tsupport
              (((onePointToFin1CLM d (h : SchwartzSpacetime d) :
                  SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
          rw [notMem_tsupport_iff_eventuallyEq] at hx0 ⊢
          simpa [onePointToFin1CLM_apply] using
            hx0.comp_tendsto
              ((continuous_apply 0).continuousAt.tendsto :
                Filter.Tendsto (fun y : NPointDomain d 1 => y 0) (nhds x) (nhds (x 0)))
        exact hzero hx
      have hpos0 : 0 < (x 0) 0 := h.property.1 hx0
      simpa [OrderedPositiveTimeRegion] using hpos0
    have hos :
        VanishesToInfiniteOrderOnCoincidence
          ((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
            ((onePointToFin1CLM d (h : SchwartzSpacetime d)) : SchwartzNPoint d 1)) :=
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d)
        (f := SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        (g := ((onePointToFin1CLM d (h : SchwartzSpacetime d)) : SchwartzNPoint d 1))
        hχ_pos hh_pos
    have hEq :
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          ((onePointToFin1CLM d (h : SchwartzSpacetime d)) : SchwartzNPoint d 1)) =
        twoPointProductLift χ (h : SchwartzSpacetime d) := by
      ext x
      exact onePoint_osConjTensorProduct_apply (d := d) χ
        (h : SchwartzSpacetime d) x
    rw [hEq] at hos
    exact hos
  let tensorMap :
      positiveTimeCompactSupportSubmodule d → ZeroDiagonalSchwartz d 2 :=
    fun h => ⟨raw h, by
      rw [hraw h]
      exact hvanish h⟩
  have htensor : Continuous tensorMap := by
    exact raw.continuous.subtype_mk _
  have hF :
      (fun h : positiveTimeCompactSupportSubmodule d =>
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift χ (h : SchwartzSpacetime d)))) =
      (fun h => OS.S 2 (tensorMap h)) := by
    funext h
    rw [show tensorMap h = ⟨twoPointProductLift χ (h : SchwartzSpacetime d), hvanish h⟩ by
      apply Subtype.ext
      simpa [tensorMap] using hraw h]
    rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointProductLift χ (h : SchwartzSpacetime d)) (hvanish h)]
  simpa [hF] using
    ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).continuous.comp htensor)

theorem onePoint_osConjTensorProduct_timeShift_apply
    (χ h : SchwartzSpacetime d) (t : ℝ)
    (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y) =
      χ (y 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1 - timeShiftVec d t) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast,
            timeShiftSchwartzNPoint_apply]
    _ = χ (y 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (y 1) := by
          simp [SCV.translateSchwartz_apply, sub_eq_add_neg]

theorem twoPoint_flattenCfg_xiShift_secondTime_eq_update
    (z : Fin 2 → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.flattenCfg 2 d (xiShift ⟨1, by omega⟩ 0 z t) =
      Function.update
        (BHW.flattenCfg 2 d z)
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        (BHW.flattenCfg 2 d z (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  · simp [BHW.flattenCfg, xiShift, Function.update]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.flattenCfg, xiShift, Function.update]
    · simp [BHW.flattenCfg, xiShift, Function.update, hμ]

omit [NeZero d] in
theorem zero_not_mem_tsupport_translate_of_notMem
    (h : SchwartzSpacetime d) (a : SpacetimeDim d)
    (ha : a ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    (0 : SpacetimeDim d) ∉
      tsupport (((SCV.translateSchwartz a h : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ)) := by
  rw [notMem_tsupport_iff_eventuallyEq] at ha ⊢
  have hcont :
      Filter.Tendsto (fun x : SpacetimeDim d => x + a)
        (nhds (0 : SpacetimeDim d)) (nhds a) := by
    simpa using ((continuous_id.add continuous_const).continuousAt.tendsto
      (x := (0 : SpacetimeDim d)))
  simpa [SCV.translateSchwartz_apply] using ha.comp_tendsto hcont

omit [NeZero d] in
theorem neg_timeShiftVec_not_mem_positive_tsupport
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    (- timeShiftVec d t : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
  intro hx
  have hpos := hh_pos hx
  have hpos0 : 0 < (- timeShiftVec d t : SpacetimeDim d) 0 := hpos
  have htime : (- timeShiftVec d t : SpacetimeDim d) 0 = -t := by
    simp [timeShiftVec]
  linarith [hpos0, ht]

private theorem onePointToFin1_tsupport_subset_orderedPositiveTimeRegion_of_tsupport_positive
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro x hx
  have hx0 : x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    by_contra hx0
    have hzero :
        (x : NPointDomain d 1) ∉ tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx0 ⊢
      simpa [onePointToFin1CLM_apply] using
        hx0.comp_tendsto ((continuous_apply 0).continuousAt.tendsto : Filter.Tendsto
          (fun y : NPointDomain d 1 => y 0) (nhds x) (nhds (x 0)))
    exact hzero hx
  have hpos0 : 0 < (x 0) 0 := hh_pos hx0
  simpa [OrderedPositiveTimeRegion] using hpos0

/-- A first honest `k = 2` continuation statement from the one-variable OS
holomorphic bridge. Choosing the left one-point factor as an OS-conjugated
center cutoff and the right one-point factor as a compactly supported
difference-variable test produces a holomorphic function on the right
half-plane whose positive-real restriction is the explicit `ξ`-shifted
Euclidean two-point integral. -/
theorem exists_singleSplit_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
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
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m g hg_ord
  refine ⟨OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G, ?_, ?_⟩
  · simpa [F, G] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G
  · intro t ht
    simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      (OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
        (t := t) ht)

/-- A first honest `k = 2` continuation statement from the one-variable OS
holomorphic bridge. Choosing the left one-point factor as an OS-conjugated
center cutoff and the right one-point factor as a compactly supported
difference-variable test produces a holomorphic function on the right
half-plane whose positive-real restriction is the explicit `ξ`-shifted
Euclidean two-point integral. -/
theorem exists_twoPoint_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
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
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)) hχ_pos
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d h : SchwartzNPoint d 1) hh_pos
  refine ⟨OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G, ?_, ?_⟩
  · simpa [F, G] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G
  · intro t ht
    have hh1_compact :
        HasCompactSupport (((((G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs 1 :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
      simpa [G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hasCompactSupport_onePointToFin1 (d := d) h hh_compact
    calc
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G (t : ℂ)
          = ∫ y : NPointDomain d (1 + 1),
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (((SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
                  (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) := by
            simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
              (OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
                (d := d) (OS := OS) (lgc := lgc) (hm := by omega)
                (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                (f := (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
                (hf_ord := hχ_pos)
                (g := (onePointToFin1CLM d h : SchwartzNPoint d 1))
                (hg_ord := hh_pos)
                (hg_compact := hh1_compact)
                (t := t) ht)
      _ = ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with y
            rw [onePoint_osConjTensorProduct_apply (d := d) χ h y]

/-- On positive real times, the explicit off-diagonal spectral Laplace function
of the OS time-shift semigroup for the simple pair `(χ, g)` is exactly the
product-shell `ξ`-shift witness integral. This is the concrete semigroup-side
real-axis formula behind the later normalized-center matching criteria. -/
theorem selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
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
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (χ (y 0) * g (y 1)) := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)) hχ_pos
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hg1_compact :
      HasCompactSupport (((((G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs 1 :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
    simpa [G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      hasCompactSupport_onePointToFin1 (d := d) g hg_compact
  calc
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
        (t : ℂ)
      = OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ) := by
          symm
          exact OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
            (d := d) OS lgc F G (t : ℂ) ht
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              (onePointToFin1CLM d g : SchwartzNPoint d 1))))) := by
          simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
            (OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
              (hf_ord := hχ_pos)
              (g := (onePointToFin1CLM d g : SchwartzNPoint d 1))
              (hg_ord := hg_pos)
              (hg_compact := hg1_compact)
              (t := t) ht)
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
              (onePointToFin1CLM d g : SchwartzNPoint d 1)) y) := by
          symm
          exact (schwinger_simpleTensor_timeShift_eq_xiShift
            (d := d) (OS := OS) (n := 1) (m := 1) (hm := by omega)
            (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            (f := (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
            (hf_ord := hχ_pos)
            (g := (onePointToFin1CLM d g : SchwartzNPoint d 1))
            (hg_ord := hg_pos)
            (t := t) ht).symm
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * g (y 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          rw [onePoint_osConjTensorProduct_apply (d := d) χ g y]

/-- For r ≥ 1, the ξ-shift stays in C_k^(r). The shift only modifies column r,
    and C_k^(r) only constrains columns with μ.val ≤ r-1. -/
private theorem xiShift_stays_in_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (j : Fin k) (t : ℝ) :
    xiShift j ⟨r, hr⟩ z₀ (t : ℂ) ∈ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  intro i μ hμ
  have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) := by
    intro heq; have := congr_arg Fin.val heq; simp at this; omega
  -- xiShift is identity at μ ≠ ⟨r'+1, _⟩
  have h_eq : ∀ i' : Fin k, xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t i' μ = z₀ i' μ := by
    intro i'
    unfold xiShift
    split_ifs with h
    · exact absurd h.2 hμ_ne
    · rfl
  rw [h_eq i]
  have h_prev : (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t ⟨i.val - 1, by omega⟩) μ =
                (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else z₀ ⟨i.val - 1, by omega⟩) μ := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
  rw [h_prev]
  exact hz₀ i μ hμ

/-- For r ≥ 1, ACR(r+1) is a subset of ACR(r): adding more imaginary-positivity
    constraints gives a smaller domain. -/
private theorem acr_succ_subset {d k r : ℕ} [NeZero d] (hr : 0 < r) :
    AnalyticContinuationRegion d k (r + 1) ⊆ AnalyticContinuationRegion d k r := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  intro z hz
  simpa [AnalyticContinuationRegion] using
    (fun i μ hμ => hz i μ (Nat.le_trans hμ (Nat.le_succ _)))

/-- **Mixed one-slice continuation domain** for the r → r+1 inductive step.

    `OneSliceContinuationDomain d k r hr i₀` is the "intermediate" domain where:
    - all ACR(r) positivity constraints hold (Im-differences > 0 for μ < r), AND
    - the new cumulative-difference coordinate for particle `i₀` at level r also
      has positive imaginary part: Im(z[i₀][r] - prev[i₀][r]) > 0,
    - but the other new r-th differences (for i ≠ i₀) remain unconstrained.

    **Why this domain matters**: ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain i₀
    (proved by `iInter_oneSliceContinuationDomain_eq_acr_succ`). The full Paley-Wiener
    continuation argument extends S_prev to ONE slice at a time: for each i₀, extend
    in the ξ[i₀][r] direction using 1D Paley-Wiener to get a holomorphic function on
    `OneSliceContinuationDomain i₀`. Then assemble all k slice extensions via Osgood's
    theorem to get holomorphicity on ACR(r+1).

    Ref: OS II, Theorem 4.1; Vladimirov §26 -/
def OneSliceContinuationDomain (d k r : ℕ) [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) : Set (Fin k → Fin (d + 1) → ℂ) :=
  { z |
      (∀ i : Fin k, ∀ μ : Fin (d + 1), μ.val < r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0) ∧
      let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
      (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 }

/-- Individual coordinate positivity condition is open (helper). -/
private theorem diffImPos_isOpen' {d k : ℕ} [NeZero d]
    (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
      (z i μ - prev μ).im > 0 } := by
  by_cases hi : i.val = 0
  · simpa [hi] using isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j))
    have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i))
    simpa [hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'

/-- `OneSliceContinuationDomain` is open. -/
theorem isOpen_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    IsOpen (OneSliceContinuationDomain d k r hr i₀) := by
  have : OneSliceContinuationDomain d k r hr i₀ =
      (⋂ i : Fin k, ⋂ μ : Fin (d + 1),
        { z : Fin k → Fin (d + 1) → ℂ |
          μ.val < r →
            let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
            (z i μ - prev μ).im > 0 }) ∩
      { z : Fin k → Fin (d + 1) → ℂ |
        let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
        (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 } := by
    ext z; simp [OneSliceContinuationDomain]
  rw [this]
  apply (isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_iInter_of_finite fun μ : Fin (d + 1) => ?_).inter (diffImPos_isOpen' i₀ ⟨r, hr⟩)
  by_cases hμ : μ.val < r
  · simpa [hμ] using diffImPos_isOpen' (d := d) (k := k) i μ
  · simp [hμ]

/-- ACR(r+1) ⊆ OneSliceContinuationDomain for each i₀. -/
theorem acr_succ_subset_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    AnalyticContinuationRegion d k (r + 1) ⊆ OneSliceContinuationDomain d k r hr i₀ := by
  intro z hz
  simp only [AnalyticContinuationRegion, OneSliceContinuationDomain, Set.mem_setOf_eq] at hz ⊢
  exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- OneSliceContinuationDomain ⊆ ACR(r) for r ≥ 1. -/
theorem oneSliceContinuationDomain_subset_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r) (i₀ : Fin k) :
    OneSliceContinuationDomain d k r hr i₀ ⊆ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  intro z hz
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  exact hz.1 i μ (by omega)

/-- ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain d k r hr i₀. -/
theorem iInter_oneSliceContinuationDomain_eq_acr_succ {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) :
    (⋂ i₀ : Fin k, OneSliceContinuationDomain d k r hr i₀) =
      AnalyticContinuationRegion d k (r + 1) := by
  ext z
  simp only [Set.mem_iInter, OneSliceContinuationDomain, AnalyticContinuationRegion,
    Set.mem_setOf_eq]
  constructor
  · intro h i μ hμ
    rcases Nat.lt_or_eq_of_le hμ with hlt | rfl
    · exact (h i).1 i μ hlt
    · exact (h i).2
  · intro hz i₀
    exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- Updating the i₀-th row's r-th entry to `prev₀ ⟨r,hr⟩ + w` (with Im(w) > 0)
    lands in `OneSliceContinuationDomain d k r hr i₀`. -/
theorem sliceUpdate_mem_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (i₀ : Fin k) {w : ℂ} (hw : 0 < w.im) :
    let prev₀ : Fin (d + 1) → ℂ :=
      if _ : i₀.val = 0 then 0 else z₀ ⟨i₀.val - 1, by omega⟩
    Function.update z₀ i₀
        (Function.update (z₀ i₀) ⟨r, hr⟩ (prev₀ ⟨r, hr⟩ + w))
      ∈ OneSliceContinuationDomain d k r hr i₀ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  have hμ_ne : (⟨r' + 1, by omega⟩ : Fin (d + 1)) ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) →
      False := fun h => h rfl
  refine ⟨fun i μ hμ => ?_, ?_⟩
  · have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) :=
        fun heq => by simp [heq] at hμ
    have h_eq : ∀ j : Fin k, Function.update z₀ i₀
        (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
          ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
            else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w)) j μ = z₀ j μ := by
      intro j
      by_cases hj : j = i₀
      · subst hj; simp [hμ_ne]
      · simp [hj]
    rw [h_eq i]
    have h_prev_eq :
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
          else Function.update z₀ i₀
            (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
              ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
                else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w))
            ⟨i.val - 1, by omega⟩) μ =
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z₀ ⟨i.val - 1, by omega⟩) μ := by
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
    rw [h_prev_eq]
    exact hz₀ i μ (by omega)
  · by_cases hi0 : i₀.val = 0
    · simpa [sub_eq_add_neg, Function.update, hi0] using hw
    · have hprev_ne : (⟨i₀.val - 1, by omega⟩ : Fin k) ≠ i₀ :=
        fun heq => absurd (congrArg Fin.val heq)
          (Nat.ne_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hi0) one_pos))
      simpa [sub_eq_add_neg, Function.update, hi0, hprev_ne, add_assoc, add_left_comm, add_comm]
        using hw


/-- **Domain restriction lemma: ACR(r+1) ⊆ ACR(r) (r ≥ 1).**

    This is a RESTRICTION lemma, not the OS II continuation step. Because
    ACR(r+1) ⊆ ACR(r) for r ≥ 1, any function holomorphic on ACR(r) is also
    holomorphic on ACR(r+1) by restriction (S_ext := S_prev).

    **This is NOT the full OS II argument.** The true OS II inductive step for r ≥ 1
    would extend holomorphicity to `OneSliceContinuationDomain`, which lies strictly
    between ACR(r+1) and ACR(r): `ACR(r+1) ⊆ OneSlice ⊆ ACR(r)`. Since OneSlice ⊆ ACR(r),
    a restriction argument suffices for holomorphicity on OneSlice, but not for the
    Paley-Wiener boundary value behavior needed to assemble the full OS continuation.
    The genuinely non-trivial OS II step is the base case r=0→1 (handled by
    `schwinger_continuation_base_step`), where ACR(0) (Im=0) and ACR(1) (Im>0)
    are disjoint and a Laplace/Paley-Wiener argument is indispensable.

    Ref: OS II, Theorem 4.1 (the domain inclusions) -/
theorem restrict_holomorphic_to_acr_succ {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (_ : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z :=
  ⟨S_prev, hS_prev.mono (acr_succ_subset hr_pos), fun _ _ => rfl⟩


/-- **Inductive continuation for `r ≥ 1` (OS II, Theorem 4.1).**

    Once the base-step has produced a holomorphic witness on `C_k^(1)`, every further
    stage `C_k^(r+1) ⊆ C_k^(r)` is obtained by restriction. The genuinely non-trivial
    analytic continuation is therefore concentrated in `schwinger_continuation_base_step`;
    this theorem is only the monotonicity step for the nested domains.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (hr : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  exact restrict_holomorphic_to_acr_succ k r hr hr_pos S_prev hS_prev

/-! ### Full analytic continuation from Euclidean to forward tube

After the base step, the active reconstruction chain already produces a holomorphic
witness on `C_k^(1)`, and `ForwardTube d k ⊆ C_k^(1)`. So the forward-tube existence
statement used below no longer depends on the separate Bochner route from
`C_k^(d+1)`.

The older Bochner approach from `C_k^(d+1)` remains mathematically interesting, but
it is not part of the active OS→Wightman pipeline here. The naive
"common SO(d+1)-orbit of the positive orthant, then convex hull" story is false, so
that side development needs a different geometric input before it can be reinstated.

Ref: OS II, Sections IV-V; Vladimirov Section 20.2 -/

/-- The forward tube already lies inside the first-step continuation region `C_k^(1)`,
    since each forward-cone difference has positive time component. -/
private theorem forwardTube_subset_acr_one {d k : ℕ} [NeZero d] :
    ForwardTube d k ⊆ AnalyticContinuationRegion d k 1 := by
  intro z hz
  rw [forwardTube_eq_imPreimage] at hz
  simp only [ForwardConeAbs, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  have htime :
      0 <
        ((z i 0).im -
          ((if h : i.val = 0 then (0 : Fin (d + 1) → ℝ)
            else fun ν => (z ⟨i.val - 1, by omega⟩ ν).im) 0)) := (hz i).1
  subst hμ0
  have htime' :
      ((if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨i.val - 1, by omega⟩) 0).im <
        (z i 0).im := by
    by_cases hi : i.val = 0
    · simpa [hi, sub_pos] using htime
    · simpa [hi, sub_pos] using htime
  simpa [Complex.sub_im, sub_pos] using htime'

/-- Iterate analytic continuation from the base-step witness on `C_k^(1)` to `C_k^(d+1)`.

    The real analytic continuation starts at `r = 1`, not `r = 0`: the base-step
    theorem `schwinger_continuation_base_step_full` produces the first holomorphic witness
    on `ACR(1)` directly from the Schwinger functional. For `r ≥ 1`, all further steps
    are restrictions along the inclusions `ACR(r+1) ⊆ ACR(r)`.

    This avoids treating `ACR(0)` as an open complex holomorphic domain and removes
    the need for a separate pointwise "base-region kernel" theorem.

    Ref: OS II, Theorem 4.1 -/
theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_rep⟩ := schwinger_continuation_base_step_full OS lgc k
  -- Invariant for r ≥ 1: holomorphicity on ACR(r) and preservation of the
  -- Euclidean pairing identity with OS.S.
  let P : ℕ → Prop := fun s =>
    ∃ (S_r : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_r (AnalyticContinuationRegion d k (s + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_r (fun j => wickRotatePoint (x j)) * (f.1 x))
  have hP0 : P 0 := ⟨S₁, hS₁_hol, hS₁_rep⟩
  have hstep : ∀ s, s + 1 < d + 1 → P s → P (s + 1) := by
    intro s hs hPs
    have hs_pos : 0 < s + 1 := Nat.succ_pos s
    rcases hPs with ⟨S_r, hS_r_hol, hS_r_rep⟩
    exact ⟨S_r, hS_r_hol.mono (acr_succ_subset hs_pos), hS_r_rep⟩
  have hP_all : ∀ s, s + 1 ≤ d + 1 → P s := by
    intro s hsle
    induction s with
    | zero =>
        exact hP0
    | succ s ih =>
        have hslt : s + 1 < d + 1 := by omega
        have hsle' : s + 1 ≤ d + 1 := by omega
        exact hstep (s := s) hslt (ih hsle')
  rcases hP_all d (by simp) with ⟨S_ext, hS_ext_hol, hS_ext_rep⟩
  exact ⟨S_ext, hS_ext_hol, hS_ext_rep⟩

/-- The chosen continuation witness together with the symmetry and growth
package inherited from the upstream `ACR(1)` assembly theorem.

This is the honest full theorem surface for the selected continuation witness
before restricting to the forward tube: besides ACR(1) holomorphy and Euclidean
reproduction, the same witness also carries forward-tube holomorphy,
permutation symmetry, common complex translation invariance, and global
polynomial growth on the forward tube. -/
theorem full_analytic_continuation_with_acr_symmetry_growth
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (AnalyticContinuationRegion d k 1) ∧
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        W_analytic (fun j => z (σ j)) = W_analytic z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        W_analytic (fun j => z j + a) = W_analytic z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (W_analytic (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        W_analytic (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d k,
          ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid, hS₁_perm, hS₁_trans, hS₁_negCanonical,
    C_bd, N, hC, hgrowth⟩ :=
    schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
      (d := d) OS lgc k
  refine ⟨S₁, hS₁_hol,
    hS₁_hol.mono (forwardTube_subset_acr_one (d := d) (k := k)),
    hS₁_euclid, hS₁_perm, hS₁_trans, hS₁_negCanonical, C_bd, N, hC, ?_⟩
  intro z hz
  exact hgrowth z ((forwardTube_subset_acr_one (d := d) (k := k)) hz)

/-- Forward-tube projection of
`full_analytic_continuation_with_acr_symmetry_growth`. -/
theorem full_analytic_continuation_with_symmetry_growth
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        W_analytic (fun j => z (σ j)) = W_analytic z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        W_analytic (fun j => z j + a) = W_analytic z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (W_analytic (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        W_analytic (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d k,
          ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨S₁, _hS₁_acr, hS₁_hol, hS₁_euclid, hS₁_perm, hS₁_trans,
    hS₁_negCanonical, C_bd, N, hC, hgrowth⟩ :=
    full_analytic_continuation_with_acr_symmetry_growth OS lgc k
  exact ⟨S₁, hS₁_hol, hS₁_euclid, hS₁_perm, hS₁_trans, hS₁_negCanonical,
    C_bd, N, hC, hgrowth⟩

/-- The same witness chosen by `full_analytic_continuation`, together with the
polynomial-growth package inherited from the upstream `ACR(1)` assembly theorem.

This keeps the OS-specific continuation side theorem-based: downstream boundary-
value arguments can use a growth theorem for the chosen witness without
introducing any extra OS-specific axiom. -/
theorem full_analytic_continuation_with_growth
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d k,
          ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid, _hS₁_perm, _hS₁_trans, _hS₁_negCanonical,
    C_bd, N, hC, hgrowth⟩ :=
    full_analytic_continuation_with_symmetry_growth OS lgc k
  refine ⟨S₁, hS₁_hol, hS₁_euclid, C_bd, N, hC, hgrowth⟩

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid, _C_bd, _N, _hC, _hgrowth⟩ :=
    full_analytic_continuation_with_growth OS lgc k
  refine ⟨S₁, hS₁_hol, hS₁_euclid⟩

/-! ### Downstream Boundary Values

Phase 4 boundary values, Phase 5 transfer theorems, and the final bridge
theorems now live in `OSToWightmanBoundaryValues.lean`. This file keeps the
semigroup and analytic-continuation core, including the live
`schwinger_continuation_base_step` blocker. -/

end
