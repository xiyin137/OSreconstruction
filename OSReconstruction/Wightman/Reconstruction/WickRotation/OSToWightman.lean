/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanACRKernelPackage
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# OS to Wightman Analytic Continuation Core

This file contains the continuation chain and general-k base step.
Base definitions (tube domains, coordinate helpers) are in
`OSToWightmanBase.lean`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal LineDeriv
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
    (hDense : Dense
      (((Submodule.span ℂ S : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k))))
    (hEq : ∀ f ∈ S, OS.S k f = ∫ x : NPointDomain d k, K x * (f.1 x)) :
    ∀ f : ZeroDiagonalSchwartz d k,
      OS.S k f = ∫ x : NPointDomain d k, K x * (f.1 x) := by
  have hL_eq :
      L = OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k := by
    apply ContinuousLinearMap.eq_of_eq_on_dense L
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k) hDense
    intro f hf
    change f ∈ Submodule.span ℂ S at hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro g hg
      rw [hL_apply]
      exact (hEq g hg).symm
    · simpa [OsterwalderSchraderAxioms.schwingerCLM] using (OS.E0_linear k).map_zero.symm
    · intro u v _ _ hu hv
      simp [hu, hv]
    · intro c u _ hu
      simp [hu]
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

private def admissibleProductTensorSubmodule {d : ℕ} (k : ℕ) :
    Submodule ℂ (ZeroDiagonalSchwartz d k) :=
  Submodule.span ℂ (admissibleProductTensorSet (d := d) k)

private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
    {d : ℕ} [NeZero d] {n : ℕ} {ψ : NPointDomain d n → ℂ} {f : SchwartzNPoint d n}
    (hψ : ψ.HasTemperateGrowth) (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply hψ f y)
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hψ.1 (f.smooth ⊤) x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
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
            (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
              ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ := hle
        _ = 0 := hsum_zero
    · exact hnonneg
  exact norm_eq_zero.mp hzero_norm

private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
    {d : ℕ} [NeZero d] {n : ℕ} {ψ f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) :=
  VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
    (ψ.hasTemperateGrowth) hf

omit [NeZero d] in
private theorem productTensor_cutoff_productTensor
    {d k : ℕ}
    (χs fs : Fin k → SchwartzSpacetime d) :
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs)
        (SchwartzMap.productTensor fs) =
      SchwartzMap.productTensor
        (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((SchwartzMap.productTensor χs : SchwartzNPoint d k) :
      NPointDomain d k → ℂ))
    (SchwartzMap.productTensor χs).hasTemperateGrowth
    (SchwartzMap.productTensor fs) x]
  rw [SchwartzMap.productTensor_apply]
  have hfactor :
      ∀ i : Fin k,
        (SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) (x i) =
          (χs i) (x i) * (fs i) (x i) := by
    intro i
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
      (χs i).hasTemperateGrowth (fs i) (x i)]
    simp [smul_eq_mul]
  simp [SchwartzMap.productTensor_apply, hfactor, smul_eq_mul, Finset.prod_mul_distrib]

omit [NeZero d] in
private theorem tsupport_productTensor_subset_pi_tsupport
    {d k : ℕ} (fs : Fin k → SchwartzSpacetime d) :
    tsupport
      ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
        NPointDomain d k → ℂ)
      ⊆ {x | ∀ i : Fin k, x i ∈ tsupport ((fs i : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ)} := by
  intro x hx i
  by_contra hxi
  have hlocal :
      ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) =ᶠ[𝓝 (x i)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxi
  have hcoord :
      Filter.Tendsto (fun y : NPointDomain d k => y i) (𝓝 x) (𝓝 (x i)) :=
    (continuous_apply i).continuousAt
  have hlocal_pi :
      ∀ᶠ y in 𝓝 x, (fs i) (y i) = 0 :=
    hcoord.eventually hlocal
  have hprod_zero :
      ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hlocal_pi] with y hy
    rw [SchwartzMap.productTensor_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hy
  exact (notMem_tsupport_iff_eventuallyEq.mpr hprod_zero) hx

omit [NeZero d] in
private theorem productTensor_vanishes_of_pairwise_disjoint_tsupport
    {d k : ℕ} (fs : Fin k → SchwartzSpacetime d)
    (hpair :
      ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((fs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ))) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hxprod hxcoin
  rcases hxcoin with ⟨i, j, hij, hEq⟩
  have hxi :
      x i ∈ tsupport ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
    tsupport_productTensor_subset_pi_tsupport fs hxprod i
  have hxj :
      x j ∈ tsupport ((fs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
    tsupport_productTensor_subset_pi_tsupport fs hxprod j
  exact Set.disjoint_left.mp (hpair i j hij) hxi (by simpa [hEq] using hxj)

omit [NeZero d] in
private theorem cutoff_productTensor_mem_admissibleProductTensorSubmodule
    {d k : ℕ} (χs fs : Fin k → SchwartzSpacetime d)
    (hχpair :
      ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((χs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ))) :
    let gs : Fin k → SchwartzSpacetime d :=
      fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)
    ∃ hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor gs),
      (⟨SchwartzMap.productTensor gs, hvanish⟩ : ZeroDiagonalSchwartz d k) ∈
        admissibleProductTensorSubmodule (d := d) k := by
  intro gs
  have hpair_gs :
      ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((gs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((gs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
    intro i j hij
    refine (hχpair i j hij).mono ?_ ?_
    · intro x hx
      exact (SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (f := (fs i)) hx).2
    · intro x hx
      exact (SchwartzMap.tsupport_smulLeftCLM_subset
        (g := ((χs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (f := (fs j)) hx).2
  let hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor gs) :=
    productTensor_vanishes_of_pairwise_disjoint_tsupport gs hpair_gs
  refine ⟨hvanish, ?_⟩
  exact Submodule.subset_span ⟨gs, hvanish, rfl⟩

omit [NeZero d] in
private theorem product_cutoff_fixed_mem_closure_admissibleProductTensorSubmodule
    {d k : ℕ} (χs : Fin k → SchwartzSpacetime d)
    (hχpair :
      ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((χs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ)))
    (F : ZeroDiagonalSchwartz d k)
    (hfix :
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs) F.1 = F.1) :
    F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  let S_all : Set (SchwartzNPoint d k) :=
    {G : SchwartzNPoint d k | ∃ fs : Fin k → SchwartzSpacetime d,
      G = SchwartzMap.productTensor fs}
  let M_all : Submodule ℂ (SchwartzNPoint d k) := Submodule.span ℂ S_all
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    admissibleProductTensorSubmodule (d := d) k
  let T : SchwartzNPoint d k →L[ℂ] SchwartzNPoint d k :=
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs)
  let coeZ : ZeroDiagonalSchwartz d k → SchwartzNPoint d k := fun z => z.1
  let coeL : ZeroDiagonalSchwartz d k →ₗ[ℂ] SchwartzNPoint d k :=
    { toFun := coeZ
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hT_maps :
      ∀ G ∈ (M_all : Set (SchwartzNPoint d k)), T G ∈ B.map coeL := by
    intro G hG
    change G ∈ M_all at hG
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
    · intro G hG
      rcases hG with ⟨fs, rfl⟩
      let gs : Fin k → SchwartzSpacetime d :=
        fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)
      obtain ⟨hvanish, hmem⟩ :=
        cutoff_productTensor_mem_admissibleProductTensorSubmodule χs fs hχpair
      refine ⟨⟨SchwartzMap.productTensor gs, hvanish⟩, hmem, ?_⟩
      change coeZ ⟨SchwartzMap.productTensor gs, hvanish⟩ =
        T (SchwartzMap.productTensor fs)
      dsimp [coeZ, T, gs]
      exact (productTensor_cutoff_productTensor χs fs).symm
    · simpa using (Submodule.zero_mem (B.map coeL))
    · intro G H _ _ hG_mem hH_mem
      simpa [map_add] using (Submodule.add_mem (B.map coeL) hG_mem hH_mem)
    · intro c G _ hG_mem
      simpa [map_smulₛₗ] using (Submodule.smul_mem (B.map coeL) c hG_mem)
  have hF_all :
      F.1 ∈ closure ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
        Set (SchwartzNPoint d k)) := by
    simpa [M_all, S_all] using (productTensor_span_dense d k F.1)
  have hTF_image :
      T F.1 ∈ closure (T '' ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
        Set (SchwartzNPoint d k))) := by
    have hmem_image_closure :
        T F.1 ∈ T '' closure ((M_all : Submodule ℂ (SchwartzNPoint d k)) :
          Set (SchwartzNPoint d k)) := ⟨F.1, hF_all, rfl⟩
    exact image_closure_subset_closure_image T.continuous hmem_image_closure
  have hTF_closure_map :
      T F.1 ∈ closure ((B.map coeL : Submodule ℂ (SchwartzNPoint d k)) :
        Set (SchwartzNPoint d k)) := by
    exact closure_mono (by
      rintro _ ⟨G, hG, rfl⟩
      exact hT_maps G hG) hTF_image
  have hmap :
      ((B.map coeL : Submodule ℂ (SchwartzNPoint d k)) :
        Set (SchwartzNPoint d k)) =
        coeZ '' ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)) := by
    exact Submodule.map_coe coeL B
  have hfull :
      F.1 ∈ closure
        (coeZ '' ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k))) := by
    rw [← hmap]
    simpa [T, hfix] using hTF_closure_map
  have hsub :
      F ∈ closure ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
        Set (ZeroDiagonalSchwartz d k)) := by
    exact
      (closure_subtype
        (x := (F : ↥(zeroDiagonalSubmodule d k)))
        (s := ((B : Submodule ℂ (ZeroDiagonalSchwartz d k)) :
          Set (ZeroDiagonalSchwartz d k)))).mpr
        (by simpa [coeZ] using hfull)
  simpa [B] using hsub

omit [NeZero d] in
private theorem finite_product_cutoff_decomposition_mem_closure_admissibleProductTensorSubmodule
    {d k : ℕ} {α : Type*} [Fintype α]
    (χs : α → Fin k → SchwartzSpacetime d)
    (hχpair :
      ∀ a, ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((χs a i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((χs a j : SchwartzSpacetime d) : SpacetimeDim d → ℂ)))
    (F : ZeroDiagonalSchwartz d k)
    (pieces : α → ZeroDiagonalSchwartz d k)
    (hdecomp : F = ∑ a, pieces a)
    (hfix :
      ∀ a,
        SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor (χs a))
          (pieces a).1 = (pieces a).1) :
    F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    admissibleProductTensorSubmodule (d := d) k
  have hpieces :
      ∀ a, pieces a ∈ (B.topologicalClosure : Set (ZeroDiagonalSchwartz d k)) := by
    intro a
    simpa [B, Submodule.topologicalClosure_coe] using
      product_cutoff_fixed_mem_closure_admissibleProductTensorSubmodule
        (d := d) (k := k) (χs a) (hχpair a) (pieces a) (hfix a)
  have hsum :
      (∑ a, pieces a) ∈ (B.topologicalClosure : Set (ZeroDiagonalSchwartz d k)) := by
    exact Submodule.sum_mem B.topologicalClosure (fun a _ha => hpieces a)
  rw [hdecomp]
  simpa [B, Submodule.topologicalClosure_coe] using hsum

omit [NeZero d] in
private theorem product_box_supported_mem_closure_admissibleProductTensorSubmodule
    {d k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ))
    (U : Fin k → Set (SpacetimeDim d))
    (hU_open : ∀ i, IsOpen (U i))
    (hU_pair :
      ∀ i j : Fin k, i ≠ j → Disjoint (U i) (U j))
    (hF_box :
      tsupport (F.1 : NPointDomain d k → ℂ) ⊆
        {x | ∀ i : Fin k, x i ∈ U i}) :
    F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  let K : Fin k → Set (SpacetimeDim d) := fun i =>
    (fun x : NPointDomain d k => x i) ''
      tsupport (F.1 : NPointDomain d k → ℂ)
  have hK_compact : ∀ i, IsCompact (K i) := by
    intro i
    exact hF_comp.isCompact.image (continuous_apply i)
  have hK_sub : ∀ i, K i ⊆ U i := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hF_box hx i
  have hcut_exists :
      ∀ i, ∃ χ : SchwartzSpacetime d,
        (∀ y ∈ K i, χ y = 1) ∧
        tsupport ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆ U i := by
    intro i
    exact
      SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
        (m := d + 1) (K := K i) (U := U i)
        (hK_compact i) (hU_open i) (hK_sub i)
  choose χs hχ_one hχ_sub using hcut_exists
  have hχpair :
      ∀ i j : Fin k, i ≠ j →
        Disjoint
          (tsupport ((χs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
          (tsupport ((χs j : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
    intro i j hij
    exact (hU_pair i j hij).mono (hχ_sub i) (hχ_sub j)
  have hfix :
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.productTensor χs) F.1 = F.1 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((SchwartzMap.productTensor χs : SchwartzNPoint d k) :
        NPointDomain d k → ℂ))
      (SchwartzMap.productTensor χs).hasTemperateGrowth F.1 x]
    by_cases hx : x ∈ tsupport (F.1 : NPointDomain d k → ℂ)
    · have hprod_one :
          (SchwartzMap.productTensor χs : SchwartzNPoint d k) x = 1 := by
        rw [SchwartzMap.productTensor_apply]
        apply Finset.prod_eq_one
        intro i _hi
        exact hχ_one i (x i) ⟨x, hx, rfl⟩
      simp [hprod_one, smul_eq_mul]
    · have hzero : (F.1 : NPointDomain d k → ℂ) x = 0 :=
        image_eq_zero_of_notMem_tsupport hx
      simp [hzero, smul_eq_mul]
  exact
    product_cutoff_fixed_mem_closure_admissibleProductTensorSubmodule
      (d := d) (k := k) χs hχpair F hfix

private theorem exists_finite_schwartz_partitionOfUnity_on_compact_openCover
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let V : α → Set E := fun i => U i ∩ Metric.ball (0 : E) (R + 1)
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact (hU_open i).inter Metric.isOpen_ball
  have hV_relcompact : ∀ i, ∃ c r, V i ⊆ Metric.closedBall c r := by
    intro i
    refine ⟨(0 : E), R + 1, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hV_cover : K ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxR : dist x (0 : E) ≤ R := by
      simpa [dist_comm] using Metric.mem_closedBall.mp (hR hx)
    have hxball : x ∈ Metric.ball (0 : E) (R + 1) := by
      rw [Metric.mem_ball]
      linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, hxball⟩⟩
  obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      (E := E) hK hV_open hV_relcompact hV_cover
  refine ⟨χ, hχ_compact, ?_, hχ_sum⟩
  intro i
  exact (hχ_sub i).trans Set.inter_subset_left

private theorem finite_product_box_cover_mem_closure_admissibleProductTensorSubmodule
    {d : ℕ} [NeZero d] {k : ℕ} {α : Type*} [Fintype α]
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ))
    (V : α → Set (NPointDomain d k))
    (hV_open : ∀ a, IsOpen (V a))
    (hcover : tsupport (F.1 : NPointDomain d k → ℂ) ⊆ ⋃ a, V a)
    (U : α → Fin k → Set (SpacetimeDim d))
    (hU_open : ∀ a i, IsOpen (U a i))
    (hU_pair :
      ∀ a, ∀ i j : Fin k, i ≠ j → Disjoint (U a i) (U a j))
    (hV_box : ∀ a, V a ⊆ {x | ∀ i : Fin k, x i ∈ U a i}) :
    F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  obtain ⟨θ, _hθ_compact, hθ_sub, hθ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d k) hF_comp.isCompact hV_open hcover
  let rawPiece : α → SchwartzNPoint d k := fun a =>
    SchwartzMap.smulLeftCLM ℂ (θ a : NPointDomain d k → ℂ) F.1
  have hrawPiece_vanish :
      ∀ a, VanishesToInfiniteOrderOnCoincidence (rawPiece a) := by
    intro a
    simpa [rawPiece] using
      VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (d := d) F.2 (ψ := θ a)
  let pieces : α → ZeroDiagonalSchwartz d k := fun a =>
    ⟨rawPiece a, hrawPiece_vanish a⟩
  have hraw_sum : F.1 = ∑ a, rawPiece a := by
    simpa [rawPiece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) θ F.1
        (by
          intro x hx
          simpa using hθ_sum x hx)
  have hdecomp : F = ∑ a, pieces a := by
    let coeL : ZeroDiagonalSchwartz d k →ₗ[ℂ] SchwartzNPoint d k :=
      { toFun := fun z => z.1
        map_add' := by intro a b; rfl
        map_smul' := by intro c a; rfl }
    have hsum_coe :
        (∑ a, pieces a).1 = ∑ a, (pieces a).1 := by
      change coeL (∑ a, pieces a) = ∑ a, coeL (pieces a)
      rw [map_sum]
    apply SetCoe.ext
    change F.1 = (∑ a, pieces a).1
    rw [hsum_coe]
    simpa [pieces, rawPiece] using hraw_sum
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    admissibleProductTensorSubmodule (d := d) k
  have hpiece_comp :
      ∀ a, HasCompactSupport ((pieces a).1 : NPointDomain d k → ℂ) := by
    intro a
    refine hF_comp.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport ((pieces a).1 : NPointDomain d k → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (θ a : NPointDomain d k → ℂ))
        (f := F.1)) hx_ts).1
  have hpiece_box :
      ∀ a, tsupport ((pieces a).1 : NPointDomain d k → ℂ) ⊆
        {x | ∀ i : Fin k, x i ∈ U a i} := by
    intro a x hx
    exact hV_box a
      (hθ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (θ a : NPointDomain d k → ℂ))
          (f := F.1)) hx).2)
  have hpieces :
      ∀ a, pieces a ∈ (B.topologicalClosure : Set (ZeroDiagonalSchwartz d k)) := by
    intro a
    simpa [B, Submodule.topologicalClosure_coe] using
      product_box_supported_mem_closure_admissibleProductTensorSubmodule
        (d := d) (k := k) (pieces a) (hpiece_comp a) (U a)
        (hU_open a) (hU_pair a) (hpiece_box a)
  have hsum :
      (∑ a, pieces a) ∈ (B.topologicalClosure : Set (ZeroDiagonalSchwartz d k)) := by
    exact Submodule.sum_mem B.topologicalClosure (fun a _ha => hpieces a)
  rw [hdecomp]
  simpa [B, Submodule.topologicalClosure_coe] using hsum

private theorem exists_pairwise_disjoint_coordinate_balls
    {d : ℕ} [NeZero d] {k : ℕ} (x : NPointDomain d k)
    (hx : x ∉ CoincidenceLocus d k) :
    ∃ r : ℝ, 0 < r ∧
      ∀ i j : Fin k, i ≠ j →
        Disjoint (Metric.ball (x i) r) (Metric.ball (x j) r) := by
  classical
  let pairs : Finset (Fin k × Fin k) :=
    (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2)
  by_cases hpairs : pairs.Nonempty
  · let δ : ℝ := pairs.inf' hpairs (fun p => dist (x p.1) (x p.2))
    have hδ_pos : 0 < δ := by
      rw [Finset.lt_inf'_iff hpairs]
      intro p hp
      have hp_ne : p.1 ≠ p.2 := by
        simpa [pairs] using hp
      have hcoord_ne : x p.1 ≠ x p.2 := by
        intro hEq
        exact hx ⟨p.1, p.2, hp_ne, hEq⟩
      exact dist_pos.mpr hcoord_ne
    refine ⟨δ / 3, by positivity, ?_⟩
    intro i j hij
    have hp : (i, j) ∈ pairs := by
      simp [pairs, hij]
    have hδ_le : δ ≤ dist (x i) (x j) :=
      Finset.inf'_le (s := pairs) (f := fun p => dist (x p.1) (x p.2)) hp
    apply Metric.ball_disjoint_ball
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro i j hij
    have hp : (i, j) ∈ pairs := by
      simp [pairs, hij]
    exact (hpairs ⟨(i, j), hp⟩).elim

private theorem coincidence_free_compactSupport_mem_closure_admissibleProductTensorSubmodule
    {d : ℕ} [NeZero d] {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ))
    (hF_disj :
      Disjoint
        (tsupport (F.1 : NPointDomain d k → ℂ))
        (CoincidenceLocus d k)) :
    F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  classical
  let K : Set (NPointDomain d k) := tsupport (F.1 : NPointDomain d k → ℂ)
  let r : K → ℝ := fun y =>
    Classical.choose
      (exists_pairwise_disjoint_coordinate_balls
        (d := d) (k := k) y.1
        (by
          intro hy
          exact Set.disjoint_left.mp hF_disj y.2 hy))
  have hr_pos : ∀ y : K, 0 < r y := by
    intro y
    exact (Classical.choose_spec
      (exists_pairwise_disjoint_coordinate_balls
        (d := d) (k := k) y.1
        (by
          intro hy
          exact Set.disjoint_left.mp hF_disj y.2 hy))).1
  have hr_disj :
      ∀ y : K, ∀ i j : Fin k, i ≠ j →
        Disjoint (Metric.ball (y.1 i) (r y)) (Metric.ball (y.1 j) (r y)) := by
    intro y
    exact (Classical.choose_spec
      (exists_pairwise_disjoint_coordinate_balls
        (d := d) (k := k) y.1
        (by
          intro hy
          exact Set.disjoint_left.mp hF_disj y.2 hy))).2
  let Vβ : K → Set (NPointDomain d k) := fun y =>
    {z | ∀ i : Fin k, z i ∈ Metric.ball (y.1 i) (r y)}
  have hVβ_open : ∀ y : K, IsOpen (Vβ y) := by
    intro y
    change IsOpen {z : NPointDomain d k | ∀ i : Fin k,
      z i ∈ Metric.ball (y.1 i) (r y)}
    have h :
        IsOpen (⋂ i : Fin k,
          {z : NPointDomain d k | z i ∈ Metric.ball (y.1 i) (r y)}) :=
      isOpen_iInter_of_finite (fun i : Fin k =>
        Metric.isOpen_ball.preimage
          (show Continuous (fun z : NPointDomain d k => z i) from continuous_apply i))
    convert h using 1
    ext z
    simp
  have hK_cover : K ⊆ ⋃ y : K, Vβ y := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    intro i
    exact Metric.mem_ball_self (hr_pos ⟨x, hx⟩)
  obtain ⟨s, hscover⟩ :=
    hF_comp.isCompact.elim_finite_subcover Vβ hVβ_open hK_cover
  let α := {y : K // y ∈ s}
  let V : α → Set (NPointDomain d k) := fun a => Vβ a.1
  let U : α → Fin k → Set (SpacetimeDim d) := fun a i =>
    Metric.ball (a.1.1 i) (r a.1)
  have hV_open : ∀ a : α, IsOpen (V a) := by
    intro a
    exact hVβ_open a.1
  have hcover : K ⊆ ⋃ a : α, V a := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨y, hys, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  have hU_open : ∀ a : α, ∀ i, IsOpen (U a i) := by
    intro a i
    exact Metric.isOpen_ball
  have hU_pair :
      ∀ a : α, ∀ i j : Fin k, i ≠ j → Disjoint (U a i) (U a j) := by
    intro a i j hij
    exact hr_disj a.1 i j hij
  have hV_box : ∀ a : α, V a ⊆ {x | ∀ i : Fin k, x i ∈ U a i} := by
    intro a x hx
    exact hx
  exact
    finite_product_box_cover_mem_closure_admissibleProductTensorSubmodule
      (d := d) (k := k) F hF_comp V hV_open hcover U hU_open hU_pair hV_box

private def pairCollisionSq {d : ℕ} (k : ℕ) (i j : Fin k) (x : NPointDomain d k) : ℝ :=
  ∑ μ : Fin (d + 1), (x i μ - x j μ) * (x i μ - x j μ)

private theorem pairCollisionSq_eq_zero_of_eq
    {d k : ℕ} {i j : Fin k} {x : NPointDomain d k} (hij : x i = x j) :
    pairCollisionSq (d := d) k i j x = 0 := by
  simp [pairCollisionSq, hij]

private theorem coordinate_hasTemperateGrowth
    {d : ℕ} {k : ℕ} (i : Fin k) (μ : Fin (d + 1)) :
    (fun x : NPointDomain d k => x i μ).HasTemperateGrowth := by
  let πi : NPointDomain d k →L[ℝ] SpacetimeDim d :=
    ContinuousLinearMap.proj i
  let πμ : SpacetimeDim d →L[ℝ] ℝ :=
    ContinuousLinearMap.proj μ
  simpa [πi, πμ] using
    (πμ.hasTemperateGrowth.comp πi.hasTemperateGrowth)

private theorem pairCollisionSq_hasTemperateGrowth
    {d : ℕ} {k : ℕ} (i j : Fin k) :
    (fun x : NPointDomain d k => pairCollisionSq (d := d) k i j x).HasTemperateGrowth := by
  have hterm :
      ∀ μ ∈ (Finset.univ : Finset (Fin (d + 1))),
        ((fun x : NPointDomain d k => (x i μ - x j μ) * (x i μ - x j μ)) :
          NPointDomain d k → ℝ).HasTemperateGrowth := by
    intro μ _hμ
    have hdiff :
        (fun x : NPointDomain d k => x i μ - x j μ).HasTemperateGrowth :=
      (coordinate_hasTemperateGrowth (d := d) i μ).sub
        (coordinate_hasTemperateGrowth (d := d) j μ)
    simpa using hdiff.mul hdiff
  simpa [pairCollisionSq] using
    Function.HasTemperateGrowth.sum (s := (Finset.univ : Finset (Fin (d + 1)))) hterm

private def pairCollisionFarFactor
    {d k : ℕ} (r : ℝ) (i j : Fin k) (x : NPointDomain d k) : ℂ :=
  (SCV.smoothCutoff ((r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2) : ℂ)

private theorem pairCollisionFarFactor_hasTemperateGrowth
    {d k : ℕ} (r : ℝ) (i j : Fin k) :
    (pairCollisionFarFactor (d := d) r i j).HasTemperateGrowth := by
  have hsq := pairCollisionSq_hasTemperateGrowth (d := d) (k := k) i j
  have harg :
      (fun x : NPointDomain d k =>
        (r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2).HasTemperateGrowth := by
    simpa [sub_eq_add_neg] using
      ((Function.HasTemperateGrowth.const ((r * r)⁻¹)).mul hsq).add
        (Function.HasTemperateGrowth.const (-2 : ℝ))
  change Function.HasTemperateGrowth
    (fun x : NPointDomain d k =>
      (SCV.smoothCutoff ((r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2) : ℂ))
  exact SCV.smoothCutoff_complex_hasTemperateGrowth.comp harg

private theorem pairCollisionFarFactor_zero_of_pairSq_le
    {d k : ℕ} {r : ℝ} (hr : 0 < r) {i j : Fin k} {x : NPointDomain d k}
    (hx : pairCollisionSq (d := d) k i j x ≤ r * r) :
    pairCollisionFarFactor (d := d) r i j x = 0 := by
  have hrr : 0 < r * r := mul_pos hr hr
  have harg :
      (r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2 ≤ -1 := by
    have hmul : (r * r)⁻¹ * pairCollisionSq (d := d) k i j x ≤ 1 := by
      rw [inv_mul_le_one₀ hrr]
      exact hx
    linarith
  change (SCV.smoothCutoff ((r * r)⁻¹ * pairCollisionSq (d := d) k i j x - 2) : ℂ) = 0
  exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one harg

private abbrev collisionPairIndex (k : ℕ) :=
  {p : Fin k × Fin k // p.1 ≠ p.2}

private theorem hasTemperateGrowth_finset_prod_complex
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ι → E → ℂ}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x : E => s.prod (fun i => f i x)).HasTemperateGrowth := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    simpa using (Function.HasTemperateGrowth.const (1 : ℂ))
  · intro a s has ih hf
    have hfa : (f a).HasTemperateGrowth := hf a (by simp)
    have hfs : (fun x : E => s.prod (fun i => f i x)).HasTemperateGrowth :=
      ih (fun i hi => hf i (by simp [has, hi]))
    simpa [Finset.prod_insert has, Pi.mul_apply] using hfa.mul hfs

private def collisionFarCutoff {d k : ℕ} (r : ℝ) : NPointDomain d k → ℂ :=
  fun x =>
    (Finset.univ : Finset (collisionPairIndex k)).prod
      (fun p => pairCollisionFarFactor (d := d) r p.1.1 p.1.2 x)

private theorem collisionFarCutoff_hasTemperateGrowth
    {d k : ℕ} (r : ℝ) :
    (collisionFarCutoff (d := d) (k := k) r).HasTemperateGrowth := by
  classical
  simpa [collisionFarCutoff] using
    hasTemperateGrowth_finset_prod_complex
      (s := (Finset.univ : Finset (collisionPairIndex k)))
      (f := fun p x => pairCollisionFarFactor (d := d) r p.1.1 p.1.2 x)
      (fun p _hp => pairCollisionFarFactor_hasTemperateGrowth (d := d) r p.1.1 p.1.2)

private theorem collisionFarCutoff_support_pairSq_lt
    {d k : ℕ} {r : ℝ} (hr : 0 < r) {i j : Fin k} (hij : i ≠ j) :
    Function.support (collisionFarCutoff (d := d) (k := k) r) ⊆
      {x : NPointDomain d k | r * r < pairCollisionSq (d := d) k i j x} := by
  intro x hx
  by_contra hnot
  let p0 : collisionPairIndex k := ⟨(i, j), hij⟩
  have hfactor_zero :
      pairCollisionFarFactor (d := d) r p0.1.1 p0.1.2 x = 0 := by
    simpa [p0] using
      pairCollisionFarFactor_zero_of_pairSq_le (d := d) hr (le_of_not_gt hnot)
  have hprod_zero :
      collisionFarCutoff (d := d) (k := k) r x = 0 := by
    simpa [collisionFarCutoff, p0] using
      (Finset.prod_eq_zero (s := (Finset.univ : Finset (collisionPairIndex k)))
        (i := p0) (Finset.mem_univ p0) hfactor_zero)
  exact hx hprod_zero

private theorem collisionFarCutoff_tsupport_pairSq_le
    {d k : ℕ} {r : ℝ} (hr : 0 < r) {i j : Fin k} (hij : i ≠ j) :
    tsupport (collisionFarCutoff (d := d) (k := k) r) ⊆
      {x : NPointDomain d k | r * r ≤ pairCollisionSq (d := d) k i j x} := by
  refine closure_minimal ?support ?closed
  · exact (collisionFarCutoff_support_pairSq_lt (d := d) hr hij).trans <| by
      intro x hx
      simpa using le_of_lt hx
  · exact isClosed_le continuous_const
      (pairCollisionSq_hasTemperateGrowth (d := d) (k := k) i j).1.continuous

private theorem collisionFarCutoff_tsupport_disjoint_coincidence
    {d k : ℕ} {r : ℝ} (hr : 0 < r) :
    Disjoint
      (tsupport (collisionFarCutoff (d := d) (k := k) r))
      (CoincidenceLocus d k) := by
  rw [Set.disjoint_left]
  intro x hx hcoin
  rcases hcoin with ⟨i, j, hij, hEq⟩
  have hle :
      r * r ≤ pairCollisionSq (d := d) k i j x :=
    collisionFarCutoff_tsupport_pairSq_le (d := d) hr hij hx
  have hzero : pairCollisionSq (d := d) k i j x = 0 :=
    pairCollisionSq_eq_zero_of_eq (d := d) (k := k) hEq
  have hrr : 0 < r * r := mul_pos hr hr
  linarith

private def collisionFarPart
    {d : ℕ} [NeZero d] {k : ℕ} (r : ℝ)
    (F : ZeroDiagonalSchwartz d k) : ZeroDiagonalSchwartz d k :=
  ⟨SchwartzMap.smulLeftCLM ℂ (collisionFarCutoff (d := d) (k := k) r) F.1,
    VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth
      (collisionFarCutoff_hasTemperateGrowth (d := d) (k := k) r) F.2⟩

private theorem collisionFarPart_hasCompactSupport
    {d : ℕ} [NeZero d] {k : ℕ} {r : ℝ} (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ)) :
    HasCompactSupport
      (((collisionFarPart (d := d) (k := k) r F).1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) := by
  refine hF_comp.mono' ?_
  intro x hx
  have hx_ts :
      x ∈ tsupport
        (((collisionFarPart (d := d) (k := k) r F).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) :=
    subset_closure hx
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := collisionFarCutoff (d := d) (k := k) r) (f := F.1) hx_ts).1

private theorem collisionFarPart_tsupport_disjoint_coincidence
    {d : ℕ} [NeZero d] {k : ℕ} {r : ℝ} (hr : 0 < r) (F : ZeroDiagonalSchwartz d k) :
    Disjoint
      (tsupport
        (((collisionFarPart (d := d) (k := k) r F).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ))
      (CoincidenceLocus d k) := by
  rw [Set.disjoint_left]
  intro x hx hcoin
  have hx_cut :
      x ∈ tsupport (collisionFarCutoff (d := d) (k := k) r) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := collisionFarCutoff (d := d) (k := k) r) (f := F.1) hx).2
  exact Set.disjoint_left.mp
    (collisionFarCutoff_tsupport_disjoint_coincidence (d := d) (k := k) hr)
    hx_cut hcoin

private theorem collisionFarPart_mem_closure_admissibleProductTensorSubmodule
    {d : ℕ} [NeZero d] {k : ℕ} {r : ℝ} (hr : 0 < r)
    (F : ZeroDiagonalSchwartz d k)
    (hF_comp : HasCompactSupport (F.1 : NPointDomain d k → ℂ)) :
    collisionFarPart (d := d) (k := k) r F ∈ closure
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) :=
  coincidence_free_compactSupport_mem_closure_admissibleProductTensorSubmodule
    (d := d) (k := k) (collisionFarPart (d := d) (k := k) r F)
    (collisionFarPart_hasCompactSupport (d := d) (k := k) F hF_comp)
    (collisionFarPart_tsupport_disjoint_coincidence (d := d) (k := k) hr F)

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
    (hDense : Dense
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k))) :
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
  exact
    acrOne_productTensor_witness_euclidKernelPackage_from_acrGrowth
      (d := d) k S_prod hS_prod_holo hS_prod_perm hS_prod_trans hS_prod_growth

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

/-!
### Pairwise small-collar estimates

The remaining density step needs the analogue of the checked `k = 2`
small-origin cutoff estimate for every coordinate pair.  This section develops
the reusable pairwise packet in scratch before promoting it.
-/

private abbrev proofideas_spacetimeUnitBallBumpRadius
    (R : ℝ) (hR : 0 < R) : SchwartzSpacetime d :=
  OSReconstruction.unitBallBumpSchwartzPiRadius (d + 1) R hR

private theorem proofideas_unitBallBumpSchwartzPi_zero_of_two_le_norm {m : ℕ}
    {x : Fin m → ℝ} (hx : 2 ≤ ‖x‖) :
    OSReconstruction.unitBallBumpSchwartzPi m x = 0 := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      OSReconstruction.unitBallBumpSchwartzPi m x = f x := by
    change (HasCompactSupport.toSchwartzMap hf_compact hf_smooth :
      SchwartzMap (Fin m → ℝ) ℂ) x = f x
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [happly]
  rw [show f x = ((b x : ℝ) : ℂ) by rfl]
  refine congrArg (fun r : ℝ => (r : ℂ)) ?_
  have hdist : 2 ≤ dist x 0 := by simpa [dist_eq_norm] using hx
  exact b.zero_of_le_dist hdist

private theorem proofideas_spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm
    {R : ℝ} (hR : 0 < R) {x : SpacetimeDim d}
    (hx : 2 * R ≤ ‖x‖) :
    proofideas_spacetimeUnitBallBumpRadius (d := d) R hR x = 0 := by
  rw [proofideas_spacetimeUnitBallBumpRadius, OSReconstruction.unitBallBumpSchwartzPiRadius_apply]
  apply proofideas_unitBallBumpSchwartzPi_zero_of_two_le_norm
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  rw [le_inv_mul_iff₀ hR]
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hx

private abbrev proofideas_pairDiffCLM {k : ℕ} (i j : Fin k) :
    NPointDomain d k →L[ℝ] SpacetimeDim d :=
  ContinuousLinearMap.proj (R := ℝ) (ι := Fin k) (φ := fun _ => SpacetimeDim d) i -
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin k) (φ := fun _ => SpacetimeDim d) j

private theorem proofideas_pairDiffCLM_apply {k : ℕ} (i j : Fin k)
    (x : NPointDomain d k) :
    proofideas_pairDiffCLM (d := d) i j x = x i - x j := by
  ext μ
  rfl

private theorem proofideas_pairDiffCLM_opNorm_le_two {k : ℕ} (i j : Fin k) :
    ‖proofideas_pairDiffCLM (d := d) i j‖ ≤ (2 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  calc
    ‖proofideas_pairDiffCLM (d := d) i j x‖ = ‖x i - x j‖ := by
      rw [proofideas_pairDiffCLM_apply]
    _ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖x‖ := by
      exact add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm x j)
    _ = 2 * ‖x‖ := by ring

set_option maxHeartbeats 800000 in
private theorem proofideas_exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : SpacetimeDim d),
        ‖iteratedFDeriv ℝ n
            ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖ ≤
          C * (δ⁻¹) ^ n := by
  let ψ : SchwartzSpacetime d := OSReconstruction.unitBallBumpSchwartzPi (d + 1)
  obtain ⟨C, hC, hCbound⟩ := (ψ : SchwartzSpacetime d).decay 0 n
  refine ⟨C, le_of_lt hC, ?_⟩
  intro δ hδ x
  let e : SpacetimeDim d →L[ℝ] SpacetimeDim d :=
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
      (Units.mk0 δ hδ.ne')).symm) : SpacetimeDim d ≃L[ℝ] SpacetimeDim d).toContinuousLinearMap
  have he_apply (y : SpacetimeDim d) : e y = δ⁻¹ • y := by
    change
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) = δ⁻¹ • y
    rw [show
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SpacetimeDim d)
        (Units.mk0 δ hδ.ne')).symm) y) =
          ((↑((Units.mk0 δ hδ.ne')⁻¹) : ℝ) • y) by rfl]
    simp [Units.val_inv_eq_inv_val]
  have he_norm : ‖e‖ ≤ δ⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound e (inv_nonneg.mpr hδ.le) ?_
    intro y
    calc
      ‖e y‖ = ‖δ⁻¹ • y‖ := by rw [he_apply]
      _ = ‖δ⁻¹‖ * ‖y‖ := norm_smul _ _
      _ = δ⁻¹ * ‖y‖ := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
      _ ≤ δ⁻¹ * ‖y‖ := by rfl
  have hcomp :
      iteratedFDeriv ℝ n
          (((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ)) x =
        (((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e)) := by
    dsimp [proofideas_spacetimeUnitBallBumpRadius, ψ]
    simpa using
      e.iteratedFDeriv_comp_right
        (f := ((OSReconstruction.unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((OSReconstruction.unitBallBumpSchwartzPi (d + 1) : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) x‖
        =
      ‖(((iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x))
          ).compContinuousLinearMap (fun _ : Fin n => e))‖ := by
            rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n ((ψ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (e x)‖ *
          ∏ _ : Fin n, ‖e‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _ : Fin n, ‖e‖ := by
            gcongr
            simpa using hCbound (e x)
    _ = C * ‖e‖ ^ n := by simp
    _ ≤ C * (δ⁻¹) ^ n := by
            gcongr

private theorem proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
    {k : ℕ} (i j : Fin k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d k),
        ‖iteratedFDeriv ℝ n
            (fun y : NPointDomain d k =>
              (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (proofideas_pairDiffCLM (d := d) i j y)) x‖ ≤
          C * (δ⁻¹) ^ n := by
  obtain ⟨C, hC_nonneg, hCbound⟩ :=
    proofideas_exists_iteratedFDeriv_spacetimeUnitBallBumpRadius_bound (d := d) n
  refine ⟨C * (2 : ℝ) ^ n, mul_nonneg hC_nonneg (pow_nonneg (by norm_num) n), ?_⟩
  intro δ hδ x
  have hcomp :
      iteratedFDeriv ℝ n
          (fun y : NPointDomain d k =>
            (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
              (proofideas_pairDiffCLM (d := d) i j y)) x =
        (iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)).compContinuousLinearMap
            (fun _ : Fin n => proofideas_pairDiffCLM (d := d) i j) := by
    simpa using
      (proofideas_pairDiffCLM (d := d) i j).iteratedFDeriv_comp_right
        (f := ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
        ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d).smooth n)
        (x := x) (i := n) le_rfl
  calc
    ‖iteratedFDeriv ℝ n
        (fun y : NPointDomain d k =>
          (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
            (proofideas_pairDiffCLM (d := d) i j y)) x‖
        =
      ‖(iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)).compContinuousLinearMap
            (fun _ : Fin n => proofideas_pairDiffCLM (d := d) i j)‖ := by
              rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ n
          ((proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) (proofideas_pairDiffCLM (d := d) i j x)‖ *
          ∏ _ : Fin n, ‖proofideas_pairDiffCLM (d := d) i j‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, ‖proofideas_pairDiffCLM (d := d) i j‖ := by
          gcongr
          exact hCbound δ hδ (proofideas_pairDiffCLM (d := d) i j x)
    _ ≤ (C * (δ⁻¹) ^ n) * ∏ _ : Fin n, (2 : ℝ) := by
          gcongr
          exact proofideas_pairDiffCLM_opNorm_le_two (d := d) i j
    _ = (C * (2 : ℝ) ^ n) * (δ⁻¹) ^ n := by
          simp [mul_assoc, mul_left_comm, mul_comm]

private theorem proofideas_pairSmallCutoff_support_pair_norm_le
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (i j : Fin k) :
    Function.support
        (fun x : NPointDomain d k =>
          (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
            (proofideas_pairDiffCLM (d := d) i j x)) ⊆
      {x : NPointDomain d k | ‖x i - x j‖ ≤ 2 * δ} := by
  intro x hx
  by_contra hxball
  have hnorm : 2 * δ ≤ ‖x i - x j‖ := le_of_not_ge hxball
  have hzero :
      (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
          (proofideas_pairDiffCLM (d := d) i j x) = 0 := by
    rw [proofideas_pairDiffCLM_apply]
    exact proofideas_spacetimeUnitBallBumpRadius_zero_of_two_mul_le_norm (d := d) hδ hnorm
  exact hx (by simpa [Function.mem_support] using hzero)

private theorem proofideas_iteratedFDeriv_lineDeriv_eq_snoc_npoint {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v x : NPointDomain d k)
    (u : Fin n → NPointDomain d k) :
    iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x u =
      iteratedFDeriv ℝ (n + 1) ((f : SchwartzNPoint d k) : NPointDomain d k → ℂ) x
        (Fin.snoc u v) := by
  have hsucc :
      (∂^{Fin.snoc u v} f : SchwartzNPoint d k) = ∂^{u} (∂_{v} f) := by
    simpa using (LineDeriv.iteratedLineDerivOp_succ_right (m := Fin.snoc u v) (f := f))
  have hsucc_apply := congrArg (fun g : SchwartzNPoint d k => g x) hsucc
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := f) (m := Fin.snoc u v) (x := x),
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := (∂_{v} f : SchwartzNPoint d k)) (m := u) (x := x)] using hsucc_apply.symm

private theorem proofideas_lineDerivOp_comm_npoint {k : ℕ}
    (f : SchwartzNPoint d k)
    (v w : NPointDomain d k) :
    ∂_{v} ((∂_{w} f : SchwartzNPoint d k)) =
      ∂_{w} ((∂_{v} f : SchwartzNPoint d k)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzNPoint d k))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d k → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : NPointDomain d k → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzNPoint d k))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

private theorem proofideas_lineDerivOp_iterated_comm_npoint {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v : NPointDomain d k) (u : Fin n → NPointDomain d k) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact proofideas_lineDerivOp_comm_npoint f v (u (Fin.last n))

private theorem proofideas_fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint
    {k n : ℕ}
    (f : SchwartzNPoint d k)
    (v x : NPointDomain d k) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : NPointDomain d k → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzNPoint d k => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [proofideas_lineDerivOp_iterated_comm_npoint (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzNPoint d k) : NPointDomain d k → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzNPoint d k)) (m := u) (x := x))

private theorem proofideas_seminorm_zero_lineDeriv_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (v : NPointDomain d k) (n : ℕ) :
    SchwartzMap.seminorm ℝ 0 n (LineDeriv.lineDerivOp v f : SchwartzNPoint d k) ≤
      ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
  refine SchwartzMap.seminorm_le_bound ℝ 0 n
    (LineDeriv.lineDerivOp v f : SchwartzNPoint d k) (by positivity) ?_
  intro x
  calc
    ‖x‖ ^ 0 *
        ‖iteratedFDeriv ℝ n
            (((LineDeriv.lineDerivOp v f : SchwartzNPoint d k) : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) x‖
        =
      ‖iteratedFDeriv ℝ n
          (((LineDeriv.lineDerivOp v f : SchwartzNPoint d k) : SchwartzNPoint d k) :
            NPointDomain d k → ℂ) x‖ := by
            simp
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x v‖ := by
          rw [← proofideas_fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv_npoint]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n (f : NPointDomain d k → ℂ)) x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (n + 1) (f : NPointDomain d k → ℂ) x‖ * ‖v‖ := by
          rw [norm_fderiv_iteratedFDeriv]
    _ ≤ (SchwartzMap.seminorm ℝ 0 (n + 1) f) * ‖v‖ := by
          gcongr
          exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f (n + 1) x
    _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) f := by
          ring

private theorem proofideas_iteratedLineDeriv_seminorm_zero_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (j n : ℕ) :
    ∀ u : Fin j → NPointDomain d k,
      SchwartzMap.seminorm ℝ 0 n (LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  induction j generalizing f n with
  | zero =>
      intro u
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      intro u
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      calc
        SchwartzMap.seminorm ℝ 0 n (∂_{u 0} (∂^{Fin.tail u} f) : SchwartzNPoint d k)
            ≤ ‖u 0‖ * SchwartzMap.seminorm ℝ 0 (n + 1) (∂^{Fin.tail u} f : SchwartzNPoint d k) := by
              exact proofideas_seminorm_zero_lineDeriv_le_npoint
                (f := ∂^{Fin.tail u} f) (v := u 0) (n := n)
        _ ≤ ‖u 0‖ *
              ((∏ i, ‖Fin.tail u i‖) * SchwartzMap.seminorm ℝ 0 (n + 1 + j) f) := by
              gcongr
              exact ih (f := f) (n := n + 1) (u := Fin.tail u)
        _ = (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + (j + 1)) f := by
              rw [Fin.prod_univ_succ, add_assoc]
              have htail : (∏ i : Fin j, ‖Fin.tail u i‖) = ∏ i : Fin j, ‖u i.succ‖ := rfl
              rw [htail]
              ring

private theorem proofideas_norm_iteratedFDeriv_iteratedLineDeriv_le_npoint {k : ℕ}
    (f : SchwartzNPoint d k) (j n : ℕ) :
    ∀ (u : Fin j → NPointDomain d k) (x : NPointDomain d k),
      ‖iteratedFDeriv ℝ n ((LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) x‖ ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) f := by
  intro u x
  exact le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (∂^{u} f) n x)
    (proofideas_iteratedLineDeriv_seminorm_zero_le_npoint (f := f) (j := j) (n := n) u)

private theorem proofideas_iteratedLineDeriv_preserves_zeroDiagonal {k j : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (u : Fin j → NPointDomain d k) :
    VanishesToInfiniteOrderOnCoincidence (LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) := by
  induction j generalizing f with
  | zero =>
      simpa [LineDeriv.iteratedLineDerivOp_fin_zero] using hf
  | succ j ih =>
      have hu : u = Fin.snoc (Fin.init u) (u (Fin.last j)) := by
        exact (Fin.snoc_init_self u).symm
      rw [hu, LineDeriv.iteratedLineDerivOp_succ_right]
      simp only [Fin.init_snoc, Fin.snoc_last]
      have hline :
          VanishesToInfiniteOrderOnCoincidence
            (LineDeriv.lineDerivOp (u (Fin.last j)) f : SchwartzNPoint d k) := by
        intro q y hy
        ext w
        have hzero := hf (q + 1) y hy
        have hzero_apply :
            iteratedFDeriv ℝ (q + 1) (f : NPointDomain d k → ℂ) y
              (Fin.snoc w (u (Fin.last j))) = 0 := by
          simpa using congrArg
            (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => NPointDomain d k) ℂ =>
              T (Fin.snoc w (u (Fin.last j)))) hzero
        simpa using
          (proofideas_iteratedFDeriv_lineDeriv_eq_snoc_npoint
            (f := f) (v := u (Fin.last j)) (x := y) (u := w)).trans hzero_apply
      exact ih (f := LineDeriv.lineDerivOp (u (Fin.last j)) f) hline (Fin.init u)

private def proofideas_coincidenceCollapse {k : ℕ} (i j : Fin k) (x : NPointDomain d k) :
    NPointDomain d k :=
  fun q => if q = i ∨ q = j then midpoint ℝ (x i) (x j) else x q

private theorem proofideas_coincidenceCollapse_mem_CoincidenceLocus {k : ℕ}
    (x : NPointDomain d k) (i j : Fin k) (hij : i ≠ j) :
    proofideas_coincidenceCollapse (d := d) i j x ∈ CoincidenceLocus d k := by
  refine ⟨i, j, hij, ?_⟩
  ext μ
  simp [proofideas_coincidenceCollapse, hij]

private theorem proofideas_norm_sub_coincidenceCollapse_le_pairDifference {k : ℕ}
    (x : NPointDomain d k) (i j : Fin k) (hij : i ≠ j) :
    ‖x - proofideas_coincidenceCollapse (d := d) i j x‖ ≤ ‖x i - x j‖ := by
  change ↑(Finset.univ.sup fun q => ‖(x - proofideas_coincidenceCollapse (d := d) i j x) q‖₊) ≤
    ‖x i - x j‖
  have hdistNN :
      Finset.univ.sup
          (fun q => ‖(x - proofideas_coincidenceCollapse (d := d) i j x) q‖₊) ≤
        ‖x i - x j‖₊ := by
    refine Finset.sup_le_iff.mpr ?_
    intro q _hq
    by_cases hqi : q = i
    · subst q
      have hqreal :
          ‖(x - proofideas_coincidenceCollapse (d := d) i j x) i‖ ≤ ‖x i - x j‖ := by
        calc
          ‖(x - proofideas_coincidenceCollapse (d := d) i j x) i‖ =
              ‖x i - midpoint ℝ (x i) (x j)‖ := by
                simp [proofideas_coincidenceCollapse, hij]
          _ = ‖(⅟ (2 : ℝ)) • (x i - x j)‖ := by rw [left_sub_midpoint]
          _ = ‖(⅟ (2 : ℝ))‖ * ‖x i - x j‖ := norm_smul _ _
          _ ≤ 1 * ‖x i - x j‖ := by
              gcongr
              norm_num
          _ = ‖x i - x j‖ := by ring
      exact_mod_cast hqreal
    · by_cases hqj : q = j
      · subst q
        have hqreal :
            ‖(x - proofideas_coincidenceCollapse (d := d) i j x) j‖ ≤ ‖x i - x j‖ := by
          calc
            ‖(x - proofideas_coincidenceCollapse (d := d) i j x) j‖ =
                ‖x j - midpoint ℝ (x i) (x j)‖ := by
                  simp [proofideas_coincidenceCollapse, hqi]
            _ = ‖(⅟ (2 : ℝ)) • (x j - x i)‖ := by rw [right_sub_midpoint]
            _ = ‖(⅟ (2 : ℝ))‖ * ‖x j - x i‖ := norm_smul _ _
            _ ≤ 1 * ‖x j - x i‖ := by
                gcongr
                norm_num
            _ = ‖x i - x j‖ := by rw [norm_sub_rev, one_mul]
        exact_mod_cast hqreal
      · simp [proofideas_coincidenceCollapse, hqi, hqj]
  exact_mod_cast hdistNN

set_option maxHeartbeats 600000 in
private theorem proofideas_exists_iteratedLineDeriv_pair_flat_bound
    {k : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (j m : ℕ) (a b : Fin k) (hab : a ≠ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Fin j → NPointDomain d k) (x : NPointDomain d k),
        ‖(LineDeriv.iteratedLineDerivOp u f : SchwartzNPoint d k) x‖ ≤
          C * ‖x a - x b‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 (j + (m + 1)) f
  have hA_nonneg : 0 ≤ A := by positivity
  refine ⟨A / (((Nat.factorial m : ℕ) : ℝ)), by positivity, ?_⟩
  intro u x
  let F : SchwartzNPoint d k := ∂^{u} f
  let c : NPointDomain d k := proofideas_coincidenceCollapse (d := d) a b x
  let v : NPointDomain d k := x - c
  let L : ℝ →L[ℝ] NPointDomain d k :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c)) ∘ L
  have hF_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (F : NPointDomain d k → ℂ) := fun r => by
    simpa [F] using (F.smooth r)
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c)) :=
    fun r => by
      simpa using (hF_contDiff r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_coin : c ∈ CoincidenceLocus d k := by
    simpa [c] using proofideas_coincidenceCollapse_mem_CoincidenceLocus (d := d) x a b hab
  have hF_vanish :
      VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F] using proofideas_iteratedLineDeriv_preserves_zeroDiagonal (f := f) hf u
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro q hq
    have hq_zero :
        iteratedDerivWithin q g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
          ((hg_contDiff q).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ q g 0 =
            (iteratedFDeriv ℝ q (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
              (L 0)).compContinuousLinearMap (fun _ : Fin q => L) := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
            (hshift_contDiff q) (x := 0) (i := q) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ q (F : NPointDomain d k → ℂ) (L 0 + c) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hF_vanish q c hc_coin
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hq_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      calc
        ‖L s‖ = ‖s • v‖ := by rfl
        _ = ‖s‖ * ‖v‖ := norm_smul s v
        _ = ‖v‖ * ‖s‖ := by ring
        _ ≤ ‖v‖ * ‖s‖ := le_rfl
    rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : NPointDomain d k => (F : NPointDomain d k → ℂ)
            (z + c)) (L t)).compContinuousLinearMap (fun _ : Fin (m + 1) => L) := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d k => (F : NPointDomain d k → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    have hFbound :
        ‖iteratedFDeriv ℝ (m + 1) (F : NPointDomain d k → ℂ) (L t + c)‖ ≤
          A * ∏ i, ‖u i‖ := by
      simpa [A, F, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
        proofideas_norm_iteratedFDeriv_iteratedLineDeriv_le_npoint
          (f := f) (j := j) (n := m + 1) u (L t + c)
    have hprod_nonneg : 0 ≤ ∏ _ : Fin (m + 1), ‖L‖ := by positivity
    have huprod_nonneg : 0 ≤ ∏ i, ‖u i‖ := by
      simpa using Finset.prod_nonneg (fun i _ => norm_nonneg (u i))
    have hcoeff_nonneg : 0 ≤ A * ∏ i, ‖u i‖ := by
      exact mul_nonneg hA_nonneg huprod_nonneg
    have hLpow_all : ∀ n : ℕ, ‖L‖ ^ n ≤ ‖v‖ ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            ‖L‖ ^ (n + 1) = ‖L‖ ^ n * ‖L‖ := by ring_nf
            _ ≤ ‖v‖ ^ n * ‖v‖ := by
                  exact mul_le_mul ih hL (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
            _ = ‖v‖ ^ (n + 1) := by ring_nf
    let D :=
      iteratedFDeriv ℝ (m + 1) (F : NPointDomain d k → ℂ) (L t + c)
    have hDcomp :
        ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖ ≤
          ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := by
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    calc
      ‖D.compContinuousLinearMap (fun _ : Fin (m + 1) => L)‖
          ≤ ‖D‖ * ∏ _ : Fin (m + 1), ‖L‖ := hDcomp
      _ ≤ (A * ∏ i, ‖u i‖) * ∏ _ : Fin (m + 1), ‖L‖ := by
            exact mul_le_mul_of_nonneg_right hFbound hprod_nonneg
      _ = (A * ∏ i, ‖u i‖) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_left (hLpow_all (m + 1)) hcoeff_nonneg
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hdist :
      ‖v‖ ≤ ‖x a - x b‖ := by
    simpa [v, c] using proofideas_norm_sub_coincidenceCollapse_le_pairDifference (d := d) x a b hab
  have hg_one : g 1 = F x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply]
  calc
    ‖(F : NPointDomain d k → ℂ) x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ ((A * ∏ i, ‖u i‖) * ‖v‖ ^ (m + 1)) *
          (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
          simpa [hTaylor_zero] using hrem
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
          field_simp [Nat.cast_ne_zero]
          ring
    _ ≤ (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x a - x b‖ ^ (m + 1) * ∏ i, ‖u i‖ := by
          gcongr

private theorem proofideas_exists_iteratedFDeriv_pair_flat_bound
    {k : ℕ}
    (f : SchwartzNPoint d k)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (q m : ℕ) (a b : Fin k) (hab : a ≠ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : NPointDomain d k,
        ‖iteratedFDeriv ℝ q (f : NPointDomain d k → ℂ) x‖ ≤
          C * ‖x a - x b‖ ^ (m + 1) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    proofideas_exists_iteratedLineDeriv_pair_flat_bound
      (f := f) hf q m a b hab
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  have hCx : 0 ≤ C * ‖x a - x b‖ ^ (m + 1) := by positivity
  rw [ContinuousMultilinearMap.opNorm_le_iff hCx]
  intro u
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, mul_assoc, mul_left_comm, mul_comm]
    using hC u x

private theorem proofideas_pair_power_factor_le
    {k M q : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ_le : δ ≤ 1)
    {x : NPointDomain d k} {a b : Fin k} (hx : ‖x a - x b‖ ≤ 2 * δ)
    (hq : q ∈ Finset.range (M + 1)) :
    (δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1) ≤ (2 : ℝ) ^ (M + 1) * δ := by
  have hq_le : q ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hpow : ‖x a - x b‖ ^ (M + 1) ≤ (2 * δ) ^ (M + 1) := by
    gcongr
  have hδ_inv_ge_one : 1 ≤ δ⁻¹ := by
    rw [one_le_inv₀ hδ]
    exact hδ_le
  have hdelta_inv_mono : (δ⁻¹) ^ q ≤ (δ⁻¹) ^ M := by
    exact pow_le_pow_right₀ hδ_inv_ge_one hq_le
  have hcancel : (δ⁻¹) ^ M * δ ^ (M + 1) = δ := by
    calc
      (δ⁻¹) ^ M * δ ^ (M + 1) = ((δ⁻¹) ^ M * δ ^ M) * δ := by
            rw [pow_succ']
            ring
      _ = (((δ ^ M)⁻¹ * δ ^ M) * δ) := by rw [inv_pow]
      _ = δ := by simp [pow_ne_zero M hδ.ne']
  calc
    (δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1)
        ≤ (δ⁻¹) ^ q * (2 * δ) ^ (M + 1) := by
            gcongr
    _ ≤ (δ⁻¹) ^ M * (2 * δ) ^ (M + 1) := by
          gcongr
    _ = (2 : ℝ) ^ (M + 1) * ((δ⁻¹) ^ M * δ ^ (M + 1)) := by
          rw [mul_pow]
          ring
    _ = (2 : ℝ) ^ (M + 1) * δ := by rw [hcancel]

set_option maxHeartbeats 1000000 in
private theorem proofideas_pairSmallCutoff_seminorm_le_linear
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b) :
    ∀ (N M : ℕ),
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
          SchwartzMap.seminorm ℝ N M
            (SchwartzMap.smulLeftCLM ℂ
              (fun x : NPointDomain d k =>
                (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                  (proofideas_pairDiffCLM (d := d) a b x))
              F.1 : SchwartzNPoint d k) ≤
              A * δ := by
  intro N M
  let B : ℕ → ℝ := fun q =>
    Classical.choose (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
      (d := d) a b q)
  let H : ℕ → ℝ := fun q =>
    Classical.choose
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : NPointDomain d k)).1 hF_compact.isBounded
  let R : ℝ := max R0 1
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have htsupport_F :
      tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR0 hx)
  have hB_nonneg : ∀ q : ℕ, 0 ≤ B q := by
    intro q
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
        (d := d) a b q)).1
  have hB_bound :
      ∀ q : ℕ, ∀ (δ : ℝ) (hδ : 0 < δ) (x : NPointDomain d k),
        ‖iteratedFDeriv ℝ q
            (fun y : NPointDomain d k =>
              (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
                (proofideas_pairDiffCLM (d := d) a b y)) x‖ ≤
          B q * (δ⁻¹) ^ q := by
    intro q δ hδ x
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pairSmallCutoff_bound
        (d := d) a b q)).2 δ hδ x
  have hH_nonneg : ∀ q : ℕ, 0 ≤ H q := by
    intro q
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)).1
  have hH_bound :
      ∀ q : ℕ, ∀ x : NPointDomain d k,
        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
          H q * ‖x a - x b‖ ^ (M + 1) := by
    intro q x
    exact (Classical.choose_spec
      (proofideas_exists_iteratedFDeriv_pair_flat_bound
        (d := d) (f := F.1) F.2 (q := M - q) (m := M) a b hab)).2 x
  let A : ℝ :=
    ∑ q ∈ Finset.range (M + 1),
      (M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro q hq
    have hBq : 0 ≤ B q := hB_nonneg q
    have hHq : 0 ≤ H q := hH_nonneg q
    have hRN : 0 ≤ R ^ N := pow_nonneg hR_nonneg N
    positivity
  refine ⟨A, hA_nonneg, ?_⟩
  intro δ hδ hδ_le_one
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let fδ : SchwartzNPoint d k := SchwartzMap.smulLeftCLM ℂ ηδ F.1
  have hη_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ηδ := by
    fun_prop
  have hF_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (F.1 : NPointDomain d k → ℂ) := by
    simpa using (F.1 : SchwartzNPoint d k).smooth'
  have hη_temp : ηδ.HasTemperateGrowth := by
    fun_prop
  have hfun :
      ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) = fun x => ηδ x * F.1 x := by
    funext x
    simpa [fδ, ηδ, smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply (g := ηδ) hη_temp F.1 x)
  have hsupp_eta :
      Function.support ηδ ⊆ {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    simpa [ηδ] using
      proofideas_pairSmallCutoff_support_pair_norm_le (d := d) hδ a b
  have hclosed_pair : IsClosed {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    have hclosed_raw :
        IsClosed {x : NPointDomain d k |
          ‖proofideas_pairDiffCLM (d := d) a b x‖ ≤ 2 * δ} :=
      isClosed_le ((proofideas_pairDiffCLM (d := d) a b).continuous.norm) continuous_const
    simpa [proofideas_pairDiffCLM_apply] using hclosed_raw
  have htsupport_eta :
      tsupport ηδ ⊆ {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} :=
    closure_minimal hsupp_eta hclosed_pair
  have htsupport_fδ_pair :
      tsupport ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_eta
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := F.1) hx).2)
  have htsupport_fδ_compact :
      tsupport ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact htsupport_F
      ((SchwartzMap.tsupport_smulLeftCLM_subset (g := ηδ) (f := F.1) hx).1)
  have hsupport_deriv_pair :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) ⊆
        {x : NPointDomain d k | ‖x a - x b‖ ≤ 2 * δ} := by
    intro x hx
    exact htsupport_fδ_pair
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ)) hx)
  have hsupport_deriv_compact :
      Function.support (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)) ⊆
        Metric.closedBall (0 : NPointDomain d k) R := by
    intro x hx
    exact htsupport_fδ_compact
      (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := M)
        (f := ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ)) hx)
  have hbound :
      ∀ x : NPointDomain d k,
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x‖ ≤
          A * δ := by
    intro x
    by_cases hx :
        x ∈ Function.support
          (iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    · have hxpair : ‖x a - x b‖ ≤ 2 * δ := hsupport_deriv_pair hx
      have hxR : x ∈ Metric.closedBall (0 : NPointDomain d k) R :=
        hsupport_deriv_compact hx
      have hRN : ‖x‖ ^ N ≤ R ^ N := by
        gcongr
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
      have hsmul :=
        norm_iteratedFDeriv_smul_le (𝕜 := ℝ)
          hη_smooth hF_smooth x (n := M) (by exact_mod_cast le_top)
      calc
        ‖x‖ ^ N * ‖iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x‖
            = ‖x‖ ^ N * ‖iteratedFDeriv ℝ M (fun y => ηδ y * F.1 y) x‖ := by
                rw [hfun]
        _ ≤ ‖x‖ ^ N *
              ∑ q ∈ Finset.range (M + 1),
                (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ := by
                exact mul_le_mul_of_nonneg_left hsmul (by positivity)
        _ = ∑ q ∈ Finset.range (M + 1),
              ‖x‖ ^ N *
                ((M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                  ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ q ∈ Finset.range (M + 1),
              ((M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                refine Finset.sum_le_sum ?_
                intro q hq
                have hBq := hB_bound q δ hδ x
                have hHq := hH_bound q x
                have hBq_nonneg : 0 ≤ B q := hB_nonneg q
                have hHq_nonneg : 0 ≤ H q := hH_nonneg q
                have hBq_rhs_nonneg : 0 ≤ B q * (δ⁻¹) ^ q := by positivity
                have hchoose_nonneg : 0 ≤ (M.choose q : ℝ) := by positivity
                have hprod :
                    ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
                      (B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1)) := by
                  exact mul_le_mul hBq hHq (norm_nonneg _) hBq_rhs_nonneg
                have hterm_coeff :
                    (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖ ≤
                      (M.choose q : ℝ) *
                        ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1))) := by
                  calc
                    (M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖
                        =
                      (M.choose q : ℝ) * (‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖) := by
                          ring
                    _ ≤ (M.choose q : ℝ) *
                          ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1))) := by
                          exact mul_le_mul_of_nonneg_left hprod hchoose_nonneg
                have hcoeff_nonneg : 0 ≤ (M.choose q : ℝ) * B q * H q := by
                  exact mul_nonneg (mul_nonneg hchoose_nonneg hBq_nonneg) hHq_nonneg
                have hpower :
                    ‖x‖ ^ N * ((δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1)) ≤
                      R ^ N * ((2 : ℝ) ^ (M + 1) * δ) := by
                  exact mul_le_mul hRN
                    (proofideas_pair_power_factor_le (d := d) (hδ := hδ)
                      (hδ_le := hδ_le_one) (x := x) (a := a) (b := b) hxpair hq)
                    (by positivity) (pow_nonneg hR_nonneg _)
                calc
                  ‖x‖ ^ N *
                      ((M.choose q : ℝ) * ‖iteratedFDeriv ℝ q ηδ x‖ *
                        ‖iteratedFDeriv ℝ (M - q) (F.1 : NPointDomain d k → ℂ) x‖)
                      ≤
                    ‖x‖ ^ N *
                      ((M.choose q : ℝ) *
                        ((B q * (δ⁻¹) ^ q) * (H q * ‖x a - x b‖ ^ (M + 1)))) := by
                          exact mul_le_mul_of_nonneg_left hterm_coeff (by positivity)
                  _ = ((M.choose q : ℝ) * B q * H q) *
                        (‖x‖ ^ N * ((δ⁻¹) ^ q * ‖x a - x b‖ ^ (M + 1))) := by
                          ring
                  _ ≤ ((M.choose q : ℝ) * B q * H q) *
                        (R ^ N * ((2 : ℝ) ^ (M + 1) * δ)) := by
                          exact mul_le_mul_of_nonneg_left hpower hcoeff_nonneg
                  _ = ((M.choose q : ℝ) * B q * H q * R ^ N * (2 : ℝ) ^ (M + 1)) * δ := by
                          ring
        _ = A * δ := by
              simp [A, Finset.sum_mul]
    · have hzero :
          iteratedFDeriv ℝ M ((fδ : SchwartzNPoint d k) : NPointDomain d k → ℂ) x = 0 := by
        by_contra hne
        exact hx (by simpa [Function.mem_support] using hne)
      have hnonneg : 0 ≤ A * δ := by positivity
      simpa [hzero] using hnonneg
  simpa [fδ, ηδ] using
    SchwartzMap.seminorm_le_bound ℝ N M fδ (by positivity) hbound

private def proofideas_pairNearPart
    {k : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    ZeroDiagonalSchwartz d k :=
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  ⟨SchwartzMap.smulLeftCLM ℂ ηδ F.1, by
    have hη : ηδ.HasTemperateGrowth := by
      fun_prop
    exact VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth (d := d) hη F.2⟩

private theorem proofideas_pairNearPart_tendsto_zero
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le_one : ρ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        proofideas_pairNearPart (d := d) (ρ / (n + 1 : ℝ))
          (by positivity) F a b)
      Filter.atTop (nhds (0 : ZeroDiagonalSchwartz d k)) := by
  rw [tendsto_subtype_rng]
  rw [(schwartz_withSeminorms ℝ (NPointDomain d k) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  obtain ⟨A, hA_nonneg, hA_bound⟩ :=
    proofideas_pairSmallCutoff_seminorm_le_linear
      (d := d) F hF_compact a b hab p.1 p.2
  let Bnd : ℝ := A * ρ + 1
  have hBnd_pos : 0 < Bnd := by
    dsimp [Bnd]
    positivity
  have hBnd_nonneg : 0 ≤ Bnd := le_of_lt hBnd_pos
  rcases exists_nat_one_div_lt (show 0 < ε / Bnd by positivity) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let δn : ℝ := ρ / (n + 1 : ℝ)
  have hδn_pos : 0 < δn := by
    dsimp [δn]
    positivity
  have hδn_le_ρ : δn ≤ ρ := by
    have hfrac : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
      have hden : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hone_pos : 0 < (1 : ℝ) := by positivity
      simpa using (one_div_le_one_div_of_le hone_pos hden)
    calc
      δn = ρ * ((n + 1 : ℝ)⁻¹) := by simp [δn, div_eq_mul_inv]
      _ ≤ ρ * 1 := by
            simpa using (mul_le_mul_of_nonneg_left hfrac (le_of_lt hρ_pos))
      _ = ρ := by ring
  have hδn_le_one : δn ≤ 1 := le_trans hδn_le_ρ hρ_le_one
  have hsemi_le :
      schwartzSeminormFamily ℝ (NPointDomain d k) ℂ p
          (((proofideas_pairNearPart (d := d) δn hδn_pos F a b).1 : SchwartzNPoint d k) - 0) ≤
        A * δn := by
    change SchwartzMap.seminorm ℝ p.1 p.2
      ((((proofideas_pairNearPart (d := d) δn hδn_pos F a b).1 : SchwartzNPoint d k) - 0)) ≤
        A * δn
    simpa [proofideas_pairNearPart, δn] using hA_bound δn hδn_pos hδn_le_one
  have hAρ_le_Bnd : A * ρ ≤ Bnd := by
    dsimp [Bnd]
    linarith
  have hscale :
      A * δn ≤ Bnd / (n + 1 : ℝ) := by
    have hden_pos : 0 < (n + 1 : ℝ) := by positivity
    have hdiv :
        (A * ρ) / (n + 1 : ℝ) ≤ Bnd / (n + 1 : ℝ) := by
      exact div_le_div_of_nonneg_right hAρ_le_Bnd (le_of_lt hden_pos)
    simpa [δn, mul_div_assoc] using hdiv
  have hfrac_mono :
      Bnd / (n + 1 : ℝ) ≤ Bnd / (N + 1 : ℝ) := by
    have hone_div :
        (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hden : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      have hN_pos : 0 < (N + 1 : ℝ) := by positivity
      simpa using (one_div_le_one_div_of_le hN_pos hden)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hone_div hBnd_nonneg)
  have hsmall :
      Bnd / (N + 1 : ℝ) < ε := by
    have := mul_lt_mul_of_pos_left hN hBnd_pos
    calc
      Bnd / (N + 1 : ℝ) = Bnd * (1 / (N + 1 : ℝ)) := by ring
      _ < Bnd * (ε / Bnd) := this
      _ = ε := by
        field_simp [show Bnd ≠ 0 by positivity]
  exact lt_of_le_of_lt (le_trans hsemi_le (le_trans hscale hfrac_mono)) hsmall

private theorem proofideas_spacetimeUnitBallBumpRadius_one_of_norm_le
    {R : ℝ} (hR : 0 < R) {x : SpacetimeDim d}
    (hx : ‖x‖ ≤ R) :
    proofideas_spacetimeUnitBallBumpRadius (d := d) R hR x = 1 := by
  rw [proofideas_spacetimeUnitBallBumpRadius]
  apply OSReconstruction.unitBallBumpSchwartzPiRadius_one_of_mem_closedBall (m := d + 1) hR
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx

private def proofideas_pairFarPart
    {k : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    ZeroDiagonalSchwartz d k :=
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  ⟨SchwartzMap.smulLeftCLM ℂ φδ F.1, by
    have hφ : φδ.HasTemperateGrowth := by
      fun_prop
    exact VanishesToInfiniteOrderOnCoincidence.smulLeft_of_hasTemperateGrowth (d := d) hφ F.2⟩

private theorem proofideas_pairFarPart_support_pair_norm_ge
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    Function.support
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      {x : NPointDomain d k | δ ≤ ‖x a - x b‖} := by
  intro x hx
  by_contra hnot
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  have hη_one : ηδ x = 1 := by
    have hnorm : ‖x a - x b‖ ≤ δ := le_of_lt (lt_of_not_ge hnot)
    dsimp [ηδ]
    exact proofideas_spacetimeUnitBallBumpRadius_one_of_norm_le (d := d) hδ hnorm
  have hφ_temp : φδ.HasTemperateGrowth := by
    fun_prop
  have hzero :
      (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) x = 0 := by
    change (SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) x = 0
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
    simp [φδ, hη_one]
  exact hx hzero

private theorem proofideas_pairFarPart_tsupport_pair_norm_ge
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      {x : NPointDomain d k | δ ≤ ‖x a - x b‖} := by
  refine closure_minimal ?support ?closed
  · exact proofideas_pairFarPart_support_pair_norm_ge (d := d) hδ F a b
  · have hclosed_raw :
        IsClosed {x : NPointDomain d k |
          δ ≤ ‖proofideas_pairDiffCLM (d := d) a b x‖} :=
      isClosed_le continuous_const
        ((proofideas_pairDiffCLM (d := d) a b).continuous.norm)
    simpa [proofideas_pairDiffCLM_apply] using hclosed_raw

private theorem proofideas_pairFarPart_tsupport_disjoint_pair_diagonal
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    Disjoint
      (tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ))
      {x : NPointDomain d k | x a = x b} := by
  rw [Set.disjoint_left]
  intro x hx hEq
  have hle : δ ≤ ‖x a - x b‖ :=
    proofideas_pairFarPart_tsupport_pair_norm_ge (d := d) hδ F a b hx
  have hEq' : x a = x b := hEq
  have hzero : ‖x a - x b‖ = 0 := by simp [hEq']
  linarith

private theorem proofideas_pairFarPart_hasCompactSupport
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) :
    HasCompactSupport
      (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) := by
  refine hF_compact.mono' ?_
  intro x hx
  have hx_ts :
      x ∈ tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) :=
    subset_closure hx
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  change
    x ∈ tsupport
      ((SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) at hx_ts
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := φδ) (f := F.1) hx_ts).1

private theorem proofideas_pairFarPart_tsupport_subset_original
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    tsupport
        (((proofideas_pairFarPart (d := d) δ hδ F a b).1 : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
  intro x hx
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  change
    x ∈ tsupport
      ((SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) at hx
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := φδ) (f := F.1) hx).1

private theorem proofideas_pairFarPart_add_pairNearPart
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (F : ZeroDiagonalSchwartz d k) (a b : Fin k) :
    proofideas_pairFarPart (d := d) δ hδ F a b +
      proofideas_pairNearPart (d := d) δ hδ F a b = F := by
  let ηδ : NPointDomain d k → ℂ := fun x =>
    (proofideas_spacetimeUnitBallBumpRadius (d := d) δ hδ : SchwartzSpacetime d)
      (proofideas_pairDiffCLM (d := d) a b x)
  let φδ : NPointDomain d k → ℂ := fun x => (1 : ℂ) - ηδ x
  have hη_temp : ηδ.HasTemperateGrowth := by
    fun_prop
  have hφ_temp : φδ.HasTemperateGrowth := by
    fun_prop
  apply Subtype.ext
  ext x
  change
    (SchwartzMap.smulLeftCLM ℂ φδ F.1 : SchwartzNPoint d k) x +
      (SchwartzMap.smulLeftCLM ℂ ηδ F.1 : SchwartzNPoint d k) x = F.1 x
  rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp,
    SchwartzMap.smulLeftCLM_apply_apply hη_temp]
  simp only [φδ, smul_eq_mul]
  ring

private theorem proofideas_pairFarPart_tendsto
    {k : ℕ}
    (F : ZeroDiagonalSchwartz d k)
    (hF_compact : HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
    (a b : Fin k) (hab : a ≠ b)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le_one : ρ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        proofideas_pairFarPart (d := d) (ρ / (n + 1 : ℝ))
          (by positivity) F a b)
      Filter.atTop (nhds F) := by
  let near : ℕ → ZeroDiagonalSchwartz d k := fun n =>
    proofideas_pairNearPart (d := d) (ρ / (n + 1 : ℝ)) (by positivity) F a b
  let far : ℕ → ZeroDiagonalSchwartz d k := fun n =>
    proofideas_pairFarPart (d := d) (ρ / (n + 1 : ℝ)) (by positivity) F a b
  have hnear_tendsto :
      Filter.Tendsto near Filter.atTop (nhds (0 : ZeroDiagonalSchwartz d k)) :=
    proofideas_pairNearPart_tendsto_zero
      (d := d) F hF_compact a b hab hρ_pos hρ_le_one
  have hnear_val_tendsto :
      Filter.Tendsto (fun n : ℕ => (near n).1) Filter.atTop
        (nhds (0 : SchwartzNPoint d k)) := by
    rw [tendsto_subtype_rng] at hnear_tendsto
    simpa using hnear_tendsto
  have hval_tendsto :
      Filter.Tendsto (fun n : ℕ => (far n).1) Filter.atTop
        (nhds F.1) := by
    have hseq_eq :
        (fun n : ℕ => (far n).1) =
          (fun n : ℕ => F.1 - (near n).1) := by
      funext n
      have hδ : 0 < ρ / (n + 1 : ℝ) := by positivity
      have hsum_val : (far n).1 + (near n).1 = F.1 := by
        have hcoe :
            ((far n + near n : ZeroDiagonalSchwartz d k)).1 = F.1 := by
          simpa [far, near] using congrArg
            (fun z : ZeroDiagonalSchwartz d k => z.1)
            (proofideas_pairFarPart_add_pairNearPart
              (d := d) (δ := ρ / (n + 1 : ℝ)) hδ F a b)
        exact hcoe
      exact eq_sub_iff_add_eq.mpr hsum_val
    rw [hseq_eq]
    simpa [sub_eq_add_neg] using (tendsto_const_nhds.sub hnear_val_tendsto)
  rw [tendsto_subtype_rng]
  simpa [far]
    using hval_tendsto

private theorem compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSubmodule
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)} ⊆
      closure
        ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
          (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  classical
  let Pair := collisionPairIndex k
  let pairs : List Pair := (Finset.univ : Finset Pair).toList
  let B : Submodule ℂ (ZeroDiagonalSchwartz d k) :=
    admissibleProductTensorSubmodule (d := d) k
  let C : Set (ZeroDiagonalSchwartz d k) := closure ((B : Set (ZeroDiagonalSchwartz d k)))
  let Avoid (F : ZeroDiagonalSchwartz d k) (p : Pair) : Prop :=
    Disjoint
      (tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
      {x : NPointDomain d k | x p.1.1 = x p.1.2}
  let Good (l : List Pair) : Prop :=
    ∀ F : ZeroDiagonalSchwartz d k,
      HasCompactSupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) →
      (∀ p : Pair, p ∈ l → Avoid F p) →
      F ∈ C
  have hbase : Good pairs := by
    intro F hF_comp havoid
    have hF_disj :
        Disjoint
          (tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ))
          (CoincidenceLocus d k) := by
      rw [Set.disjoint_left]
      intro x hx hcoin
      rcases hcoin with ⟨i, j, hij, hEq⟩
      let p : Pair := ⟨(i, j), hij⟩
      have hp_mem : p ∈ pairs := by
        simp [pairs]
      exact Set.disjoint_left.mp (havoid p hp_mem) hx (by simpa [p] using hEq)
    simpa [C, B] using
      coincidence_free_compactSupport_mem_closure_admissibleProductTensorSubmodule
        (d := d) (k := k) F hF_comp hF_disj
  have hstep : ∀ (p : Pair) (l : List Pair), Good (p :: l) → Good l := by
    intro p l hnext F hF_comp havoid
    let far : ℕ → ZeroDiagonalSchwartz d k := fun n =>
      proofideas_pairFarPart (d := d) (1 / (n + 1 : ℝ)) (by positivity)
        F p.1.1 p.1.2
    have hfar_tendsto : Filter.Tendsto far Filter.atTop (nhds F) := by
      simpa [far] using
        proofideas_pairFarPart_tendsto (d := d) F hF_comp p.1.1 p.1.2 p.2
          (ρ := 1) (by norm_num) (by norm_num)
    have hfar_mem : ∀ n : ℕ, far n ∈ C := by
      intro n
      refine hnext (far n) ?hcomp ?havoid
      · simpa [far] using
          proofideas_pairFarPart_hasCompactSupport
            (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
            F hF_comp p.1.1 p.1.2
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst q
          simpa [Avoid, far] using
            proofideas_pairFarPart_tsupport_disjoint_pair_diagonal
              (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
              F p.1.1 p.1.2
        · dsimp [Avoid]
          rw [Set.disjoint_left]
          intro x hx hdiag
          have hx_orig :
              x ∈ tsupport ((F.1 : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
            simpa [far] using
              proofideas_pairFarPart_tsupport_subset_original
                (d := d) (δ := 1 / (n + 1 : ℝ)) (by positivity)
                F p.1.1 p.1.2 hx
          exact Set.disjoint_left.mp (havoid q hq) hx_orig hdiag
    exact isClosed_closure.mem_of_tendsto hfar_tendsto
      (Filter.Eventually.of_forall hfar_mem)
  have hreduce : ∀ l : List Pair, Good l → Good [] := by
    intro l
    induction l with
    | nil =>
        intro h
        exact h
    | cons p l ih =>
        intro h
        exact ih (hstep p l h)
  intro F hF_comp
  have hempty : Good [] := hreduce pairs hbase
  simpa [C, B] using hempty F hF_comp (by intro p hp; cases hp)

private theorem admissibleProductTensorSubmodule_dense_zeroDiagonal
    {d : ℕ} [NeZero d]
    (k : ℕ) :
    Dense
      ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
        (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
  let C : Set (ZeroDiagonalSchwartz d k) :=
    {F : ZeroDiagonalSchwartz d k |
      HasCompactSupport ((F : ZeroDiagonalSchwartz d k).1 : NPointDomain d k → ℂ)}
  have hC_dense : Dense C := dense_hasCompactSupport_zeroDiagonal (d := d) k
  have hC_subset :
      C ⊆ closure
        ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
          (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) :=
    compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSubmodule (d := d) k
  have hclosure_subset :
      closure C ⊆ closure
        ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
          (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) := by
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
      Dense
        ((admissibleProductTensorSubmodule (d := d) k : Submodule ℂ
          (ZeroDiagonalSchwartz d k)) : Set (ZeroDiagonalSchwartz d k)) :=
    admissibleProductTensorSubmodule_dense_zeroDiagonal (d := d) k
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
