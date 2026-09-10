/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib
import OSReconstruction.Wightman.WightmanAxioms
import Init
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.BlockIntegral















noncomputable section

open Topology

theorem ContinuousLinearMap.eq_of_eq_on_dense
    {𝕜 : Type*} [Semiring 𝕜]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [T2Space F]
    (T₁ T₂ : E →L[𝕜] F) {S : Set E} (hS : Dense S)
    (hT : ∀ x ∈ S, T₁ x = T₂ x) :
    T₁ = T₂ := by
  ext x
  have hclosed : IsClosed {x : E | T₁ x = T₂ x} :=
    isClosed_eq T₁.continuous T₂.continuous
  exact hclosed.closure_subset_iff.mpr (fun y hy => hT y hy) (hS.closure_eq ▸ trivial)

open SchwartzMap
open OSReconstruction

variable {d : ℕ}

/-- Any continuous linear functional on Schwartz n-point space that vanishes on
all product tensors is zero. This is the nuclear-uniqueness core of the
`k = 2` CLM-determination route. -/
theorem clm_zero_of_zero_on_productTensor (d n : ℕ)
    (L : SchwartzNPointSpace d n →L[ℂ] ℂ)
    (hL : ∀ fs : Fin n → SchwartzSpacetime d,
      L (SchwartzMap.productTensor fs) = 0) :
    L = 0 := by
  let Phi₀ : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ := 0
  obtain ⟨W₀, hW₀, hW₀_unique⟩ := schwartz_nuclear_extension d n Phi₀
  have hW₀_zero : W₀ = 0 := by
    have h0 : (0 : SchwartzNPointSpace d n →L[ℂ] ℂ) ∈
        {W | ∀ fs, W (SchwartzMap.productTensor fs) = Phi₀ fs} := by
      intro fs
      simp [Phi₀]
    exact hW₀_unique 0 h0 ▸ (hW₀_unique W₀ hW₀).symm
  have hL_extends : ∀ fs, L (SchwartzMap.productTensor fs) = Phi₀ fs := by
    intro fs
    simp [Phi₀, hL]
  exact hW₀_zero ▸ (hW₀_unique L hL_extends)

/-- The `ℂ`-linear span of Schwartz product tensors is dense in Schwartz n-point
space. This is the topological density form of the nuclear theorem already used
in `clm_zero_of_zero_on_productTensor`. -/
theorem productTensor_span_dense (d n : ℕ) :
    Dense (((Submodule.span ℂ
      {F : SchwartzNPointSpace d n |
        ∃ fs : Fin n → SchwartzSpacetime d, F = SchwartzMap.productTensor fs}) :
      Submodule ℂ (SchwartzNPointSpace d n)) : Set (SchwartzNPointSpace d n)) := by
  let S : Set (SchwartzNPointSpace d n) :=
    {F : SchwartzNPointSpace d n |
      ∃ fs : Fin n → SchwartzSpacetime d, F = SchwartzMap.productTensor fs}
  let M : Submodule ℂ (SchwartzNPointSpace d n) := Submodule.span ℂ S
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hM
  have hx : ∃ x : SchwartzNPointSpace d n, x ∉ M.topologicalClosure := by
    by_contra hx
    apply hM
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx'
    exact hx ⟨x, hx'⟩
  have hconv : Convex ℝ (M.topologicalClosure : Set (SchwartzNPointSpace d n)) := by
    simpa using (M.topologicalClosure.restrictScalars ℝ).convex
  rcases hx with ⟨x, hx⟩
  obtain ⟨f, u, hleft, hright⟩ :=
    RCLike.geometric_hahn_banach_closed_point
      (𝕜 := ℂ) (E := SchwartzNPointSpace d n)
      (x := x) (s := (M.topologicalClosure : Set (SchwartzNPointSpace d n)))
      hconv M.isClosed_topologicalClosure hx
  have hu_pos : 0 < u := by
    have hzero := hleft 0 M.topologicalClosure.zero_mem
    simpa using hzero
  have hre_zero :
      ∀ y ∈ M.topologicalClosure, (f y).re = 0 := by
    intro y hy
    by_contra hre
    let r : ℝ := (u + 1) / (f y).re
    have hlt := hleft ((r : ℂ) • y) (M.topologicalClosure.smul_mem (r : ℂ) hy)
    have hreval : (f ((r : ℂ) • y)).re = u + 1 := by
      calc
        (f ((r : ℂ) • y)).re = r * (f y).re := by
          simp [r, mul_comm]
        _ = u + 1 := by
          dsimp [r]
          field_simp [hre]
    have : ¬ u + 1 < u := by linarith
    exact this (hreval ▸ hlt)
  have hvanish :
      ∀ y ∈ M.topologicalClosure, f y = 0 := by
    intro y hy
    have hre : (f y).re = 0 := hre_zero y hy
    have hIy_re : (f ((Complex.I : ℂ) • y)).re = 0 := by
      exact hre_zero ((Complex.I : ℂ) • y) (M.topologicalClosure.smul_mem Complex.I hy)
    have him : (f y).im = 0 := by
      have htmp : -(f y).im = 0 := by
        simpa [ContinuousLinearMap.map_smul, mul_comm, mul_left_comm, mul_assoc] using hIy_re
      linarith
    exact Complex.ext hre him
  have hfS : ∀ y ∈ M, f y = 0 := by
    intro y hy
    exact hvanish y (subset_closure hy)
  have hf_prod : ∀ fs : Fin n → SchwartzSpacetime d,
      f (SchwartzMap.productTensor fs) = 0 := by
    intro fs
    exact hfS _ (Submodule.subset_span ⟨fs, rfl⟩)
  have hf_zero : f = 0 := clm_zero_of_zero_on_productTensor d n f hf_prod
  have : ¬ u < (0 : ℝ) := not_lt_of_ge hu_pos.le
  apply this
  simpa [hf_zero] using hright

/-- Two continuous linear maps on Schwartz n-point space agreeing on all
product tensors are equal. -/
theorem clm_eq_of_eq_on_productTensor (d n : ℕ)
    (L₁ L₂ : SchwartzNPointSpace d n →L[ℂ] ℂ)
    (h : ∀ fs : Fin n → SchwartzSpacetime d,
      L₁ (SchwartzMap.productTensor fs) = L₂ (SchwartzMap.productTensor fs)) :
    L₁ = L₂ := by
  have hsub : L₁ - L₂ = 0 :=
    clm_zero_of_zero_on_productTensor d n (L₁ - L₂) (by
      intro fs
      simp [h fs])
  exact sub_eq_zero.mp hsub

