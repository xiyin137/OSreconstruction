import Mathlib
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent

/-!
# Dense Set Criteria For Continuous Linear Maps

Small helper lemmas for extending identities of continuous linear maps from a
dense subset to the whole domain.

This file also hosts the current `k = 2` nuclear-uniqueness stepping stones
for the `E -> R` critical path:

- product tensors determine CLMs on Schwartz n-point space,
- for `k = 2`, agreement on `twoPointDifferenceLift` shells determines the full
  flattened CLM.
-/

noncomputable section

open Topology

theorem ContinuousLinearMap.eq_zero_of_eq_zero_on_dense
    {𝕜 : Type*} [Semiring 𝕜]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [T2Space F]
    (T : E →L[𝕜] F) {S : Set E} (hS : Dense S)
    (hT : ∀ x ∈ S, T x = 0) :
    T = 0 := by
  ext x
  simp only [ContinuousLinearMap.zero_apply]
  have hclosed : IsClosed {x : E | T x = 0} :=
    isClosed_eq T.continuous continuous_const
  exact hclosed.closure_subset_iff.mpr (fun y hy => hT y hy) (hS.closure_eq ▸ trivial)

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

/-- Operational wrapper: if two CLMs extend the same multilinear map on
product tensors, then they agree globally. -/
theorem schwinger_eq_witness_of_eq_on_products (d n : ℕ)
    (W L : SchwartzNPointSpace d n →L[ℂ] ℂ)
    (Phi : (Fin n → SchwartzSpacetime d) → ℂ)
    (hW : ∀ fs, W (SchwartzMap.productTensor fs) = Phi fs)
    (hL : ∀ fs, L (SchwartzMap.productTensor fs) = Phi fs) :
    W = L := by
  exact clm_eq_of_eq_on_productTensor d n W L (fun fs => by rw [hW, hL])

/-- For `k = 2`, agreement of two flattened CLMs on the
`twoPointDifferenceLift` shell already determines them on the whole flattened
two-point Schwartz space. -/
theorem flattened_clm_eq_of_eq_on_twoPointDifferenceShell
    (L₁ L₂ : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (h : ∀ χ h : SchwartzSpacetime d,
      L₁ (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by omega)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h)))) =
        L₂ (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by omega)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h))))) :
    L₁ = L₂ := by
  let J : SchwartzNPointSpace d 2 →L[ℂ]
      SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    (OSReconstruction.reindexSchwartzFin
      (show 2 * (d + 1) = (d + 1) + (d + 1) by omega)).comp
      (OSReconstruction.flattenSchwartzNPoint (d := d))
  let L₁' : SchwartzNPointSpace d 2 →L[ℂ] ℂ := L₁.comp J
  let L₂' : SchwartzNPointSpace d 2 →L[ℂ] ℂ := L₂.comp J
  have hprod : ∀ fs : Fin 2 → SchwartzSpacetime d,
      L₁' (SchwartzMap.productTensor fs) = L₂' (SchwartzMap.productTensor fs) := by
    intro fs
    have hshell :
        OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
            (twoPointDifferenceLift (fs 0) (fs 1)) =
          SchwartzMap.productTensor fs := by
      ext x
      simp [OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift,
        SchwartzMap.productTensor_apply]
    simpa [L₁', L₂', J, hshell] using h (fs 0) (fs 1)
  have hLift : L₁' = L₂' :=
    clm_eq_of_eq_on_productTensor d 2 L₁' L₂' hprod
  ext F
  let U : SchwartzNPointSpace d 2 :=
    OSReconstruction.unflattenSchwartzNPoint (d := d)
      (OSReconstruction.reindexSchwartzFin
        (show (d + 1) + (d + 1) = 2 * (d + 1) by omega) F)
  have hJU : J U = F := by
    let e : 2 * (d + 1) = (d + 1) + (d + 1) := by omega
    have hflat_unflat :
        OSReconstruction.flattenSchwartzNPoint (d := d)
          (OSReconstruction.unflattenSchwartzNPoint (d := d)
            (OSReconstruction.reindexSchwartzFin e.symm F)) =
          OSReconstruction.reindexSchwartzFin e.symm F := by
      ext x
      simp [OSReconstruction.flattenSchwartzNPoint_apply,
        OSReconstruction.unflattenSchwartzNPoint_apply]
    have hcast :
        (castFinCLE e.symm).symm = castFinCLE e := by
      ext x i
      rfl
    have hreindex_inv :
        OSReconstruction.reindexSchwartzFin e
          (OSReconstruction.reindexSchwartzFin e.symm F) = F := by
      ext x
      simp [OSReconstruction.reindexSchwartzFin_apply, hcast]
    calc
      J U = OSReconstruction.reindexSchwartzFin e
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.unflattenSchwartzNPoint (d := d)
                (OSReconstruction.reindexSchwartzFin e.symm F))) := by
              rfl
      _ = OSReconstruction.reindexSchwartzFin e
            (OSReconstruction.reindexSchwartzFin e.symm F) := by
            rw [hflat_unflat]
      _ = F := hreindex_inv
  rw [show L₁ F = L₁ (J U) from by rw [hJU],
      show L₂ F = L₂ (J U) from by rw [hJU]]
  exact congrFun (congrArg DFunLike.coe hLift) U
