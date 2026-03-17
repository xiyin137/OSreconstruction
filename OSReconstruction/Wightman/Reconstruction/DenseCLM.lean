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
