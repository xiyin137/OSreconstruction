/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceDerivatives

/-!
# OS-II Chapter V Real-Edge/Cauchy Transfer

This file isolates the analytic transfer in equation `(5.17)`. A holomorphic
scalar branch on a complex polydisc is restricted to the real affine slice
through its center. If that slice agrees locally with a real-edge
representative, then every mixed complex derivative, and hence every Cauchy
coefficient, is determined by the corresponding real iterated derivative.

The remaining OS-specific obligation is therefore to compute that real mixed
derivative using the reflected positive-time source pairing.
-/

noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Coordinatewise inclusion of a real finite-dimensional chart into its
complexification. -/
def realCoordinateEmbeddingCLM (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] theorem realCoordinateEmbeddingCLM_apply
    {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    realCoordinateEmbeddingCLM m x i = x i := by
  change Complex.ofRealCLM (x i) = (x i : ℂ)
  rfl

/-- The real affine slice through a complex center. -/
def realAffineSlice
    {m : ℕ}
    (f : (Fin m → ℂ) → ℂ)
    (center : Fin m → ℂ)
    (x : Fin m → ℝ) : ℂ :=
  f (center + realCoordinateEmbeddingCLM m x)

/-- A local real-edge identity transfers the complex iterated derivative to
the corresponding real iterated derivative on the affine slice. -/
theorem iteratedFDeriv_eq_realEdge_iteratedFDeriv
    {m N : ℕ}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi : IsScalarTower ℝ ℂ (Fin m → ℂ))
    {f : (Fin m → ℂ) → ℂ}
    {g : (Fin m → ℝ) → ℂ}
    {center : Fin m → ℂ}
    {U : Set (Fin m → ℂ)}
    (hU : IsOpen U)
    (hcenter : center ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hreal :
      (fun x : Fin m → ℝ => realAffineSlice f center x) =ᶠ[𝓝 0] g)
    (directions : Fin N → (Fin m → ℝ)) :
    iteratedFDeriv ℂ N f center
        (fun j i => directions j i) =
      iteratedFDeriv ℝ N g 0 directions := by
  let shift : (Fin m → ℂ) → (Fin m → ℂ) := fun z => center + z
  let shifted : (Fin m → ℂ) → ℂ := fun z => f (shift z)
  let V : Set (Fin m → ℂ) := shift ⁻¹' U
  let embed := realCoordinateEmbeddingCLM m
  let W : Set (Fin m → ℝ) := embed ⁻¹' V
  have hshift_cont : Continuous shift := by
    exact continuous_const.add continuous_id
  have hV_open : IsOpen V := hU.preimage hshift_cont
  have hzeroV : (0 : Fin m → ℂ) ∈ V := by
    simpa [V, shift] using hcenter
  have hshifted_contDiffOn :
      ContDiffOn ℂ N shifted V := by
    intro z hz
    have hzU : shift z ∈ U := hz
    have houter : ContDiffAt ℂ N f (shift z) :=
      (SCV.differentiableOn_analyticAt hU hf hzU).contDiffAt
    have hinner : ContDiffAt ℂ N shift z := by
      simpa [shift] using
        (contDiffAt_const.add contDiffAt_id :
          ContDiffAt ℂ N (fun w : Fin m → ℂ => center + w) z)
    have hcomp : ContDiffAt ℂ N shifted z := by
      simpa only [shifted, Function.comp_def] using houter.comp z hinner
    exact hcomp.contDiffWithinAt
  have hshifted_contDiffOn_real :
      ContDiffOn ℝ N shifted V :=
    @ContDiffOn.restrict_scalars
      ℝ _ (Fin m → ℂ) _ _ ℂ _ _ V shifted N
      ℂ _ _ _ hTowerPi _ hTowerC hshifted_contDiffOn
  have hW_open : IsOpen W := hV_open.preimage embed.continuous
  have hzeroW : (0 : Fin m → ℝ) ∈ W := by
    simpa [W, embed] using hzeroV
  have hcomp :=
    embed.iteratedFDerivWithin_comp_right
      hshifted_contDiffOn_real hV_open.uniqueDiffOn hW_open.uniqueDiffOn
      hzeroV (i := N) le_rfl
  have hcomp_global :
      iteratedFDeriv ℝ N (shifted ∘ embed) 0 =
        (iteratedFDeriv ℝ N shifted 0).compContinuousLinearMap
          (fun _ => embed) := by
    rw [← iteratedFDerivWithin_of_isOpen N hW_open hzeroW,
      ← iteratedFDerivWithin_of_isOpen N hV_open hzeroV]
    exact hcomp
  have hshifted_contDiffAt :
      ContDiffAt ℂ N shifted 0 :=
    hshifted_contDiffOn 0 hzeroV |>.contDiffAt
      (hV_open.mem_nhds hzeroV)
  have hrestrict :=
    @ContDiffAt.restrictScalars_iteratedFDeriv
      ℝ ℂ _ _ _ (Fin m → ℂ) _ _ _ hTowerPi
      ℂ _ _ _ hTowerC 0 shifted N hshifted_contDiffAt
  have hlocal :
      iteratedFDeriv ℝ N (shifted ∘ embed) 0 =
        iteratedFDeriv ℝ N g 0 := by
    apply
      (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ?_ N).eq_of_nhds
    simpa [realAffineSlice, shifted, shift, embed, Function.comp_def] using
      hreal
  calc
    iteratedFDeriv ℂ N f center (fun j i => directions j i) =
        iteratedFDeriv ℂ N shifted 0
          (fun j i => directions j i) := by
      have hshift :
          iteratedFDeriv ℂ N shifted 0 =
            iteratedFDeriv ℂ N f center := by
        simpa [shifted, shift] using
          (iteratedFDeriv_comp_add_left (𝕜 := ℂ) N center
            (0 : Fin m → ℂ))
      exact congrArg (fun D => D (fun j i => directions j i)) hshift.symm
    _ = iteratedFDeriv ℝ N shifted 0
          (fun j => embed (directions j)) := by
      rw [← hrestrict]
      rfl
    _ = iteratedFDeriv ℝ N (shifted ∘ embed) 0 directions := by
      rw [hcomp_global]
      rfl
    _ = iteratedFDeriv ℝ N g 0 directions := by
      rw [hlocal]

/-- The normalized Cauchy coefficient is the normalized real iterated
derivative of any locally equal real-edge representative. -/
theorem cauchyCoeffPolydisc_eq_realEdge_iteratedFDeriv
    {m : ℕ}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi : IsScalarTower ℝ ℂ (Fin (m + 1) → ℂ))
    {f : (Fin (m + 1) → ℂ) → ℂ}
    {g : (Fin (m + 1) → ℝ) → ℂ}
    {center : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc center (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hreal :
      (fun x : Fin (m + 1) → ℝ => realAffineSlice f center x) =ᶠ[𝓝 0] g)
    (α : Fin (m + 1) → ℕ) :
    SCV.cauchyCoeffPolydisc f center (fun _ => R) α =
      (((((∏ i, (α i).factorial : ℕ) : ℂ))⁻¹)) •
        iteratedFDeriv ℝ (∑ i, α i) g 0
          (fun j i =>
            if i = SCV.multiIndexEnumeration α j then 1 else 0) := by
  rw [SCV.cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
    hR hU hRU hf α]
  congr 1
  have hcenter : center ∈ U :=
    hRU (SCV.center_mem_closedPolydisc (fun _ => hR.le))
  have hderiv :=
    iteratedFDeriv_eq_realEdge_iteratedFDeriv
      hTowerC hTowerPi hU hcenter hf hreal
      (fun j (i : Fin (m + 1)) =>
        if i = SCV.multiIndexEnumeration α j then 1 else 0)
  convert hderiv using 1
  congr 1
  funext j i
  split <;> simp_all

end OSIIChapterV
end OSReconstruction
