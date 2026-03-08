/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.SCV.PaleyWiener

/-!
# BHW Translation and Schwinger Construction

This file now retains the forward-tube boundary-value and Schwinger-construction
results that are still used downstream.

The older standalone PET translation-invariance chain, culminating in the unused
`bhw_translation_invariant` theorem and its connectivity blocker, was removed
once the exported Wightman/OS theorem surfaces stopped depending on it.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]

theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 :
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 :
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n hRegular_W hSeedConn_hd2 hExtPerm_d1).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n hRegular_W hSeedConn_hd2 hExtPerm_d1).property.2.1
  -- x + iεη ∈ ForwardTube: successive differences of Im parts are ε·(η_k - η_{k-1}) ∈ V₊
  intro k
  show InOpenForwardCone d _
  -- The imaginary part of the successive difference is ε·(η_k - η_{k-1})
  have him : (fun μ => ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
      (if h : k.val = 0 then 0 else
        fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) + ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
      ε • (fun μ => η k μ - (if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
            Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
    · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      ring
  rw [him]
  exact inOpenForwardCone_smul d ε hε _ (hη_ft k)

/-- The BHW extension has the same distributional boundary values as W_n.

    The BHW extension F_ext agrees with W_analytic on the forward tube, and
    W_analytic has distributional boundary values recovering W_n by `spectrum_condition`.
    Therefore F_ext also has these boundary values: for η with each η_k ∈ V+,
    lim_{ε→0+} ∫ F_ext(x + iεη) f(x) dx = W_n(f).

    For `η : InForwardCone d n η`, the point `x + iεη` is in `ForwardTube d n` for
    every `ε > 0`. Hence `F_ext = W_analytic` pointwise on the whole integration path,
    and the claimed limit follows directly from `spectrum_condition`.

    Ref: Streater-Wightman Theorem 2-11 -/
theorem bhw_distributional_boundary_values {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 :
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 :
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n hRegular_W hSeedConn_hd2 hExtPerm_d1).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  have h_sc := (Wfn.spectrum_condition n).choose_spec.2 f η hη
  refine Filter.Tendsto.congr' ?_ h_sc
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
    (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn hRegular_W
      hSeedConn_hd2 hExtPerm_d1 f η hη ε hε).symm⟩

/-! #### Schwinger function construction -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the BHW extension F_ext (from `W_analytic_BHW`) composed
    with the Wick rotation map (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    where F_ext is the BHW extension of W_analytic to the permuted extended tube.
    We use F_ext rather than W_analytic because F_ext is defined and well-behaved
    on all Euclidean points (not just time-ordered ones), and carries the complex
    Lorentz invariance and permutation symmetry needed for E1b and E3.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ n : ℕ,
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 : ∀ n : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z) :
    SchwingerFunctions d :=
  fun n f =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val
        (fun k => wickRotatePoint (x k)) * (f x)

end
