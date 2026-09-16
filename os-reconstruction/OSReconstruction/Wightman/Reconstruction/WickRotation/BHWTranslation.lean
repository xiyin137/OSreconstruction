/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import Init
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Segment
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslationCore
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.SCV.PaleyWiener













open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]











-- `W_analytic_translation_on_forwardTube`, `permutedExtendedTube_isConnected`,
-- and `forwardTube_inter_translate_nonempty` are now provided by BHWTranslationCore.








/-- A normalized basepoint cutoff (Schwartz function with integral 1),
constructed from a smooth compactly supported bump function. -/
noncomputable def exists_normalized_cutoff (d : ℕ) [NeZero d] :
    BHW.NormalizedBasepointCutoff d :=
  BHW.normalizedCutoffOfBump d

namespace BHW

omit [NeZero d] in
/-- The reduced difference map sends forward-tube points to the reduced forward tube.

For z ∈ ForwardTube, the successive differences z_{j+1} - z_j have imaginary
parts in V₊ by definition, which is exactly the reduced forward-tube condition. -/
private theorem reducedDiffMap_mem_reducedForwardTubeN [NeZero d]
    (m : ℕ) {z : Fin (m + 1) → Fin (d + 1) → ℂ}
    (hz : z ∈ ForwardTube d (m + 1)) :
    reducedDiffMap (m + 1) d z ∈ ReducedForwardTubeN d m := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hz_pft : z ∈ PermutedForwardTube d (m + 1) 1 := by
    simpa [PermutedForwardTube] using hz
  have hpft := reducedDiffMap_mem_reducedPermutedForwardTube_of_mem_permutedForwardTube
    (1 : Equiv.Perm (Fin (m + 1))) hz_pft
  rwa [mem_reducedPermutedForwardTube, permOnReducedDiff_one] at hpft

omit [NeZero d] in
/-- Route 1 extension agrees with the spectrum-condition witness on the forward tube.

This is the key bridge: `route1AbsoluteBHWExtensionCanonical` is a pullback from
reduced coordinates, so it agrees with the input function on the forward tube
(where the input was descended from the spectrum condition). -/
theorem route1_agrees_with_old_on_forwardTube [NeZero d]
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (m : ℕ) (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    route1AbsoluteBHWExtensionCanonical Wfn χ m z =
      (Wfn.spectrum_condition (m + 1)).choose z := by
  -- Unfold to reduced BHW extension applied to reducedDiffMap z
  set hInput := route1ReducedAnalyticInputExists (d := d) Wfn χ m
  set ext := route1ReducedBHWExtension (d := d) Wfn χ hInput
  -- route1AbsoluteBHWExtensionCanonical z = ext.toFun (reducedDiffMap z)
  show ext.toFun (reducedDiffMap (m + 1) d z) = (Wfn.spectrum_condition (m + 1)).choose z
  -- reducedDiffMap z ∈ ReducedForwardTubeN, so ext agrees with the input there
  have hred : reducedDiffMap (m + 1) d z ∈ ReducedForwardTubeN d m :=
    reducedDiffMap_mem_reducedForwardTubeN m hz
  calc ext.toFun (reducedDiffMap (m + 1) d z)
      = hInput.toFun (reducedDiffMap (m + 1) d z) :=
          ext.agrees_on_reducedForwardTube _ hred
    _ = (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
          (reducedDiffMap (m + 1) d z) := rfl
    _ = (Wfn.spectrum_condition (m + 1)).choose z :=
          route1ReducedPreInputFromSpectrumCondition_factorization (d := d) Wfn m z hz

omit [NeZero d] in
/-- Route 1 extension is holomorphic on the permuted extended tube.

The Route 1 extension is a composition of the reduced BHW extension
(holomorphic on reduced PET) with the reduced difference map (a CLM,
hence holomorphic everywhere). Since reduced PET = reducedDiffMap '' PET,
the composition is holomorphic on PET. -/
theorem route1_holomorphicOn_PET [NeZero d]
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    DifferentiableOn ℂ (route1AbsoluteBHWExtensionCanonical Wfn χ m)
      (PermutedExtendedTube d (m + 1)) := by
  set hInput := route1ReducedAnalyticInputExists (d := d) Wfn χ m
  set ext := route1ReducedBHWExtension (d := d) Wfn χ hInput
  -- route1AbsoluteBHWExtensionCanonical = ext.toFun ∘ reducedDiffMap
  show DifferentiableOn ℂ (fun z => ext.toFun (reducedDiffMap (m + 1) d z))
    (PermutedExtendedTube d (m + 1))
  apply DifferentiableOn.comp ext.holomorphic
    (reducedDiffMap (m + 1) d).differentiable.differentiableOn
  -- For z ∈ PET, reducedDiffMap z ∈ reducedPermutedExtendedTube (which = reducedDiffMap '' PET)
  intro z hz
  exact Set.mem_image_of_mem _ hz

end BHW

/-- **BHW extension is translation invariant on the permuted extended tube.**

    The n-point Wightman function W_n(z₁, ..., zₙ) depends only on the differences
    z_k - z_{k-1}, hence is invariant under simultaneous translation z_k ↦ z_k + c
    for any constant c ∈ ℂ^{d+1}. The BHW extension inherits this property.

    **Proof.** By Route 1 (reduced difference coordinates): the Route 1 extension
    `G = route1AbsoluteBHWExtensionCanonical` is a pullback from reduced coordinates,
    hence algebraically translation-invariant. By BHW uniqueness (`W_analytic_BHW_unique`),
    `G = F_ext` on PET, so:

      F_ext(z+c) = G(z+c)  [BHW uniqueness]
               = G(z)      [algebraic: G is a pullback from reduced coords]
               = F_ext(z)  [BHW uniqueness]

    Ref: Streater-Wightman §2.5 (translation invariance);
    Jost, "The General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  -- Trivial cases
  by_cases hc : c = 0
  · simp [hc]
  by_cases hn : n = 0
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simp [hshift]
  -- Cast n to m + 1 form
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- Route 1 construction
  let χ := exists_normalized_cutoff d
  set G := BHW.route1AbsoluteBHWExtensionCanonical Wfn χ m
  -- G is holomorphic on PET (in the BHW namespace sense, then bridge)
  have hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d (m + 1)) := by
    rw [← BHW_permutedExtendedTube_eq]
    exact BHW.route1_holomorphicOn_PET Wfn χ m
  -- G agrees with W_analytic on FT
  have hG_ft : ∀ w ∈ ForwardTube d (m + 1),
      G w = (Wfn.spectrum_condition (m + 1)).choose w := by
    intro w hw
    exact BHW.route1_agrees_with_old_on_forwardTube Wfn χ m w
      (BHW_forwardTube_eq (d := d) (n := m + 1) ▸ hw)
  -- By BHW uniqueness: G = F_ext on PET
  have hG_eq : ∀ w ∈ PermutedExtendedTube d (m + 1),
      G w = (W_analytic_BHW Wfn (m + 1)).val w :=
    W_analytic_BHW_unique Wfn (m + 1) G hG_holo hG_ft
  -- 3-step calc via Route 1 translation invariance
  calc (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ)
      = G (fun k μ => z k μ + c μ) := (hG_eq _ hzc).symm
    _ = G z := BHW.route1AbsoluteBHWExtensionCanonical_translate Wfn χ m z c
    _ = (W_analytic_BHW Wfn (m + 1)).val z := hG_eq z hz













/-- **F_ext has a well-defined value on TranslatedPET.**

    If z+c₁ and z+c₂ are both in PET, then F_ext(z+c₁) = F_ext(z+c₂).
    Proof: Apply `bhw_translation_invariant` with translation (c₂ - c₁). -/
theorem F_ext_value_on_translatedPET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c₁ c₂ : Fin (d + 1) → ℂ)
    (h₁ : (fun k μ => z k μ + c₁ μ) ∈ PermutedExtendedTube d n)
    (h₂ : (fun k μ => z k μ + c₂ μ) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c₁ μ) =
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c₂ μ) := by
  have key := bhw_translation_invariant Wfn (fun μ => c₂ μ - c₁ μ)
    (fun k μ => z k μ + c₁ μ) h₁
    (by convert h₂ using 1; ext k μ; ring)
  simpa [sub_eq_add_neg, add_assoc] using key.symm

/-- The BHW extension evaluated via a TranslatedPET witness.

    For z ∈ TranslatedPET, this evaluates F_ext at z + c for some c with z+c ∈ PET.
    By `F_ext_value_on_translatedPET`, the result is independent of the witness c. -/
noncomputable def F_ext_on_translatedPET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) : ℂ :=
  (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ)

/-- `F_ext_on_translatedPET` agrees with `F_ext` on PET. -/
theorem F_ext_on_translatedPET_eq_on_PET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n)
    (hz_tpet : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET Wfn z hz_tpet =
    (W_analytic_BHW Wfn n).val z := by
  unfold F_ext_on_translatedPET
  have := F_ext_value_on_translatedPET Wfn z hz_tpet.choose 0
    hz_tpet.choose_spec
    (show (fun k μ => z k μ + (0 : Fin (d + 1) → ℂ) μ) ∈ PermutedExtendedTube d n by
      simp_rw [Pi.zero_apply, add_zero]; exact hz_pet)
  simp_rw [Pi.zero_apply, add_zero] at this
  exact this

/-- `F_ext_on_translatedPET` is translation-invariant on TranslatedPET. -/
theorem F_ext_on_translatedPET_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n) :
    F_ext_on_translatedPET Wfn z hz =
    F_ext_on_translatedPET Wfn (fun k μ => z k μ + c μ) hzc := by
  simp only [F_ext_on_translatedPET]
  show (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) =
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ + hzc.choose μ)
  have := F_ext_value_on_translatedPET Wfn z hz.choose (fun μ => c μ + hzc.choose μ)
    hz.choose_spec
    (show (fun k μ => z k μ + (fun μ => c μ + hzc.choose μ) μ) ∈ PermutedExtendedTube d n by
      convert hzc.choose_spec using 1; ext k μ; ring)
  convert this using 2
  ext k μ; ring

/-- Total-function version of `F_ext_on_translatedPET`: returns the TranslatedPET
    value when z ∈ TranslatedPET, else 0. This gives a well-defined integrand
    everywhere, with the "correct" BHW-extended value on the only set that matters
    (the complement is null for Wick-rotated Euclidean configurations, by
    `ae_euclidean_points_in_translatedPET`). -/
noncomputable def F_ext_on_translatedPET_total {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  if hz : z ∈ TranslatedPET d n then
    F_ext_on_translatedPET Wfn z hz
  else 0

/-- On PET, `F_ext_on_translatedPET_total` unfolds to the raw BHW extension. -/
theorem F_ext_on_translatedPET_total_eq_on_PET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n) :
    F_ext_on_translatedPET_total Wfn z =
    (W_analytic_BHW Wfn n).val z := by
  have hz_tpet : z ∈ TranslatedPET d n :=
    PermutedExtendedTube_subset_TranslatedPET hz_pet
  simp only [F_ext_on_translatedPET_total, dif_pos hz_tpet]
  exact F_ext_on_translatedPET_eq_on_PET Wfn z hz_pet hz_tpet

/-- `F_ext_on_translatedPET_total` is translation-invariant on TranslatedPET. -/
theorem F_ext_on_translatedPET_total_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn z =
    F_ext_on_translatedPET_total Wfn (fun k μ => z k μ + c μ) := by
  have hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n :=
    translatedPET_translate hz c
  simp only [F_ext_on_translatedPET_total, dif_pos hz, dif_pos hzc]
  exact F_ext_on_translatedPET_translation_invariant Wfn z c hz hzc

/-- `F_ext_on_translatedPET_total` is permutation-invariant on `TranslatedPET`. -/
theorem F_ext_on_translatedPET_total_perm_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn z =
    F_ext_on_translatedPET_total Wfn (fun k => z (σ k)) := by
  let zσ : Fin n → Fin (d + 1) → ℂ := fun k => z (σ k)
  have hzc : (fun k μ => z k μ + hz.choose μ) ∈ PermutedExtendedTube d n :=
    hz.choose_spec
  have hzσc : (fun k μ => zσ k μ + hz.choose μ) ∈ PermutedExtendedTube d n := by
    simpa [zσ] using permutedExtendedTube_perm (d := d) (n := n) σ hzc
  have hzσ : zσ ∈ TranslatedPET d n := ⟨hz.choose, hzσc⟩
  have hperm :
      (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hz.choose μ) := by
    simpa [zσ] using
      (((W_analytic_BHW Wfn n).property.2.2.2 σ
        (fun k μ => z k μ + hz.choose μ) hzc)).symm
  have hbridge :
      (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hz.choose μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hzσ.choose μ) :=
    F_ext_value_on_translatedPET Wfn zσ hz.choose hzσ.choose hzσc hzσ.choose_spec
  rw [F_ext_on_translatedPET_total, dif_pos hz, F_ext_on_translatedPET,
    F_ext_on_translatedPET_total, dif_pos hzσ, F_ext_on_translatedPET]
  exact hperm.trans hbridge

/-- Euclidean rotations preserve the total TranslatedPET extension. -/
theorem F_ext_on_translatedPET_total_rotation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hz : (fun k => wickRotatePoint (x k)) ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) =
    F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (R.mulVec (x k))) := by
  let Λ := ComplexLorentzGroup.ofEuclidean R hR_det hR_orth
  let z : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (x k)
  let zR : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (R.mulVec (x k))
  let cR : Fin (d + 1) → ℂ := fun μ => ∑ ν, Λ.val μ ν * hz.choose ν
  have hzc : (fun k μ => z k μ + hz.choose μ) ∈ PermutedExtendedTube d n :=
    hz.choose_spec
  have hzR_add :
      (fun k μ => zR k μ + cR μ) =
        BHW.complexLorentzAction Λ (fun k μ => z k μ + hz.choose μ) := by
    ext k μ
    rw [show zR k μ = ∑ ν, Λ.val μ ν * wickRotatePoint (x k) ν by
      simpa [zR, z, BHW.complexLorentzAction] using
        wickRotatePoint_ofEuclidean R hR_det hR_orth (x k) μ]
    simp [cR, BHW.complexLorentzAction, z]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ν hν
    ring
  have hzR_pet : (fun k μ => zR k μ + cR μ) ∈ PermutedExtendedTube d n := by
    have hzcBHW :
        (fun k μ => z k μ + hz.choose μ) ∈ BHW.PermutedExtendedTube d n := by
      simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzc
    have hzR_petBHW :
        BHW.complexLorentzAction Λ (fun k μ => z k μ + hz.choose μ) ∈
          BHW.PermutedExtendedTube d n :=
      BHW.complexLorentzAction_mem_permutedExtendedTube hzcBHW Λ
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := n), hzR_add] using hzR_petBHW
  have hzR : zR ∈ TranslatedPET d n := ⟨cR, hzR_pet⟩
  have hlor :
      (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + cR μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) := by
    have h :=
      (W_analytic_BHW Wfn n).property.2.2.1 Λ (fun k μ => z k μ + hz.choose μ) hzc
    rw [hzR_add]
    exact h
  have hbridge :
      (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + cR μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + hzR.choose μ) :=
    F_ext_value_on_translatedPET Wfn zR cR hzR.choose hzR_pet hzR.choose_spec
  simp only [F_ext_on_translatedPET_total, dif_pos hz, dif_pos hzR, F_ext_on_translatedPET,
    z, zR]
  exact hlor.symm.trans hbridge

/-- The smeared BHW extension equals the smeared W_analytic for approach directions
    within the forward tube cone.

    When the approach direction η has successive differences in V₊ (not just
    per-component V₊), the point x + iεη lies in the forward tube for all ε > 0.
    Since F_ext = W_analytic on the forward tube (BHW property 2), the integrals
    agree pointwise in ε, so the limits (distributional boundary values) also agree.

    This captures the forward-tube membership calculation: for z_k = x_k + iεη_k,
    the successive difference of imaginary parts is ε(η_k - η_{k-1}), which lies in
    V₊ when η has successive differences in V₊ and ε > 0 (V₊ is a cone).

    Ref: Streater-Wightman, Theorem 2-11; BHW property 2 -/
theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n).property.2.1
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
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  have h_sc := (Wfn.spectrum_condition n).choose_spec.2.2 f η hη
  refine Filter.Tendsto.congr' ?_ h_sc
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
    (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn f η hη ε hε).symm⟩



/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the **TranslatedPET-extended** BHW kernel
    `F_ext_on_translatedPET_total` composed with the Wick rotation map
    (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_on_translatedPET_total(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    `F_ext_on_translatedPET_total` agrees with `F_ext` on PET and extends to
    `TranslatedPET` via translation invariance (`bhw_translation_invariant`),
    returning 0 on the null set where wick(x) ∉ TranslatedPET. This is crucial
    for `n ≥ d+2`, where Wick-rotated Euclidean configurations generically lie
    in `TranslatedPET \ PET` (see `W11Counterexample.lean`). On this set, the
    raw `F_ext` value would be arbitrary `Classical.choice` garbage, but the
    TranslatedPET-extended value is the unique translation-invariant extension.

    Important: this full-Schwartz pairing belongs to the Wightman side of the
    story. Wightman functions are tempered distributions on all of
    `SchwartzNPoint`, so there is no problem with a raw full-Schwartz pairing
    appearing here.

    What the corrected OS-I axiom surface forbids is interpreting this raw
    Euclidean Wick-rotated formula as the honest Schwinger object. The honest
    Euclidean Schwinger family of the project lives on `ZeroDiagonalSchwartz`.
    So the present definition should be read as the raw Wightman-side
    Wick-rotated boundary pairing, while `constructSchwingerFunctions` below is
    the actual zero-diagonal Euclidean Schwinger family.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def wickRotatedBoundaryPairing (Wfn : WightmanFunctions d) :
    (n : ℕ) → SchwartzNPoint d n → ℂ :=
  fun n f =>
    ∫ x : NPointDomain d n,
      F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) * (f x)

/-- The honest OS-I Euclidean family extracted from Wightman functions: the raw
    Wick-rotated pairing restricted to `ZeroDiagonalSchwartz`.

    This is the Euclidean Schwinger family that should appear in the OS axioms
    and in the `R -> E` direction. -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f => wickRotatedBoundaryPairing Wfn n f.1

/-- Auxiliary alias for the honest zero-diagonal Schwinger family. -/
abbrev constructZeroDiagonalSchwingerFunctions (Wfn : WightmanFunctions d) :
    ZeroDiagonalSchwingerFunctions d :=
  constructSchwingerFunctions Wfn

end
