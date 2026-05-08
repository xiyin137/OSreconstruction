import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Compact
import OSReconstruction.SCV.EuclideanWeylOpen
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# OS45 BHW/Jost source-patch carriers

This file starts the direct OS I section 4.5 BHW/Jost carrier layer for the
theorem-2 locality route.  It contains only data surfaces and algebraic
bookkeeping after the analytic continuation data has been supplied.
-/

noncomputable section

open Complex Topology MeasureTheory NormedSpace

namespace BHW

variable {d n : ℕ} [NeZero d]

omit [NeZero d] in
/-- The real Wick-rotation map on `n`-point Euclidean configurations is
continuous.  This is the public version needed by OS45 source-patch
integrability lemmas. -/
theorem continuous_wickRotateRealConfig :
    Continuous (fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hcoord : Continuous (fun x : NPointDomain d n => x k 0) :=
      (continuous_apply 0).comp (continuous_apply k)
    simpa [wickRotatePoint] using
      continuous_const.mul (Complex.continuous_ofReal.comp hcoord)
  · simpa [wickRotatePoint, hμ] using
      (Complex.continuous_ofReal.comp
        ((continuous_apply μ).comp (continuous_apply k)))

omit [NeZero d] in
/-- Permuting point labels is complex differentiable in the finite product
configuration space. -/
theorem differentiable_permAct (σ : Equiv.Perm (Fin n)) :
    Differentiable ℂ (BHW.permAct (d := d) σ) := by
  rw [differentiable_pi]
  intro k
  simpa [BHW.permAct] using
    (differentiable_apply (σ k) :
      Differentiable ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ => z (σ k)))

omit [NeZero d] in
/-- The adjacent preimage of the ordinary extended tube under a finite source
permutation is open. -/
theorem isOpen_permAct_preimage_extendedTube
    (σ : Equiv.Perm (Fin n)) :
    IsOpen {z : Fin n → Fin (d + 1) → ℂ |
      BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n} :=
  BHW.isOpen_extendedTube.preimage
    (BHW.continuous_permAct (d := d) (n := n) σ)

/-- The BHW extension of the selected boundary-value witness is holomorphic on
the ordinary extended tube. -/
theorem differentiableOn_extendF_bvt_F_extendedTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n))
      (BHW.ExtendedTube d n) := by
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv_BHW :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  exact BHW.extendF_holomorphicOn n (bvt_F OS lgc n)
    hF_holo_BHW hF_cinv_BHW

/-- The adjacent initial branch obtained by precomposing `extendF` with a
source permutation is holomorphic on the corresponding preimage of the
ordinary extended tube. -/
theorem differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) σ z))
      {z | BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n} := by
  have hExtend :=
    BHW.differentiableOn_extendF_bvt_F_extendedTube
      (d := d) OS lgc n
  have hperm_diff := BHW.differentiable_permAct (d := d) (n := n) σ
  have hmaps :
      Set.MapsTo
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.permAct (d := d) σ z)
        {z | BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n}
        (BHW.ExtendedTube d n) := by
    intro z hz
    exact hz
  intro z hz
  exact (hExtend _ (hmaps hz)).comp z
    ((hperm_diff z).differentiableWithinAt) hmaps

/-- On an open Euclidean ordered source patch, the identity Wick trace is
integrable against every compactly supported Schwartz test supported in the
patch. -/
theorem integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)))
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp : tsupport (ψ : NPointDomain d n → ℂ) ⊆ V) :
    Integrable
      (fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u) := by
  let H : NPointDomain d n → ℂ :=
    fun u => bvt_F OS lgc n (fun k => wickRotatePoint (u k))
  have hF_cont : ContinuousOn (bvt_F OS lgc n) (_root_.ForwardTube d n) :=
    (bvt_F_holomorphic OS lgc n).continuousOn
  have hH_cont : ContinuousOn H V := by
    refine hF_cont.comp
      (BHW.continuous_wickRotateRealConfig (d := d) (n := n)).continuousOn ?_
    intro x hx
    simpa using
      (wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) (hV_ordered x hx))
  exact SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
    (H := H) (ψ := ψ) (U := V) hV_open hH_cont ⟨hψ_comp, hψ_supp⟩

/-- Any permuted Wick trace is integrable on the same ordered source patch.
The only extra input is the already checked permutation invariance of the
chosen OS boundary-value witness. -/
theorem integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)))
    (ρ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp : tsupport (ψ : NPointDomain d n → ℂ) ⊆ V) :
    Integrable
      (fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u (ρ k))) * ψ u) := by
  have hid :=
    BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector
      (d := d) OS lgc n V hV_open hV_ordered ψ hψ_comp hψ_supp
  refine hid.congr (ae_of_all _ ?_)
  intro u
  have hperm := bvt_F_perm (d := d) OS lgc n ρ (fun k => wickRotatePoint (u k))
  simpa using congrArg (fun c : ℂ => c * ψ u) hperm.symm

/-- On an open real source patch whose selected permutation lands in the
extended tube, the corresponding `extendF` real-source trace is integrable
against every compactly supported Schwartz test supported in the patch. -/
theorem integrable_extendF_realSource_mul_schwartz_of_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (ρ : Equiv.Perm (Fin n))
    (hVρ_ET : ∀ x ∈ V,
      BHW.realEmbed (fun k => x (ρ k)) ∈ BHW.ExtendedTube d n)
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp : tsupport (ψ : NPointDomain d n → ℂ) ⊆ V) :
    Integrable
      (fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => u (ρ k))) * ψ u) := by
  let H : NPointDomain d n → ℂ :=
    fun u => BHW.extendF (bvt_F OS lgc n)
      (BHW.realEmbed (fun k => u (ρ k)))
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv_BHW :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExt_cont :
      ContinuousOn (BHW.extendF (bvt_F OS lgc n)) (BHW.ExtendedTube d n) :=
    (BHW.extendF_holomorphicOn n (bvt_F OS lgc n)
      hF_holo_BHW hF_cinv_BHW).continuousOn
  have hmap_cont :
      Continuous
        (fun x : NPointDomain d n =>
          BHW.realEmbed (fun k => x (ρ k))) :=
    BHW.continuous_realEmbedNPoint.comp (BHW.continuous_permNPoint ρ)
  have hH_cont : ContinuousOn H V := by
    refine hExt_cont.comp hmap_cont.continuousOn ?_
    intro x hx
    exact hVρ_ET x hx
  exact SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
    (H := H) (ψ := ψ) (U := V) hV_open hH_cont ⟨hψ_comp, hψ_supp⟩

/-- On the canonical Figure-2-4 source patch, every permuted Wick trace is
integrable against every compactly supported Schwartz test supported in the
patch. -/
theorem integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp :
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) :
    Integrable
      (fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u (ρ k))) * ψ u) := by
  exact BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
    (d := d) OS lgc n
    (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
    (BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi)
    (BHW.os45Figure24SourcePatch_ordered (d := d) hd n i hi)
    ρ ψ hψ_comp hψ_supp

/-- On the canonical Figure-2-4 source patch, the ordinary real `extendF`
trace is integrable against every compactly supported Schwartz test supported
in the patch. -/
theorem integrable_extendF_realSource_mul_schwartz_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp :
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) :
    Integrable
      (fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u) := by
  simpa using
    BHW.integrable_extendF_realSource_mul_schwartz_of_ET
      (d := d) OS lgc n
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
      (BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi)
      (1 : Equiv.Perm (Fin n))
      (BHW.os45Figure24SourcePatch_realEmbed_mem_extendedTube
        (d := d) hd n i hi)
      ψ hψ_comp hψ_supp

/-- On the canonical Figure-2-4 source patch, the adjacent swapped real
`extendF` trace is integrable against every compactly supported Schwartz test
supported in the patch. -/
theorem integrable_extendF_swapRealSource_mul_schwartz_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (ψ : SchwartzNPoint d n)
    (hψ_comp : HasCompactSupport (ψ : NPointDomain d n → ℂ))
    (hψ_supp :
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) :
    Integrable
      (fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed
            (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
          ψ u) := by
  exact
    BHW.integrable_extendF_realSource_mul_schwartz_of_ET
      (d := d) OS lgc n
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
      (BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi)
      (Equiv.swap i ⟨i.val + 1, hi⟩)
      (BHW.os45Figure24SourcePatch_swapRealEmbed_mem_extendedTube
        (d := d) hd n i hi)
      ψ hψ_comp hψ_supp

/-- Equality of two compact Wick pairings gives zero of the paired Wick
branch difference, once the two paired Wick traces are integrable. -/
theorem integral_wickBranchDifference_mul_eq_zero_of_pairing_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hτ_int :
      Integrable
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) * ψ u))
    (hid_int :
      Integrable
        (fun u : NPointDomain d n =>
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u))
    (hpair :
      (∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) * ψ u)
        =
      ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u) :
    ∫ u : NPointDomain d n,
        (bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * ψ u = 0 := by
  have hfun :
      (fun u : NPointDomain d n =>
          (bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) -
            bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * ψ u)
        =
      fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) * ψ u -
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
    funext u
    ring
  calc
    (∫ u : NPointDomain d n,
        (bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * ψ u)
        =
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (τ k))) * ψ u) -
        (∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u) := by
        rw [hfun]
        exact MeasureTheory.integral_sub hτ_int hid_int
    _ = 0 := sub_eq_zero.mpr hpair

/-- The OS45 Euclidean-edge compact pairing equality gives the Wick-side
branch-difference distributional zero used by the BHW/Jost pair-data carrier,
with integrability kept explicit.

This is the checked bridge from the OS §4.5 Euclidean symmetry layer to the
`hwick_zero` input of `os45_pairData_difference_realTrace_zero_of_wickDistributionZero`. -/
theorem os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (ρ : Equiv.Perm (Fin n))
    (hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hV_swap_ordered : ∀ x ∈ V,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        Integrable
          (fun u : NPointDomain d n =>
            bvt_F OS lgc n
              (fun k => wickRotatePoint
                (u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * ψ u))
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        Integrable
          (fun u : NPointDomain d n =>
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u)) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
      ∫ u : NPointDomain d n,
          (bvt_F OS lgc n
              (fun k => wickRotatePoint
                (u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
            bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
            ψ u = 0 := by
  intro ψ hψ_comp hψ_supp
  have hpair :
      (∫ u : NPointDomain d n,
          bvt_F OS lgc n
            (fun k => wickRotatePoint
              (u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * ψ u)
        =
      ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u :=
    BHW.os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
      (d := d) OS lgc n i hi V hV_jost ρ hV_ordered
      hV_swap_ordered ψ hψ_supp
  exact
    BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq
      (d := d) OS lgc n (Equiv.swap i ⟨i.val + 1, hi⟩) ψ
      (hτ_int ψ hψ_comp hψ_supp)
      (hid_int ψ hψ_comp hψ_supp) hpair

/-- On the canonical Figure-2-4 source patch, the adjacent Wick branch
difference has zero compact-test pairing.  This packages the checked
Euclidean-edge equality with the canonical source-patch geometry and the
checked Wick integrability specializations. -/
theorem os45_wickBranchDifference_zero_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
      ∫ u : NPointDomain d n,
          (bvt_F OS lgc n
              (fun k => wickRotatePoint
                (u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
            bvt_F OS lgc n (fun k => wickRotatePoint (u k))) * ψ u = 0 := by
  exact
    BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector
      (d := d) OS lgc n i hi
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
      (BHW.os45Figure24SourcePatch_jost (d := d) hd n i hi)
      (1 : Equiv.Perm (Fin n))
      (BHW.os45Figure24SourcePatch_ordered (d := d) hd n i hi)
      (by
        intro x hx
        simpa using
          BHW.os45Figure24SourcePatch_swap_ordered
            (d := d) hd n i hi x hx)
      (by
        intro ψ hψ_comp hψ_supp
        exact
          BHW.integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch
            (d := d) hd OS lgc n i hi
            (Equiv.swap i ⟨i.val + 1, hi⟩) ψ hψ_comp hψ_supp)
      (by
        intro ψ hψ_comp hψ_supp
        exact
          BHW.integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch
            (d := d) hd OS lgc n i hi
            (1 : Equiv.Perm (Fin n)) ψ hψ_comp hψ_supp)

/-- Source-patch BHW/Jost hull geometry on one OS45 Figure-2-4 patch.

This is the geometric carrier used before the analytic continuation theorem
supplies the ordinary and adjacent branches on `U`. -/
structure OS45SourcePatchBHWJostHullData
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n)) where
  τ : Equiv.Perm (Fin n)
  τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
  x0 : NPointDomain d n
  x0_mem : x0 ∈ V
  z0 : Fin n → Fin (d + 1) → ℂ
  z0_eq : z0 = fun k => wickRotatePoint (x0 k)
  U : Set (Fin n → Fin (d + 1) → ℂ)
  U_eq : U = BHW.os45SourcePatchBHWJostHull d n τ z0
  V_open : IsOpen V
  V_nonempty : V.Nonempty
  U_open : IsOpen U
  U_connected : IsConnected U
  wick_id_mem :
    ∀ x, x ∈ V → (fun k => wickRotatePoint (x k)) ∈ U
  real_id_mem :
    ∀ x, x ∈ V → BHW.realEmbed x ∈ U
  wick_id_ET :
    ∀ x, x ∈ V →
      (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n
  real_id_ET :
    ∀ x, x ∈ V → BHW.realEmbed x ∈ BHW.ExtendedTube d n
  real_tau_ET :
    ∀ x, x ∈ V →
      BHW.permAct (d := d) τ (BHW.realEmbed x) ∈ BHW.ExtendedTube d n

/-- The canonical Figure-2-4 source patch has the exact source-patch
BHW/Jost hull geometry required by the later branch-continuation theorem. -/
def os45_sourcePatch_bhwJostHullData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let V : Set (NPointDomain d n) :=
    BHW.os45Figure24SourcePatch (d := d) (n := n) i hi
  let hVne : V.Nonempty :=
    BHW.nonempty_os45Figure24SourcePatch (d := d) hd n i hi
  let x0 : NPointDomain d n := Classical.choose hVne
  have hx0 : x0 ∈ V := Classical.choose_spec hVne
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x0 k)
  have hz0_ET : z0 ∈ BHW.ExtendedTube d n := by
    exact
      BHW.os45Figure24SourcePatch_wick_mem_extendedTube
        (d := d) hd n i hi x0 hx0
  have hz0_ambient : z0 ∈ BHW.os45SourcePatchBHWJostAmbient d n τ :=
    Or.inl hz0_ET
  refine
    { τ := τ
      τ_eq := rfl
      x0 := x0
      x0_mem := hx0
      z0 := z0
      z0_eq := rfl
      U := BHW.os45SourcePatchBHWJostHull d n τ z0
      U_eq := rfl
      V_open := BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi
      V_nonempty := hVne
      U_open :=
        BHW.os45SourcePatchBHWJostHull_open
          (d := d) (n := n) τ z0 hz0_ambient
      U_connected :=
        BHW.os45SourcePatchBHWJostHull_connected
          (d := d) (n := n) τ z0 hz0_ambient
      wick_id_mem := ?_
      real_id_mem := ?_
      wick_id_ET := ?_
      real_id_ET := ?_
      real_tau_ET := ?_ }
  · intro x hx
    exact
      BHW.mem_os45SourcePatchBHWJostHull_of_extendedTube
        (d := d) (n := n) τ hz0_ET
        (BHW.os45Figure24SourcePatch_wick_mem_extendedTube
          (d := d) hd n i hi x hx)
  · intro x hx
    exact
      BHW.mem_os45SourcePatchBHWJostHull_of_extendedTube
        (d := d) (n := n) τ hz0_ET
        (BHW.os45Figure24SourcePatch_realEmbed_mem_extendedTube
          (d := d) hd n i hi x hx)
  · exact BHW.os45Figure24SourcePatch_wick_mem_extendedTube
      (d := d) hd n i hi
  · exact BHW.os45Figure24SourcePatch_realEmbed_mem_extendedTube
      (d := d) hd n i hi
  · intro x hx
    simpa [τ] using
      BHW.os45Figure24SourcePatch_permAct_realEmbed_mem_extendedTube
        (d := d) hd n i hi x hx

namespace OS45SourcePatchBHWJostHullData

variable {hd : 2 ≤ d}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {i : Fin n} {hi : i.val + 1 < n}
variable {V : Set (NPointDomain d n)}

/-- The stored complex carrier is definitionally a source-patch hull. -/
theorem U_hull
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    ∃ z0, H.U = BHW.os45SourcePatchBHWJostHull d n H.τ z0 :=
  ⟨H.z0, H.U_eq⟩

/-- The selected Wick seed lies in the stored hull. -/
theorem base_wick_mem_U
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    H.z0 ∈ H.U := by
  rw [H.z0_eq]
  exact H.wick_id_mem H.x0 H.x0_mem

/-- The selected Wick seed lies in the ordinary extended tube. -/
theorem base_wick_mem_extendedTube
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    H.z0 ∈ BHW.ExtendedTube d n := by
  rw [H.z0_eq]
  exact H.wick_id_ET H.x0 H.x0_mem

/-- The stored source-patch hull is path-connected. -/
theorem U_isPathConnected
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    IsPathConnected H.U := by
  rw [H.U_eq]
  exact
    BHW.os45SourcePatchBHWJostHull_isPathConnected
      (d := d) (n := n) H.τ H.z0
      (Or.inl H.base_wick_mem_extendedTube)

/-- The selected real seed lies in the stored hull. -/
theorem base_real_mem_U
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    BHW.realEmbed H.x0 ∈ H.U :=
  H.real_id_mem H.x0 H.x0_mem

/-- The selected real seed lies in the ordinary extended tube. -/
theorem base_real_mem_extendedTube
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    BHW.realEmbed H.x0 ∈ BHW.ExtendedTube d n :=
  H.real_id_ET H.x0 H.x0_mem

/-- The selected real seed lies in the adjacent preimage of the ordinary
extended tube. -/
theorem base_real_mem_adjacentExtendedTubePreimage
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    BHW.permAct (d := d) H.τ (BHW.realEmbed H.x0) ∈
      BHW.ExtendedTube d n :=
  H.real_tau_ET H.x0 H.x0_mem

/-- The ordinary extended tube is contained in the OS45 BHW/Jost ambient. -/
theorem extendedTube_subset_ambient
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    BHW.ExtendedTube d n ⊆
      BHW.os45SourcePatchBHWJostAmbient d n H.τ := by
  intro z hz
  exact Or.inl hz

/-- The adjacent preimage of the ordinary extended tube is contained in the
OS45 BHW/Jost ambient. -/
theorem adjacentExtendedTubePreimage_subset_ambient
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} ⊆
      BHW.os45SourcePatchBHWJostAmbient d n H.τ := by
  intro z hz
  exact Or.inr hz

/-- The ordinary extended tube meets the stored source-patch hull. -/
theorem extendedTube_meets_U
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    (BHW.ExtendedTube d n ∩ H.U).Nonempty :=
  ⟨BHW.realEmbed H.x0, H.base_real_mem_extendedTube, H.base_real_mem_U⟩

/-- The adjacent preimage of the ordinary extended tube meets the stored
source-patch hull. -/
theorem adjacentExtendedTubePreimage_meets_U
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    ({z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} ∩
        H.U).Nonempty :=
  ⟨BHW.realEmbed H.x0, H.base_real_mem_adjacentExtendedTubePreimage,
    H.base_real_mem_U⟩

/-- The full adjacent preimage of the ordinary extended tube lies in the
stored OS45 source-patch hull.  The proof joins the Wick base point to the
real seed inside the ordinary extended tube, then joins that real seed to the
target point inside the adjacent preimage. -/
theorem adjacentExtendedTubePreimage_subset_U
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V) :
    {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} ⊆ H.U := by
  intro z hz
  rw [H.U_eq]
  letI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin (d + 1) → ℂ) := Pi.locallyConvexSpace
  letI : LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    Pi.locallyConvexSpace
  let A : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
  have hET_path : IsPathConnected (BHW.ExtendedTube d n) :=
    (IsOpen.isConnected_iff_isPathConnected
      (U := BHW.ExtendedTube d n) BHW.isOpen_extendedTube).mp
      (BHW.isConnected_extendedTube (d := d) (n := n))
  have hjoin_base_real :
      JoinedIn (BHW.os45SourcePatchBHWJostAmbient d n H.τ)
        H.z0 (BHW.realEmbed H.x0) :=
    (hET_path.joinedIn H.z0 H.base_wick_mem_extendedTube
      (BHW.realEmbed H.x0) H.base_real_mem_extendedTube).mono
      (by
        intro w hw
        exact Or.inl hw)
  have hA_open : IsOpen A :=
    BHW.isOpen_extendedTube.preimage
      (BHW.continuous_permAct (d := d) (n := n) H.τ)
  have hA_preconnected : IsPreconnected A := by
    have hA_eq :
        A =
          (fun w : Fin n → Fin (d + 1) → ℂ =>
            BHW.permAct (d := d) H.τ⁻¹ w) ''
            BHW.ExtendedTube d n := by
      ext y
      constructor
      · intro hy
        refine ⟨BHW.permAct (d := d) H.τ y, hy, ?_⟩
        ext k μ
        simp [BHW.permAct]
      · rintro ⟨w, hw, rfl⟩
        have hcancel :
            BHW.permAct (d := d) H.τ
                (BHW.permAct (d := d) H.τ⁻¹ w) = w := by
          ext k μ
          simp [BHW.permAct]
        simpa [A, hcancel] using hw
    have hpre :
        IsPreconnected
          ((fun w : Fin n → Fin (d + 1) → ℂ =>
            BHW.permAct (d := d) H.τ⁻¹ w) ''
            BHW.ExtendedTube d n) :=
      (BHW.isConnected_extendedTube (d := d) (n := n)).2.image _
        (BHW.continuous_permAct (d := d) (n := n) H.τ⁻¹).continuousOn
    simpa [hA_eq] using hpre
  have hA_connected : IsConnected A :=
    ⟨⟨BHW.realEmbed H.x0, H.base_real_mem_adjacentExtendedTubePreimage⟩,
      hA_preconnected⟩
  have hA_path : IsPathConnected A :=
    (IsOpen.isConnected_iff_isPathConnected (U := A) hA_open).mp
      hA_connected
  have hjoin_real_z :
      JoinedIn (BHW.os45SourcePatchBHWJostAmbient d n H.τ)
        (BHW.realEmbed H.x0) z :=
    (hA_path.joinedIn (BHW.realEmbed H.x0)
      H.base_real_mem_adjacentExtendedTubePreimage z hz).mono
      H.adjacentExtendedTubePreimage_subset_ambient
  exact hjoin_base_real.trans hjoin_real_z

end OS45SourcePatchBHWJostHullData

/-- Pair of ordinary/adjacent BHW-Jost branches on one selected OS45 source
patch hull.

The carrier records exactly the data needed before subtracting the two
branches: both branches are holomorphic on the same connected domain, both
match their Wick traces on the selected Wick real section, and both match the
ordinary `extendF` real traces on the selected source real section. -/
structure OS45SourcePatchBHWJostPairData
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n)) where
  τ : Equiv.Perm (Fin n)
  τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
  U : Set (Fin n → Fin (d + 1) → ℂ)
  V_open : IsOpen V
  V_nonempty : V.Nonempty
  U_open : IsOpen U
  U_connected : IsConnected U
  wick_mem :
    ∀ x, x ∈ V → (fun k => wickRotatePoint (x k)) ∈ U
  real_mem :
    ∀ x, x ∈ V → BHW.realEmbed x ∈ U
  Bord : (Fin n → Fin (d + 1) → ℂ) → ℂ
  Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ
  Bord_holo : DifferentiableOn ℂ Bord U
  Btau_holo : DifferentiableOn ℂ Btau U
  Bord_wick_trace :
    ∀ x, x ∈ V →
      Bord (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  Btau_wick_trace :
    ∀ x, x ∈ V →
      Btau (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))
  Bord_real_trace :
    ∀ x, x ∈ V →
      Bord (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
  Btau_real_trace :
    ∀ x, x ∈ V →
      Btau (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (τ k)))

namespace OS45SourcePatchBHWJostPairData

variable {hd : 2 ≤ d}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {i : Fin n} {hi : i.val + 1 < n}
variable {V : Set (NPointDomain d n)}

/-- Assemble the pair carrier once the ordinary and adjacent BHW/Jost branches
on the checked source-patch hull have been produced. -/
def ofHullDataAndBranches
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (Bord Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (Bord_holo : DifferentiableOn ℂ Bord H.U)
    (Btau_holo : DifferentiableOn ℂ Btau H.U)
    (Bord_wick_trace :
      ∀ x, x ∈ V →
        Bord (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)))
    (Btau_wick_trace :
      ∀ x, x ∈ V →
        Btau (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (H.τ k))))
    (Bord_real_trace :
      ∀ x, x ∈ V →
        Bord (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))
    (Btau_real_trace :
      ∀ x, x ∈ V →
        Btau (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (H.τ k)))) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V where
  τ := H.τ
  τ_eq := H.τ_eq
  U := H.U
  V_open := H.V_open
  V_nonempty := H.V_nonempty
  U_open := H.U_open
  U_connected := H.U_connected
  wick_mem := H.wick_id_mem
  real_mem := H.real_id_mem
  Bord := Bord
  Btau := Btau
  Bord_holo := Bord_holo
  Btau_holo := Btau_holo
  Bord_wick_trace := Bord_wick_trace
  Btau_wick_trace := Btau_wick_trace
  Bord_real_trace := Bord_real_trace
  Btau_real_trace := Btau_real_trace

/-- Restrict a BHW/Jost pair carrier to a smaller real source patch while
keeping the same complex hull and branches. -/
def restrict
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (W : Set (NPointDomain d n))
    (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty)
    (hW_subset : W ⊆ V) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi W where
  τ := P.τ
  τ_eq := P.τ_eq
  U := P.U
  V_open := hW_open
  V_nonempty := hW_nonempty
  U_open := P.U_open
  U_connected := P.U_connected
  wick_mem := fun x hx => P.wick_mem x (hW_subset hx)
  real_mem := fun x hx => P.real_mem x (hW_subset hx)
  Bord := P.Bord
  Btau := P.Btau
  Bord_holo := P.Bord_holo
  Btau_holo := P.Btau_holo
  Bord_wick_trace := fun x hx => P.Bord_wick_trace x (hW_subset hx)
  Btau_wick_trace := fun x hx => P.Btau_wick_trace x (hW_subset hx)
  Bord_real_trace := fun x hx => P.Bord_real_trace x (hW_subset hx)
  Btau_real_trace := fun x hx => P.Btau_real_trace x (hW_subset hx)

/-- Restrict a BHW/Jost pair carrier to the canonical Figure-2-4 source
patch. -/
def restrict_figure24SourcePatch
    (hd : 2 ≤ d)
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi
        (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) :=
  P.restrict
    (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
    (BHW.isOpen_os45Figure24SourcePatch (d := d) n i hi)
    (BHW.nonempty_os45Figure24SourcePatch (d := d) hd n i hi)
    hsource_subset

/-- Difference branch attached to a BHW/Jost pair carrier. -/
def difference
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z => P.Btau z - P.Bord z

/-- The difference branch is holomorphic on the selected hull. -/
theorem difference_holo
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V) :
    DifferentiableOn ℂ P.difference P.U :=
  P.Btau_holo.sub P.Bord_holo

/-- Wick trace formula for the difference branch. -/
theorem difference_wick_trace
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    {x : NPointDomain d n} (hx : x ∈ V) :
    P.difference (fun k => wickRotatePoint (x k)) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  simp [difference, P.Btau_wick_trace x hx, P.Bord_wick_trace x hx]

/-- Real trace formula for the difference branch. -/
theorem difference_real_trace
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    {x : NPointDomain d n} (hx : x ∈ V) :
    P.difference (BHW.realEmbed x) =
      BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (P.τ k))) -
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  simp [difference, P.Btau_real_trace x hx, P.Bord_real_trace x hx]

end OS45SourcePatchBHWJostPairData

/-- Distributional vanishing of a BHW/Jost pair's Wick trace difference on a
real source patch forces pointwise vanishing of the checked difference branch
on the connected BHW/Jost hull.

This is the OS-free Wick-real-section identity theorem specialized to
`OS45SourcePatchBHWJostPairData`. -/
theorem os45_pairData_difference_identity_of_wickDistributionZero
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hwick_zero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            (bvt_F OS lgc n
                (fun k => wickRotatePoint (u (P.τ k))) -
              bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
              ψ u = 0) :
    Set.EqOn P.difference 0 P.U := by
  refine
    eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
      (d := d) (n := n) P.U V P.U_open P.U_connected P.V_open
      P.V_nonempty P.wick_mem P.difference (fun _ => 0)
      P.difference_holo (differentiableOn_const (c := (0 : ℂ))) ?_
  intro ψ hψ_comp hψ_supp
  have htrace :
      (∫ u : NPointDomain d n,
          P.difference (fun k => wickRotatePoint (u k)) * ψ u)
        =
      ∫ u : NPointDomain d n,
          (bvt_F OS lgc n
              (fun k => wickRotatePoint (u (P.τ k))) -
            bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
            ψ u := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ V
    · change
        P.difference (fun k => wickRotatePoint (u k)) * ψ u =
          (bvt_F OS lgc n
              (fun k => wickRotatePoint (u (P.τ k))) -
            bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
            ψ u
      rw [P.difference_wick_trace hu]
    · have hψ_zero : ψ u = 0 := by
        have hnot :
            u ∉ tsupport (ψ : NPointDomain d n → ℂ) :=
          fun hu_supp => hu (hψ_supp hu_supp)
        exact image_eq_zero_of_notMem_tsupport hnot
      simp [hψ_zero]
  calc
    (∫ u : NPointDomain d n,
        P.difference (fun k => wickRotatePoint (u k)) * ψ u)
        =
      ∫ u : NPointDomain d n,
        (bvt_F OS lgc n
            (fun k => wickRotatePoint (u (P.τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
          ψ u := htrace
    _ = 0 := hwick_zero ψ hψ_comp hψ_supp
    _ = ∫ u : NPointDomain d n, (0 : ℂ) * ψ u := by simp

/-- Distributional Wick trace zero for a BHW/Jost pair gives the exact
`P.difference` real-trace zero consumed by the checked compact source-patch
algebra. -/
theorem os45_pairData_difference_realTrace_zero_of_wickDistributionZero
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hwick_zero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            (bvt_F OS lgc n
                (fun k => wickRotatePoint (u (P.τ k))) -
              bvt_F OS lgc n (fun k => wickRotatePoint (u k))) *
              ψ u = 0) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
      ∫ u : NPointDomain d n,
          P.difference (BHW.realEmbed u) * ψ u = 0 := by
  intro ψ _hψ_comp hψ_supp
  have hidentity :
      Set.EqOn P.difference 0 P.U :=
    BHW.os45_pairData_difference_identity_of_wickDistributionZero
      (d := d) (n := n) P hwick_zero
  calc
    (∫ u : NPointDomain d n,
        P.difference (BHW.realEmbed u) * ψ u)
        =
      ∫ u : NPointDomain d n, (0 : ℂ) := by
        apply MeasureTheory.integral_congr_ae
        apply Filter.Eventually.of_forall
        intro u
        by_cases hu : u ∈ V
        · have hzero : P.difference (BHW.realEmbed u) = 0 :=
            hidentity (P.real_mem u hu)
          simp [hzero]
        · have hψ_zero : ψ u = 0 := by
            have hnot :
                u ∉ tsupport (ψ : NPointDomain d n → ℂ) :=
              fun hu_supp => hu (hψ_supp hu_supp)
            exact image_eq_zero_of_notMem_tsupport hnot
          simp [hψ_zero]
    _ = 0 := by simp

/-- If the BHW/Jost pair's abstract difference branch vanishes
distributionally on tests supported in its real source patch, then the explicit
`extendF` real source-branch difference vanishes on those same tests.

The only support argument is that a Schwartz test with `tsupport ⊆ V` is zero
outside `V`, so the pair's real-trace formula may be used under the integral. -/
theorem realSourceBranchDifference_zero_of_pairData_difference_zero
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            P.difference (BHW.realEmbed u) * ψ u = 0) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
      ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (P.τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0 := by
  intro ψ hψ_comp hψ_supp
  have hint :
      (∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (P.τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u)
        =
      ∫ u : NPointDomain d n,
          P.difference (BHW.realEmbed u) * ψ u := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ V
    · change
        (BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (P.τ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u =
          P.difference (BHW.realEmbed u) * ψ u
      rw [P.difference_real_trace hu]
    · have hψ_zero : ψ u = 0 := by
        have hnot :
            u ∉ tsupport (ψ : NPointDomain d n → ℂ) :=
          fun hu_supp => hu (hψ_supp hu_supp)
        exact image_eq_zero_of_notMem_tsupport hnot
      simp [hψ_zero]
  exact hint.trans (hzero ψ hψ_comp hψ_supp)

/-- Zero of the integrated real source-branch difference is exactly equality
of the two compact source-branch pairings.

This is pure measure algebra.  The analytic work is proving the displayed
zero integral from the BHW/Jost difference branch and the Wick-side compact
identity. -/
theorem integral_realSourceBranchDifference_eq_zero_to_pairing_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (hid_int :
      Integrable
        (fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      Integrable
        (fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) * ψ u))
    (hzero :
      ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
      =
    ∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => u (τ k))) * ψ u := by
  have hfun :
      (fun u : NPointDomain d n =>
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u)
        =
      fun u : NPointDomain d n =>
        BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u := by
    funext u
    ring
  have hsub :
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u) -
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u) = 0 := by
    calc
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => u (τ k))) * ψ u) -
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
          =
        ∫ u : NPointDomain d n,
          (BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => u (τ k))) -
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u := by
            rw [hfun]
            exact (MeasureTheory.integral_sub hτ_int hid_int).symm
      _ = 0 := hzero
  exact (sub_eq_zero.mp hsub).symm

/-- Source-patch compact pairing equality follows from vanishing of the real
source-branch difference distribution on the canonical Figure-2-4 source
patch.

The theorem is deliberately explicit about integrability.  The remaining
BHW/Jost analytic work is to construct the branch-difference zero statement
and these integrability facts from the OS I section 4.5 continuation data. -/
theorem os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            (BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    ∀ ψ : SchwartzNPoint d n,
      HasCompactSupport (ψ : NPointDomain d n → ℂ) →
      tsupport (ψ : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
      (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u)
        =
      ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
            ψ u := by
  intro ψ hψ_comp hψ_supp
  exact
    BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq
      (d := d) OS lgc n (Equiv.swap i ⟨i.val + 1, hi⟩) ψ
      (hid_int ψ hψ_comp hψ_supp)
      (hτ_int ψ hψ_comp hψ_supp)
      (hzero ψ hψ_comp hψ_supp)

/-- A real source-branch-difference zero theorem packages directly into the
compact Figure-2-4 Wick-pairing packet.

This is the final algebraic step after the direct OS I section 4.5/BHW-Jost
analysis supplies the zero real-difference distribution on the canonical
source patch. -/
def os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            (BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) * ψ u = 0) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_sourcePatchPairing
    (d := d) hd OS lgc n i hi
    (BHW.os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero
      (d := d) OS lgc n i hi hid_int hτ_int hzero)

/-- A BHW/Jost pair carrier plus distributional vanishing of its abstract
difference branch packages directly into the compact Figure-2-4 Wick-pairing
packet, provided the canonical source patch is contained in the carrier's real
patch.

This is the main algebraic consumer for the next analytic step:
construct the pair from OS I section 4.5 and prove the distributional zero of
`P.difference` on the canonical source patch. -/
def os45CompactFigure24WickPairingEq_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V)
    (hid_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            P.difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero
    (d := d) hd OS lgc n i hi hid_int hτ_int
    (by
      intro ψ hψ_comp hψ_supp
      have hzero_τ :=
        BHW.realSourceBranchDifference_zero_of_pairData_difference_zero
          (d := d) (n := n) P hzero ψ hψ_comp
          (hψ_supp.trans hsource_subset)
      simpa [P.τ_eq] using hzero_τ)

/-- A full adjacent family of BHW/Jost pair carriers with distributionally
zero difference branches packages into the compact Figure-2-4 Wick-pairing
family. -/
def os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc :=
  fun i hi =>
    BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero
      (d := d) hd OS lgc n i hi (P i hi) (hsource_subset i hi)
      (hid_int i hi) (hτ_int i hi) (hzero i hi)

/-- A full adjacent family of zero-difference BHW/Jost pair carriers supplies
the direct source distributional adjacent-tube anchor. -/
def sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
      (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero)

/-- A full adjacent family of zero-difference BHW/Jost pair carriers supplies
the older selected-adjacent Jost anchor packet. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero
      (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero)

/-- OS-selected naming wrapper for the direct source anchor produced from a
full adjacent family of zero-difference BHW/Jost pair carriers. -/
def bvt_F_distributionalJostAnchor_of_pairData_difference_zero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hid_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u))
    (hτ_int :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        Integrable
          (fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
              ψ u))
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero
    (d := d) hd OS lgc n V P hsource_subset hid_int hτ_int hzero

/-- Canonical-integrability variant of
`os45CompactFigure24WickPairingEq_of_pairData_difference_zero`.

After the Figure-2-4 source-patch membership lemmas, the ordinary and adjacent
real `extendF` integrability hypotheses are supplied automatically. -/
def os45CompactFigure24WickPairingEq_of_pairData_difference_zero_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V)
    (hzero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V →
        ∫ u : NPointDomain d n,
            P.difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero
    (d := d) hd OS lgc n i hi P hsource_subset
    (BHW.integrable_extendF_realSource_mul_schwartz_on_figure24SourcePatch
      (d := d) hd OS lgc n i hi)
    (BHW.integrable_extendF_swapRealSource_mul_schwartz_on_figure24SourcePatch
      (d := d) hd OS lgc n i hi)
    hzero

/-- Canonical-integrability variant of the full adjacent family compact
packet producer from BHW/Jost pair carriers. -/
def os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc :=
  fun i hi =>
    BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero_canonical
      (d := d) hd OS lgc n i hi (P i hi) (hsource_subset i hi)
      (hzero i hi)

/-- Canonical-integrability variant of the direct source anchor producer from
a full adjacent family of zero-difference BHW/Jost pair carriers. -/
def sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero_canonical
      (d := d) hd OS lgc n V P hsource_subset hzero)

/-- Canonical-integrability variant of the older selected-adjacent Jost anchor
packet producer from BHW/Jost pair carriers. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_difference_zero_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero_canonical
      (d := d) hd OS lgc n V P hsource_subset hzero)

/-- OS-selected naming wrapper for the canonical-integrability direct source
anchor produced from BHW/Jost pair carriers. -/
def bvt_F_distributionalJostAnchor_of_pairData_difference_zero_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi)
    (hzero :
      ∀ (i : Fin n) (hi : i.val + 1 < n) (ψ : SchwartzNPoint d n),
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ V i hi →
        ∫ u : NPointDomain d n,
            (P i hi).difference (BHW.realEmbed u) * ψ u = 0) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero_canonical
    (d := d) hd OS lgc n V P hsource_subset hzero

/-- A BHW/Jost pair carrier whose real source patch contains the canonical
Figure-2-4 source patch already gives the compact Figure-2-4 Wick-pairing
packet.

The checked Euclidean-edge theorem supplies the Wick distributional zero on
the canonical source patch; `P` transfers it through the pair-data
Wick/real-trace fields. -/
def os45CompactFigure24WickPairingEq_of_pairData_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc := by
  let P0 :=
    BHW.OS45SourcePatchBHWJostPairData.restrict_figure24SourcePatch
      (d := d) (n := n) hd P hsource_subset
  have hwick_zero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            ((bvt_F OS lgc n fun k => wickRotatePoint (u (P0.τ k))) -
              bvt_F OS lgc n fun k => wickRotatePoint (u k)) * ψ u = 0 := by
    intro ψ hψ_comp hψ_supp
    have hcanon :=
      BHW.os45_wickBranchDifference_zero_on_figure24SourcePatch
        (d := d) hd OS lgc n i hi ψ hψ_comp hψ_supp
    simpa [P0.τ_eq] using hcanon
  have hreal_zero :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆
          BHW.os45Figure24SourcePatch (d := d) (n := n) i hi →
        ∫ u : NPointDomain d n,
            P0.difference (BHW.realEmbed u) * ψ u = 0 :=
    BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero
      (d := d) (n := n) P0 hwick_zero
  exact
    BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero_canonical
      (d := d) hd OS lgc n i hi P0 (by intro x hx; exact hx) hreal_zero

/-- A full adjacent family of BHW/Jost pair carriers gives the compact
Figure-2-4 Wick-pairing family once each carrier contains its canonical source
patch. -/
def os45CompactFigure24WickPairingEq_family_of_pairData_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc :=
  fun i hi =>
    BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical
      (d := d) hd OS lgc n i hi (P i hi) (hsource_subset i hi)

/-- Direct source anchor from a full adjacent family of BHW/Jost pair carriers.
No additional distributional-zero or integrability inputs remain. -/
def sourceDistributionalAdjacentTubeAnchor_of_pairData_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_canonical
      (d := d) hd OS lgc n V P hsource_subset)

/-- Older selected-adjacent Jost anchor packet from a full adjacent family of
BHW/Jost pair carriers. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_canonical
      (d := d) hd OS lgc n V P hsource_subset)

/-- OS-selected naming wrapper for the direct source anchor produced from a
full adjacent family of BHW/Jost pair carriers. -/
def bvt_F_distributionalJostAnchor_of_pairData_canonical
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (V : ∀ (i : Fin n), i.val + 1 < n → Set (NPointDomain d n))
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi (V i hi))
    (hsource_subset :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ V i hi) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_canonical
    (d := d) hd OS lgc n V P hsource_subset

/-- If the BHW/Jost pair carrier is already built on the canonical
Figure-2-4 source patch, no separate source-containment input remains. -/
def os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi
        (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical
    (d := d) hd OS lgc n i hi P (by intro x hx; exact hx)

/-- Full adjacent family version of
`os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch`. -/
def os45CompactFigure24WickPairingEq_family_of_pairData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi
          (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc :=
  fun i hi =>
    BHW.os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch
      (d := d) hd OS lgc n i hi (P i hi)

/-- Direct source anchor from pair carriers constructed directly on the
canonical Figure-2-4 source patches. -/
def sourceDistributionalAdjacentTubeAnchor_of_pairData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi
          (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_on_figure24SourcePatch
      (d := d) hd OS lgc n P)

/-- Older selected-adjacent Jost anchor packet from pair carriers constructed
directly on the canonical Figure-2-4 source patches. -/
def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi
          (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n :=
  BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
    (d := d) OS lgc n
    (BHW.os45CompactFigure24WickPairingEq_family_of_pairData_on_figure24SourcePatch
      (d := d) hd OS lgc n P)

/-- OS-selected naming wrapper for the direct source anchor produced from
pair carriers on the canonical Figure-2-4 source patches. -/
def bvt_F_distributionalJostAnchor_of_pairData_on_figure24SourcePatch
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (P :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        BHW.OS45SourcePatchBHWJostPairData
          (d := d) hd OS lgc n i hi
          (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
  BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_on_figure24SourcePatch
    (d := d) hd OS lgc n P

end BHW
