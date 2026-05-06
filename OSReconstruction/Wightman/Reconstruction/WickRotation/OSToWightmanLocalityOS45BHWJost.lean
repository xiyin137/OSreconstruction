import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Compact
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# OS45 BHW/Jost source-patch carriers

This file starts the direct OS I section 4.5 BHW/Jost carrier layer for the
theorem-2 locality route.  It contains only data surfaces and algebraic
bookkeeping after the analytic continuation data has been supplied.
-/

noncomputable section

open Complex Topology MeasureTheory

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
