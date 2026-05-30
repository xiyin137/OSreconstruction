/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal

/-!
# OS45 Figure 2-4 Seed Charts

This file contains small geometric support for the direct OS45 Figure 2-4
route.  It keeps the genuine OS I `(4.12)` seed as the initial analytic
element and shrinks it to the two-sheet initial overlap before later
one-branch continuation.
-/

noncomputable section

open scoped ContDiff
open Set MeasureTheory Filter

namespace BHW

/-- The genuine OS I `(4.12)` seed chart can be chosen as a metric ball inside
both its raw preimage-forward-tube seed window and the Figure-2-4 two-sheet
initial overlap.

This is only the incoming-domain preparation for the adjacent one-branch
gallery.  It does not replace the raw seed by the downstream deterministic
endpoint branch `extendF ∘ permAct`, and it proves no boundary-value equality
between the ordinary and adjacent endpoint branches. -/
theorem OS45BHWJostHullData.OS412SeedWindow_initialSectorOverlap_metricBallChart
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          (BHW.permAct (d := d) P.τ
            (fun k => wickRotatePoint (x k))) r ∧
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        (({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
          (BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ)) ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch (BHW.permAct (d := d) P.τ
          (fun k => wickRotatePoint (x k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let W : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ
  have hW_open : IsOpen W :=
    BHW.isOpen_extendedTube.inter
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ)
  have hseedW :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ W := by
    simpa [W] using H.OS412Seed_mem_initialSectorOverlap x hx
  rcases
      H.OS412SeedWindow_metricBallChartInWindow OS lgc hx
        hW_open hseedW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, hcenter, hC0_open,
      hC0_pre, hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  exact
    ⟨C0, C0branch, r, hr_pos, hC0_ball, hcenter, hC0_open,
      hC0_pre, by simpa [W] using hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩

/-- The same raw OS I `(4.12)` seed chart, stated at the actual adjacent Wick
point.

The upstream adjacent analytic element is seeded at
`fun k => wickRotatePoint (x (P.τ k))`.  This theorem keeps that point explicit
and records both OS-normalized values at the seed.  It is still only the seed
chart, not the later seed-to-ordinary-Wick transport. -/
theorem OS45BHWJostHullData.OS412AdjacentWick_initialSectorOverlap_metricBallChart
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ (C0 : Set (Fin n → Fin (d + 1) → ℂ))
      (C0branch : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (r : ℝ),
      0 < r ∧
      C0 =
        Metric.ball
          (fun k => wickRotatePoint (x (P.τ k))) r ∧
      (fun k => wickRotatePoint (x (P.τ k))) ∈ C0 ∧
      IsOpen C0 ∧
      IsPreconnected C0 ∧
      C0 ⊆
        (({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
          (BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ)) ∧
      DifferentiableOn ℂ C0branch C0 ∧
      Set.EqOn C0branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) C0 ∧
      C0branch (fun k => wickRotatePoint (x (P.τ k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) ∧
      C0branch (fun k => wickRotatePoint (x (P.τ k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  rcases H.OS412SeedWindow_initialSectorOverlap_metricBallChart
      OS lgc hx with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, hcenter, hC0_open,
      hC0_pre, hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  have hseed_eq :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) =
        fun k => wickRotatePoint (x (P.τ k)) :=
    BHW.os45Figure24_permAct_ordinaryWick_eq_adjacentWick
      (d := d) (n := n) (hd := hd) (P := P) x
  have htrace_adj :
      C0branch (fun k => wickRotatePoint (x (P.τ k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
    rw [← hseed_eq]
    exact hC0_trace
  have hperm :
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
    simpa [BHW.permAct] using
      bvt_F_perm (d := d) OS lgc n P.τ
        (fun k => wickRotatePoint (x k))
  exact
    ⟨C0, C0branch, r, hr_pos, by
      rw [← hseed_eq]
      exact hC0_ball, by
      rw [← hseed_eq]
      exact hcenter, hC0_open, hC0_pre, hC0_sub, hC0_holo, hC0_eq,
      htrace_adj.trans hperm, htrace_adj⟩

/-- The genuine raw `(4.12)` seed point and the ordinary Wick point are
contained in one connected open carrier inside the checked local hull. -/
theorem OS45BHWJostHullData.OS412Seed_ordinaryWick_connectedNeighborhood
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen U ∧ IsConnected U ∧
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ U ∧
      (fun k => wickRotatePoint (x k)) ∈ U ∧
      U ⊆ H.ΩJ := by
  exact
    ⟨H.ΩJ, H.ΩJ_open, H.ΩJ_connected,
      (H.permAct_ordinaryWick_mem_OS412SeedWindow x hx).2,
      H.ordinaryWick_mem x hx, subset_rfl⟩

/-- Endpoint shrink for the raw `(4.12)` seed-to-ordinary-Wick carrier:
given any open neighborhood of the ordinary Wick endpoint, shrink to a metric
ball contained in that neighborhood and in the connected carrier. -/
theorem OS45BHWJostHullData.OS412Seed_ordinaryWick_endpointMetricBall
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hzordW : (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ)) (r : ℝ),
      IsOpen U ∧ IsConnected U ∧
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈ U ∧
      (fun k => wickRotatePoint (x k)) ∈ U ∧
      U ⊆ H.ΩJ ∧
      0 < r ∧
      Metric.ball (fun k => wickRotatePoint (x k)) r ⊆ U ∩ W := by
  rcases H.OS412Seed_ordinaryWick_connectedNeighborhood hx with
    ⟨U, hU_open, hU_connected, hseedU, hzordU, hU_sub⟩
  rcases SCV.exists_metric_ball_subset_inter_of_mem_open
      hU_open hzordU hW_open hzordW with ⟨r, hr_pos, hr_sub⟩
  exact ⟨U, r, hU_open, hU_connected, hseedU, hzordU, hU_sub, hr_pos, hr_sub⟩

/-- Any checked path inside the two-sheet Figure-2-4 initial overlap is
contained in a connected open carrier still inside that two-sheet overlap. -/
theorem initialSectorOverlap_connectedNeighborhood_of_joinedIn
    [NeZero d] (τ : Equiv.Perm (Fin n))
    {a b : Fin n → Fin (d + 1) → ℂ}
    (hjoin : JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n τ) a b) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen U ∧ IsConnected U ∧ a ∈ U ∧ b ∈ U ∧
      U ⊆ BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n τ := by
  have hΩ_open :
      IsOpen (BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n τ) :=
    BHW.isOpen_extendedTube.inter
      (BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) τ)
  haveI :
      LocallyConvexSpace ℝ (Fin n → Fin (d + 1) → ℂ) :=
    NormedSpace.toLocallyConvexSpace
  haveI :
      LocPathConnectedSpace (Fin n → Fin (d + 1) → ℂ) :=
    LocallyConvexSpace.toLocPathConnectedSpace
      (Fin n → Fin (d + 1) → ℂ)
  exact
    SCV.exists_open_connected_neighborhood_of_joinedIn_subset_open
      hΩ_open hjoin

/-- Endpoint metric-ball shrink for a checked path inside the two-sheet
Figure-2-4 initial overlap. -/
theorem initialSectorOverlap_endpointMetricBall_of_joinedIn
    [NeZero d] (τ : Equiv.Perm (Fin n))
    {a b : Fin n → Fin (d + 1) → ℂ}
    (hjoin : JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n τ) a b)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W) (hbW : b ∈ W) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ)) (r : ℝ),
      IsOpen U ∧ IsConnected U ∧ a ∈ U ∧ b ∈ U ∧
      U ⊆ BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n τ ∧
      0 < r ∧ Metric.ball b r ⊆ U ∩ W := by
  rcases BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn τ hjoin with
    ⟨U, hU_open, hU_connected, haU, hbU, hU_sub⟩
  rcases SCV.exists_metric_ball_subset_inter_of_mem_open
      hU_open hbU hW_open hbW with ⟨r, hr_pos, hr_sub⟩
  exact ⟨U, r, hU_open, hU_connected, haU, hbU, hU_sub, hr_pos, hr_sub⟩

/-- The genuine adjacent `(4.12)` Wick seed is connected, inside the two-sheet
Figure-2-4 initial overlap, to the permuted horizontal common-edge endpoint.

This composes the three checked corridor fragments: adjacent Wick to the
rotated adjacent lift, along the lift, and then through the Lorentz connector
to the permuted ordinary identity-path endpoint.  It is still carrier geometry;
it does not assert any equality of branch values. -/
theorem os45Figure24_joined_adjacentWick_to_permActCommonEdge_initialSectorOverlap
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    JoinedIn
      (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
      (fun k => wickRotatePoint (x (P.τ k)))
      (BHW.permAct (d := d) P.τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))) := by
  classical
  have h01 :
      JoinedIn
        (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
        (fun k => wickRotatePoint (x (P.τ k)))
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval)) :=
    BHW.os45Figure24_joined_adjacentWick_to_adjLift0_initialSectorOverlap
      (d := d) (n := n) hd P x hx
  have h12 :
      JoinedIn
        (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (0 : unitInterval))
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (1 : unitInterval)) :=
    BHW.os45Figure24_joined_adjLift0_to_adjLift1_initialSectorOverlap
      (d := d) (n := n) hd P x hx
  have h23 :
      JoinedIn
        (BHW.ExtendedTube d n ∩ BHW.permutedExtendedTubeSector d n P.τ)
        (BHW.os45Figure24AdjacentLift
          (d := d) (n := n) hd P.τ x (1 : unitInterval))
        (BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)))) := by
    simpa [BHW.os45Figure24IdentityPath_one (d := d) (n := n) x] using
      BHW.os45Figure24_joined_adjLift_to_permActIdentityPath_initialSectorOverlap
        (d := d) (n := n) hd P hx (1 : unitInterval)
  exact h01.trans (h12.trans h23)

/-- Endpoint collar for the composed `(4.12)` seed-to-common-edge corridor.

Given any open neighborhood of the permuted horizontal common-edge endpoint,
shrink to a metric ball inside that neighborhood and inside a connected carrier
which still contains the genuine adjacent Wick seed.  This is the local carrier
needed before transporting the adjacent branch value to the horizontal edge. -/
theorem os45Figure24_adjacentWick_to_permActCommonEdge_endpointMetricBall
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      BHW.permAct (d := d) P.τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x))) ∈ W) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ)) (r : ℝ),
      IsOpen U ∧ IsConnected U ∧
      (fun k => wickRotatePoint (x (P.τ k))) ∈ U ∧
      BHW.permAct (d := d) P.τ
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x))) ∈ U ∧
      U ⊆ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ ∧
      0 < r ∧
      Metric.ball
        (BHW.permAct (d := d) P.τ
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)))) r ⊆ U ∩ W := by
  exact
    BHW.initialSectorOverlap_endpointMetricBall_of_joinedIn P.τ
      (BHW.os45Figure24_joined_adjacentWick_to_permActCommonEdge_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P) hx)
      hW_open hcommonW

end BHW
