import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BranchPullback

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- The two adjacent ordered Wick traces used in the OS45 common chart both lie
in the OS-II ACR-one domain. -/
theorem adjacent_wick_traces_mem_acrOne
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hx_swap_ordered :
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
        AnalyticContinuationRegion d n 1 ∧
    BHW.permAct (d := d) ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => wickRotatePoint (x k))) ∈
        AnalyticContinuationRegion d n 1 := by
  constructor
  · exact BHW.wickRotate_ordered_mem_acrOne (d := d) (n := n) ρ hx_ordered
  · simpa [BHW.permAct_wickRotatePoint] using
      BHW.wickRotate_ordered_mem_acrOne
        (d := d) (n := n)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        hx_swap_ordered

/-- The common OS45 real chart point lies in both pulled real-branch domains
for the original branch and the adjacent relabelled branch. -/
theorem os45CommonChart_real_mem_pulledRealBranchDomain_pair
    (τ ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hxτ_ET : BHW.realEmbed (fun k => x (τ k)) ∈ BHW.ExtendedTube d n) :
    BHW.os45CommonChartCLE (d := d) (n := n) ρ (BHW.realEmbed x) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
        BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
  constructor
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) ρ x hx_ET
    simpa using hmem
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) (τ.symm * ρ) (fun k => x (τ k)) hxτ_ET
    have hmem' :
        BHW.os45QuarterTurnConfig (d := d) (n := n)
            (fun k => BHW.realEmbed (fun j => x (τ j)) ((τ.symm * ρ) k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      simpa [Equiv.Perm.mul_apply] using hmem
    have hcommon :
        BHW.os45QuarterTurnConfig
            (d := d) (n := n) (fun k => BHW.realEmbed x (ρ k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      have hchart :=
        BHW.os45QuarterTurnConfig_reindexed_realBranch_eq
          (d := d) (n := n) τ ρ x
      exact hchart ▸ hmem'
    simpa [BHW.os45CommonChartCLE_apply] using hcommon

/-- Convert a common-chart OS45 branch-difference envelope into the direct
coordinate `AdjacentOSEOWDifferenceEnvelope` consumed by the real-edge
distributional equality theorem.

The hard EOW/common-boundary construction is deliberately an input here.  This
lemma only performs the checked coordinate pullback through the common chart and
packages the resulting direct Wick and real traces. -/
def adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (ρ : Equiv.Perm (Fin n))
    (Uc : Set (Fin n → Fin (d + 1) → ℂ))
    (Hc : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hUc_open : IsOpen Uc)
    (hUc_conn : IsConnected Uc)
    (hHc_holo : DifferentiableOn ℂ Hc Uc)
    (hwick_mem :
      ∀ x ∈ V,
        os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k)) ∈ Uc)
    (hreal_mem :
      ∀ x ∈ V,
        os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed x) ∈ Uc)
    (hwick_trace :
      ∀ x ∈ V,
        Hc (os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k))) =
          bvt_F OS lgc n
            (fun k => wickRotatePoint
              (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)))
    (hreal_trace :
      ∀ x ∈ V,
        Hc (os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed x)) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) :
    AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V := by
  let Qρe := os45CommonChartCLE (d := d) (n := n) ρ
  let U : Set (Fin n → Fin (d + 1) → ℂ) := Qρe ⁻¹' Uc
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => Hc (Qρe z)
  have hU_open : IsOpen U := by
    exact hUc_open.preimage Qρe.continuous
  have hU_eq : U = Qρe.symm '' Uc := by
    ext z
    constructor
    · intro hz
      refine ⟨Qρe z, hz, ?_⟩
      exact Qρe.symm_apply_apply z
    · rintro ⟨w, hw, rfl⟩
      have hq : Qρe (Qρe.symm w) = w := Qρe.apply_symm_apply w
      simpa [U, hq] using hw
  have hU_conn : IsConnected U := by
    rw [hU_eq]
    exact hUc_conn.image Qρe.symm Qρe.symm.continuous.continuousOn
  have hH_holo : DifferentiableOn ℂ H U := by
    intro z hz
    exact (hHc_holo (Qρe z) hz).comp z
      Qρe.differentiableAt.differentiableWithinAt
      (by
        intro y hy
        exact hy)
  refine
    { U := U
      U_open := hU_open
      U_connected := hU_conn
      H := H
      H_holo := hH_holo
      wick_mem := ?wick_mem
      real_mem := ?real_mem
      wick_diff := ?wick_diff
      real_diff := ?real_diff }
  · intro x hx
    exact hwick_mem x hx
  · intro x hx
    exact hreal_mem x hx
  · intro x hx
    simpa [H, Qρe] using hwick_trace x hx
  · intro x hx
    simpa [H, Qρe] using hreal_trace x hx

end BHW
