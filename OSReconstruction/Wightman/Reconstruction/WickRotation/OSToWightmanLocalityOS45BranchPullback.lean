import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Bridge

noncomputable section

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- The branch-specific common-chart pullback used on the real side of the OS45
slot-1 common-boundary step.  We first invert the fixed quarter-turn chart and
then undo the branch label by `σ.symm`, so evaluation on the common real edge
recovers the original unswapped/swapped real branch value rather than a
relabelled surrogate. -/
def os45PulledRealBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    BHW.extendF (bvt_F OS lgc n)
      (BHW.permAct (d := d) σ.symm
        ((os45QuarterTurnCLE (d := d) (n := n)).symm z))

/-- Domain of the branch-specific real pullback: points of the common chart whose
inverse image, after undoing the branch label, lies in the extended tube. -/
def os45PulledRealBranchDomain
    (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z |
    BHW.permAct (d := d) σ.symm
      ((os45QuarterTurnCLE (d := d) (n := n)).symm z) ∈
        BHW.ExtendedTube d n}

/-- The pullback domain is open. -/
theorem isOpen_os45PulledRealBranchDomain
    (σ : Equiv.Perm (Fin n)) :
    IsOpen (os45PulledRealBranchDomain (d := d) (n := n) σ) := by
  have hperm_cont :
      Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.permAct (d := d) σ.symm z) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (σ.symm k))
  change IsOpen
    ((fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.permAct (d := d) σ.symm
          ((os45QuarterTurnCLE (d := d) (n := n)).symm z)) ⁻¹'
      BHW.ExtendedTube d n)
  exact BHW.isOpen_extendedTube.preimage
    (hperm_cont.comp (os45QuarterTurnCLE (d := d) (n := n)).symm.continuous)

/-- The branch-specific real pullback is holomorphic on its natural chart
domain. -/
theorem os45PulledRealBranch_holomorphicOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (os45PulledRealBranch (d := d) (n := n) OS lgc σ)
      (os45PulledRealBranchDomain (d := d) (n := n) σ) := by
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) = bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExtend_holo :
      DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n))
        (BHW.ExtendedTube d n) :=
    BHW.extendF_holomorphicOn n (bvt_F OS lgc n) hF_holo hF_cinv
  have hperm_diff :
      Differentiable ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.permAct (d := d) σ.symm z) := by
    rw [differentiable_pi]
    intro k
    simpa [BHW.permAct] using
      (differentiable_apply (σ.symm k) :
        Differentiable ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => z (σ.symm k)))
  have hpull_diff :
      Differentiable ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.permAct (d := d) σ.symm
            ((os45QuarterTurnCLE (d := d) (n := n)).symm z)) :=
    hperm_diff.comp (os45QuarterTurnCLE (d := d) (n := n)).symm.differentiable
  have hpull_maps :
      Set.MapsTo
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.permAct (d := d) σ.symm
            ((os45QuarterTurnCLE (d := d) (n := n)).symm z))
        (os45PulledRealBranchDomain (d := d) (n := n) σ)
        (BHW.ExtendedTube d n) := by
    intro z hz
    exact hz
  intro z hz
  exact (hExtend_holo _ (hpull_maps hz)).comp z
    ((hpull_diff z).differentiableWithinAt) hpull_maps

/-- The common-chart point coming from the `σ`-labelled real branch lies in the
natural pullback domain precisely when the original real branch lies in the
extended tube. -/
theorem os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n) :
    os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) ∈
      os45PulledRealBranchDomain (d := d) (n := n) σ := by
  let Q := os45QuarterTurnCLE (d := d) (n := n)
  have hQ :
      os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) =
        Q (fun k => BHW.realEmbed x (σ k)) := by
    simpa [Q] using
      (os45QuarterTurnCLE_apply (d := d) (n := n)
        (fun k => BHW.realEmbed x (σ k))).symm
  rw [os45PulledRealBranchDomain]
  rw [hQ]
  change
    BHW.permAct (d := d) σ.symm
      (Q.symm (Q (fun k => BHW.realEmbed x (σ k)))) ∈
      BHW.ExtendedTube d n
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have hperm :
      BHW.permAct (d := d) σ.symm
        (fun k => BHW.realEmbed x (σ k)) =
      BHW.realEmbed x := by
    ext k μ
    simp [BHW.permAct]
  simpa [hperm] using hx_ET

/-- Evaluating the branch-specific real pullback on the explicit OS45 real
branch chart recovers the original real branch value. -/
theorem os45PulledRealBranch_apply_realBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45PulledRealBranch (d := d) (n := n) OS lgc σ
        (os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  let Q := os45QuarterTurnCLE (d := d) (n := n)
  have hQ :
      os45QuarterTurnConfig (fun k => BHW.realEmbed x (σ k)) =
        Q (fun k => BHW.realEmbed x (σ k)) := by
    simpa [Q] using
      (os45QuarterTurnCLE_apply (d := d) (n := n)
        (fun k => BHW.realEmbed x (σ k))).symm
  rw [os45PulledRealBranch]
  rw [hQ, ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  ext k μ
  simp [BHW.permAct]

/-- If we relabel the real branch by `τ` and simultaneously adjust the chart
permutation to `τ.symm * ρ`, the explicit OS45 quarter-turn chart point is
unchanged. This is the branch-level common-chart identity needed to compare the
two adjacent real branches at one common edge point. -/
theorem os45QuarterTurnConfig_reindexed_realBranch_eq
    (τ ρ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45QuarterTurnConfig
        (fun k => BHW.realEmbed (fun j => x (τ j)) ((τ.symm * ρ) k)) =
      os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k)) := by
  congr 1
  ext k μ
  simp [BHW.realEmbed]

/-- Evaluating the pullback for the relabelled branch `τ.symm * ρ` at the
common-chart point determined by `ρ` recovers the original relabelled real
branch value. -/
theorem os45PulledRealBranch_apply_reindexed_commonPoint
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ ρ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45PulledRealBranch (d := d) (n := n) OS lgc (τ.symm * ρ)
        (os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))) := by
  rw [← os45QuarterTurnConfig_reindexed_realBranch_eq
      (d := d) (n := n) τ ρ x]
  simpa using
    os45PulledRealBranch_apply_realBranch
      (d := d) (n := n) OS lgc (τ.symm * ρ) (fun k => x (τ k))

/-- On the common OS45 real-chart point determined by `ρ`, the difference
between the relabelled branch `τ.symm * ρ` and the original branch `ρ`
recovers the honest adjacent real-edge branch difference. -/
theorem os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ ρ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    os45PulledRealBranch (d := d) (n := n) OS lgc (τ.symm * ρ)
        (os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k))) -
      os45PulledRealBranch (d := d) (n := n) OS lgc ρ
        (os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k)))
      =
    BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))) -
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  rw [os45PulledRealBranch_apply_reindexed_commonPoint
      (d := d) (n := n) OS lgc τ ρ x]
  rw [os45PulledRealBranch_apply_realBranch (d := d) (n := n) OS lgc ρ x]

end BHW
