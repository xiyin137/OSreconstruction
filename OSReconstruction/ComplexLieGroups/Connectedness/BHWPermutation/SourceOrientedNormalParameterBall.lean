import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter

/-!
# Small connected balls in normal-parameter coordinates

This file packages the metric-ball shrink used by the rank-deficient
Schur/residual local-image producer.  The underlying normal-parameter topology
is induced from finite product coordinates; the single finite-function
coordinate homeomorphism supplies honest metric balls.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Normal-parameter balls are the pullback of finite-coordinate metric balls. -/
def sourceOrientedNormalParameterBall
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (ε : ℝ) :
    Set (SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :=
  (sourceOrientedNormalParameterFiniteCoordHomeomorph
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)) ⁻¹'
      sourceOrientedNormalParameterFiniteCoordBall d n r ε

/-- Normal-parameter balls are monotone in the radius. -/
theorem sourceOrientedNormalParameterBall_mono
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) :
    sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
      (hrD := hrD) (hrn := hrn) ε₁ ⊆
    sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
      (hrD := hrD) (hrn := hrn) ε₂ := by
  intro p hp
  simpa [sourceOrientedNormalParameterBall,
    sourceOrientedNormalParameterFiniteCoordBall] using
    Metric.ball_subset_ball hε hp

/-- The finite-coordinate pullback ball is open, connected, and contains the
normal center. -/
theorem sourceOrientedNormalParameterBall_open_connected_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {ε : ℝ}
    (hε : 0 < ε) :
    IsOpen (sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
      (hrD := hrD) (hrn := hrn) ε) ∧
      IsConnected (sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
        (hrD := hrD) (hrn := hrn) ε) ∧
      sourceOrientedNormalCenterParameter d n r hrD hrn ∈
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε := by
  let e := sourceOrientedNormalParameterFiniteCoordHomeomorph
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  rcases sourceOrientedNormalParameterFiniteCoordBall_open_connected_center
      d n r hε with ⟨hopen, hconn, hcenter⟩
  constructor
  · exact hopen.preimage e.continuous
  constructor
  · have himage :
        e.symm '' sourceOrientedNormalParameterFiniteCoordBall d n r ε =
          sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
            (hrD := hrD) (hrn := hrn) ε := by
      ext p
      constructor
      · rintro ⟨c, hc, rfl⟩
        simpa [sourceOrientedNormalParameterBall, e] using hc
      · intro hp
        exact
          ⟨e p, by simpa [sourceOrientedNormalParameterBall, e] using hp,
            by simp [e]⟩
    rw [← himage]
    exact hconn.image e.symm e.symm.continuous.continuousOn
  · simpa [sourceOrientedNormalParameterBall, e,
      sourceOrientedNormalParameterFiniteCoord_center]
      using hcenter

/-- Every neighborhood of the normal center contains a positive-radius
normal-parameter coordinate ball. -/
theorem exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {U : Set (SourceOrientedRankDeficientNormalParameter d n r hrD hrn)}
    (hU : U ∈ 𝓝 (sourceOrientedNormalCenterParameter d n r hrD hrn)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆ U := by
  let e := sourceOrientedNormalParameterFiniteCoordHomeomorph
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  let p0 := sourceOrientedNormalCenterParameter d n r hrD hrn
  have himage_nhds : e '' U ∈ 𝓝 (e p0) := by
    have hpre : e ⁻¹' (e '' U) ∈ 𝓝 p0 := by
      have hpre_eq : e ⁻¹' (e '' U) = U := by
        ext p
        constructor
        · rintro ⟨u, hu, heu⟩
          have hpu : p = u := e.injective heu.symm
          simpa [hpu] using hu
        · intro hp
          exact ⟨p, hp, rfl⟩
      simpa [p0, hpre_eq] using hU
    have hmap : e '' U ∈ Filter.map e (𝓝 p0) := by
      exact Filter.mem_map.mpr hpre
    rw [← e.isLocalHomeomorph.map_nhds_eq p0]
    exact hmap
  rcases Metric.mem_nhds_iff.mp himage_nhds with ⟨ε, hε, hε_sub⟩
  refine ⟨ε, hε, ?_⟩
  intro p hp
  have hep : e p ∈ e '' U := hε_sub hp
  rcases hep with ⟨u, hu, heu⟩
  have hpu : p = u := e.injective heu.symm
  simpa [hpu] using hu

/-- A positive-radius normal-parameter ball can be chosen inside the
invertible-head locus. -/
theorem exists_sourceOrientedNormalParameterBall_subset_head_det_isUnit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            IsUnit p.head.det} :=
  exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
    d n r hrD hrn
    (sourceOrientedNormalParameter_head_det_isUnit_mem_nhds_center d n r hrD hrn)

end BHW
