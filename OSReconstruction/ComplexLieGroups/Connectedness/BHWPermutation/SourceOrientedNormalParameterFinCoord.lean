import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameterBall

/-!
# `Fin m` coordinates for rank-deficient normal parameters

The rank-deficient residual-polydisc interface uses parameter sets in
`Fin m -> ℂ`.  `SourceOrientedNormalParameter.lean` already gives a canonical
finite index type for the head/mixed/tail normal coordinates.  This file
reindexes that finite function space to `Fin (Fintype.card _)`, and records the
basic metric-ball facts used by the compact residual-polydisc producer.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The dimension of the finite coordinate model for a normal-parameter
space. -/
abbrev sourceOrientedNormalParameterFinCoordDim (d n r : ℕ) : ℕ :=
  Fintype.card (SourceOrientedNormalParameterFiniteCoordIndex d n r)

/-- Reindex the canonical finite normal-parameter coordinate type by
`Fin (card _)`. -/
noncomputable def sourceOrientedNormalParameterFiniteCoordIndexEquivFin
    (d n r : ℕ) :
    SourceOrientedNormalParameterFiniteCoordIndex d n r ≃
      Fin (sourceOrientedNormalParameterFinCoordDim d n r) :=
  Fintype.equivFin (SourceOrientedNormalParameterFiniteCoordIndex d n r)

/-- Homeomorphism from the canonical finite function coordinate model to
`Fin m -> ℂ`, where `m` is the finite coordinate count. -/
noncomputable def sourceOrientedNormalParameterFiniteCoordFunctionHomeomorph
    (d n r : ℕ) :
    (SourceOrientedNormalParameterFiniteCoordIndex d n r → ℂ) ≃ₜ
      (Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ) where
  toEquiv :=
    { toFun := fun x k =>
        x ((sourceOrientedNormalParameterFiniteCoordIndexEquivFin d n r).symm k)
      invFun := fun y i =>
        y (sourceOrientedNormalParameterFiniteCoordIndexEquivFin d n r i)
      left_inv := by
        intro x
        funext i
        simp [sourceOrientedNormalParameterFiniteCoordIndexEquivFin]
      right_inv := by
        intro y
        funext k
        simp [sourceOrientedNormalParameterFiniteCoordIndexEquivFin] }
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact
      continuous_apply
        ((sourceOrientedNormalParameterFiniteCoordIndexEquivFin d n r).symm k)
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact
      continuous_apply
        (sourceOrientedNormalParameterFiniteCoordIndexEquivFin d n r i)

/-- Normal-parameter coordinates as a concrete `Fin m -> ℂ` homeomorphism. -/
noncomputable def sourceOrientedNormalParameterFinCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn ≃ₜ
      (Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ) :=
  (sourceOrientedNormalParameterFiniteCoordHomeomorph
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).trans
    (sourceOrientedNormalParameterFiniteCoordFunctionHomeomorph d n r)

/-- The encoded normal center in the `Fin m -> ℂ` coordinate model. -/
def sourceOrientedNormalParameterFinCenterCoord
    (d n r : ℕ) :
    Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ :=
  sourceOrientedNormalParameterFiniteCoordFunctionHomeomorph d n r
    (sourceOrientedNormalParameterFiniteCenterCoord d n r)

@[simp]
theorem sourceOrientedNormalParameterFinCoordHomeomorph_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterFinCoordHomeomorph
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      sourceOrientedNormalParameterFinCenterCoord d n r := by
  unfold sourceOrientedNormalParameterFinCoordHomeomorph
    sourceOrientedNormalParameterFinCenterCoord
  change
    sourceOrientedNormalParameterFiniteCoordFunctionHomeomorph d n r
        (sourceOrientedNormalParameterFiniteCoord
          (sourceOrientedNormalCenterParameter d n r hrD hrn)) =
      sourceOrientedNormalParameterFiniteCoordFunctionHomeomorph d n r
        (sourceOrientedNormalParameterFiniteCenterCoord d n r)
  rw [sourceOrientedNormalParameterFiniteCoord_center]

/-- The open finite-coordinate ball around the normal center. -/
def sourceOrientedNormalParameterFinCoordOpenBall
    (d n r : ℕ)
    (ε : ℝ) :
    Set (Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ) :=
  Metric.ball (sourceOrientedNormalParameterFinCenterCoord d n r) ε

/-- The closed finite-coordinate ball around the normal center. -/
def sourceOrientedNormalParameterFinCoordClosedBall
    (d n r : ℕ)
    (ε : ℝ) :
    Set (Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ) :=
  Metric.closedBall (sourceOrientedNormalParameterFinCenterCoord d n r) ε

theorem isOpen_sourceOrientedNormalParameterFinCoordOpenBall
    (d n r : ℕ)
    (ε : ℝ) :
    IsOpen (sourceOrientedNormalParameterFinCoordOpenBall d n r ε) := by
  simp [sourceOrientedNormalParameterFinCoordOpenBall]

theorem isCompact_sourceOrientedNormalParameterFinCoordClosedBall
    (d n r : ℕ)
    (ε : ℝ) :
    IsCompact (sourceOrientedNormalParameterFinCoordClosedBall d n r ε) := by
  exact isCompact_closedBall _ _

theorem sourceOrientedNormalParameterFinCoordOpenBall_subset_closedBall
    (d n r : ℕ)
    {ε δ : ℝ}
    (hεδ : ε ≤ δ) :
    sourceOrientedNormalParameterFinCoordOpenBall d n r ε ⊆
      sourceOrientedNormalParameterFinCoordClosedBall d n r δ := by
  intro c hc
  exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hεδ hc)

/-- The encoded normal center lies in every positive-radius open ball. -/
theorem sourceOrientedNormalParameterFinCenterCoord_mem_openBall
    (d n r : ℕ)
    {ε : ℝ}
    (hε : 0 < ε) :
    sourceOrientedNormalParameterFinCenterCoord d n r ∈
      sourceOrientedNormalParameterFinCoordOpenBall d n r ε := by
  simp [sourceOrientedNormalParameterFinCoordOpenBall, hε]

/-- The encoded normal center lies in every nonnegative-radius closed ball. -/
theorem sourceOrientedNormalParameterFinCenterCoord_mem_closedBall
    (d n r : ℕ)
    {ε : ℝ}
    (hε : 0 ≤ ε) :
    sourceOrientedNormalParameterFinCenterCoord d n r ∈
      sourceOrientedNormalParameterFinCoordClosedBall d n r ε := by
  simp [sourceOrientedNormalParameterFinCoordClosedBall, hε]

/-- Every finite-coordinate neighborhood of the normal center contains a
positive-radius closed ball around the center. -/
theorem exists_sourceOrientedNormalParameterFinCoordClosedBall_subset_of_mem_nhds_center
    (d n r : ℕ)
    {U : Set (Fin (sourceOrientedNormalParameterFinCoordDim d n r) → ℂ)}
    (hU : U ∈ 𝓝 (sourceOrientedNormalParameterFinCenterCoord d n r)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterFinCoordClosedBall d n r ε ⊆ U := by
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε / 2, half_pos hε_pos, ?_⟩
  exact
    (Metric.closedBall_subset_ball (half_lt_self hε_pos)).trans hε_sub

end BHW
