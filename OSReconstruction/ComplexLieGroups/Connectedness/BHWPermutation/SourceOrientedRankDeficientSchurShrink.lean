import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameterBall
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Schur-coordinate shrinks for normal parameters

This file packages the topology-only shrink from the normal center to the
Schur head, mixed, and residual-tail coordinates.  The later quantitative
local-image proof supplies concrete coordinate neighborhoods; this file proves
that they can be pulled back to a connected normal-parameter ball.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

@[simp]
theorem sourceOrientedNormalParameterSchurHead_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurHead d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      sourceHeadMetric d r hrD := by
  simp [sourceOrientedNormalParameterSchurHead,
    sourceOrientedNormalCenterParameter]

@[simp]
theorem sourceOrientedNormalParameterSchurMixed_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurMixed d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      0 := by
  simp [sourceOrientedNormalParameterSchurMixed,
    sourceOrientedNormalCenterParameter]

@[simp]
theorem sourceOrientedNormalParameterSchurTail_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurTail d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      0 := by
  ext u v
  simp [sourceOrientedNormalParameterSchurTail, sourceShiftedTailGram,
    sourceVectorMinkowskiInner, sourceTailEmbed,
    sourceOrientedNormalCenterParameter]

/-- Any neighborhoods of the center Schur head, mixed, and residual-tail
coordinates contain a positive-radius normal-parameter ball after pullback. -/
theorem exists_sourceOrientedNormalParameterBall_subset_schur_nhds
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {Uh : Set (Matrix (Fin r) (Fin r) ℂ)}
    (hUh : Uh ∈ 𝓝 (sourceHeadMetric d r hrD))
    {Um : Set (Matrix (Fin r) (Fin (n - r)) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin r) (Fin (n - r)) ℂ))
    {Ut : Set (Matrix (Fin (n - r)) (Fin (n - r)) ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            sourceOrientedNormalParameterSchurHead d n r hrD hrn p ∈ Uh ∧
              sourceOrientedNormalParameterSchurMixed d n r hrD hrn p ∈ Um ∧
              sourceOrientedNormalParameterSchurTail d n r hrD hrn p ∈ Ut} := by
  let p0 := sourceOrientedNormalCenterParameter d n r hrD hrn
  have hhead_nhds :
      (sourceOrientedNormalParameterSchurHead d n r hrD hrn) ⁻¹' Uh ∈
        𝓝 p0 := by
    have hUh' :
        Uh ∈
          𝓝 (sourceOrientedNormalParameterSchurHead d n r hrD hrn p0) := by
      simpa [p0] using hUh
    exact
      (continuous_sourceOrientedNormalParameterSchurHead d n r hrD hrn).continuousAt
        hUh'
  have hmixed_nhds :
      (sourceOrientedNormalParameterSchurMixed d n r hrD hrn) ⁻¹' Um ∈
        𝓝 p0 := by
    have hUm' :
        Um ∈
          𝓝 (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p0) := by
      simpa [p0] using hUm
    exact
      (continuous_sourceOrientedNormalParameterSchurMixed d n r hrD hrn).continuousAt
        hUm'
  have htail_nhds :
      (sourceOrientedNormalParameterSchurTail d n r hrD hrn) ⁻¹' Ut ∈
        𝓝 p0 := by
    have hUt' :
        Ut ∈
          𝓝 (sourceOrientedNormalParameterSchurTail d n r hrD hrn p0) := by
      simpa [p0] using hUt
    exact
      (continuous_sourceOrientedNormalParameterSchurTail d n r hrD hrn).continuousAt
        hUt'
  have hU :
      {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
        sourceOrientedNormalParameterSchurHead d n r hrD hrn p ∈ Uh ∧
          sourceOrientedNormalParameterSchurMixed d n r hrD hrn p ∈ Um ∧
          sourceOrientedNormalParameterSchurTail d n r hrD hrn p ∈ Ut} ∈
        𝓝 p0 := by
    refine
      Filter.mem_of_superset
        (Filter.inter_mem hhead_nhds
          (Filter.inter_mem hmixed_nhds htail_nhds)) ?_
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  exact
    exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
      d n r hrD hrn hU

/-- Any neighborhoods of the raw normal head, mixed, and tail coordinates at
the normal center contain a positive-radius normal-parameter ball. -/
theorem exists_sourceOrientedNormalParameterBall_subset_coordinate_nhds
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {Uh : Set (Matrix (Fin r) (Fin r) ℂ)}
    (hUh : Uh ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) ℂ))
    {Um : Set (Matrix (Fin (n - r)) (Fin r) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin (n - r)) (Fin r) ℂ))
    {Ut : Set (Fin (n - r) → Fin (d + 1 - r) → ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            p.head ∈ Uh ∧ p.mixed ∈ Um ∧ p.tail ∈ Ut} := by
  let p0 := sourceOrientedNormalCenterParameter d n r hrD hrn
  have hhead_nhds :
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.head) ⁻¹' Uh ∈ 𝓝 p0 := by
    have hUh' :
        Uh ∈
          𝓝 ((fun p :
              SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
              p.head) p0) := by
      simpa [p0, sourceOrientedNormalCenterParameter] using hUh
    exact
      (continuous_sourceOrientedNormalParameter_head
        (d := d) (n := n) (r := r) (hrD := hrD)
        (hrn := hrn)).continuousAt hUh'
  have hmixed_nhds :
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.mixed) ⁻¹' Um ∈ 𝓝 p0 := by
    have hUm' :
        Um ∈
          𝓝 ((fun p :
              SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
              p.mixed) p0) := by
      simpa [p0, sourceOrientedNormalCenterParameter] using hUm
    exact
      (continuous_sourceOrientedNormalParameter_mixed
        (d := d) (n := n) (r := r) (hrD := hrD)
        (hrn := hrn)).continuousAt hUm'
  have htail_nhds :
      (fun p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
        p.tail) ⁻¹' Ut ∈ 𝓝 p0 := by
    have hUt' :
        Ut ∈
          𝓝 ((fun p :
              SourceOrientedRankDeficientNormalParameter d n r hrD hrn =>
              p.tail) p0) := by
      simpa [p0, sourceOrientedNormalCenterParameter] using hUt
    exact
      (continuous_sourceOrientedNormalParameter_tail
        (d := d) (n := n) (r := r) (hrD := hrD)
        (hrn := hrn)).continuousAt hUt'
  have hU :
      {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
        p.head ∈ Uh ∧ p.mixed ∈ Um ∧ p.tail ∈ Ut} ∈ 𝓝 p0 := by
    refine
      Filter.mem_of_superset
        (Filter.inter_mem hhead_nhds
          (Filter.inter_mem hmixed_nhds htail_nhds)) ?_
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  exact
    exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
      d n r hrD hrn hU

/-- A positive normal-parameter ball can be chosen inside simultaneous raw
coordinate bounds around the normal center. -/
theorem exists_sourceOrientedNormalParameterBall_subset_coordinate_bounds
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius tailRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (htailRadius : 0 < tailRadius) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            (∀ a b,
              ‖p.head a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ <
                headRadius) ∧
            (∀ u a, ‖p.mixed u a‖ < mixedRadius) ∧
            (∀ u μ, ‖p.tail u μ‖ < tailRadius)} := by
  have hUh :
      {H : Matrix (Fin r) (Fin r) ℂ |
        ∀ a b, ‖H a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ <
          headRadius} ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) ℂ) := by
    have hopen :
        IsOpen
          {H : Matrix (Fin r) (Fin r) ℂ |
            ∀ a b, ‖H a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ <
              headRadius} := by
      simp only [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro a
      apply isOpen_iInter_of_finite
      intro b
      exact isOpen_lt (by fun_prop) continuous_const
    exact hopen.mem_nhds (by intro a b; simpa using hheadRadius)
  have hUm :
      {M : Matrix (Fin (n - r)) (Fin r) ℂ |
        ∀ u a, ‖M u a‖ < mixedRadius} ∈
        𝓝 (0 : Matrix (Fin (n - r)) (Fin r) ℂ) := by
    have hopen :
        IsOpen
          {M : Matrix (Fin (n - r)) (Fin r) ℂ |
            ∀ u a, ‖M u a‖ < mixedRadius} := by
      simp only [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro u
      apply isOpen_iInter_of_finite
      intro a
      exact isOpen_lt (by fun_prop) continuous_const
    exact hopen.mem_nhds (by intro u a; simpa using hmixedRadius)
  have hUt :
      {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
        ∀ u μ, ‖q u μ‖ < tailRadius} ∈
        𝓝 (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ) := by
    have hopen :
        IsOpen
          {q : Fin (n - r) → Fin (d + 1 - r) → ℂ |
            ∀ u μ, ‖q u μ‖ < tailRadius} := by
      simp only [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro u
      apply isOpen_iInter_of_finite
      intro μ
      exact isOpen_lt (by fun_prop) continuous_const
    exact hopen.mem_nhds (by intro u μ; simpa using htailRadius)
  exact
    exists_sourceOrientedNormalParameterBall_subset_coordinate_nhds
      d n r hrD hrn hUh hUm hUt

end BHW
