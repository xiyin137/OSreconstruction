import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadSliceGaugeIFT
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientSliceParameter
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTubeResidual

/-!
# `Fin m` coordinates for sliced rank-deficient normal parameters

The constructible rank-deficient Schur image theorem uses the sliced normal
parameter type, while the residual-polydisc interface uses parameter sets in
`Fin m -> ℂ`.  This file supplies the finite-coordinate model for the sliced
parameters and the compact/open tube shrink obtained by decoding those
coordinates, forgetting the slice proof, and using the existing source-level
normal-form return map.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Linear finite-dimensional coordinates for sliced normal parameters:
the head slice is first put in symmetric `K = H * η - η` coordinates. -/
abbrev sourceOrientedSlicedNormalParameterLinearCoordType
    (d n r : ℕ) : Type :=
  sourceSymmetricMatrixSubmodule r ×
    Matrix (Fin (n - r)) (Fin r) ℂ ×
      (Fin (n - r) → Fin (d + 1 - r) → ℂ)

/-- The finite coordinate dimension of a sliced normal-parameter space. -/
abbrev sourceOrientedSlicedNormalParameterFinCoordDim
    (d n r : ℕ) : ℕ :=
  Module.finrank ℂ (sourceOrientedSlicedNormalParameterLinearCoordType d n r)

/-- Sliced normal parameters in linear head/mixed/tail coordinates. -/
noncomputable def sourceOrientedSlicedNormalParameterLinearCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn ≃ₜ
      sourceOrientedSlicedNormalParameterLinearCoordType d n r :=
  (sourceOrientedSlicedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).trans
    ((sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).prodCongr
      (Homeomorph.refl
        (Matrix (Fin (n - r)) (Fin r) ℂ ×
          (Fin (n - r) → Fin (d + 1 - r) → ℂ))))

/-- Sliced normal-parameter coordinates as a concrete `Fin m -> ℂ`
homeomorphism. -/
noncomputable def sourceOrientedSlicedNormalParameterFinCoordHomeomorph
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn ≃ₜ
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ) :=
  (sourceOrientedSlicedNormalParameterLinearCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).trans
    (ContinuousLinearEquiv.ofFinrankEq
      (𝕜 := ℂ)
      (E := sourceOrientedSlicedNormalParameterLinearCoordType d n r)
      (F := Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ)
      (by simp [sourceOrientedSlicedNormalParameterFinCoordDim])).toHomeomorph

/-- The encoded sliced normal center in the `Fin m -> ℂ` coordinate model. -/
noncomputable def sourceOrientedSlicedNormalParameterFinCenterCoord
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ :=
  sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
    (sourceOrientedSlicedNormalCenterParameter d n r hrD hrn)

theorem sourceOrientedSlicedNormalParameterFinCoordHomeomorph_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
        (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
        (sourceOrientedSlicedNormalCenterParameter d n r hrD hrn) =
      sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn :=
  rfl

/-- The open finite-coordinate ball around the sliced normal center. -/
def sourceOrientedSlicedNormalParameterFinCoordOpenBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (ε : ℝ) :
    Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ) :=
  Metric.ball
    (sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn) ε

/-- The closed finite-coordinate ball around the sliced normal center. -/
def sourceOrientedSlicedNormalParameterFinCoordClosedBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (ε : ℝ) :
    Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ) :=
  Metric.closedBall
    (sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn) ε

theorem isOpen_sourceOrientedSlicedNormalParameterFinCoordOpenBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (ε : ℝ) :
    IsOpen
      (sourceOrientedSlicedNormalParameterFinCoordOpenBall
        d n r hrD hrn ε) := by
  simp [sourceOrientedSlicedNormalParameterFinCoordOpenBall]

theorem isCompact_sourceOrientedSlicedNormalParameterFinCoordClosedBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (ε : ℝ) :
    IsCompact
      (sourceOrientedSlicedNormalParameterFinCoordClosedBall
        d n r hrD hrn ε) := by
  exact isCompact_closedBall _ _

theorem sourceOrientedSlicedNormalParameterFinCoordOpenBall_subset_closedBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {ε δ : ℝ}
    (hεδ : ε ≤ δ) :
    sourceOrientedSlicedNormalParameterFinCoordOpenBall d n r hrD hrn ε ⊆
      sourceOrientedSlicedNormalParameterFinCoordClosedBall d n r hrD hrn δ := by
  intro c hc
  exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hεδ hc)

/-- The encoded sliced center lies in every positive-radius open ball. -/
theorem sourceOrientedSlicedNormalParameterFinCenterCoord_mem_openBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {ε : ℝ}
    (hε : 0 < ε) :
    sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn ∈
      sourceOrientedSlicedNormalParameterFinCoordOpenBall
        d n r hrD hrn ε := by
  simp [sourceOrientedSlicedNormalParameterFinCoordOpenBall, hε]

/-- The encoded sliced center lies in every nonnegative-radius closed ball. -/
theorem sourceOrientedSlicedNormalParameterFinCenterCoord_mem_closedBall
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {ε : ℝ}
    (hε : 0 ≤ ε) :
    sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn ∈
      sourceOrientedSlicedNormalParameterFinCoordClosedBall
        d n r hrD hrn ε := by
  simp [sourceOrientedSlicedNormalParameterFinCoordClosedBall, hε]

/-- The finite-coordinate image of an open sliced-parameter set is open. -/
theorem isOpen_sourceOrientedSlicedNormalParameterFinCoord_image
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn)}
    (hW : IsOpen W) :
    IsOpen
      (sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn) ''
        W) := by
  exact
    (sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).isOpenMap W hW

/-- If a sliced-parameter set contains the center, its finite-coordinate image
contains the encoded center. -/
theorem sourceOrientedSlicedNormalParameterFinCenterCoord_mem_image
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn)}
    (hcenter :
      sourceOrientedSlicedNormalCenterParameter d n r hrD hrn ∈ W) :
    sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn ∈
      sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn) ''
        W :=
  ⟨sourceOrientedSlicedNormalCenterParameter d n r hrD hrn, hcenter, rfl⟩

/-- Transfer a sliced-parameter containment into a closed finite-coordinate
ball to the corresponding image containment. -/
theorem sourceOrientedSlicedNormalParameterFinCoord_image_subset_closedBall
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {ε : ℝ}
    {W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn)}
    (hW :
      W ⊆
        (sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)) ⁻¹'
          sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n r hrD hrn ε) :
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn) ''
        W ⊆
      sourceOrientedSlicedNormalParameterFinCoordClosedBall
        d n r hrD hrn ε := by
  rintro c ⟨p, hpW, rfl⟩
  exact hW hpW

/-- Every finite-coordinate neighborhood of the sliced center contains a
positive-radius closed ball around the center. -/
theorem exists_sourceOrientedSlicedNormalParameterFinCoordClosedBall_subset_of_mem_nhds_center
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {U : Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ)}
    (hU :
      U ∈ 𝓝
        (sourceOrientedSlicedNormalParameterFinCenterCoord d n r hrD hrn)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n r hrD hrn ε ⊆ U := by
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε / 2, half_pos hε_pos, ?_⟩
  exact
    (Metric.closedBall_subset_ball (half_lt_self hε_pos)).trans hε_sub

/-- Decoding sliced finite coordinates and forgetting the slice proof is
continuous. -/
theorem continuous_slicedFinCoord_toNormalParameter
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n} :
    Continuous
      (fun c : Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n r) → ℂ =>
        ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).symm c).toNormalParameter) :=
  (continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).comp
    (sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)).symm.continuous

namespace SourceOrientedRankDeficientNormalFormData

/-- The sliced-parameter preimage of the extended tube is a neighborhood of
the sliced center after forgetting the slice and returning to original source
coordinates. -/
theorem toOriginal_slicedNormalParameterVector_mem_ET_mem_nhds_center
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    {p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn |
      N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            p.toNormalParameter) ∈
        ExtendedTube d n} ∈
      𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) := by
  have hT :
      Tendsto
        (fun p :
            SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn =>
          p.toNormalParameter)
        (𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn))
        (𝓝 (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn)) := by
    simpa using
      (continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
        (d := d) (n := n) (r := N.r)
        (hrD := N.hrD) (hrn := N.hrn)).continuousAt
  exact hT N.toOriginal_normalParameterVector_mem_ET_mem_nhds_center

/-- In sliced `Fin m -> ℂ` coordinates, choose a positive closed ball around
the encoded sliced center whose decoded returned source tuples stay in the
extended tube. -/
theorem exists_slicedFinCoordClosedBall_toOriginal_mem_ET
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε ⊆
          {c : Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ |
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
                  ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
                    (d := d) (n := n) (r := N.r)
                    (hrD := N.hrD) (hrn := N.hrn)).symm c).toNormalParameter) ∈
              ExtendedTube d n} := by
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let U :
      Set (SourceOrientedRankDeficientSlicedNormalParameter
        d n N.r N.hrD N.hrn) :=
    {p |
      N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            p.toNormalParameter) ∈
        ExtendedTube d n}
  have hU : U ∈
      𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) :=
    N.toOriginal_slicedNormalParameterVector_mem_ET_mem_nhds_center
  have hcoord :
      e.symm ⁻¹' U ∈
        𝓝
          (sourceOrientedSlicedNormalParameterFinCenterCoord
            d n N.r N.hrD N.hrn) := by
    have hcenter :
        e.symm
            (sourceOrientedSlicedNormalParameterFinCenterCoord
              d n N.r N.hrD N.hrn) =
          sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn := by
      change e.symm
          (e (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn)) =
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn
      exact e.symm_apply_apply _
    have hs :
        Tendsto e.symm
          (𝓝
            (sourceOrientedSlicedNormalParameterFinCenterCoord
              d n N.r N.hrD N.hrn))
          (𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn)) := by
      have hs0 :
          Tendsto e.symm
            (𝓝
              (sourceOrientedSlicedNormalParameterFinCenterCoord
                d n N.r N.hrD N.hrn))
            (𝓝
              (e.symm
                (sourceOrientedSlicedNormalParameterFinCenterCoord
                  d n N.r N.hrD N.hrn))) :=
        e.symm.continuous.continuousAt
      simpa [hcenter] using hs0
    exact hs hU
  rcases
    exists_sourceOrientedSlicedNormalParameterFinCoordClosedBall_subset_of_mem_nhds_center
      hcoord with
    ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro c hc
  exact hε_sub hc

/-- The compact/open sliced finite-coordinate parameter pair for the
tube-stability part of the residual-polydisc producer. -/
theorem exists_slicedFinCoordCompactOpen_toOriginal_mem_ET
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ ε : ℝ,
      0 < ε ∧
        IsCompact
          (sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε) ∧
        IsOpen
          (sourceOrientedSlicedNormalParameterFinCoordOpenBall
            d n N.r N.hrD N.hrn ε) ∧
        sourceOrientedSlicedNormalParameterFinCoordOpenBall
            d n N.r N.hrD N.hrn ε ⊆
          sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε ∧
        sourceOrientedSlicedNormalParameterFinCenterCoord
            d n N.r N.hrD N.hrn ∈
          sourceOrientedSlicedNormalParameterFinCoordOpenBall
            d n N.r N.hrD N.hrn ε ∧
        (∀ c,
          c ∈ sourceOrientedSlicedNormalParameterFinCoordClosedBall
              d n N.r N.hrD N.hrn ε →
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
                  ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
                    (d := d) (n := n) (r := N.r)
                    (hrD := N.hrD) (hrn := N.hrn)).symm c).toNormalParameter) ∈
              ExtendedTube d n) := by
  rcases N.exists_slicedFinCoordClosedBall_toOriginal_mem_ET with
    ⟨ε, hε_pos, hε_tube⟩
  refine
    ⟨ε, hε_pos,
      isCompact_sourceOrientedSlicedNormalParameterFinCoordClosedBall
        d n N.r N.hrD N.hrn ε,
      isOpen_sourceOrientedSlicedNormalParameterFinCoordOpenBall
        d n N.r N.hrD N.hrn ε,
      sourceOrientedSlicedNormalParameterFinCoordOpenBall_subset_closedBall
        d n N.r N.hrD N.hrn le_rfl,
      sourceOrientedSlicedNormalParameterFinCenterCoord_mem_openBall
        d n N.r N.hrD N.hrn hε_pos,
      ?_⟩
  intro c hc
  exact hε_tube hc

/-- The decoded sliced finite-coordinate normal vector is continuous on any
compact coordinate ball. -/
theorem continuousOn_slicedFinCoord_normalParameterVector_closedBall
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (ε : ℝ) :
    ContinuousOn
      (fun c :
          Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ =>
        sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
          ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
            (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn)).symm c).toNormalParameter)
      (sourceOrientedSlicedNormalParameterFinCoordClosedBall
        d n N.r N.hrD N.hrn ε) :=
  ((continuous_sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn).comp
    (continuous_slicedFinCoord_toNormalParameter
      (d := d) (n := n) (r := N.r)
      (hrD := N.hrD) (hrn := N.hrn))).continuousOn

/-- Sliced-parameter version of the original-coordinate max-rank/tail
max-rank bridge. -/
theorem toOriginal_slicedNormalParameterVector_maxRank_iff_tail
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn)
    (hH : IsUnit p.toNormalParameter.head.det) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
              p.toNormalParameter))) ↔
      SourceShiftedTailOrientedMaxRankAt d N.r N.hrD (n - N.r)
        (sourceShiftedTailOrientedInvariant d N.r N.hrD (n - N.r) p.tail) :=
  N.toOriginal_normalParameterVector_maxRank_iff_tail p.toNormalParameter hH

/-- Finite-coordinate membership bridge for the original-coordinate image
coming from a sliced normal-parameter image. -/
theorem slicedFinCoord_originalImage_mem_varietyTransport
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    {W :
      Set (SourceOrientedRankDeficientSlicedNormalParameter
        d n N.r N.hrD N.hrn)}
    {Ω : Set (SourceOrientedVariety d n)}
    (hmem :
      ∀ p, p ∈ W →
        sourceOrientedSlicedNormalParameterVarietyPoint
          d n N.r N.hrD N.hrn p ∈ Ω) :
    ∀ c,
      c ∈
          sourceOrientedSlicedNormalParameterFinCoordHomeomorph
              (d := d) (n := n) (r := N.r)
              (hrD := N.hrD) (hrn := N.hrn) ''
            W →
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
              ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
                (d := d) (n := n) (r := N.r)
                (hrD := N.hrD) (hrn := N.hrn)).symm c).toNormalParameter)) ∈
          sourceOrientedVarietyUnderlyingSet d n
            (N.varietyTransport.invFun '' Ω) := by
  intro c hc
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  rcases hc with ⟨p, hpW, rfl⟩
  rw [e.symm_apply_apply]
  rw [sourceOrientedVarietyUnderlyingSet]
  refine ⟨N.varietyTransport.invFun
      (sourceOrientedSlicedNormalParameterVarietyPoint
        d n N.r N.hrD N.hrn p), ?_, ?_⟩
  · exact ⟨_, hmem p hpW, rfl⟩
  · simpa [e, sourceOrientedSlicedNormalParameterVarietyPoint,
      SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using N.originalNormalVarietyPoint_eq_toOriginal p.toNormalParameter

/-- Finite-coordinate surjectivity bridge for the original-coordinate image
coming from a sliced normal-parameter image. -/
theorem slicedFinCoord_originalImage_surj_varietyTransport
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    {W :
      Set (SourceOrientedRankDeficientSlicedNormalParameter
        d n N.r N.hrD N.hrn)}
    {Ω : Set (SourceOrientedVariety d n)}
    (hsurj :
      Ω ⊆
        sourceOrientedSlicedNormalParameterVarietyPoint
          d n N.r N.hrD N.hrn '' W) :
    sourceOrientedVarietyUnderlyingSet d n
        (N.varietyTransport.invFun '' Ω) ⊆
      (fun c =>
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
              ((sourceOrientedSlicedNormalParameterFinCoordHomeomorph
                (d := d) (n := n) (r := N.r)
                (hrD := N.hrD) (hrn := N.hrn)).symm c).toNormalParameter))) ''
        (sourceOrientedSlicedNormalParameterFinCoordHomeomorph
            (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn) '' W) := by
  intro G hG
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  rw [sourceOrientedVarietyUnderlyingSet] at hG
  rcases hG with ⟨Gv, hGv, hG⟩
  rcases hGv with ⟨Hv, hHvΩ, hHvGv⟩
  rcases hsurj hHvΩ with ⟨p, hpW, hpHv⟩
  refine ⟨e p, ⟨p, hpW, rfl⟩, ?_⟩
  have htransport :
      (N.varietyTransport.invFun Hv).1 =
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
              p.toNormalParameter)) := by
    rw [← hpHv]
    simpa [e, sourceOrientedSlicedNormalParameterVarietyPoint,
      SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using N.originalNormalVarietyPoint_eq_toOriginal p.toNormalParameter
  have hactual :
      sourceOrientedMinkowskiInvariant d n
        (N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            p.toNormalParameter)) = G := by
    rw [← hG]
    exact htransport.symm.trans (congrArg Subtype.val hHvGv)
  simpa [e] using hactual

end SourceOrientedRankDeficientNormalFormData

end BHW
