import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientSchurWindowShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeNormal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurReconstruct

/-!
# Canonical extracted Schur image for rank-deficient source charts

This file exposes the honest extracted-image set for the remaining
rank-deficient local-image producer.  The set is cut out by the local
head-gauge chart, the extracted Schur mixed coordinate, and target-shaped
shifted-tail residual bounds.  The two algebraic inclusions are checked here;
the remaining analytic/topological input is openness of this extracted set.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The subtype normal-image candidate cut out by head-gauge Schur extraction.
It is the set that should be open in `SourceOrientedVariety d n`: the selected
head lies in the gauge domain, the gauge factor and mixed Schur coefficient
lie in the chosen coordinate windows, and the gauge-selected shifted residual
tail satisfies the target-shaped tail-radius bounds. -/
def sourceOrientedHeadGaugeSchurExtractedImage
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedVariety d n) :=
  {Gv |
    let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
    let H := Head.factor Acoord
    let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
    Acoord ∈ Head.U ∧
      H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
      sourceSchurMixedCoeff n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
        sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
      (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
      (∀ ι, ‖T.det ι‖ < Tail.tailEta)}

/-- Forward inclusion for the extracted image: a normal parameter in a
head-gauge-compatible Schur window satisfies exactly the extracted
head/mixed/residual-tail conditions. -/
theorem sourceOrientedNormalParameterVarietyPoint_mem_headGaugeSchurExtractedImage
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p ∈
      sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail := by
  let Gv := sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  let H := Head.factor Acoord
  let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
  have hpDomain : p.head ∈ Head.factorDomain := hdomain hp.1
  have hAeq :
      Acoord = sourceHeadFactorGramSymmCoord d r hrD p.head := by
    simpa [Gv, Acoord] using
      sourceOrientedSchurHeadBlockSymm_normalParameter d n r hrD hrn p
  have hHeadU : Acoord ∈ Head.U := by
    rw [hAeq]
    exact Head.factorDomain_mem p.head hpDomain
  have hfactor : H = p.head := by
    dsimp [H]
    rw [hAeq]
    exact Head.factor_left_inverse p.head hpDomain
  have hmixed :
      sourceSchurMixedCoeff n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1) =
        p.mixed := by
    simpa [Gv] using
      SourceOrientedRankDeficientAlgebraicNormalFormData.schurWindow_normalParameter_headGauge_mixedCoeff_eq
        Head hdomain p hp
  have htail :
      T = sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
    simpa [Gv, Acoord, H, T] using
      SourceOrientedRankDeficientAlgebraicNormalFormData.schurWindow_normalParameter_headGauge_residualTail_eq
        Head hdomain p hp
  have hfactor' :
      Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2) =
        p.head := by
    simpa [Acoord, H] using hfactor
  have htail' :
      sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1
          (Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2)) =
        sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
    simpa [Acoord, H, T] using htail
  change
    (let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
     let H := Head.factor Acoord
     let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
     Acoord ∈ Head.U ∧
       H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
       sourceSchurMixedCoeff n r hrn Gv.1
           (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
         sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
       (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
       (∀ ι, ‖T.det ι‖ < Tail.tailEta))
  dsimp only
  refine ⟨hHeadU, ?_, ?_, ?_, ?_⟩
  · simpa [hfactor'] using hp.1
  · simpa [hmixed] using hp.2.1
  · intro u v
    have h := hp.2.2.2.1 u v
    simpa [htail'] using h
  · intro ι
    have h := hp.2.2.2.2 ι
    simpa [htail'] using h

/-- Reverse inclusion for the extracted image.  A source-variety point whose
head-gauge Schur extraction lies in the target-shaped windows is reconstructed
by a normal parameter in the corresponding Schur window. -/
theorem sourceOrientedHeadGaugeSchurExtractedImage_subset_normalParameter_image
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail ⊆
      sourceOrientedNormalParameterVarietyPoint d n r hrD hrn ''
        sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail := by
  intro Gv hGv
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  let H := Head.factor Acoord
  let L := sourceSchurMixedCoeff n r hrn Gv.1
    (sourceOrientedSchurHeadBlock n r hrn Gv.1)
  let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
  change
    (let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
     let H := Head.factor Acoord
     let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
     Acoord ∈ Head.U ∧
       H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
       sourceSchurMixedCoeff n r hrn Gv.1
           (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
         sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
       (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
       (∀ ι, ‖T.det ι‖ < Tail.tailEta)) at hGv
  dsimp only at hGv
  rcases hGv with ⟨hHeadU, hH_window, hL_window, hT_gram, hT_det⟩
  let R : SourceOrientedSchurResidualData d n r hrD hrn Gv.1 :=
    sourceOriented_schurResidualData_of_headGauge
      hd hrD hrn Head Gv.2 hHeadU
  have hT_mem :
      T ∈ sourceShiftedTailOrientedVariety d r hrD (n - r) := by
    simpa [T, H, Acoord] using
      sourceOrientedSchurResidualTailData_mem_variety
        hd hrD hrn Head Gv.2 hHeadU
  rcases Tail.tailRealize T hT_mem hT_gram hT_det with
    ⟨q, hq_coord, hqT⟩
  have hqR :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) q = R.tail := by
    simpa [R, T, H, Acoord,
      sourceOriented_schurResidualData_of_headGauge,
      sourceOriented_schurResidualData_of_tail_mem] using hqT
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := R.headFactor
      mixed := R.L
      tail := q }
  have hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [p, R, H, Acoord,
        sourceOriented_schurResidualData_of_headGauge,
        sourceOriented_schurResidualData_of_tail_mem] using hH_window
    · simpa [p, R, L, H, Acoord,
        sourceOriented_schurResidualData_of_headGauge,
        sourceOriented_schurResidualData_of_tail_mem] using hL_window
    · refine ⟨?_, ?_, ?_⟩
      · simpa [p] using hq_coord
      · intro u v
        have hproj :
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v =
              T.gram u v := by
          exact congrFun (congrFun (congrArg SourceShiftedTailOrientedData.gram hqT) u) v
        rw [hproj]
        exact hT_gram u v
      · intro ι
        have hproj :
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι =
              T.det ι := by
          exact congrFun (congrArg SourceShiftedTailOrientedData.det hqT) ι
        rw [hproj]
        exact hT_det ι
  refine ⟨p, hp, ?_⟩
  apply Subtype.ext
  have hrecon :=
    sourceOriented_reconstruct_from_schurResidual
      d n r hn hrD hrn Gv.2 R hqR
  simpa [sourceOrientedNormalParameterVarietyPoint, p] using hrecon

end BHW
