import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTubeResidualPolydisc

/-!
# Density of max-rank points in the oriented extended-tube image

This file provides the domain-level max-rank density input needed by the
oriented removable-singularity/Riemann-extension route.  The proof is local:
max-rank centers are immediate, and rank-deficient centers use the checked
residual chart producer, whose parameter image contains dense max-rank
parameters and consists of actual extended-tube source invariants.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- On the oriented extended-tube image, not lying in the exceptional-rank
locus is the same as being max-rank. -/
theorem not_exceptional_rank_iff_maxRank
    {d n : ℕ}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedExtendedTubeDomain d n) :
    G ∉ {H | SourceOrientedExceptionalRank d n H} ↔
      SourceOrientedMaxRankAt d n G := by
  exact
    not_sourceOrientedExceptionalRank_iff_maxRank
      (d := d) (n := n)
      (sourceOrientedExtendedTubeDomain_subset_variety d n hG)

/-- Max-rank oriented source points are dense in the oriented extended-tube
image, stated with the explicit max-rank locus.  At a rank-deficient center
this is exactly the density field of the checked residual chart, pushed from
the parameter image back to the domain. -/
theorem sourceOrientedMaxRank_dense_in_domain_inter_maxRank
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ) :
    sourceOrientedExtendedTubeDomain d n ⊆
      closure
        (sourceOrientedExtendedTubeDomain d n ∩
          {G | SourceOrientedMaxRankAt d n G}) := by
  intro G hG
  rcases hG with ⟨z0, hz0, rfl⟩
  by_cases hmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)
  · exact subset_closure ⟨⟨z0, hz0, rfl⟩, hmax⟩
  · let C := sourceOriented_rankDeficient_residualChart hd n hz0 hmax
    have hdense :=
      C.maxRank_dense_parameters C.c0 C.c0_mem
    have hsubset :
        ((fun c' =>
            sourceOrientedMinkowskiInvariant d n (C.toVec c')) ''
          {c' | c' ∈ C.P ∧
            SourceOrientedMaxRankAt d n
              (sourceOrientedMinkowskiInvariant d n (C.toVec c'))}) ⊆
          sourceOrientedExtendedTubeDomain d n ∩
            {G | SourceOrientedMaxRankAt d n G} := by
      intro G hG
      rcases hG with ⟨c, hc, rfl⟩
      exact
        ⟨⟨C.toVec c, C.toVec_mem c (C.P_subset_K hc.1), rfl⟩,
          hc.2⟩
    have hclosed :=
      closure_mono hsubset hdense
    simpa [C.toVec_c0_invariant] using hclosed

/-- The non-exceptional locus is dense in the oriented extended-tube image.
This is the form consumed by the normal analytic-space Riemann extension. -/
theorem sourceOrientedMaxRank_dense_in_domain
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ) :
    sourceOrientedExtendedTubeDomain d n ⊆
      closure
        (sourceOrientedExtendedTubeDomain d n \
          {G | SourceOrientedExceptionalRank d n G}) := by
  have hdense :=
    sourceOrientedMaxRank_dense_in_domain_inter_maxRank (d := d) hd n
  refine fun G hG => closure_mono ?_ (hdense hG)
  intro H hH
  exact
    ⟨hH.1,
      (not_exceptional_rank_iff_maxRank (d := d) (n := n) hH.1).2 hH.2⟩

end BHW
