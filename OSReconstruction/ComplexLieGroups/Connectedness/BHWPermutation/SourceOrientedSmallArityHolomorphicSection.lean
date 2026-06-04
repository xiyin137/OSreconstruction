import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexZeroSectionAt
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHolomorphicSection

/-!
# Small-arity source-oriented holomorphic sections

This file completes the `n < d + 1` max-rank branch.  In this range the
oriented determinant coordinates are vacuous, so an ordinary complex source
Gram zero-section at the actual extended-tube base point gives the desired
ambient holomorphic section.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- In the small-arity case, max-rank points have an ambient holomorphic local
section of the source-oriented invariant map through the extended tube. -/
noncomputable def sourceOrientedMaxRank_localSection_smallArity
    {d n : ℕ}
    [NeZero d]
    (hn : n < d + 1)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    SourceOrientedLocalHolomorphicSectionData (d := d) n
      (sourceOrientedMinkowskiInvariant d n z0) := by
  classical
  have hHW : HWSourceGramMaxRankAt d n z0 :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt d n z0).1
      hmax
  have hreg : SourceComplexGramRegularAt d n z0 :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt_any d n hHW
  let hexMinor := exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg
  let I : Fin (min n (d + 1)) → Fin n := Classical.choose hexMinor
  have hI_spec :
      Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
            sourceComplexRegularMinor d n I J z0 ≠ 0 :=
    Classical.choose_spec hexMinor
  have hI : Function.Injective I := hI_spec.1
  let hexJ := hI_spec.2
  let J : Fin (min n (d + 1)) → Fin (d + 1) := Classical.choose hexJ
  have hJ_spec :
      Function.Injective J ∧ sourceComplexRegularMinor d n I J z0 ≠ 0 :=
    Classical.choose_spec hexJ
  have hJ : Function.Injective J := hJ_spec.1
  have hminor : sourceComplexRegularMinor d n I J z0 ≠ 0 := hJ_spec.2
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor
  let qOfG : SourceOrientedGramData d n →
      Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ :=
    fun G => sourceSelectedComplexGramFlatCoordCLM n m I G.gram
  let target :
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) →
        sourceSelectedComplexSymCoordSubspace n m I ×
          LinearMap.ker
            (sourceSelectedComplexGramDifferentialToSym d n m z0 I) :=
    fun q => sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q
  let sec :
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) →
        Fin n → Fin (d + 1) → ℂ :=
    fun q => e.symm (target q)
  let hexD := exists_sourceSelectedComplexGramZeroSectionAt_good_ball
      d n hI hJ hminor
      (isOpen_extendedTube (d := d) (n := n)) hz0
  let D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) :=
    Classical.choose hexD
  have hD_spec :
      IsOpen D ∧ IsConnected D ∧
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0)) ∈ D ∧
      (∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).target) ∧
      (∀ q ∈ D,
        (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q) ∈
            ExtendedTube d n) ∧
      (∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q)) ≠ 0) ∧
      (∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))).IsInvertible) :=
    Classical.choose_spec hexD
  have hD_open : IsOpen D := hD_spec.1
  have hq0D :
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0)) ∈ D :=
    hD_spec.2.2.1
  have hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).target :=
    hD_spec.2.2.2.1
  have hD_ET :
      ∀ q ∈ D,
        (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q) ∈
            ExtendedTube d n :=
    hD_spec.2.2.2.2.1
  have hD_minor :
      ∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q)) ≠ 0 :=
    hD_spec.2.2.2.2.2.1
  have hD_invertible :
      ∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))).IsInvertible :=
    hD_spec.2.2.2.2.2.2
  let Ω : Set (SourceOrientedGramData d n) := {G | qOfG G ∈ D}
  have hq_cont : Continuous qOfG := by
    exact
      (sourceSelectedComplexGramFlatCoordCLM n m I).continuous.comp
        (continuous_sourceOrientedGramData_gram (d := d) (n := n))
  have hΩ_open : IsOpen Ω := by
    exact hD_open.preimage hq_cont
  have hcenterΩ :
      sourceOrientedMinkowskiInvariant d n z0 ∈ Ω := by
    have hq :
        qOfG (sourceOrientedMinkowskiInvariant d n z0) =
          (sourceSelectedComplexSymCoordFinEquiv n m hI)
            (sourceSelectedComplexGramMap d n m I z0) := by
      simpa [qOfG, m, sourceOrientedMinkowskiInvariant,
        SourceOrientedGramData.gram] using
        sourceSelectedComplexGramFlatCoordCLM_source d n m hI z0
    simpa [Ω, qOfG, m, hq] using hq0D
  refine
    { Ω := Ω
      Ω_open := hΩ_open
      center_mem := hcenterΩ
      toVec := fun G => sec (qOfG G)
      toVec_mem := ?_
      toVec_right_inv := ?_
      toVec_holomorphic := ?_ }
  · intro G hG
    exact hD_ET (qOfG G) hG
  · intro G hG
    let q := qOfG G
    have hqD : q ∈ D := hG.1
    have hGgram_var : G.gram ∈ sourceComplexGramVariety d n := by
      rcases hG.2 with ⟨w, rfl⟩
      exact ⟨w, by
        simp [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram]⟩
    have hsectionSel :
        sourceSelectedComplexGramMap d n m I (sec q) =
          (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
      simpa [sec, target, e, q, m] using
        sourceSelectedComplexGramZeroSectionAt_selectedGram d n hI hJ hminor q
          (hD_target q hqD)
    have hGselSubtype :
        (⟨sourceSelectedComplexGramCoord n m I G.gram, by
          rcases hGgram_var with ⟨z, hz⟩
          rw [← hz]
          intro a b
          simp [sourceSelectedComplexGramCoord_apply,
            sourceMinkowskiGram_symm d n z (I a) (I b)]⟩ :
          sourceSelectedComplexSymCoordSubspace n m I) =
          (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
      exact sourceSelectedComplexGramCoord_eq_of_flatCoord_eq d n m hI hGgram_var rfl
    have hsel :
        sourceSelectedComplexGramCoord n m I
            (sourceMinkowskiGram d n (sec q)) =
          sourceSelectedComplexGramCoord n m I G.gram := by
      have hleft := congrArg Subtype.val hsectionSel
      have hright := congrArg Subtype.val hGselSubtype
      exact hleft.trans hright.symm
    have hgram :
        sourceMinkowskiGram d n (sec q) = G.gram :=
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
        d n hI (hD_minor q hqD) hGgram_var hsel
    apply SourceOrientedGramData.ext
    · simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
        q, sec]
        using hgram
    · funext ι
      have hle : d + 1 ≤ n := by
        simpa using Fintype.card_le_of_embedding ι
      exact False.elim (by omega)
  · have hsection_diff :
        DifferentiableOn ℂ sec D := by
      simpa [sec, target, e, m] using
        sourceSelectedComplexGramZeroSectionAt_differentiableOn d n hI hJ hminor
          hD_target hD_invertible
    have hq_diff : Differentiable ℂ qOfG := by
      have hgram_diff :
          Differentiable ℂ (fun G : SourceOrientedGramData d n => G.gram) := by
        change Differentiable ℂ (fun G : SourceOrientedGramData d n => G.1)
        exact differentiable_fst
      exact (sourceSelectedComplexGramFlatCoordCLM n m I).differentiable.comp hgram_diff
    exact hsection_diff.comp hq_diff.differentiableOn (by
      intro G hG
      exact hG)

end BHW
