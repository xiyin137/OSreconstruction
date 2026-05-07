import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalRealization
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameterBall
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWAdaptedTubeRepresentative

/-!
# Tube-valued rank-deficient residual polydiscs

This file records the corrected interface between the rank-deficient
normal-form Schur construction and the local-realization layer.  The hard
Hall-Wightman input is a tube-valued residual polydisc whose image, ambient
open set, surjectivity, and max-rank-density fields are already expressed in
the original oriented invariant coordinates.

In particular, the reduction below does not apply an ambient
`SourceOrientedInvariantTransportEquiv` to source-matrix normal-form
coordinates.  Source changes are represented only through actual source
tuples and the variety-relative transport interface.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Source-label linear changes are continuous in the source tuple. -/
theorem continuous_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (sourceTupleLinearChange d n M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  refine continuous_finset_sum _ ?_
  intro a _ha
  exact continuous_const.mul
    ((continuous_apply μ).comp (continuous_apply a))

/-- Source-level normal-form data for the rank-deficient extended-tube
residual chart.

The canonical normal source `normalBase` is kept separate from the
extended-tube representative `adaptedBase`.  The map `toOriginal` is the only
route back to original source tuples; tube membership for nearby residual
vectors is not inferred from the variety transport and is supplied by the
residual-polydisc data below. -/
structure SourceOrientedRankDeficientNormalFormData
    (d n : ℕ)
    (z0 : Fin n → Fin (d + 1) → ℂ) where
  r : ℕ
  hrD : r < d + 1
  hrn : r ≤ n
  adaptedBase : Fin n → Fin (d + 1) → ℂ
  adaptedBase_mem : adaptedBase ∈ ExtendedTube d n
  adaptedBase_same_oriented :
    sourceOrientedMinkowskiInvariant d n adaptedBase =
      sourceOrientedMinkowskiInvariant d n z0
  normalBase : Fin n → Fin (d + 1) → ℂ
  normalBase_eq : normalBase = hwLemma3CanonicalSource d n r
  varietyTransport : SourceOrientedVarietyTransportEquiv d n
  toOriginal :
    (Fin n → Fin (d + 1) → ℂ) →
      Fin n → Fin (d + 1) → ℂ
  toOriginal_continuous : Continuous toOriginal
  toOriginal_normalBase_eq_adaptedBase :
    toOriginal normalBase = adaptedBase
  toOriginal_normalBase_invariant :
    sourceOrientedMinkowskiInvariant d n (toOriginal normalBase) =
      sourceOrientedMinkowskiInvariant d n z0
  toOriginal_oriented :
    ∀ z,
      sourceTupleOrientedVarietyPoint d n (toOriginal z) =
        varietyTransport.invFun (sourceTupleOrientedVarietyPoint d n z)

namespace SourceOrientedRankDeficientNormalFormData

/-- Build source-level normal-form data from an explicit invertible source
matrix and Lorentz transformation that send the adapted base tuple to the
canonical Lemma-3 source.

The inverse return map is the actual source-tuple map
`M⁻¹` after `Λ⁻¹`; the associated invariant transport is only the checked
variety-relative source-matrix transport. -/
noncomputable def ofSourceMatrixLorentz
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {adaptedBase : Fin n → Fin (d + 1) → ℂ}
    (hadaptedBase_mem : adaptedBase ∈ ExtendedTube d n)
    (hadaptedBase_same_oriented :
      sourceOrientedMinkowskiInvariant d n adaptedBase =
        sourceOrientedMinkowskiInvariant d n z0)
    {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    (Λ : ComplexLorentzGroup d)
    (hcanonical :
      complexLorentzAction Λ (sourceTupleLinearChange d n M adaptedBase) =
        hwLemma3CanonicalSource d n r) :
    SourceOrientedRankDeficientNormalFormData d n z0 where
  r := r
  hrD := hrD
  hrn := hrn
  adaptedBase := adaptedBase
  adaptedBase_mem := hadaptedBase_mem
  adaptedBase_same_oriented := hadaptedBase_same_oriented
  normalBase := hwLemma3CanonicalSource d n r
  normalBase_eq := rfl
  varietyTransport :=
    sourceOrientedVarietySourceMatrixTransportEquivOfMatrix d n M hM
  toOriginal := fun z =>
    sourceTupleLinearChange d n M⁻¹ (complexLorentzAction Λ⁻¹ z)
  toOriginal_continuous :=
    (continuous_sourceTupleLinearChange d n M⁻¹).comp
      (continuous_complexLorentzAction_snd (d := d) (n := n) Λ⁻¹)
  toOriginal_normalBase_eq_adaptedBase := by
    rw [← hcanonical]
    rw [complexLorentzAction_inv]
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.nonsing_inv_mul (A := M) hM]
    exact sourceTupleLinearChange_one d n adaptedBase
  toOriginal_normalBase_invariant := by
    rw [← hcanonical]
    rw [complexLorentzAction_inv]
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.nonsing_inv_mul (A := M) hM]
    rw [sourceTupleLinearChange_one]
    exact hadaptedBase_same_oriented
  toOriginal_oriented := by
    intro z
    apply Subtype.ext
    dsimp [sourceTupleOrientedVarietyPoint,
      SourceOrientedVarietyTransportEquiv.invFun,
      sourceOrientedVarietySourceMatrixTransportEquivOfMatrix,
      sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix,
      sourceOrientedGramVarietySourceMatrixEquivOfMatrix,
      sourceOrientedGramVarietySourceMatrixMap]
    rw [sourceOrientedMinkowskiInvariant_sourceTupleLinearChange]
    rw [sourceOrientedMinkowskiInvariant_complexLorentzAction]

/-- Existence of source-level normal-form data from an already adapted
extended-tube representative.

This theorem packages the checked finite Schur normal-form algebra and the
checked Lorentz/Witt normalization.  It deliberately assumes the adapted
extended-tube representative as input; proving that representative exists is
the separate Hall-Wightman Lemma-3 adapted-representative target. -/
theorem exists_ofAdaptedBase
    (d n : ℕ)
    {z0 adaptedBase : Fin n → Fin (d + 1) → ℂ}
    (hadaptedBase_mem : adaptedBase ∈ ExtendedTube d n)
    (hadaptedBase_same_oriented :
      sourceOrientedMinkowskiInvariant d n adaptedBase =
        sourceOrientedMinkowskiInvariant d n z0)
    (hrank_lt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n adaptedBase) < d + 1)
    (hadapted :
      Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d n adaptedBase)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n adaptedBase)) :
    ∃ N : SourceOrientedRankDeficientNormalFormData d n z0,
      N.adaptedBase = adaptedBase := by
  classical
  let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n adaptedBase
  let r : ℕ := sourceGramMatrixRank n G
  have hrD : r < d + 1 := by
    simpa [r, G] using hrank_lt
  have hrn : r ≤ n := by
    simpa [r, G] using sourceGramMatrixRank_le_arity n G
  have hGsym : G ∈ sourceSymmetricMatrixSpace n := by
    intro i j
    exact sourceMinkowskiGram_symm d n adaptedBase i j
  have hGrank : (Matrix.of fun i j : Fin n => G i j).rank = r := by
    change sourceGramMatrixRank n G = r
    rfl
  rcases exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
      (n := n) (r := r) (Z := G) hGsym hGrank with
    ⟨I, hI, hminor⟩
  rcases exists_sourcePermutation_movingPrincipalBlockToHead
      n r hrn hI with
    ⟨σ, hσ⟩
  let Gp : Fin n → Fin n → ℂ := sourcePermuteComplexGram n σ G
  have hGpsym : Gp ∈ sourceSymmetricMatrixSpace n :=
    sourcePermuteComplexGram_mem_sourceSymmetricMatrixSpace n σ hGsym
  let A : Matrix (Fin r) (Fin r) ℂ := sourceHeadHeadBlock n r hrn Gp
  let B : Matrix (Fin (n - r)) (Fin r) ℂ := sourceTailHeadBlock n r hrn Gp
  let C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
    sourceTailTailBlock n r hrn Gp
  have hBlock :
      sourcePermuteComplexGram n σ G = sourceBlockMatrix n r hrn A B C := by
    simpa [Gp, A, B, C] using
      (sourceBlockMatrix_of_headTailBlocks n r hrn Gp hGpsym).symm
  have hA_det_eq : A.det = sourceMatrixMinor n r I I G := by
    change Matrix.det (sourceHeadHeadBlock n r hrn Gp) =
      sourceMatrixMinor n r I I G
    have hmat :
        sourceHeadHeadBlock n r hrn Gp =
          fun a b : Fin r => G (I a) (I b) := by
      ext a b
      simp [sourceHeadHeadBlock, Gp, sourcePermuteComplexGram, hσ a, hσ b]
    rw [hmat]
    rfl
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hA_det_eq]
    exact hminor
  have hAsym : A.transpose = A := by
    simpa [A] using
      sourceHeadHeadBlock_symm_of_sourceSymmetric n r hrn hGpsym
  have hRankGp : sourceGramMatrixRank n Gp = r := by
    simpa [Gp, r] using
      sourceGramMatrixRank_sourcePermuteComplexGram n σ G
  have hSchur : C - B * A⁻¹ * B.transpose = 0 := by
    exact hwLemma3_schurComplement_eq_zero_of_rank_eq
      n r hrn hGpsym hBlock hRankGp hA
  rcases complexSymmetric_invertible_congruence_to_sourceHeadMetric
      d r hrD hAsym hA with
    ⟨P, hPunit, hP⟩
  let M : Matrix (Fin n) (Fin n) ℂ :=
    hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P
  have hMunit : IsUnit M.det := by
    simpa [M] using
      hwLemma3_normalFormSourceChangeMatrix_det_isUnit
        n r hrn σ hA hPunit
  have hGram :
      sourceGramCongruence n M G =
        hwLemma3CanonicalGram d n r hrD hrn := by
    simpa [M, Gp, A, B, C] using
      hwLemma3_normalFormSourceChangeMatrix_canonicalGram
        d n r hrD hrn hBlock hA hAsym hSchur hP
  rcases
      hwLemma3_normalFormSourceChange_exists_complexLorentz_to_canonicalSource_of_adapted
        d n r hrD hrn (σ := σ) (A := A) (B := B) (P := P)
        hA hPunit hGram (by simpa [G] using hadapted) with
    ⟨Λ, hΛ⟩
  refine
    ⟨SourceOrientedRankDeficientNormalFormData.ofSourceMatrixLorentz
      (d := d) (n := n) (z0 := z0) r hrD hrn
      hadaptedBase_mem hadaptedBase_same_oriented hMunit Λ
      (by simpa [M] using hΛ), rfl⟩

/-- Existence of source-level rank-deficient normal-form data from an original
extended-tube tuple.  The adapted representative is produced inside the
ordinary extended tube before the source-matrix/Lorentz normal-form transport
is assembled. -/
theorem exists_ofExtendedTube
    [NeZero d]
    (hd : 2 ≤ d)
    {n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hlow :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    ∃ N : SourceOrientedRankDeficientNormalFormData d n z0,
      N.adaptedBase ∈ ExtendedTube d n := by
  classical
  let G0 : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
  have hrank_lt :
      sourceGramMatrixRank n G0 < d + 1 :=
    sourceOriented_notMaxRank_sourceGramMatrixRank_lt_fullFrame
      d n z0 hlow
  rcases hwLemma3_extendedTube_adaptedRankRepresentative
      (d := d) hd hz0 with
    ⟨adaptedBase, hadapted_mem, hadapted_gram, hadapted_span⟩
  have hadapted_rank_lt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n adaptedBase) < d + 1 := by
    simpa [G0, hadapted_gram] using hrank_lt
  have hadapted_oriented :
      sourceOrientedMinkowskiInvariant d n adaptedBase =
        sourceOrientedMinkowskiInvariant d n z0 :=
    sourceOrientedMinkowskiInvariant_eq_of_sameGram_rank_lt
      (d := d) n hadapted_gram hadapted_rank_lt
  have hadapted_span' :
      Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d n adaptedBase)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n adaptedBase) := by
    simpa [hadapted_gram] using hadapted_span
  rcases exists_ofAdaptedBase
      d n hadapted_mem hadapted_oriented
      hadapted_rank_lt hadapted_span' with
    ⟨N, _hN_adapted⟩
  exact ⟨N, N.adaptedBase_mem⟩

/-- Forget the extended-tube return map and keep the checked algebraic
normal-image transport carried by the same normal-form packet. -/
noncomputable def toAlgebraicNormalFormData
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    SourceOrientedRankDeficientAlgebraicNormalFormData d n
      (sourceOrientedMinkowskiInvariant d n z0) where
  r := N.r
  hrD := N.hrD
  hrn := N.hrn
  varietyTransport := N.varietyTransport
  canonical_to_original := by
    have hcanon :
        sourceTupleOrientedVarietyPoint d n N.normalBase =
          hwLemma3CanonicalSourceOrientedVariety d n N.r := by
      rw [N.normalBase_eq]
      rfl
    calc
      (N.varietyTransport.invFun
          (hwLemma3CanonicalSourceOrientedVariety d n N.r)).1 =
          (N.varietyTransport.invFun
            (sourceTupleOrientedVarietyPoint d n N.normalBase)).1 := by
            rw [hcanon]
      _ =
          sourceOrientedMinkowskiInvariant d n
            (N.toOriginal N.normalBase) := by
            exact (congrArg Subtype.val
              (N.toOriginal_oriented N.normalBase)).symm
      _ = sourceOrientedMinkowskiInvariant d n z0 :=
          N.toOriginal_normalBase_invariant

@[simp]
theorem toAlgebraicNormalFormData_r
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    N.toAlgebraicNormalFormData.r = N.r :=
  rfl

@[simp]
theorem toAlgebraicNormalFormData_varietyTransport
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    N.toAlgebraicNormalFormData.varietyTransport = N.varietyTransport :=
  rfl

/-- The algebraic transported normal image attached to a tube normal-form
packet is the actual original-coordinate invariant of the returned source
tuple. -/
theorem originalNormalVarietyPoint_eq_toOriginal
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    (N.toAlgebraicNormalFormData.originalNormalVarietyPoint p).1 =
      sourceOrientedMinkowskiInvariant d n
        (N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p)) := by
  have h :=
    congrArg Subtype.val
      (N.toOriginal_oriented
        (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p))
  simpa [toAlgebraicNormalFormData, sourceOrientedNormalParameterVarietyPoint,
    sourceTupleOrientedVarietyPoint] using h.symm

/-- For the actual original-coordinate normal image, max-rank is exactly
max-rank of the shifted residual tail, provided the head factor is invertible. -/
theorem toOriginal_normalParameterVector_maxRank_iff_tail
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
    (hH : IsUnit p.head.det) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p))) ↔
      SourceShiftedTailOrientedMaxRankAt d N.r N.hrD (n - N.r)
        (sourceShiftedTailOrientedInvariant d N.r N.hrD (n - N.r) p.tail) := by
  rw [← N.originalNormalVarietyPoint_eq_toOriginal p]
  rw [N.toAlgebraicNormalFormData.originalNormalVarietyPoint_maxRank_iff p]
  exact
    sourceOrientedNormalParameterVector_maxRank_iff_tail
      d n N.r N.hrD N.hrn p hH

/-- The actual returned normal-parameter source tuple is centered at the
adapted extended-tube representative. -/
theorem toOriginal_normalParameterVector_center
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    N.toOriginal
        (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
          (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn)) =
      N.adaptedBase := by
  rw [sourceOrientedNormalParameterVector_center]
  rw [← N.normalBase_eq]
  exact N.toOriginal_normalBase_eq_adaptedBase

/-- The returned normal-parameter source tuple is continuous in the normal
parameter. -/
theorem continuous_toOriginal_normalParameterVector
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn =>
        N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p)) :=
  N.toOriginal_continuous.comp
    (continuous_sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn)

/-- The original-coordinate invariant of the returned normal-parameter tuple
is continuous. -/
theorem continuous_originalNormalInvariant
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    Continuous
      (fun p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn =>
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p))) :=
  (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).comp
    N.continuous_toOriginal_normalParameterVector

/-- The normal-parameter preimage of the extended tube is a neighborhood of
the normal center after returning to original source coordinates. -/
theorem toOriginal_normalParameterVector_mem_ET_mem_nhds_center
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
      N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p) ∈
        ExtendedTube d n} ∈
      𝓝 (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn) := by
  have hcenter :
      N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn)) ∈
        ExtendedTube d n := by
    rw [N.toOriginal_normalParameterVector_center]
    exact N.adaptedBase_mem
  exact
    N.continuous_toOriginal_normalParameterVector.continuousAt
      ((isOpen_extendedTube (d := d) (n := n)).mem_nhds hcenter)

/-- Choose a positive normal-parameter ball on which the returned source
tuples remain in the extended tube. -/
theorem exists_normalParameterBall_toOriginal_mem_ET
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p) ∈
              ExtendedTube d n} :=
  exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
    d n N.r N.hrD N.hrn
    N.toOriginal_normalParameterVector_mem_ET_mem_nhds_center

end SourceOrientedRankDeficientNormalFormData

/-- Compact residual-polydisc data in normal source coordinates, with all
image and density statements already returned in the original oriented
invariant coordinates.

The field `toOriginal_residualVector_mem_ET` is the analytic tube-stability
input.  The fields `Ω`, `originalInvariant_mem`, `image_surj`, and
`maxRank_dense_original` are deliberately original-coordinate statements, so
the chart assembly below is purely mechanical. -/
structure SourceOrientedResidualPolydiscData
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) where
  m : ℕ
  c0 : Fin m → ℂ
  K : Set (Fin m → ℂ)
  P : Set (Fin m → ℂ)
  K_compact : IsCompact K
  P_open : IsOpen P
  P_subset_K : P ⊆ K
  c0_mem : c0 ∈ P
  residualVector :
    (Fin m → ℂ) → Fin n → Fin (d + 1) → ℂ
  residualVector_continuousOn :
    ContinuousOn residualVector K
  residualVector_c0 :
    residualVector c0 = N.normalBase
  toOriginal_residualVector_mem_ET :
    ∀ c, c ∈ K →
      N.toOriginal (residualVector c) ∈ ExtendedTube d n
  Ω : Set (SourceOrientedGramData d n)
  Ω_open : IsOpen Ω
  Ω_center :
    sourceOrientedMinkowskiInvariant d n z0 ∈ Ω
  originalInvariant_mem :
    ∀ c, c ∈ K →
      sourceOrientedMinkowskiInvariant d n
        (N.toOriginal (residualVector c)) ∈
        Ω ∩ sourceOrientedGramVariety d n
  image_surj :
    Ω ∩ sourceOrientedGramVariety d n ⊆
      (fun c =>
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal (residualVector c))) '' P
  maxRank_dense_original :
    ∀ c, c ∈ P →
      sourceOrientedMinkowskiInvariant d n
          (N.toOriginal (residualVector c)) ∈
        closure
          ((fun c' =>
            sourceOrientedMinkowskiInvariant d n
              (N.toOriginal (residualVector c'))) ''
            {c' | c' ∈ P ∧
              SourceOrientedMaxRankAt d n
                (sourceOrientedMinkowskiInvariant d n
                  (N.toOriginal (residualVector c')))})

namespace SourceOrientedResidualPolydiscData

/-- A corrected residual polydisc directly assembles the residual chart
expected by the local-realization layer. -/
noncomputable def to_residualChart
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {N : SourceOrientedRankDeficientNormalFormData d n z0}
    (D : SourceOrientedResidualPolydiscData d n N)
    (hz0 : z0 ∈ ExtendedTube d n) :
    SourceOrientedRankDeficientResidualChartData d n z0 where
  m := D.m
  Ω := D.Ω
  Ω_open := D.Ω_open
  center_mem_ET := hz0
  K := D.K
  K_compact := D.K_compact
  P := D.P
  P_open := D.P_open
  P_subset_K := D.P_subset_K
  c0 := D.c0
  c0_mem := D.c0_mem
  toVec := fun c => N.toOriginal (D.residualVector c)
  toVec_continuousOn :=
    N.toOriginal_continuous.comp_continuousOn D.residualVector_continuousOn
  toVec_mem := by
    intro c hc
    exact D.toOriginal_residualVector_mem_ET c hc
  toVec_c0_invariant := by
    simpa [D.residualVector_c0] using N.toOriginal_normalBase_invariant
  toInv_eq := by
    intro c hc
    exact D.originalInvariant_mem c hc
  image_surj := by
    intro G hG
    exact D.image_surj hG
  maxRank_dense_parameters := by
    intro c hc
    exact D.maxRank_dense_original c hc

end SourceOrientedResidualPolydiscData

/-- Field accessor for the tube-stability part of a corrected residual
polydisc. -/
theorem sourceOriented_residualPolydisc_tubeStability
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (D : SourceOrientedResidualPolydiscData d n N) :
    ∀ c, c ∈ D.K →
      N.toOriginal (D.residualVector c) ∈ ExtendedTube d n :=
  D.toOriginal_residualVector_mem_ET

/-- Field accessor for the original-coordinate image-surjectivity part of a
corrected residual polydisc. -/
theorem sourceOriented_residualPolydisc_imageSurj
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (D : SourceOrientedResidualPolydiscData d n N) :
    ∃ Ω : Set (SourceOrientedGramData d n),
      IsOpen Ω ∧
        sourceOrientedMinkowskiInvariant d n z0 ∈ Ω ∧
        (∀ c, c ∈ D.K →
          sourceOrientedMinkowskiInvariant d n
            (N.toOriginal (D.residualVector c)) ∈
            Ω ∩ sourceOrientedGramVariety d n) ∧
        Ω ∩ sourceOrientedGramVariety d n ⊆
          (fun c =>
            sourceOrientedMinkowskiInvariant d n
              (N.toOriginal (D.residualVector c))) '' D.P :=
  ⟨D.Ω, D.Ω_open, D.Ω_center, D.originalInvariant_mem, D.image_surj⟩

/-- Field accessor for the original-coordinate max-rank-density part of a
corrected residual polydisc. -/
theorem sourceOriented_residualPolydisc_maxRankDense
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    (D : SourceOrientedResidualPolydiscData d n N) :
    ∀ c, c ∈ D.P →
      sourceOrientedMinkowskiInvariant d n
          (N.toOriginal (D.residualVector c)) ∈
        closure
          ((fun c' =>
            sourceOrientedMinkowskiInvariant d n
              (N.toOriginal (D.residualVector c'))) ''
            {c' | c' ∈ D.P ∧
              SourceOrientedMaxRankAt d n
                (sourceOrientedMinkowskiInvariant d n
                  (N.toOriginal (D.residualVector c')))}) :=
  D.maxRank_dense_original

/-- The corrected hard producer target for the rank-deficient branch: for
each rank-deficient extended-tube center, produce source-level normal-form
data and an original-coordinate tube residual polydisc. -/
def SourceOrientedRankDeficientTubeResidualPolydiscProducer
    (d n : ℕ) : Type :=
  ∀ {z0 : Fin n → Fin (d + 1) → ℂ},
    z0 ∈ ExtendedTube d n →
      ¬ SourceOrientedMaxRankAt d n
          (sourceOrientedMinkowskiInvariant d n z0) →
        Σ N : SourceOrientedRankDeficientNormalFormData d n z0,
          SourceOrientedResidualPolydiscData d n N

/-- A tube residual-polydisc producer is exactly strong enough to supply the
rank-deficient residual-chart producer consumed by
`SourceOrientedLocalRealization.lean`. -/
noncomputable def
    sourceOrientedRankDeficientResidualChartProducer_of_tubeResidualPolydiscProducer
    {d n : ℕ}
    (H : SourceOrientedRankDeficientTubeResidualPolydiscProducer d n) :
    SourceOrientedRankDeficientResidualChartProducer d n := by
  intro z0 hz0 hlow
  exact (H hz0 hlow).2.to_residualChart hz0

end BHW
