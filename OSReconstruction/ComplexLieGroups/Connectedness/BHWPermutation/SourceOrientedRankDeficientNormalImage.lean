import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientCanonical
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurParameter

/-!
# Normal-parameter images in the oriented source variety

The rank-deficient local-image producer works with parameterized maps into the
oriented source variety subtype.  This file packages the checked normal
Schur/residual parameter map in that subtype-valued form and transports it back
from the canonical Lemma-3 source point to the original exceptional point using
the variety-relative normal-form transport.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The normal Schur/residual parameter map, valued in the oriented source
variety subtype. -/
noncomputable def sourceOrientedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    SourceOrientedVariety d n :=
  ⟨sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p),
    ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩⟩

@[simp]
theorem sourceOrientedNormalParameterVarietyPoint_val
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1 =
      sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p) :=
  rfl

/-- The normal-parameter source-variety map is continuous. -/
theorem continuous_sourceOrientedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn) := by
  apply Continuous.subtype_mk
  exact
    (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).comp
      (continuous_sourceOrientedNormalParameterVector d n r hrD hrn)

/-- At the center parameter, the subtype-valued normal image is the canonical
Lemma-3 source point. -/
@[simp]
theorem sourceOrientedNormalParameterVarietyPoint_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterVarietyPoint d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      hwLemma3CanonicalSourceOrientedVariety d n r := by
  apply Subtype.ext
  simp [sourceOrientedNormalParameterVarietyPoint,
    hwLemma3CanonicalSourceOrientedVariety,
    sourceOrientedNormalParameterVector_center]

/-- Principal Schur head block associated to a normal parameter. -/
noncomputable def sourceOrientedNormalParameterSchurHead
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin r) (Fin r) ℂ :=
  p.head * sourceHeadMetric d r hrD * p.headᵀ

/-- Principal Schur mixed block associated to a normal parameter, in the
head/tail orientation used by `sourcePrincipalSchurGraph`. -/
noncomputable def sourceOrientedNormalParameterSchurMixed
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin r) (Fin (n - r)) ℂ :=
  (p.mixed * sourceOrientedNormalParameterSchurHead d n r hrD hrn p)ᵀ

/-- Principal Schur residual block associated to a normal parameter. -/
noncomputable def sourceOrientedNormalParameterSchurTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
  Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  sourceShiftedTailGram d r hrD (n - r) p.tail

/-- Maximal rank for the shifted residual-tail oriented datum: the ordinary
tail Gram has maximal possible rank in the residual spacetime dimension. -/
def SourceShiftedTailOrientedMaxRankAt
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (T : SourceShiftedTailOrientedData d r hrD m) : Prop :=
  sourceGramMatrixRank m T.gram = min (d + 1 - r) m

/-- Each coordinate of the padded tail embedding is continuous in the tail
coordinate vector. -/
theorem continuous_sourceTailEmbed_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (μ : Fin (d + 1)) :
    Continuous (fun q : Fin (d + 1 - r) → ℂ =>
      sourceTailEmbed d r hrD q μ) := by
  unfold sourceTailEmbed
  split
  · fun_prop
  · fun_prop

/-- The shifted tail Gram map is continuous in finite tail coordinates. -/
theorem continuous_sourceShiftedTailGram
    (d r m : ℕ)
    (hrD : r < d + 1) :
    Continuous (sourceShiftedTailGram d r hrD m) := by
  unfold sourceShiftedTailGram sourceVectorMinkowskiInner
  apply continuous_pi
  intro u
  apply continuous_pi
  intro v
  refine continuous_finset_sum _ ?_
  intro μ _
  have hu : Continuous (fun q : Fin m → Fin (d + 1 - r) → ℂ =>
      sourceTailEmbed d r hrD (q u) μ) :=
    (continuous_sourceTailEmbed_apply d r hrD μ).comp (continuous_apply u)
  have hv : Continuous (fun q : Fin m → Fin (d + 1 - r) → ℂ =>
      sourceTailEmbed d r hrD (q v) μ) :=
    (continuous_sourceTailEmbed_apply d r hrD μ).comp (continuous_apply v)
  fun_prop

/-- The normal-parameter Schur head block is continuous. -/
theorem continuous_sourceOrientedNormalParameterSchurHead
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterSchurHead d n r hrD hrn) := by
  unfold sourceOrientedNormalParameterSchurHead
  have hh := continuous_sourceOrientedNormalParameter_head
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  fun_prop

/-- The normal-parameter Schur mixed block is continuous. -/
theorem continuous_sourceOrientedNormalParameterSchurMixed
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterSchurMixed d n r hrD hrn) := by
  unfold sourceOrientedNormalParameterSchurMixed
  have hm := continuous_sourceOrientedNormalParameter_mixed
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have hhead := continuous_sourceOrientedNormalParameterSchurHead d n r hrD hrn
  fun_prop

/-- The normal-parameter Schur residual-tail block is continuous. -/
theorem continuous_sourceOrientedNormalParameterSchurTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterSchurTail d n r hrD hrn) := by
  unfold sourceOrientedNormalParameterSchurTail
  exact (continuous_sourceShiftedTailGram d r (n - r) hrD).comp
    (continuous_sourceOrientedNormalParameter_tail
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn))

/-- On the invertible-head part of normal-parameter space, the ordinary Gram
coordinate of the normal image is the principal Schur graph with residual
`sourceShiftedTailGram`. -/
theorem sourceOrientedNormalParameterVarietyPoint_gram_sourcePrincipalSchurGraph
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1.gram =
      sourcePrincipalSchurGraph n (sourceHeadTailEquiv n r hrn)
        (sourceOrientedNormalParameterSchurHead d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurTail d n r hrD hrn p) := by
  let A : Matrix (Fin r) (Fin r) ℂ :=
    p.head * sourceHeadMetric d r hrD * p.headᵀ
  have hA : IsUnit A.det := by
    change IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det
    have hη : IsUnit (sourceHeadMetric d r hrD).det :=
      sourceHeadMetric_det_isUnit d r hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hH
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  have hcancel :
      (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ)) *
          (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹ = p.mixed := by
    calc
      (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ)) *
          (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹
          = p.mixed * ((p.head * sourceHeadMetric d r hrD * p.headᵀ) *
              (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹) := by
                rw [Matrix.mul_assoc]
      _ = p.mixed * (1 : Matrix (Fin r) (Fin r) ℂ) := by
            rw [Matrix.mul_nonsing_inv _ hA]
      _ = p.mixed := by rw [Matrix.mul_one]
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn a))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn b)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceHeadTailEquiv_apply_tail, sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn a))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn v)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_head_tailParameterVector]
      rw [sourceHeadMetric_transpose]
      simp [Matrix.mul_assoc]
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceHeadTailEquiv_apply_tail, sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn u))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn b)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_tailParameterVector_head]
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_tail,
        sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn u))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn v)) = _
      rw [sourceVectorMinkowskiInner_tailParameterVector_tail]
      rw [hcancel]
      rw [sourceHeadMetric_transpose]
      simp [sourceShiftedTailGram, Matrix.mul_assoc]
      abel

/-- Full oriented-data form of the principal Schur graph equality.  The
determinant coordinate is retained from the already-realized normal parameter,
while the ordinary Gram coordinate is exposed as a Schur graph. -/
theorem sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1 =
      ((sourcePrincipalSchurGraph n (sourceHeadTailEquiv n r hrn)
        (sourceOrientedNormalParameterSchurHead d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurTail d n r hrD hrn p),
        (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1.det) :
          SourceOrientedGramData d n) := by
  apply Prod.ext
  · exact
      sourceOrientedNormalParameterVarietyPoint_gram_sourcePrincipalSchurGraph
        d n r hrD hrn p hH
  · rfl

/-- On the invertible-head normal-parameter locus, max-rank of the full
normal image is exactly max-rank of the shifted residual tail. -/
theorem sourceOrientedNormalParameterVector_maxRank_iff_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) ↔
      SourceShiftedTailOrientedMaxRankAt d r hrD (n - r)
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail) := by
  rw [show sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p) =
        (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1 by rfl]
  rw [sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph
    d n r hrD hrn p hH]
  have hA : IsUnit
      (sourceOrientedNormalParameterSchurHead d n r hrD hrn p).det := by
    change IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det
    have hη : IsUnit (sourceHeadMetric d r hrD).det :=
      sourceHeadMetric_det_isUnit d r hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hH
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  have hAsym :
      (sourceOrientedNormalParameterSchurHead d n r hrD hrn p)ᵀ =
        sourceOrientedNormalParameterSchurHead d n r hrD hrn p := by
    exact sourceNormalHeadGram_transpose d n r hrD hrn p
  have hSsym :
      (sourceOrientedNormalParameterSchurTail d n r hrD hrn p)ᵀ =
        sourceOrientedNormalParameterSchurTail d n r hrD hrn p := by
    ext u v
    simp [sourceOrientedNormalParameterSchurTail, sourceShiftedTailGram,
      sourceVectorMinkowskiInner_comm]
  have hrmin : Fintype.card (Fin r) ≤ min (d + 1) n := by
    exact le_min (by simpa using Nat.le_of_lt hrD) (by simpa using hrn)
  have hiff :=
    sourcePrincipalSchurGraph_sourceGramMatrixRank_eq_iff_residual_rank
      n (min (d + 1) n) (sourceHeadTailEquiv n r hrn)
      (A := sourceOrientedNormalParameterSchurHead d n r hrD hrn p)
      (B := sourceOrientedNormalParameterSchurMixed d n r hrD hrn p)
      (S := sourceOrientedNormalParameterSchurTail d n r hrD hrn p)
      hA hAsym hSsym hrmin
  have hmin_sub : min (d + 1) n - r = min (d + 1 - r) (n - r) := by
    rw [← Nat.sub_min_sub_right]
  simpa [SourceOrientedMaxRankAt, SourceShiftedTailOrientedMaxRankAt,
    SourceOrientedGramData.gram, sourceGramMatrixRank,
    sourceOrientedNormalParameterSchurTail, hmin_sub] using hiff

namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- The normal-parameter image transported from canonical normal form back to
the original exceptional source-variety point. -/
noncomputable def originalNormalVarietyPoint
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    SourceOrientedVariety d n :=
  N.varietyTransport.invFun
    (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)

@[simp]
theorem originalNormalVarietyPoint_val
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    (N.originalNormalVarietyPoint p).1 =
      (N.varietyTransport.invFun
        (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)).1 :=
  rfl

/-- The transported normal-parameter source-variety map is continuous. -/
theorem continuous_originalNormalVarietyPoint
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0) :
    Continuous N.originalNormalVarietyPoint :=
  N.varietyTransport.continuous_invFun.comp
    (continuous_sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)

/-- The transported normal image is centered at the original exceptional point. -/
theorem originalNormalVarietyPoint_center
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0) :
    (N.originalNormalVarietyPoint
      (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn)).1 = G0 := by
  rw [originalNormalVarietyPoint, sourceOrientedNormalParameterVarietyPoint_center]
  exact N.canonical_to_original

/-- Max-rank of the transported image is exactly max-rank of the canonical
normal-parameter image. -/
theorem originalNormalVarietyPoint_maxRank_iff
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1 ↔
      SourceOrientedMaxRankAt d n
        (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p).1 :=
  N.varietyTransport.invFun_maxRank_iff
    (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)

/-- On the invertible-head normal-parameter box, max-rank of the transported
original image is exactly full residual-tail rank in the shifted Schur
coordinate. -/
theorem originalNormalVarietyPoint_maxRank_iff_tail_rank
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
    (hH : IsUnit p.head.det) :
    SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1 ↔
      (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
        d + 1 - N.r := by
  rw [N.originalNormalVarietyPoint_maxRank_iff]
  rw [sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph
    d n N.r N.hrD N.hrn p hH]
  have hA : IsUnit
      (sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p).det := by
    change IsUnit (p.head * sourceHeadMetric d N.r N.hrD * p.headᵀ).det
    have hη : IsUnit (sourceHeadMetric d N.r N.hrD).det :=
      sourceHeadMetric_det_isUnit d N.r N.hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hH
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  have hAsym :
      (sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p)ᵀ =
        sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p := by
    exact sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p
  have hSsym :
      (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p)ᵀ =
        sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p := by
    ext u v
    simp [sourceOrientedNormalParameterSchurTail, sourceShiftedTailGram,
      sourceVectorMinkowskiInner_comm]
  have hrDle : Fintype.card (Fin N.r) ≤ d + 1 := by
    simpa using Nat.le_of_lt N.hrD
  simpa using
    (sourceOrientedMaxRankAt_sourcePrincipalSchurGraph_iff_residual_rank
      (d := d) (n := n) hn (sourceHeadTailEquiv n N.r N.hrn)
      (A := sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p)
      (B := sourceOrientedNormalParameterSchurMixed d n N.r N.hrD N.hrn p)
      (S := sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p)
      hA hAsym hSsym hrDle
      (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p).1.det)

/-- On any parameter box already contained in the invertible-head locus, the
max-rank preimage of the transported normal image is exactly the residual-tail
exact-rank slice. -/
theorem parameterBox_maxRank_preimage_eq_tailRank
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (hhead :
      parameterBox ⊆
        {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
          IsUnit p.head.det}) :
    parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1} =
      parameterBox ∩
        {p |
          (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
            d + 1 - N.r} := by
  ext p
  constructor
  · rintro ⟨hp, hmax⟩
    exact ⟨hp, (N.originalNormalVarietyPoint_maxRank_iff_tail_rank
      hn p (hhead hp)).1 hmax⟩
  · rintro ⟨hp, hrank⟩
    exact ⟨hp, (N.originalNormalVarietyPoint_maxRank_iff_tail_rank
      hn p (hhead hp)).2 hrank⟩

end SourceOrientedRankDeficientAlgebraicNormalFormData

end BHW
