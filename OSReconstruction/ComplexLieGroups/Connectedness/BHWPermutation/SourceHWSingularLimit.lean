import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceFullComplexLorentzWitt

/-!
# Hall-Wightman singular-limit support

This file packages the low-rank Hall-Wightman two-curve contraction data and
proves the analytic limit consumer.  The hard geometry is the future producer
of the data; once the data are available, equality of the extended functions
is a continuity and Lorentz-invariance argument.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The singular alternative in Hall-Wightman Lemma 2, packaged as the
limiting data used by the analytic branch law.  Both endpoint configurations
have complex-Lorentz orbit curves in the ordinary extended tube, and both
curves converge to the same extended-tube base. -/
structure HWSameSourceGramSingularContractionData
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) where
  base : Fin n → Fin (d + 1) → ℂ
  curve_left : ℝ → Fin n → Fin (d + 1) → ℂ
  curve_right : ℝ → Fin n → Fin (d + 1) → ℂ
  base_mem : base ∈ ExtendedTube d n
  curve_left_mem : ∀ t, curve_left t ∈ ExtendedTube d n
  curve_right_mem : ∀ t, curve_right t ∈ ExtendedTube d n
  curve_left_tendsto_base : Tendsto curve_left atTop (nhds base)
  curve_right_tendsto_base : Tendsto curve_right atTop (nhds base)
  curve_left_orbit :
    ∀ t, ∃ Λ : ComplexLorentzGroup d, curve_left t = complexLorentzAction Λ z
  curve_right_orbit :
    ∀ t, ∃ Λ : ComplexLorentzGroup d, curve_right t = complexLorentzAction Λ w

/-- A complex subspace is totally isotropic for the source Minkowski pairing
when every two of its vectors pair to zero. -/
def ComplexMinkowskiTotallyIsotropicSubspace
    (d : ℕ)
    (R : Submodule ℂ (Fin (d + 1) → ℂ)) : Prop :=
  ∀ x y : R,
    sourceComplexMinkowskiInner d
      (x : Fin (d + 1) → ℂ)
      (y : Fin (d + 1) → ℂ) = 0

/-- If all vectors in a finite frame pair to zero, their span is a totally
isotropic subspace. -/
theorem complexMinkowskiTotallyIsotropic_span_range
    (d s : ℕ)
    (q : Fin s → Fin (d + 1) → ℂ)
    (hq_pair : ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (Submodule.span ℂ (Set.range q)) := by
  intro x y
  refine Submodule.span_induction ?hmem ?hzero ?hadd ?hsmul x.2
  · intro v hv
    rcases hv with ⟨c, rfl⟩
    refine Submodule.span_induction ?hmem_y ?hzero_y ?hadd_y ?hsmul_y y.2
    · intro u hu
      rcases hu with ⟨c', rfl⟩
      exact hq_pair c c'
    · simp [sourceComplexMinkowskiInner]
    · intro u v _ _ hu hv
      rw [sourceComplexMinkowskiInner_add_right, hu, hv, add_zero]
    · intro a u _ hu
      rw [sourceComplexMinkowskiInner_smul_right, hu, mul_zero]
  · simp [sourceComplexMinkowskiInner]
  · intro u v _ _ hu hv
    rw [sourceComplexMinkowskiInner_add_left, hu, hv, add_zero]
  · intro a u _ hu
    rw [sourceComplexMinkowskiInner_smul_left, hu, mul_zero]

/-- If each vector of a finite frame is orthogonal to `M`, every vector in
the span of that frame is orthogonal to `M`. -/
theorem span_frame_orthogonal_to_subspace
    (d s : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hq_orth :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (q c)
          (m : Fin (d + 1) → ℂ) = 0)
    {v : Fin (d + 1) → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range q)) :
    ∀ m : M,
      sourceComplexMinkowskiInner d v (m : Fin (d + 1) → ℂ) = 0 := by
  intro m
  refine Submodule.span_induction ?hmem ?hzero ?hadd ?hsmul hv
  · intro u hu
    rcases hu with ⟨c, rfl⟩
    exact hq_orth c m
  · simp [sourceComplexMinkowskiInner]
  · intro u v _ _ hu hv
    rw [sourceComplexMinkowskiInner_add_left, hu, hv, add_zero]
  · intro a u _ hu
    rw [sourceComplexMinkowskiInner_smul_left, hu, mul_zero]

/-- Hall-Wightman Lemma-2 low-rank normal form before taking the common
limit.  It records an initial Lorentz alignment of the left endpoint, a common
base plus finite totally isotropic residual frame, the dual frame used to
build the null-boost family, and the contracted orbit curves with their
extended-tube membership and convergence fields. -/
structure HWLowRankIsotropicNormalForm
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) where
  Λ0 : ComplexLorentzGroup d
  ξ : Fin n → Fin (d + 1) → ℂ
  s : ℕ
  aLeft : Fin n → Fin s → ℂ
  aRight : Fin n → Fin s → ℂ
  q : Fin s → Fin (d + 1) → ℂ
  qDual : Fin s → Fin (d + 1) → ℂ
  left_eq :
    complexLorentzAction Λ0 z =
      fun i => ξ i + ∑ c : Fin s, aLeft i c • q c
  right_eq :
    w = fun i => ξ i + ∑ c : Fin s, aRight i c • q c
  base_mem : ξ ∈ ExtendedTube d n
  q_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0
  qDual_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0
  q_dual :
    ∀ c c',
      sourceComplexMinkowskiInner d (q c) (qDual c') =
        if c = c' then (1 : ℂ) else 0
  q_orth :
    ∀ c i, sourceComplexMinkowskiInner d (q c) (ξ i) = 0
  qDual_orth :
    ∀ c i, sourceComplexMinkowskiInner d (qDual c) (ξ i) = 0
  contract : ℝ → ComplexLorentzGroup d
  contract_fix_ξ :
    ∀ t i, complexLorentzVectorAction (contract t) (ξ i) = ξ i
  contract_scale_q :
    ∀ t c,
      complexLorentzVectorAction (contract t) (q c) =
        ((Real.exp (-t) : ℝ) : ℂ) • q c
  contract_scale_qDual :
    ∀ t c,
      complexLorentzVectorAction (contract t) (qDual c) =
        ((Real.exp t : ℝ) : ℂ) • qDual c
  contracted_left_mem :
    ∀ t, complexLorentzAction (contract t * Λ0) z ∈ ExtendedTube d n
  contracted_right_mem :
    ∀ t, complexLorentzAction (contract t) w ∈ ExtendedTube d n
  contracted_left_tendsto :
    Tendsto
      (fun t : ℝ => complexLorentzAction (contract t * Λ0) z)
      atTop (nhds ξ)
  contracted_right_tendsto :
    Tendsto
      (fun t : ℝ => complexLorentzAction (contract t) w)
      atTop (nhds ξ)

/-- The low-rank normal form contains exactly the two orbit curves required by
the singular contraction-data API. -/
def HWLowRankIsotropicNormalForm.toContractionData
    {d n : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (N : HWLowRankIsotropicNormalForm d n z w) :
    HWSameSourceGramSingularContractionData d n z w where
  base := N.ξ
  curve_left := fun t => complexLorentzAction (N.contract t * N.Λ0) z
  curve_right := fun t => complexLorentzAction (N.contract t) w
  base_mem := N.base_mem
  curve_left_mem := N.contracted_left_mem
  curve_right_mem := N.contracted_right_mem
  curve_left_tendsto_base := N.contracted_left_tendsto
  curve_right_tendsto_base := N.contracted_right_tendsto
  curve_left_orbit := fun t => ⟨N.contract t * N.Λ0, rfl⟩
  curve_right_orbit := fun t => ⟨N.contract t, rfl⟩

/-- Public wrapper for converting a low-rank Hall-Wightman normal form into
the singular contraction data consumed by the analytic limit theorem. -/
def hw_lowRank_isotropicNormalForm_to_contractionData
    {d n : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    (N : HWLowRankIsotropicNormalForm d n z w) :
    HWSameSourceGramSingularContractionData d n z w :=
  N.toContractionData

/-- Once the Hall-Wightman singular contraction data are available, endpoint
value equality is a purely analytic limit argument: `extendF F` is continuous
on the extended tube, each contraction curve has constant value by complex
Lorentz invariance, and both curves converge to the same base point. -/
theorem hw_sameSourceGram_singularLimit_extendF_eq
    (d n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    (hsingular : HWSameSourceGramSingularContractionData d n z w) :
    extendF F z = extendF F w := by
  have hExtend_cont :
      ContinuousOn (extendF F) (ExtendedTube d n) :=
    (extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hleft_val :
      ∀ t, extendF F (hsingular.curve_left t) = extendF F z := by
    intro t
    rcases hsingular.curve_left_orbit t with ⟨Λ, hΛ⟩
    rw [hΛ]
    exact extendF_complexLorentzInvariant_of_cinv n F hF_cinv Λ z hz
  have hright_val :
      ∀ t, extendF F (hsingular.curve_right t) = extendF F w := by
    intro t
    rcases hsingular.curve_right_orbit t with ⟨Λ, hΛ⟩
    rw [hΛ]
    exact extendF_complexLorentzInvariant_of_cinv n F hF_cinv Λ w hw
  have hleft_lim :
      Tendsto
        (fun t : ℝ => extendF F (hsingular.curve_left t))
        atTop (nhds (extendF F hsingular.base)) :=
    (hExtend_cont.continuousWithinAt hsingular.base_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hsingular.curve_left_tendsto_base,
          Eventually.of_forall hsingular.curve_left_mem⟩)
  have hright_lim :
      Tendsto
        (fun t : ℝ => extendF F (hsingular.curve_right t))
        atTop (nhds (extendF F hsingular.base)) :=
    (hExtend_cont.continuousWithinAt hsingular.base_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hsingular.curve_right_tendsto_base,
          Eventually.of_forall hsingular.curve_right_mem⟩)
  have hz_lim :
      Tendsto (fun _ : ℝ => extendF F z)
        atTop (nhds (extendF F hsingular.base)) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall fun t => hleft_val t) hleft_lim
  have hw_lim :
      Tendsto (fun _ : ℝ => extendF F w)
        atTop (nhds (extendF F hsingular.base)) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall fun t => hright_val t) hright_lim
  have hz_base : extendF F z = extendF F hsingular.base :=
    tendsto_nhds_unique tendsto_const_nhds hz_lim
  have hw_base : extendF F w = extendF F hsingular.base :=
    tendsto_nhds_unique tendsto_const_nhds hw_lim
  exact hz_base.trans hw_base.symm

end BHW
