import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeSupport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurTailNormal

/-!
# Head-gauge normal-parameter data

The remaining Witt/head-normalization theorem must not merely assert that a
Schur residual tail lies on the shifted-tail variety.  It must identify the
source-variety point with a normal-parameter invariant whose head coordinate is
the local head-gauge factor.  This file records that exact data surface and
checks the mechanical consumers: residual-tail membership and the full Schur
residual packet.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Normal-parameter representative data matched to a local head gauge.

The hard geometric producer for this structure is the finite-dimensional
proper-complex Witt extension carrying the actual selected head frame to the
head-gauge frame, followed by the Schur decomposition of the remaining tail
vectors. -/
structure SourceOrientedHeadGaugeNormalParameterData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) where
  p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  invariant_eq :
    G =
      sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p)
  head_eq :
    Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
      p.head

/-- The normal parameter whose head coordinate is the local head-gauge factor
and whose mixed/tail coordinates are zero.  This is the target head frame used
before the transformed tail coordinates are chosen. -/
def sourceOrientedHeadGaugeHeadParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  mixed := 0
  tail := 0

@[simp]
theorem sourceOrientedHeadGaugeHeadParameter_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head).head =
      Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) := by
  rfl

/-- The local head gauge identifies the actual selected head Gram matrix with
the normal-form head Gram matrix of the gauge head frame. -/
theorem sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (a b : Fin r) :
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
      sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) b) := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hfactor :
      p0.head * sourceHeadMetric d r hrD * p0.headᵀ =
        sourceOrientedSchurHeadBlock n r hrn G := by
    simpa [Acoord, p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_gram Acoord hHead
  calc
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
        sourceOrientedSchurHeadBlock n r hrn G a b := by
          subst G
          rfl
    _ = (p0.head * sourceHeadMetric d r hrD * p0.headᵀ) a b := by
          rw [hfactor]
    _ = sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 a)
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 b) := by
          exact
            (sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector
              d n r hrD hrn p0 a b).symm

/-- The gauge normal head frame is linearly independent. -/
theorem sourceOriented_headGauge_normalHead_linearIndependent
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    LinearIndependent ℂ
      (fun a : Fin r =>
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) := by
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hp0_det : IsUnit p0.head.det := by
    simpa [p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_det_unit
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hη : IsUnit (sourceHeadMetric d r hrD).det :=
    sourceHeadMetric_det_isUnit d r hrD
  have hp0t : IsUnit p0.headᵀ.det :=
    Matrix.isUnit_det_transpose p0.head hp0_det
  have hheadGram :
      IsUnit (p0.head * sourceHeadMetric d r hrD * p0.headᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hp0_det.mul hη).mul hp0t
  have hA :
      IsUnit
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p0))).det := by
    rw [sourceOrientedSchurHeadBlock_normalParameter]
    exact hheadGram
  have hLI :=
    sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
      d n r hrn
      (sourceOrientedNormalParameterVector d n r hrD hrn p0) hA
  simpa [sourceOrientedNormalParameterVector_head] using hLI

namespace SourceOrientedHeadGaugeNormalParameterData

/-- The matched head-gauge normal-parameter head is invertible. -/
theorem head_det_unit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    IsUnit D.p.head.det := by
  simpa [D.head_eq] using
    Head.factor_det_unit
      (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead

/-- A matched head-gauge normal-parameter representative gives the required
shifted residual-tail membership. -/
theorem residualTail_mem_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  exact
    sourceOrientedSchurResidualTailData_mem_variety_of_eq_normalParameter
      d n r hrD hrn D.p D.invariant_eq D.head_eq
      (head_det_unit d n r hrD hrn Head hHead D)

/-- A matched head-gauge normal-parameter representative mechanically produces
the full Schur residual packet. -/
def schurResidualData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem
    d n r hrD hrn hGvar Head hHead
    (residualTail_mem_variety d n r hrD hrn Head hHead D)

end SourceOrientedHeadGaugeNormalParameterData

/-- If a proper complex Lorentz transformation carries one realizing source
tuple to a normal-parameter tuple whose head is the local gauge factor, then
the matched head-gauge normal-parameter data follows by oriented-invariant
preservation.

The remaining hard theorem is therefore exactly the finite-dimensional
construction of such a Lorentz normalization. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛ :
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn p) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head where
  p := p
  invariant_eq := by
    calc
      G = sourceOrientedMinkowskiInvariant d n z := hz
      _ = sourceOrientedMinkowskiInvariant d n (complexLorentzAction Λ z) := by
        exact (sourceOrientedMinkowskiInvariant_complexLorentzAction
          (d := d) (n := n) Λ z).symm
      _ = sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p) := by
        rw [hΛ]
  head_eq := hhead

/-- Blockwise version of
`sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized`, using the
head/tail source-label split. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_head_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceHead hrn a))
    (hΛtail :
      ∀ u : Fin (n - r),
        complexLorentzAction Λ z (finSourceTail hrn u) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceTail hrn u)) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    d n r hrD hrn hGvar Head hz hhead Λ (by
      ext i μ
      rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
      · exact congrFun (hΛhead a) μ
      · exact congrFun (hΛtail u) μ)

end BHW
