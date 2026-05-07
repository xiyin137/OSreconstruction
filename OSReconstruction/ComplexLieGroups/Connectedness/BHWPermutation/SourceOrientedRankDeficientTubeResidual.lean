import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalRealization
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

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
