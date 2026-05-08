import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameLocalImage

/-!
# Full-frame hypersurface transport from the implicit kernel chart

This file packages the checked inverse-function chart from
`SourceOrientedFullFrameLocalImage` into the first local transport statement:
small kernel coordinates are realized by actual gauge-slice points on the
full-frame oriented hypersurface.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The full-frame oriented hypersurface after restricting the ambient product
coordinate space to symmetric coordinates. -/
def sourceFullFrameSymmetricHypersurfaceCoord (d : ℕ) :
    Set (sourceFullFrameSymmetricCoordSubmodule d) :=
  {H | sourceFullFrameSymmetricEquation d H = 0}

/-- The actual full-frame oriented image variety, restricted to symmetric
coordinates. -/
def sourceFullFrameSymmetricVarietyCoord (d : ℕ) :
    Set (sourceFullFrameSymmetricCoordSubmodule d) :=
  {H | (H : SourceFullFrameOrientedCoord d) ∈ sourceFullFrameOrientedGramVarietyCoord d}

/-- The nonzero-determinant sheet, restricted to symmetric full-frame
coordinates. -/
def sourceFullFrameSymmetricDetNonzeroCoord (d : ℕ) :
    Set (sourceFullFrameSymmetricCoordSubmodule d) :=
  {H | (H : SourceFullFrameOrientedCoord d) ∈ sourceFullFrameOrientedCoord_detNonzero d}

@[simp]
theorem mem_sourceFullFrameSymmetricHypersurfaceCoord
    {d : ℕ} {H : sourceFullFrameSymmetricCoordSubmodule d} :
    H ∈ sourceFullFrameSymmetricHypersurfaceCoord d ↔
      sourceFullFrameSymmetricEquation d H = 0 :=
  Iff.rfl

@[simp]
theorem mem_sourceFullFrameSymmetricVarietyCoord
    {d : ℕ} {H : sourceFullFrameSymmetricCoordSubmodule d} :
    H ∈ sourceFullFrameSymmetricVarietyCoord d ↔
      (H : SourceFullFrameOrientedCoord d) ∈
        sourceFullFrameOrientedGramVarietyCoord d :=
  Iff.rfl

@[simp]
theorem mem_sourceFullFrameSymmetricDetNonzeroCoord
    {d : ℕ} {H : sourceFullFrameSymmetricCoordSubmodule d} :
    H ∈ sourceFullFrameSymmetricDetNonzeroCoord d ↔
      (H : SourceFullFrameOrientedCoord d) ∈
        sourceFullFrameOrientedCoord_detNonzero d :=
  Iff.rfl

theorem sourceFullFrameSymmetricDetNonzeroCoord_open
    (d : ℕ) :
    IsOpen (sourceFullFrameSymmetricDetNonzeroCoord d) := by
  simpa [sourceFullFrameSymmetricDetNonzeroCoord] using
    (sourceFullFrameOrientedCoord_detNonzero_open d).preimage continuous_subtype_val

/-- The full-frame gauge-slice map lands in the symmetric hypersurface. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_mem_hypersurface
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
      sourceFullFrameSymmetricHypersurfaceCoord d := by
  have h :=
    (sourceFullFrameGaugeSliceMap_mem_hypersurface d M0 S X).2
  simpa [sourceFullFrameSymmetricHypersurfaceCoord,
    sourceFullFrameSymmetricEquation, sourceFullFrameGaugeSliceMapSymmetric]
    using h

/-- The full-frame gauge-slice map lands in the actual oriented image variety,
viewed inside symmetric coordinates. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_mem_varietyCoord
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
      sourceFullFrameSymmetricVarietyCoord d := by
  simpa [sourceFullFrameSymmetricVarietyCoord,
    sourceFullFrameGaugeSliceMapSymmetric] using
    sourceFullFrameGaugeSliceMap_mem_varietyCoord d M0 S X

theorem sourceFullFrameSymmetricBase_mem_detNonzeroCoord
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    sourceFullFrameSymmetricBase d M0 ∈
      sourceFullFrameSymmetricDetNonzeroCoord d := by
  simpa [sourceFullFrameSymmetricDetNonzeroCoord, sourceFullFrameSymmetricBase,
    sourceFullFrameOrientedCoord_detNonzero] using hM0.ne_zero

theorem sourceFullFrameGaugeSliceMapSymmetric_detNonzero_mem_nhds_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    {X : S.slice |
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
        sourceFullFrameSymmetricDetNonzeroCoord d} ∈ 𝓝 (0 : S.slice) := by
  have hcont :=
    (sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt d hM0 S).continuousAt
  have hbase :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S 0 ∈
        sourceFullFrameSymmetricDetNonzeroCoord d := by
    simpa using sourceFullFrameSymmetricBase_mem_detNonzeroCoord d hM0
  exact hcont.preimage_mem_nhds
    ((sourceFullFrameSymmetricDetNonzeroCoord_open d).mem_nhds hbase)

set_option synthInstance.maxHeartbeats 120000 in
/-- A target kernel coordinate of the local chart is realized by an actual
gauge-slice point on the full-frame symmetric hypersurface, and its kernel
projection coordinate is the prescribed target point. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_hypersurface
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker}
    (hK :
      K ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target) :
    ∃ X : S.slice,
      X ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∧
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
        sourceFullFrameSymmetricHypersurfaceCoord d ∧
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
          sourceFullFrameSymmetricBase d M0) = K := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  refine ⟨e.symm K, e.map_target hK, ?_, ?_⟩
  · exact sourceFullFrameGaugeSliceMapSymmetric_mem_hypersurface d M0 S (e.symm K)
  · have hright :=
      sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget
        d hM0 S hK
    simpa [e, sourceFullFrameGaugeSliceImplicitKernelMap,
      sourceFullFrameSymmetricEquation_implicitChart_snd] using hright

set_option synthInstance.maxHeartbeats 120000 in
/-- Every sufficiently small kernel coordinate is realized by an actual
gauge-slice point on the full-frame symmetric hypersurface. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_hypersurface
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ∀ᶠ K in
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker),
      ∃ X : S.slice,
        X ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∧
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
          sourceFullFrameSymmetricHypersurfaceCoord d ∧
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
            sourceFullFrameSymmetricBase d M0) = K := by
  filter_upwards
    [sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero d hM0 S] with K hK
  exact sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_hypersurface d hM0 S hK

set_option synthInstance.maxHeartbeats 120000 in
/-- A target kernel coordinate of the local chart is realized by an actual
gauge-slice point on the full-frame oriented image variety, and its kernel
projection coordinate is the prescribed target point. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_varietyCoord
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker}
    (hK :
      K ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target) :
    ∃ X : S.slice,
      X ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∧
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
        sourceFullFrameSymmetricVarietyCoord d ∧
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
          sourceFullFrameSymmetricBase d M0) = K := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  refine ⟨e.symm K, e.map_target hK, ?_, ?_⟩
  · exact sourceFullFrameGaugeSliceMapSymmetric_mem_varietyCoord d M0 S (e.symm K)
  · have hright :=
      sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget
        d hM0 S hK
    simpa [e, sourceFullFrameGaugeSliceImplicitKernelMap,
      sourceFullFrameSymmetricEquation_implicitChart_snd] using hright

set_option synthInstance.maxHeartbeats 120000 in
/-- Every sufficiently small kernel coordinate is realized by an actual
gauge-slice point on the full-frame oriented image variety. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_varietyCoord
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ∀ᶠ K in
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker),
      ∃ X : S.slice,
        X ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∧
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
          sourceFullFrameSymmetricVarietyCoord d ∧
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
            sourceFullFrameSymmetricBase d M0) = K := by
  filter_upwards
    [sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero d hM0 S] with K hK
  exact sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_varietyCoord d hM0 S hK

set_option synthInstance.maxHeartbeats 120000 in
/-- Pull back the determinant-nonzero sheet along the inverse kernel chart:
for sufficiently small kernel coordinates, the lifted gauge-slice frame still
has nonzero determinant. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_symm_detNonzero_mem_nhds_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker |
      sourceFullFrameGaugeSliceMapSymmetric d M0 S
        ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm K) ∈
        sourceFullFrameSymmetricDetNonzeroCoord d} ∈
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  have hdet :=
    sourceFullFrameGaugeSliceMapSymmetric_detNonzero_mem_nhds_zero d hM0 S
  have hcont : ContinuousAt (e.symm :
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker → S.slice) 0 :=
    e.continuousAt_symm
      (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget d hM0 S)
  have hsymm0 :
      e.symm (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) = (0 : S.slice) := by
    have hleft :=
      sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource
        d hM0 S
        (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S)
    simpa [e] using hleft
  have hdet' :
      {X : S.slice |
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
          sourceFullFrameSymmetricDetNonzeroCoord d} ∈ 𝓝 (e.symm 0) := by
    simpa [hsymm0] using hdet
  simpa [e] using hcont.preimage_mem_nhds hdet'

set_option synthInstance.maxHeartbeats 120000 in
/-- Pull back the symmetric implicit-chart source along the inverse kernel
chart: for sufficiently small kernel coordinates, the lifted gauge-slice
symmetric coordinate lies in the implicit-chart source. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_symm_implicitSource_mem_nhds_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker |
      sourceFullFrameGaugeSliceMapSymmetric d M0 S
        ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm K) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source} ∈
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  have hsymm0 : e.symm (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) = (0 : S.slice) := by
    have hleft :=
      sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource
        d hM0 S
        (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S)
    simpa [e] using hleft
  have hcont_symm : ContinuousAt (e.symm :
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker → S.slice) 0 :=
    e.continuousAt_symm
      (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget d hM0 S)
  have hcont_gauge :
      ContinuousAt (sourceFullFrameGaugeSliceMapSymmetric d M0 S) (e.symm 0) := by
    simpa [hsymm0] using
      (sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt d hM0 S).continuousAt
  have hcomp :
      ContinuousAt
        (fun K =>
          sourceFullFrameGaugeSliceMapSymmetric d M0 S (e.symm K))
        (0 :
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d M0)).ker) :=
    hcont_gauge.comp hcont_symm
  have hbase :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S (e.symm 0) =
        sourceFullFrameSymmetricBase d M0 := by
    rw [hsymm0]
    exact sourceFullFrameGaugeSliceMapSymmetric_zero d M0 S
  have hsource :
      (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source ∈
        𝓝 (sourceFullFrameGaugeSliceMapSymmetric d M0 S (e.symm 0)) := by
    simpa [hbase] using
      sourceFullFrameSymmetricEquation_implicitChart_source_mem_nhds_base
        d hM0
  simpa [e] using hcomp.preimage_mem_nhds hsource

set_option synthInstance.maxHeartbeats 120000 in
/-- Every sufficiently small kernel coordinate is realized by an actual
gauge-slice point on the determinant-nonzero full-frame oriented image
variety. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_detNonzero_varietyCoord
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ∀ᶠ K in
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker),
      ∃ X : S.slice,
        X ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∧
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
          sourceFullFrameSymmetricVarietyCoord d ∧
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
          sourceFullFrameSymmetricDetNonzeroCoord d ∧
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
            sourceFullFrameSymmetricBase d M0) = K := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  filter_upwards
    [sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero d hM0 S,
      sourceFullFrameGaugeSliceImplicitKernel_symm_detNonzero_mem_nhds_zero d hM0 S]
    with K hK hdet
  refine ⟨e.symm K, e.map_target hK, ?_, ?_, ?_⟩
  · exact sourceFullFrameGaugeSliceMapSymmetric_mem_varietyCoord d M0 S (e.symm K)
  · simpa [e] using hdet
  · have hright :=
      sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget
        d hM0 S hK
    simpa [e, sourceFullFrameGaugeSliceImplicitKernelMap,
      sourceFullFrameSymmetricEquation_implicitChart_snd] using hright

end BHW
