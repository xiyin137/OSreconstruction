import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameHolomorphicSection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameJacobi

/-!
# Real-compatible full-frame kernel map

This file keeps the real-compatible full-frame implicit-kernel derivative
support separate from the chart packaging file.  The key point is that the
kernel coordinate used for the real route is based on the explicit
determinant-direction projection, not on the arbitrary closed-complement
projection used by the generic complex local-image chart.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 700000 in
/-- Ambient symmetric-equation local chart using the determinant-direction
projection as its kernel coordinate.  This is the ambient comparison chart for
the real-compatible full-frame route; unlike
`sourceFullFrameSymmetricEquation_implicitChart`, its right coordinate is the
explicit projection `sourceFullFrameRealCompatibleKernelProjection`. -/
noncomputable def sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    OpenPartialHomeomorph
      (sourceFullFrameSymmetricCoordSubmodule d)
      (ℂ × (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) := by
  haveI hE : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
    sourceFullFrameSymmetricCoordSubmodule_completeSpace d
  let M0 := M0R.map Complex.ofReal
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  let K := L.ker
  haveI hK : CompleteSpace K := by infer_instance
  let P : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ] K :=
    sourceFullFrameRealCompatibleKernelProjection d hM0R
  have hstrict : HasStrictFDerivAt f L H0S := by
    simpa [f, L, H0S, M0, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange_left : L.range = ⊤ := by
    simpa [L, M0] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d)
        (H0 := sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R).ne_zero
  have hP_strict : HasStrictFDerivAt
      (fun H : sourceFullFrameSymmetricCoordSubmodule d => P (H - H0S))
      P H0S := by
    have hsubarg : HasStrictFDerivAt
        (fun H : sourceFullFrameSymmetricCoordSubmodule d => H - H0S)
        (1 : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
          sourceFullFrameSymmetricCoordSubmodule d) H0S := by
      have hid : HasStrictFDerivAt
          (fun H : sourceFullFrameSymmetricCoordSubmodule d => H)
          (1 : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
            sourceFullFrameSymmetricCoordSubmodule d) H0S :=
        hasStrictFDerivAt_id H0S
      exact hid.sub_const H0S
    have hlin0 : HasStrictFDerivAt
        (fun X : sourceFullFrameSymmetricCoordSubmodule d => P X)
        P (H0S - H0S) := by
      exact @ContinuousLinearMap.hasStrictFDerivAt ℂ _
        (sourceFullFrameSymmetricCoordSubmodule d) _ _ _ K _ _ _ P
        (x := H0S - H0S)
    have hcomp := HasStrictFDerivAt.comp (𝕜 := ℂ) (x := H0S)
        (g := fun X : sourceFullFrameSymmetricCoordSubmodule d => P X)
        (f := fun H : sourceFullFrameSymmetricCoordSubmodule d => H - H0S)
        hlin0 hsubarg
    simpa [P, ContinuousLinearMap.comp_id] using hcomp
  have hrange_right : P.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro K
    refine ⟨(K : sourceFullFrameSymmetricCoordSubmodule d), ?_⟩
    exact sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R K
  have hcompl : IsCompl L.ker P.ker := by
    simpa [P, L, M0] using
      (LinearMap.isCompl_of_proj
        (sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R))
  let φ : @ImplicitFunctionData ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK :=
    @ImplicitFunctionData.mk ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK
      f L (fun H => P (H - H0S)) P H0S
      hstrict hP_strict hrange_left hrange_right hcompl
  exact @ImplicitFunctionData.toOpenPartialHomeomorph ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK φ

@[simp]
theorem sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC_apply
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d) :
    sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R H =
      (sourceFullFrameSymmetricEquation d H,
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (H - sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) := by
  unfold sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 700000 in
/-- The determinant-direction ambient symmetric-equation chart contains the
base selected symmetric coordinate. -/
theorem sourceFullFrameRealCompatibleSymmetricEquation_base_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) ∈
      (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R).source := by
  haveI hE : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
    sourceFullFrameSymmetricCoordSubmodule_completeSpace d
  let M0 := M0R.map Complex.ofReal
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  let K := L.ker
  haveI hK : CompleteSpace K := by infer_instance
  let P : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ] K :=
    sourceFullFrameRealCompatibleKernelProjection d hM0R
  have hstrict : HasStrictFDerivAt f L H0S := by
    simpa [f, L, H0S, M0, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange_left : L.range = ⊤ := by
    simpa [L, M0] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d)
        (H0 := sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R).ne_zero
  have hP_strict : HasStrictFDerivAt
      (fun H : sourceFullFrameSymmetricCoordSubmodule d => P (H - H0S))
      P H0S := by
    have hsubarg : HasStrictFDerivAt
        (fun H : sourceFullFrameSymmetricCoordSubmodule d => H - H0S)
        (1 : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
          sourceFullFrameSymmetricCoordSubmodule d) H0S := by
      have hid : HasStrictFDerivAt
          (fun H : sourceFullFrameSymmetricCoordSubmodule d => H)
          (1 : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
            sourceFullFrameSymmetricCoordSubmodule d) H0S :=
        hasStrictFDerivAt_id H0S
      exact hid.sub_const H0S
    have hlin0 : HasStrictFDerivAt
        (fun X : sourceFullFrameSymmetricCoordSubmodule d => P X)
        P (H0S - H0S) := by
      exact @ContinuousLinearMap.hasStrictFDerivAt ℂ _
        (sourceFullFrameSymmetricCoordSubmodule d) _ _ _ K _ _ _ P
        (x := H0S - H0S)
    have hcomp := HasStrictFDerivAt.comp (𝕜 := ℂ) (x := H0S)
        (g := fun X : sourceFullFrameSymmetricCoordSubmodule d => P X)
        (f := fun H : sourceFullFrameSymmetricCoordSubmodule d => H - H0S)
        hlin0 hsubarg
    simpa [P, ContinuousLinearMap.comp_id] using hcomp
  have hrange_right : P.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro K
    refine ⟨(K : sourceFullFrameSymmetricCoordSubmodule d), ?_⟩
    exact sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R K
  have hcompl : IsCompl L.ker P.ker := by
    simpa [P, L, M0] using
      (LinearMap.isCompl_of_proj
        (sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R))
  let φ : @ImplicitFunctionData ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK :=
    @ImplicitFunctionData.mk ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK
      f L (fun H => P (H - H0S)) P H0S
      hstrict hP_strict hrange_left hrange_right hcompl
  change H0S ∈
    (@ImplicitFunctionData.toOpenPartialHomeomorph ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK φ).source
  exact
    @ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source ℂ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) inferInstance inferInstance hE
      ℂ inferInstance inferInstance inferInstance
      K inferInstance inferInstance hK φ

theorem sourceFullFrameRealCompatibleSymmetricEquation_eq_of_zero_projection_eq
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    {H G : sourceFullFrameSymmetricCoordSubmodule d}
    (hH_source :
      H ∈ (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R).source)
    (hG_source :
      G ∈ (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R).source)
    (hH_zero : sourceFullFrameSymmetricEquation d H = 0)
    (hG_zero : sourceFullFrameSymmetricEquation d G = 0)
    (hproj :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (H - sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (G - sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) :
    H = G := by
  let e := sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
    d hM0R
  have hH_chart :
      e H =
        (0, sourceFullFrameRealCompatibleKernelProjection d hM0R
          (H - sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) := by
    rw [sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC_apply]
    rw [hH_zero]
  have hG_chart :
      e G =
        (0, sourceFullFrameRealCompatibleKernelProjection d hM0R
          (G - sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) := by
    rw [sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC_apply]
    rw [hG_zero]
  have heq : e H = e G := by
    rw [hH_chart, hG_chart, hproj]
  have hsymm := congrArg e.symm heq
  simpa [e.left_inv hH_source, e.left_inv hG_source] using hsymm

theorem sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_realCompatibleProjection_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (S : SourceFullFrameGaugeSliceData d (M0R.map Complex.ofReal))
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (X : S.slice)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S X ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hprojection :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameGaugeSliceMapSymmetric d
              (M0R.map Complex.ofReal) S X -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) :
    sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG =
      sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S X := by
  have hG_zero :
      sourceFullFrameSymmetricEquation d
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG) = 0 := by
    have hvar :=
      sourceFullFrameSelectedSymmetricCoordOfSource_mem_varietyCoord
        d n ι hG
    have hhyp :
        ((sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG :
            sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) ∈
          sourceFullFrameOrientedHypersurfaceCoord d :=
      sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface d hvar
    simpa [sourceFullFrameSymmetricEquation] using hhyp.2
  have hX_zero :
      sourceFullFrameSymmetricEquation d
          (sourceFullFrameGaugeSliceMapSymmetric d
            (M0R.map Complex.ofReal) S X) = 0 := by
    have hhyp :=
      sourceFullFrameGaugeSliceMapSymmetric_mem_hypersurface d
        (M0R.map Complex.ofReal) S X
    simpa [sourceFullFrameSymmetricHypersurfaceCoord] using hhyp
  exact
    sourceFullFrameRealCompatibleSymmetricEquation_eq_of_zero_projection_eq
      d hM0R hG_source hX_source hG_zero hX_zero hprojection

theorem sourceFullFrameOrientedCoordOfSource_eq_gaugeSliceMap_of_realCompatibleProjection_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (S : SourceFullFrameGaugeSliceData d (M0R.map Complex.ofReal))
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (X : S.slice)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S X ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hprojection :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameGaugeSliceMapSymmetric d
              (M0R.map Complex.ofReal) S X -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))) :
    sourceFullFrameOrientedCoordOfSource d n ι G =
      sourceFullFrameGaugeSliceMap d (M0R.map Complex.ofReal) S X := by
  have hsym :=
    sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_realCompatibleProjection_eq
      d n ι hM0R S hG X hG_source hX_source hprojection
  have hcoe := congrArg
    (fun H : sourceFullFrameSymmetricCoordSubmodule d =>
      (H : SourceFullFrameOrientedCoord d)) hsym
  simpa [sourceFullFrameSelectedSymmetricCoordOfSource,
    sourceFullFrameGaugeSliceMapSymmetric] using hcoe

theorem sourceFullFrameGauge_reconstructInvariant_eq_of_realCompatibleProjection_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (S : SourceFullFrameGaugeSliceData d (M0R.map Complex.ofReal))
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (y : sourceFullFrameMaxRankChartModel d n ι
      (M0R.map Complex.ofReal) S)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S y.1 ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source)
    (hprojection :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameGaugeSliceMapSymmetric d
              (M0R.map Complex.ofReal) S y.1 -
            sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)))
    (hmixed :
      y.2 = sourceSelectedMixedRows d n ι G) :
    sourceFullFrameGauge_reconstructInvariant d n ι
        (M0R.map Complex.ofReal) S y = G := by
  have hsel :
      sourceFullFrameOrientedCoordOfSource d n ι G =
        sourceFullFrameGaugeSliceMap d (M0R.map Complex.ofReal) S y.1 :=
    sourceFullFrameOrientedCoordOfSource_eq_gaugeSliceMap_of_realCompatibleProjection_eq
      d n ι hM0R S hG y.1 hG_source hX_source hprojection
  have hsel_reconstruct :
      sourceFullFrameOrientedCoordOfSource d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι
            (M0R.map Complex.ofReal) S y) =
        sourceFullFrameOrientedCoordOfSource d n ι G := by
    calc
      sourceFullFrameOrientedCoordOfSource d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι
            (M0R.map Complex.ofReal) S y) =
          sourceFullFrameOrientedGramCoord d
            (sourceFullFrameGauge_reconstructFrame d n ι
              (M0R.map Complex.ofReal) S y) := by
        exact
          sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq
            d n ι (M0R.map Complex.ofReal) S y
      _ = sourceFullFrameGaugeSliceMap d (M0R.map Complex.ofReal) S y.1 := by
        rfl
      _ = sourceFullFrameOrientedCoordOfSource d n ι G := hsel.symm
  have hdet_reconstruct :
      (sourceFullFrameGauge_reconstructInvariant d n ι
        (M0R.map Complex.ofReal) S y).det ι ≠ 0 := by
    have hdet_eq :
        (sourceFullFrameGauge_reconstructInvariant d n ι
          (M0R.map Complex.ofReal) S y).det ι = G.det ι := by
      simpa [sourceFullFrameOrientedCoordOfSource] using
        congrArg Prod.snd hsel_reconstruct
    rw [hdet_eq]
    exact hdet
  have hframe_det :
      (sourceFullFrameGauge_reconstructFrame d n ι
        (M0R.map Complex.ofReal) S y).det ≠ 0 := by
    rw [← sourceFullFrameGauge_reconstructInvariant_selectedDet
      d n ι (M0R.map Complex.ofReal) S y]
    exact hdet_reconstruct
  have hmixed_reconstruct :
      sourceSelectedMixedRows d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι
            (M0R.map Complex.ofReal) S y) =
        sourceSelectedMixedRows d n ι G := by
    calc
      sourceSelectedMixedRows d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι
            (M0R.map Complex.ofReal) S y) = y.2 := by
        exact
          sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero
            d n ι (M0R.map Complex.ofReal) S y hframe_det
      _ = sourceSelectedMixedRows d n ι G := hmixed
  exact
    sourceFullFrameGauge_reconstructInvariant_eq_of_selectedCoord_eq_mixedRows_eq
      d n ι (M0R.map Complex.ofReal) S y hG hdet hsel_reconstruct
      hmixed_reconstruct

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The explicit real-compatible kernel-coordinate map has the same strict
derivative as the generic implicit-kernel map. -/
theorem sourceFullFrameRealCompatibleExplicitKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleExplicitKernelMap d hM0R)
      (sourceFullFrameGaugeSliceKernelDerivCLM d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))) 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let M0 := M0R.map Complex.ofReal
  let Fsym := sourceFullFrameGaugeSliceMapSymmetric d M0 S
  let H0S := sourceFullFrameSymmetricBase d M0
  let P := sourceFullFrameRealCompatibleKernelProjection d hM0R
  have hF : HasStrictFDerivAt Fsym
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) 0 := by
    simpa [Fsym, M0, S, hM0C] using
      sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt d hM0C S
  have hsub : HasStrictFDerivAt (fun X : S.slice => Fsym X - H0S)
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) 0 := by
    exact hF.sub_const H0S
  have hP : HasStrictFDerivAt
      (P : sourceFullFrameSymmetricCoordSubmodule d →
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
      P (Fsym 0 - H0S) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ _
      ((sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
      _ _ _
      P (x := Fsym 0 - H0S)
  have hcomp : HasStrictFDerivAt
      (fun X : S.slice => P (Fsym X - H0S))
      (P.comp (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S)) 0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : S.slice))
        (g := (P : sourceFullFrameSymmetricCoordSubmodule d →
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker))
        (f := fun X : S.slice => Fsym X - H0S) hP hsub)
  have hclm : P.comp (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S := by
    apply ContinuousLinearMap.ext
    intro X
    have hp := sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X)
    simpa [P, sourceFullFrameGaugeSliceKernelDerivCLM] using hp
  have hcomp' : HasStrictFDerivAt
      (fun X : S.slice => P (Fsym X - H0S))
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S) 0 :=
    hcomp.congr_fderiv hclm
  refine hcomp'.congr_of_eventuallyEq ?_
  filter_upwards with X
  simp [sourceFullFrameRealCompatibleExplicitKernelMap, P, Fsym, H0S, S, M0]

/-- The explicit real-compatible kernel map written in the finite coordinates
of the checked real-form slice. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelMap
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ) :=
  fun q =>
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      (sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        (F.complexCoordEquiv q))

set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F 0 = 0 := by
  simp [sourceFullFrameRealCompatibleNormalizedKernelMap,
    sourceFullFrameRealSliceKernelCoordEquiv]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The explicit real-compatible normalized kernel map has identity strict
derivative at the origin. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F)
      (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let Es : K →L[ℂ] (Fin F.realModelDim → ℂ) := E.symm
  let f := sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
  let c : (Fin F.realModelDim → ℂ) →L[ℂ] S.slice := F.complexCoordEquiv
  let e : S.slice ≃L[ℂ] K :=
    sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S
  have hf : HasStrictFDerivAt f (e : S.slice →L[ℂ] K) 0 := by
    rw [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
    exact sourceFullFrameRealCompatibleExplicitKernelMap_hasStrictFDerivAt
      d hM0R
  have hc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => c q) c
      (0 : Fin F.realModelDim → ℂ) :=
    c.hasStrictFDerivAt
  have hc0 : c (0 : Fin F.realModelDim → ℂ) = 0 := by
    simp [c]
  have hf0 : HasStrictFDerivAt f (e : S.slice →L[ℂ] K)
      (c (0 : Fin F.realModelDim → ℂ)) := by
    simpa [hc0] using hf
  have hfc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => f (c q))
      ((e : S.slice →L[ℂ] K).comp c) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := f) (f := fun q : Fin F.realModelDim → ℂ => c q) hf0 hc)
  have hsymm : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es (0 : K) :=
    ContinuousLinearMap.hasStrictFDerivAt Es (x := (0 : K))
  have hf_zero : f 0 = 0 := by
    simp [f]
  have hf_c0 : f (c (0 : Fin F.realModelDim → ℂ)) = 0 := by
    rw [hc0]
    exact hf_zero
  have hsymm0 : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es
      (f (c (0 : Fin F.realModelDim → ℂ))) := by
    rw [hf_c0]
    exact hsymm
  have hcomp : HasStrictFDerivAt
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q)))
      (Es.comp ((e : S.slice →L[ℂ] K).comp c)) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := (Es : K → (Fin F.realModelDim → ℂ)))
        (f := fun q : Fin F.realModelDim → ℂ => f (c q)) hsymm0 hfc)
  have hfun :
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q))) =
        sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F := by
    funext q
    rfl
  have hderiv :
      Es.comp ((e : S.slice →L[ℂ] K).comp c) =
        (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) := by
    apply ContinuousLinearMap.ext
    intro q
    change Es (e (c q)) = q
    rw [show Es (e (c q)) =
        F.complexCoordEquiv.symm (e.symm (e (F.complexCoordEquiv q))) by
      rfl]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ContinuousLinearEquiv.symm_apply_apply F.complexCoordEquiv q
  simpa [hfun, hderiv] using hcomp

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The complex inverse-function chart for the determinant-direction
normalized kernel map.  This is the complex chart that is compatible with the
real route; it uses `sourceFullFrameRealCompatibleKernelProjection`, not the
generic closed-complement projection. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph (Fin F.realModelDim → ℂ) (Fin F.realModelDim → ℂ) := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  exact @HasStrictFDerivAt.toOpenPartialHomeomorph ℂ _
    (Fin F.realModelDim → ℂ) _ _ (Fin F.realModelDim → ℂ) _ _
    f e 0 inferInstance hderiv

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F : (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F := by
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The determinant-direction complex normalized kernel chart contains the
origin in its source. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).source := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  unfold sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

/-- The determinant-direction complex normalized kernel chart contains the
origin in its target. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
      d hM0R F
  have htarget :=
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F).map_source hsource
  simpa using htarget

/-- The determinant-direction complex kernel chart transported from finite
coordinates back to the explicit complex full-frame slice. -/
noncomputable def sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker :=
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  F.complexCoordEquiv.symm.toHomeomorph.toOpenPartialHomeomorph |>.trans
    ((sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F).trans E.toHomeomorph.toOpenPartialHomeomorph)

@[simp]
theorem sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
      d hM0R F :
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice →
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) =
      sourceFullFrameRealCompatibleExplicitKernelMap d hM0R := by
  funext X
  simp [sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC,
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe,
    sourceFullFrameRealCompatibleNormalizedKernelMap]

/-- The determinant-direction slice-kernel chart contains the origin in its
source. -/
theorem sourceFullFrameRealCompatibleSliceKernelC_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 :
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice) ∈
      (sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
        d hM0R F).source := by
  unfold sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
  simp [sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
    d hM0R F]

/-- The determinant-direction slice-kernel chart contains the origin in its
target. -/
theorem sourceFullFrameRealCompatibleSliceKernelC_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 :
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) ∈
      (sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealCompatibleSliceKernelC_zero_mem_chartSource d hM0R F
  have htarget :=
    (sourceFullFrameRealCompatibleSliceKernelOpenPartialHomeomorphC
      d hM0R F).map_source hsource
  simpa using htarget

set_option synthInstance.maxHeartbeats 100000 in
/-- The restricted symmetric equation derivative has real value on
componentwise complexified real symmetric coordinates at a complexified real
full-frame base. -/
theorem sourceFullFrameSymmetricEquationDerivCLM_realComplexify_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : SourceFullFrameRealOrientedCoord d)
    (hYsym : ∀ a b : Fin (d + 1), Y.1 a b = Y.1 b a) :
    Complex.im (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
      ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
        intro a b
        change (Y.1 a b : ℂ) = (Y.1 b a : ℂ)
        exact_mod_cast hYsym a b⟩) = 0 := by
  have hGramUnit :
      IsUnit
        (Matrix.of
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)).gram).det := by
    simpa [sourceFullFrameOrientedGram] using
      sourceFullFrameGram_det_isUnit_of_frame_det_isUnit
        (d := d) (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hf0 :=
    (sourceFullFrameOrientedEquation_hasFDerivAt_trace (d := d)
      (H0 := sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
      hGramUnit).fderiv
  have hf :
      fderiv ℂ (sourceFullFrameOrientedEquation d)
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)) =
      sourceFullFrameOrientedEquationDerivCLM d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) := by
    simpa [sourceFullFrameOrientedGramCoord] using hf0
  change Complex.im
      (((fderiv ℂ (sourceFullFrameOrientedEquation d)
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).comp
          (sourceFullFrameSymmetricCoordSubmodule d).subtypeL)
        ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
          intro a b
          change (Y.1 a b : ℂ) = (Y.1 b a : ℂ)
          exact_mod_cast hYsym a b⟩) = 0
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [hf]
  exact sourceFullFrameOrientedEquationDerivLinear_realComplexify_im d hM0R Y

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit determinant-direction projection preserves zero imaginary
parts in all symmetric full-frame coordinates. -/
theorem sourceFullFrameRealCompatibleKernelProjection_im_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d)
    (hHgram : ∀ a b : Fin (d + 1),
      Complex.im ((H : SourceFullFrameOrientedCoord d).1 a b) = 0)
    (hHdet : Complex.im ((H : SourceFullFrameOrientedCoord d).2) = 0) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameRealCompatibleKernelProjection d hM0R H :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameRealCompatibleKernelProjection d hM0R H :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
  let u := sourceFullFrameSymmetricDetDirection d
  have ha_im0 :
      ((sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)))
        ⟨(0, 1), sourceFullFrameDetDirection_mem_symmetric d⟩).im = 0 := by
    simpa [sourceFullFrameSymmetricDetDirection, sourceFullFrameDetDirection] using
      sourceFullFrameRealCompatibleSymmetricDetDirection_scalar_im d M0R
  have hYsym :
      ∀ a b : Fin (d + 1),
        ((H : SourceFullFrameOrientedCoord d).1 a b).re =
          ((H : SourceFullFrameOrientedCoord d).1 b a).re := by
    intro a b
    exact congrArg Complex.re (H.property a b)
  let Y : SourceFullFrameRealOrientedCoord d :=
    (fun a b => ((H : SourceFullFrameOrientedCoord d).1 a b).re,
      ((H : SourceFullFrameOrientedCoord d).2).re)
  have hH_eq : H =
      ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
        intro a b
        change (((H : SourceFullFrameOrientedCoord d).1 a b).re : ℂ) =
          (((H : SourceFullFrameOrientedCoord d).1 b a).re : ℂ)
        exact_mod_cast hYsym a b⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · funext a b
      apply Complex.ext
      · simp [Y, sourceFullFrameRealOrientedCoordComplexify]
      · simpa [Y, sourceFullFrameRealOrientedCoordComplexify] using hHgram a b
    · apply Complex.ext
      · simp [Y, sourceFullFrameRealOrientedCoordComplexify]
      · simpa [Y, sourceFullFrameRealOrientedCoordComplexify] using hHdet
  have hb_im0 : (L H).im = 0 := by
    rw [hH_eq]
    simpa [L, Y] using
      sourceFullFrameSymmetricEquationDerivCLM_realComplexify_im
        d hM0R Y hYsym
  constructor
  · intro i j
    change Complex.im (((H -
        (1 / (L u)) • (ContinuousLinearMap.smulRight L u) H :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 i j) = 0
    simp [u, sourceFullFrameSymmetricDetDirection,
      sourceFullFrameDetDirection, ContinuousLinearMap.smulRight_apply, L,
      hHgram]
  · change Complex.im (((H -
        (1 / (L u)) • (ContinuousLinearMap.smulRight L u) H :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0
    simp [u, sourceFullFrameSymmetricDetDirection,
      sourceFullFrameDetDirection, ContinuousLinearMap.smulRight_apply, L,
      hHdet, ha_im0, hb_im0]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- On a complexified real slice input, the nonlinear gauge-slice symmetric
coordinate minus the complexified real base has zero imaginary parts. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_realComplexify_sub_base_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameGaugeSliceMapSymmetric d
        (M0R.map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b)) = 0) ∧
      Complex.im ((((sourceFullFrameGaugeSliceMapSymmetric d
        (M0R.map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2)) = 0 := by
  constructor
  · intro a b
    simp [sourceFullFrameGaugeSliceMapSymmetric,
      sourceFullFrameGaugeSliceMap, sourceFullFrameSymmetricBase,
      sourceFullFrameOrientedGramCoord, sourceFullFrameOrientedGram]
  · have hmap :
        M0R.map Complex.ofReal +
            ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
          (M0R + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)).map
            Complex.ofReal := by
      ext i j
      simp
    simp [sourceFullFrameGaugeSliceMapSymmetric,
      sourceFullFrameGaugeSliceMap, sourceFullFrameSymmetricBase,
      sourceFullFrameOrientedGramCoord, sourceFullFrameOrientedGram, hmap,
      sourceFullFrame_matrix_map_ofReal_det]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit real-compatible kernel map has real-valued output on
componentwise complexified real slice inputs. -/
theorem sourceFullFrameRealCompatibleExplicitKernelMap_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let S := sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  let XC : S.slice :=
    ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
      sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
        d hM0R X.property⟩
  let H : sourceFullFrameSymmetricCoordSubmodule d :=
    sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S XC -
      sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)
  have hH :=
    sourceFullFrameGaugeSliceMapSymmetric_realComplexify_sub_base_im d hM0R X
  have hproj :=
    sourceFullFrameRealCompatibleKernelProjection_im_zero d hM0R H hH.1 hH.2
  simpa [sourceFullFrameRealCompatibleExplicitKernelMap, H, S, XC] using hproj

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The kernel derivative equivalence sends complexified real slice vectors to
real-valued kernel coordinates. -/
theorem sourceFullFrameGaugeSliceKernelDerivCLM_realComplexify_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
    let S := sourceFullFrameExplicitGaugeSliceData d hM0C
    let XC : S.slice :=
      ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
        sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
          d hM0R X.property⟩
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  intro hM0C S XC
  rcases X.property with ⟨Y, hY⟩
  let YC := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Y
  have hXc :
      ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC := by
    rw [← hY]
    simpa [hM0C, YC, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Y
  have hdiff :
      sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
        (YC : SourceFullFrameOrientedCoord d) := by
    rw [hXc]
    exact sourceFullFrameOrientedDifferential_rightInverse d hM0C YC
  constructor
  · intro a b
    change Complex.im
      ((sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
        ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map
          Complex.ofReal)).1 a b) = 0
    rw [hdiff]
    simp [YC, sourceFullFrameRealOrientedCoordComplexify]
  · change Complex.im
      (sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
        ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map
          Complex.ofReal)).2 = 0
    rw [hdiff]
    simp [YC, sourceFullFrameRealOrientedCoordComplexify]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The finite kernel-coordinate equivalence sends real finite coordinates to
real-valued kernel coordinates. -/
theorem sourceFullFrameRealSliceKernelCoordEquiv_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    (∀ a b : Fin (d + 1),
      Complex.im (((((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im (((((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let X : sourceFullFrameRealDifferentialRightInverseRange d hM0R :=
    F.realCoordEquiv q
  let XC : S.slice :=
    ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
      sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
        d hM0R X.property⟩
  have hE :
      (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC := by
    rw [sourceFullFrameRealSliceKernelCoordEquiv]
    change (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S)
        (F.complexCoordEquiv (fun i => (q i : ℂ))) = _
    rw [F.complexCoordEquiv_real_eq q]
    let K := (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
    have hcoe := congrArg (fun T : S.slice →L[ℂ] K => T XC)
      (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe d hM0C S)
    change
      ((sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S :
        S.slice →L[ℂ] K) XC) =
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S) XC
    exact hcoe
  have him := sourceFullFrameGaugeSliceKernelDerivCLM_realComplexify_im d hM0R X
  simpa [hE, hM0C, S, XC, X] using him

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- If a kernel coordinate is real-valued, applying the inverse finite
kernel-coordinate equivalence gives a real-valued finite coordinate vector. -/
theorem sourceFullFrameRealSliceKernelCoordEquiv_symm_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (K : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
    (hKgram : ∀ a b : Fin (d + 1),
      Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0)
    (hKdet : Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0) :
    ∀ i : Fin F.realModelDim,
      Complex.im (((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm K)
        i) = 0 := by
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let q : Fin F.realModelDim → ℂ := E.symm K
  let qR : Fin F.realModelDim → ℝ := fun i => (q i).re
  let qI : Fin F.realModelDim → ℝ := fun i => (q i).im
  let KR := E (fun i => (qR i : ℂ))
  let KI := E (fun i => (qI i : ℂ))
  have hKRim := sourceFullFrameRealSliceKernelCoordEquiv_real_im d hM0R F qR
  have hKIim := sourceFullFrameRealSliceKernelCoordEquiv_real_im d hM0R F qI
  have hqsplit :
      q = (fun i => (qR i : ℂ)) +
        Complex.I • (fun i => (qI i : ℂ)) := by
    ext i
    simp [qR, qI, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (q i)).symm
  have hKsplit : K = KR + Complex.I • KI := by
    calc
      K = E q := (E.apply_symm_apply K).symm
      _ = E ((fun i => (qR i : ℂ)) +
            Complex.I • (fun i => (qI i : ℂ))) := by
        rw [hqsplit]
      _ = E (fun i => (qR i : ℂ)) +
            E (Complex.I • (fun i => (qI i : ℂ))) := by
        rw [map_add]
      _ = KR + Complex.I • KI := by
        rw [map_smul]
  have hKI_zero : KI = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext a b
      have hentry := congrArg
        (fun T : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker =>
          (((T : sourceFullFrameSymmetricCoordSubmodule d) :
            SourceFullFrameOrientedCoord d).1 a b)) hKsplit
      have him := congrArg Complex.im hentry
      have himKR : Complex.im (((KR : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := hKRim.1 a b
      have himKI : Complex.im (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := hKIim.1 a b
      have hreKI : Complex.re (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := by
        simp [Submodule.coe_add, hKgram a b,
          himKR, himKI, Complex.mul_im, Complex.I_re, Complex.I_im] at him
        exact him.symm
      apply Complex.ext
      · exact hreKI
      · exact himKI
    · have hentry := congrArg
        (fun T : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker =>
          (((T : sourceFullFrameSymmetricCoordSubmodule d) :
            SourceFullFrameOrientedCoord d).2)) hKsplit
      have him := congrArg Complex.im hentry
      have himKR : Complex.im (((KR : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := hKRim.2
      have himKI : Complex.im (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := hKIim.2
      have hreKI : Complex.re (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := by
        simp [Submodule.coe_add, hKdet,
          himKR, himKI, Complex.mul_im, Complex.I_re, Complex.I_im] at him
        exact him.symm
      apply Complex.ext
      · exact hreKI
      · exact himKI
  have hqI_zero : qI = 0 := by
    have h : (fun i => (qI i : ℂ)) = 0 := by
      apply E.injective
      simpa [KI] using hKI_zero
    ext i
    have hi := congrFun h i
    exact Complex.ofReal_injective hi
  intro i
  simpa [qI] using congrFun hqI_zero i

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit real-compatible normalized kernel map preserves the real
form in finite coordinates. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    ∀ i : Fin F.realModelDim,
      Complex.im (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (fun i => (q i : ℂ)) i) = 0 := by
  let K := sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
      (F.complexCoordEquiv (fun i => (q i : ℂ)))
  have hKreal :
      (∀ a b : Fin (d + 1),
        Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
        Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := by
    dsimp [K]
    rw [F.complexCoordEquiv_real_eq q]
    exact sourceFullFrameRealCompatibleExplicitKernelMap_real_im d hM0R
      (F.realCoordEquiv q)
  have hsymm := sourceFullFrameRealSliceKernelCoordEquiv_symm_real_im
    d hM0R F K hKreal.1 hKreal.2
  simpa [sourceFullFrameRealCompatibleNormalizedKernelMap, K] using hsymm

/-- Coordinatewise complexification as a continuous real-linear map. -/
noncomputable def sourceFullFrameRealCoordinateComplexifyCLM (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem sourceFullFrameRealCoordinateComplexifyCLM_apply
    (m : ℕ) (q : Fin m → ℝ) :
    sourceFullFrameRealCoordinateComplexifyCLM m q =
      fun i => (q i : ℂ) := by
  ext i
  simp [sourceFullFrameRealCoordinateComplexifyCLM]

/-- Coordinatewise real part as a continuous real-linear map. -/
noncomputable def sourceFullFrameComplexCoordinateReCLM (m : ℕ) :
    (Fin m → ℂ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.reCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem sourceFullFrameComplexCoordinateReCLM_apply
    (m : ℕ) (q : Fin m → ℂ) :
    sourceFullFrameComplexCoordinateReCLM m q =
      fun i => (q i).re := by
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- The real restriction of the explicit normalized kernel map. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelMapReal
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℝ) → (Fin F.realModelDim → ℝ) :=
  fun q => sourceFullFrameComplexCoordinateReCLM F.realModelDim
    (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
      (sourceFullFrameRealCoordinateComplexifyCLM F.realModelDim q))

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F 0 = 0 := by
  let fC := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let incl := sourceFullFrameRealCoordinateComplexifyCLM F.realModelDim
  have harg : incl (0 : Fin F.realModelDim → ℝ) =
      (0 : Fin F.realModelDim → ℂ) := by
    ext i
    simp [incl]
  have hzero :
      fC (incl (0 : Fin F.realModelDim → ℝ)) = 0 := by
    rw [harg]
    exact sourceFullFrameRealCompatibleNormalizedKernelMap_zero d hM0R F
  ext i
  change (fC (incl (0 : Fin F.realModelDim → ℝ)) i).re = 0
  rw [hzero]
  simp

set_option synthInstance.maxHeartbeats 100000 in
/-- Complexifying the real restriction recovers the explicit normalized
complex kernel map on real finite coordinates. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_complexify
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    SCV.realToComplex
        (sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F q) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (SCV.realToComplex q) := by
  change (fun i =>
      ((sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F q i : ℝ) :
        ℂ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (fun i => (q i : ℂ))
  ext i
  apply Complex.ext
  · simp [sourceFullFrameRealCompatibleNormalizedKernelMapReal,
      sourceFullFrameRealCoordinateComplexifyCLM]
  · simpa [sourceFullFrameRealCompatibleNormalizedKernelMapReal] using
      (sourceFullFrameRealCompatibleNormalizedKernelMap_real_im
        d hM0R F q i).symm

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The real restriction of the explicit normalized kernel map has identity
strict derivative at the origin. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F)
      (1 : (Fin F.realModelDim → ℝ) →L[ℝ]
        (Fin F.realModelDim → ℝ)) 0 := by
  let m := F.realModelDim
  let fC := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let incl := sourceFullFrameRealCoordinateComplexifyCLM m
  let re := sourceFullFrameComplexCoordinateReCLM m
  have hfC : HasStrictFDerivAt fC
      (1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
    simpa [fC, m] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  have hfC_R : HasStrictFDerivAt fC
      ((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ) 0 :=
    hfC.restrictScalars ℝ
  have hincl : HasStrictFDerivAt
      (fun q : Fin m → ℝ => incl q) incl 0 :=
    incl.hasStrictFDerivAt
  have hcomp1 : HasStrictFDerivAt
      (fun q : Fin m → ℝ => fC (incl q))
      (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl)
      0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := (0 : Fin m → ℝ))
        (g := fC) (f := fun q : Fin m → ℝ => incl q) hfC_R hincl)
  have hre : HasStrictFDerivAt
      (fun z : Fin m → ℂ => re z) re
      (fC (incl (0 : Fin m → ℝ))) :=
    re.hasStrictFDerivAt
  have hcomp2 : HasStrictFDerivAt
      (fun q : Fin m → ℝ => re (fC (incl q)))
      (re.comp
        (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl))
      0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := (0 : Fin m → ℝ))
        (g := fun z : Fin m → ℂ => re z)
        (f := fun q : Fin m → ℝ => fC (incl q)) hre hcomp1)
  have hderiv :
      re.comp
        (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl) =
      (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) := by
    ext q i
    simp [re, incl, sourceFullFrameComplexCoordinateReCLM,
      sourceFullFrameRealCoordinateComplexifyCLM]
  have hfun :
      (fun q : Fin m → ℝ => re (fC (incl q))) =
        sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F := by
    funext q
    rfl
  simpa [hfun, hderiv] using hcomp2

/-- The real inverse-function chart for the real restriction of the explicit
normalized kernel map. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph (Fin F.realModelDim → ℝ) (Fin F.realModelDim → ℝ) := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F
  let e : (Fin F.realModelDim → ℝ) ≃L[ℝ] (Fin F.realModelDim → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (Fin F.realModelDim → ℝ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℝ) →L[ℝ] (Fin F.realModelDim → ℝ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
        d hM0R F
  exact @HasStrictFDerivAt.toOpenPartialHomeomorph ℝ _
    (Fin F.realModelDim → ℝ) _ _ (Fin F.realModelDim → ℝ) _ _
    f e 0 inferInstance hderiv

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F : (Fin F.realModelDim → ℝ) → (Fin F.realModelDim → ℝ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F := by
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The real normalized kernel chart contains the origin in its source. -/
theorem sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℝ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).source := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F
  let e : (Fin F.realModelDim → ℝ) ≃L[ℝ] (Fin F.realModelDim → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (Fin F.realModelDim → ℝ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℝ) →L[ℝ] (Fin F.realModelDim → ℝ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
        d hM0R F
  unfold sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

/-- The real normalized kernel chart contains the origin in its target. -/
theorem sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℝ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
      d hM0R F
  have htarget :=
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).map_source hsource
  simpa using htarget

/-- Complex frame-level target coordinate for the real-compatible normalized
kernel chart.  It sends a full-frame matrix to the determinant-direction
projected symmetric equation coordinate, written in the finite kernel target
coordinates supplied by the real-form slice packet. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetCoordC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
      Fin F.realModelDim → ℂ :=
  fun M =>
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      (sourceFullFrameRealCompatibleKernelProjection d hM0R
        (sourceFullFrameSymmetrizeCoord d
            (sourceFullFrameOrientedGramCoord d M) -
          sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)))

/-- The complex frame-level target coordinate is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleFrameTargetCoordC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordC
  exact
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm.continuous.comp
      ((sourceFullFrameRealCompatibleKernelProjection d hM0R).continuous.comp
        (((continuous_sourceFullFrameSymmetrizeCoord d).comp
          (continuous_sourceFullFrameOrientedGramCoord d)).sub
            continuous_const))

@[simp]
theorem sourceFullFrameRealCompatibleFrameTargetCoordC_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
        (M0R.map Complex.ofReal) = 0 := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordC
  have hsymm :
      sourceFullFrameSymmetrizeCoord d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)) =
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) := by
    apply Subtype.ext
    simpa [sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d
        (sourceFullFrameOrientedGramCoord_mem_symmetric d
          (M0R.map Complex.ofReal))
  rw [hsymm, sub_self]
  change (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      ((sourceFullFrameRealCompatibleKernelProjection d hM0R) 0) = 0
  rw [(sourceFullFrameRealCompatibleKernelProjection d hM0R).map_zero]
  exact (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm.map_zero

/-- Ambient source-invariant version of the determinant-direction selected
kernel coordinate, written in the same finite target coordinates as
`sourceFullFrameRealCompatibleFrameTargetCoordC`. -/
noncomputable def sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (G : SourceOrientedGramData d n) :
    Fin F.realModelDim → ℂ :=
  (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
    (sourceFullFrameRealCompatibleKernelProjection d hM0R
      (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)))

/-- On real source invariants, the ambient determinant-direction selected
kernel coordinate is exactly the frame-level target coordinate of the selected
real full-frame matrix. -/
theorem sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_realInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
        d n ι hM0R F (sourceRealOrientedMinkowskiInvariant d n x) =
      sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
        ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal) := by
  unfold sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
  unfold sourceFullFrameRealCompatibleFrameTargetCoordC
  congr 2

@[simp]
theorem sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_base
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
        d n ι hM0R F (sourceRealOrientedMinkowskiInvariant d n x0) = 0 := by
  rw [sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_realInvariant]
  exact sourceFullFrameRealCompatibleFrameTargetCoordC_base d hM0R F

/-- The ambient determinant-direction selected finite coordinate is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
        d n ι hM0R F) := by
  unfold sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
  exact
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm.continuous.comp
      ((sourceFullFrameRealCompatibleKernelProjection d hM0R).continuous.comp
        ((continuous_sourceFullFrameSelectedSymmetricCoordAmbient d n ι).sub
          continuous_const))

/-- The explicit finite index used by the real-compatible full-frame chart.
It records first the real slice coordinate and then the selected mixed-row
coordinate, so the real and complex coordinate equivalences are componentwise
compatible. -/
abbrev sourceFullFrameRealCompatibleModelIndex
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ) :=
  Sum (Fin r) (Sigma fun _ : sourceComplementIndex ι => Fin (d + 1))

/-- Explicit finite coordinate equivalence for the real product model used by
the real-compatible full-frame chart. -/
noncomputable def sourceFullFrameRealCompatibleCoordEquiv
    (𝕜 : Type*) [Semiring 𝕜]
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ) :
    (Fin (Fintype.card (sourceFullFrameRealCompatibleModelIndex ι r)) → 𝕜) ≃ₗ[𝕜]
      ((Fin r → 𝕜) × (sourceComplementIndex ι → Fin (d + 1) → 𝕜)) where
  toFun v :=
    (fun i =>
      v (Fintype.equivFin (sourceFullFrameRealCompatibleModelIndex ι r)
        (Sum.inl i)),
      fun k a =>
        v (Fintype.equivFin (sourceFullFrameRealCompatibleModelIndex ι r)
          (Sum.inr ⟨k, a⟩)))
  invFun p := fun j =>
    match (Fintype.equivFin (sourceFullFrameRealCompatibleModelIndex ι r)).symm j with
    | Sum.inl i => p.1 i
    | Sum.inr ka => p.2 ka.1 ka.2
  left_inv v := by
    ext j
    generalize hα :
      (Fintype.equivFin (sourceFullFrameRealCompatibleModelIndex ι r)).symm j = a
    cases a with
    | inl i =>
        simp [hα]
        rw [← hα, Equiv.apply_symm_apply]
    | inr ka =>
        simp [hα]
        rw [← hα, Equiv.apply_symm_apply]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp
    · funext k a
      simp
  map_add' v w := by
    apply Prod.ext
    · funext i
      simp
    · funext k a
      simp
  map_smul' c v := by
    apply Prod.ext
    · funext i
      simp
    · funext k a
      simp

/-- Real finite coordinate equivalence for the real-compatible full-frame chart. -/
noncomputable def sourceFullFrameRealCompatibleCoordEquivR
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ) :
    (Fin (Fintype.card (sourceFullFrameRealCompatibleModelIndex ι r)) → ℝ) ≃ₗ[ℝ]
      ((Fin r → ℝ) × (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :=
  sourceFullFrameRealCompatibleCoordEquiv ℝ ι r

/-- Complex finite coordinate equivalence for the real-compatible full-frame
chart, using the same explicit reindexing as the real equivalence. -/
noncomputable def sourceFullFrameRealCompatibleCoordEquivC
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ) :
    (Fin (Fintype.card (sourceFullFrameRealCompatibleModelIndex ι r)) → ℂ) ≃ₗ[ℂ]
      ((Fin r → ℂ) × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :=
  sourceFullFrameRealCompatibleCoordEquiv ℂ ι r

/-- The explicit real and complex finite coordinate equivalences commute with
componentwise complexification. -/
theorem sourceFullFrameRealCompatibleCoordEquiv_realToComplex
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ)
    (u : Fin (Fintype.card (sourceFullFrameRealCompatibleModelIndex ι r)) → ℝ) :
    sourceFullFrameRealCompatibleCoordEquivC ι r (SCV.realToComplex u) =
      (SCV.realToComplex ((sourceFullFrameRealCompatibleCoordEquivR ι r u).1),
        fun k a =>
          (((sourceFullFrameRealCompatibleCoordEquivR ι r u).2 k a : ℝ) : ℂ)) := by
  apply Prod.ext
  · funext i
    rfl
  · funext k a
    rfl

/-- Product model for the determinant-direction compatible complex chart. -/
abbrev sourceFullFrameRealCompatibleChartModel
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    (r : ℕ) :=
  (Fin r → ℂ) × (sourceComplementIndex ι → Fin (d + 1) → ℂ)

/-- Finite source coordinate obtained by inverting the compatible complex
normalized-kernel chart at the selected ambient determinant-direction
coordinate. -/
noncomputable def sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R)
    (G : SourceOrientedGramData d n) :
    Fin F.realModelDim → ℂ :=
  (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
    d hM0R F).symm
    (sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
      d n ι hM0R F G)

/-- The raw determinant-direction complex chart before the final finite
reindexing to `Fin m -> ℂ`.  Its first coordinate is the inverse finite
kernel coordinate for the checked compatible complex IFT chart; its second
coordinate is the selected mixed-row coordinate. -/
noncomputable def sourceFullFrameRealCompatibleChartRaw
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    SourceOrientedGramData d n →
      sourceFullFrameRealCompatibleChartModel ι F.realModelDim :=
  fun G =>
    (sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F G,
      sourceSelectedMixedRows d n ι G)

/-- The reconstruction inverse for the raw determinant-direction compatible
chart. -/
noncomputable def sourceFullFrameRealCompatibleChartModelToGaugeModel
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceFullFrameRealCompatibleChartModel ι F.realModelDim →
      sourceFullFrameMaxRankChartModel d n ι
        ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)) :=
  fun y => (F.complexCoordEquiv y.1, y.2)

/-- The map from raw compatible product coordinates to gauge-reconstruction
coordinates is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleChartModelToGaugeModel
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F) := by
  unfold sourceFullFrameRealCompatibleChartModelToGaugeModel
  exact F.complexCoordEquiv.continuous.comp continuous_fst |>.prodMk continuous_snd

/-- The map from raw compatible product coordinates to gauge-reconstruction
coordinates is complex differentiable. -/
theorem differentiable_sourceFullFrameRealCompatibleChartModelToGaugeModel
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Differentiable ℂ
      (sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F) := by
  unfold sourceFullFrameRealCompatibleChartModelToGaugeModel
  exact Differentiable.prodMk
    (F.complexCoordEquiv.differentiable.comp differentiable_fst)
    differentiable_snd

/-- The reconstruction inverse for the raw determinant-direction compatible
chart. -/
noncomputable def sourceFullFrameRealCompatibleChartInvRaw
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceFullFrameRealCompatibleChartModel ι F.realModelDim →
      SourceOrientedGramData d n :=
  fun y =>
    sourceFullFrameGauge_reconstructInvariant d n ι
      ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
      (sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y)

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- Reconstructing from a raw compatible model coordinate and then reading the
ambient determinant-direction finite kernel coordinate gives the normalized
kernel map of the first model coordinate. -/
theorem sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_reconstructInvariant_eq
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R)
    (y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim) :
    sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
        d n ι hM0R F
        (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F y.1 := by
  let M0 := (sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal
  let S := sourceFullFrameExplicitGaugeSliceData d
    (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  let yg : sourceFullFrameMaxRankChartModel d n ι M0 S :=
    sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y
  let H : SourceOrientedGramData d n :=
    sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y
  have hHvar : H ∈ sourceOrientedGramVariety d n := by
    simpa [H, sourceFullFrameRealCompatibleChartInvRaw, M0, S, yg] using
      sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S yg
  have hsymm :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι H =
        sourceFullFrameGaugeSliceMapSymmetric d M0 S yg.1 := by
    rw [sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety
      d n ι hHvar]
    apply Subtype.ext
    simpa [H, M0, S, yg, sourceFullFrameRealCompatibleChartInvRaw,
      sourceFullFrameRealCompatibleChartModelToGaugeModel,
      sourceFullFrameSelectedSymmetricCoordOfSource,
      sourceFullFrameGaugeSliceMapSymmetric] using
      sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq
        d n ι M0 S yg
  unfold sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
  unfold sourceFullFrameRealCompatibleNormalizedKernelMap
  unfold sourceFullFrameRealCompatibleExplicitKernelMap
  rw [hsymm]
  rfl

/-- The raw determinant-direction compatible chart domain.  It is deliberately
spelled as the conjunction of the source-variety condition, the selected
determinant-nonzero condition, and the two ambient-chart source/target shrink
conditions used by the reconstruction proof. -/
def sourceFullFrameRealCompatibleChartDomain
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Set (SourceOrientedGramData d n) :=
  {G |
    G ∈ sourceOrientedGramVariety d n ∧
      G.det ι ≠ 0 ∧
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source ∧
      sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
          d n ι hM0R F G ∈
        (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
          d hM0R F).target ∧
      sourceFullFrameGaugeSliceMapSymmetric d
          ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
          (sourceFullFrameExplicitGaugeSliceData d
            (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
          (F.complexCoordEquiv
            (sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
              ι hM0R F G)) ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source}

theorem sourceFullFrameRealCompatibleChartDomain_mem_variety
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    G ∈ sourceOrientedGramVariety d n :=
  hG.1

theorem sourceFullFrameRealCompatibleChartDomain_det_ne_zero
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    G.det ι ≠ 0 :=
  hG.2.1

theorem sourceFullFrameRealCompatibleChartDomain_maxRank
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    SourceOrientedMaxRankAt d n G :=
  sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι
    (sourceFullFrameRealCompatibleChartDomain_mem_variety hG)
    (sourceFullFrameRealCompatibleChartDomain_det_ne_zero hG)

theorem sourceFullFrameRealCompatibleChartDomain_selectedSymmetric_mem_source
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
      (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R).source :=
  hG.2.2.1

theorem sourceFullFrameRealCompatibleChartDomain_selectedKernel_mem_target
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC d n ι hM0R F G ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).target :=
  hG.2.2.2.1

theorem sourceFullFrameRealCompatibleChartDomain_gaugeSlice_mem_source
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameGaugeSliceMapSymmetric d
        ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        (F.complexCoordEquiv
          (sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
            ι hM0R F G)) ∈
      (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
        d hM0R).source :=
  hG.2.2.2.2

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- The real base invariant belongs to the raw compatible chart domain. -/
theorem sourceFullFrameRealCompatibleChartDomain_center_mem
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceRealOrientedMinkowskiInvariant d n x0 ∈
      sourceFullFrameRealCompatibleChartDomain ι hM0R F := by
  let G0 := sourceRealOrientedMinkowskiInvariant d n x0
  let M0R := sourceRealFullFrameMatrix d n ι x0
  let M0 := M0R.map Complex.ofReal
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F
  have hG0var : G0 ∈ sourceOrientedGramVariety d n := by
    simpa [G0] using sourceRealOrientedMinkowskiInvariant_mem_variety d n x0
  have hdet : G0.det ι ≠ 0 := by
    rw [sourceRealOrientedMinkowskiInvariant_det]
    exact_mod_cast hM0R.ne_zero
  have hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0 := by
    simpa [G0, M0, M0R] using
      (sourceFullFrameOrientedCoordOfSource_sourceRealOrientedMinkowskiInvariant
        d n ι x0).symm
  have hselected_source :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0 ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source := by
    rw [sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
      d n ι hG0var hM0_oriented]
    simpa [M0, M0R] using
      sourceFullFrameRealCompatibleSymmetricEquation_base_mem_chartSource
        d hM0R
  have hkernel_target :
      sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
          d n ι hM0R F G0 ∈ eK.target := by
    rw [sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_base]
    simpa [eK] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartTarget
        d hM0R F
  have hsource0 : (0 : Fin F.realModelDim → ℂ) ∈ eK.source := by
    simpa [eK] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
        d hM0R F
  have htarget0 : (0 : Fin F.realModelDim → ℂ) ∈ eK.target := by
    simpa [eK] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartTarget
        d hM0R F
  have hmap0 : eK (0 : Fin F.realModelDim → ℂ) =
      (0 : Fin F.realModelDim → ℂ) := by
    rw [sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe]
    exact sourceFullFrameRealCompatibleNormalizedKernelMap_zero d hM0R F
  have hsymm0 : eK.symm (0 : Fin F.realModelDim → ℂ) =
      (0 : Fin F.realModelDim → ℂ) :=
    ((eK.eq_symm_apply hsource0 htarget0).mpr hmap0).symm
  have hkernel_source_coord :
      sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F G0 =
        (0 : Fin F.realModelDim → ℂ) := by
    unfold sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
    rw [sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_base]
    exact hsymm0
  have hgauge_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0
          (sourceFullFrameExplicitGaugeSliceData d
            (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
          (F.complexCoordEquiv
            (sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
              ι hM0R F G0)) ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source := by
    rw [hkernel_source_coord]
    simp [sourceFullFrameGaugeSliceMapSymmetric_zero, M0, M0R,
      sourceFullFrameRealCompatibleSymmetricEquation_base_mem_chartSource
        d hM0R]
  exact ⟨hG0var, hdet, hselected_source, hkernel_target, by
    simpa [G0, M0, M0R, eK] using hgauge_source⟩

@[simp]
theorem sourceFullFrameRealCompatibleSelectedKernelSourceCoordC_base
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F
        (sourceRealOrientedMinkowskiInvariant d n x0) = 0 := by
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F
  have hsource0 : (0 : Fin F.realModelDim → ℂ) ∈ eK.source := by
    simpa [eK] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
        d hM0R F
  have htarget0 : (0 : Fin F.realModelDim → ℂ) ∈ eK.target := by
    simpa [eK] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartTarget
        d hM0R F
  have hmap0 : eK (0 : Fin F.realModelDim → ℂ) =
      (0 : Fin F.realModelDim → ℂ) := by
    rw [sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe]
    exact sourceFullFrameRealCompatibleNormalizedKernelMap_zero d hM0R F
  have hsymm0 : eK.symm (0 : Fin F.realModelDim → ℂ) =
      (0 : Fin F.realModelDim → ℂ) :=
    ((eK.eq_symm_apply hsource0 htarget0).mpr hmap0).symm
  unfold sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
  rw [sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_base]
  exact hsymm0

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- On model points whose first coordinate lies in the compatible finite
kernel-chart source, raw reconstruction is a right inverse as soon as the
reconstructed invariant lies in the raw chart domain. -/
theorem sourceFullFrameRealCompatibleChartRaw_invRaw_eq_of_source_mem_domain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy_source :
      y.1 ∈
        (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
          d hM0R F).source)
    (hy_domain :
      sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y ∈
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartRaw ι hM0R F
        (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y) = y := by
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F
  let M0 := (sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal
  let S := sourceFullFrameExplicitGaugeSliceData d
    (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  let yg : sourceFullFrameMaxRankChartModel d n ι M0 S :=
    sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y
  apply Prod.ext
  · change
      sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F
          (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y) = y.1
    unfold sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
    calc
      eK.symm
          (sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
            d n ι hM0R F
            (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y))
          =
        eK.symm
          (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F y.1) := by
          rw [sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC_reconstructInvariant_eq]
      _ = eK.symm (eK y.1) := by
          rw [sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe]
      _ = y.1 := eK.left_inv hy_source
  · have hdetH :
        (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y).det ι ≠ 0 :=
      sourceFullFrameRealCompatibleChartDomain_det_ne_zero hy_domain
    have hframe_det :
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S yg).det ≠ 0 := by
      rw [← sourceFullFrameGauge_reconstructInvariant_selectedDet
        d n ι M0 S yg]
      simpa [sourceFullFrameRealCompatibleChartInvRaw, M0, S, yg] using hdetH
    simpa [sourceFullFrameRealCompatibleChartRaw,
      sourceFullFrameRealCompatibleChartInvRaw,
      sourceFullFrameRealCompatibleChartModelToGaugeModel, M0, S, yg] using
      sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero
        d n ι M0 S yg hframe_det

/-- Model-side domain for the raw compatible chart: the finite kernel
coordinate lies in the compatible IFT source and raw reconstruction lands in
the raw source-variety chart domain.  The next shrink step proves this set is
open and uses it as the chart image. -/
def sourceFullFrameRealCompatibleModelChartDomain
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Set (sourceFullFrameRealCompatibleChartModel ι F.realModelDim) :=
  {y |
    y.1 ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).source ∧
    sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y ∈
      sourceFullFrameRealCompatibleChartDomain ι hM0R F}

theorem sourceFullFrameRealCompatibleModelChartDomain_source
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy : y ∈ sourceFullFrameRealCompatibleModelChartDomain ι hM0R F) :
    y.1 ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).source :=
  hy.1

theorem sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy : y ∈ sourceFullFrameRealCompatibleModelChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y ∈
      sourceFullFrameRealCompatibleChartDomain ι hM0R F :=
  hy.2

/-- The raw model-side domain is contained in the image of the raw chart on
the raw source-domain. -/
theorem sourceFullFrameRealCompatibleModelChartDomain_subset_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    sourceFullFrameRealCompatibleModelChartDomain ι hM0R F ⊆
      sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F := by
  intro y hy
  refine
    ⟨sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y,
      sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain hy, ?_⟩
  exact
    sourceFullFrameRealCompatibleChartRaw_invRaw_eq_of_source_mem_domain
      (sourceFullFrameRealCompatibleModelChartDomain_source hy)
      (sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain hy)

/-- The source-side shrink obtained by pulling the model-side raw chart domain
back through raw reconstruction. -/
def sourceFullFrameRealCompatibleShrunkenChartDomain
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Set (SourceOrientedGramData d n) :=
  sourceFullFrameRealCompatibleChartInvRaw ι hM0R F ''
    sourceFullFrameRealCompatibleModelChartDomain ι hM0R F

/-- The shrunken source domain lies inside the raw compatible chart domain. -/
theorem sourceFullFrameRealCompatibleShrunkenChartDomain_subset_rawDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    sourceFullFrameRealCompatibleShrunkenChartDomain ι hM0R F ⊆
      sourceFullFrameRealCompatibleChartDomain ι hM0R F := by
  rintro G ⟨y, hy, rfl⟩
  exact sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain hy

/-- On the shrunken source domain, the raw compatible chart image is exactly
the model-side raw chart domain. -/
theorem sourceFullFrameRealCompatibleChartRaw_image_shrunkenDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleShrunkenChartDomain ι hM0R F =
      sourceFullFrameRealCompatibleModelChartDomain ι hM0R F := by
  ext y
  constructor
  · rintro ⟨G, hG, hGy⟩
    rcases hG with ⟨x, hx, rfl⟩
    have hxeq :
        sourceFullFrameRealCompatibleChartRaw ι hM0R F
            (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F x) = x :=
      sourceFullFrameRealCompatibleChartRaw_invRaw_eq_of_source_mem_domain
        (sourceFullFrameRealCompatibleModelChartDomain_source hx)
        (sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain hx)
    have hyx : y = x := by
      rw [hxeq] at hGy
      exact hGy.symm
    simpa [hyx] using hx
  · intro hy
    refine
      ⟨sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y,
        ⟨y, hy, rfl⟩, ?_⟩
    exact
      sourceFullFrameRealCompatibleChartRaw_invRaw_eq_of_source_mem_domain
        (sourceFullFrameRealCompatibleModelChartDomain_source hy)
        (sourceFullFrameRealCompatibleModelChartDomain_inv_mem_domain hy)

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- The compatible complex IFT right-inverse converts the finite selected-kernel
coordinate into the determinant-direction projection equality needed by the raw
chart reconstruction proof. -/
theorem sourceFullFrameRealCompatibleChartRaw_projection_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleKernelProjection d hM0R
        (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
          sourceFullFrameSymmetricBase d
            ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) =
      sourceFullFrameRealCompatibleKernelProjection d hM0R
        (sourceFullFrameGaugeSliceMapSymmetric d
            ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
            (sourceFullFrameExplicitGaugeSliceData d
              (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
            (F.complexCoordEquiv
              (sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
                ι hM0R F G)) -
          sourceFullFrameSymmetricBase d
            ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) := by
  let q := sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F G
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F
  have htarget :=
    sourceFullFrameRealCompatibleChartDomain_selectedKernel_mem_target hG
  have hright : eK q =
      sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
        d n ι hM0R F G := by
    simpa [q, eK, sourceFullFrameRealCompatibleSelectedKernelSourceCoordC] using
      eK.right_inv htarget
  have hright' :
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F q =
        sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
          d n ι hM0R F G := by
    simpa [eK] using hright
  have hcongr :=
    congrArg (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F) hright'
  simpa [q, sourceFullFrameRealCompatibleNormalizedKernelMap,
    sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC,
    sourceFullFrameRealCompatibleExplicitKernelMap] using hcongr.symm

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 600000 in
/-- The raw compatible product chart reconstructs the original source invariant
on the shrunken determinant-direction domain. -/
theorem sourceFullFrameRealCompatibleChartInvRaw_left_inv
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartInvRaw ι hM0R F
      (sourceFullFrameRealCompatibleChartRaw ι hM0R F G) = G := by
  let q := sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F G
  let S := sourceFullFrameExplicitGaugeSliceData d
    (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  let y : sourceFullFrameMaxRankChartModel d n ι
      ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal) S :=
    (F.complexCoordEquiv q, sourceSelectedMixedRows d n ι G)
  have hGvar : G ∈ sourceOrientedGramVariety d n :=
    sourceFullFrameRealCompatibleChartDomain_mem_variety hG
  have hdet : G.det ι ≠ 0 :=
    sourceFullFrameRealCompatibleChartDomain_det_ne_zero hG
  have hselected_eq :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G =
        sourceFullFrameSelectedSymmetricCoordOfSource d n ι hGvar :=
    sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety d n ι hGvar
  have hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hGvar ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source := by
    simpa [← hselected_eq] using
      sourceFullFrameRealCompatibleChartDomain_selectedSymmetric_mem_source hG
  have hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d
          ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal) S y.1 ∈
        (sourceFullFrameRealCompatibleSymmetricEquationOpenPartialHomeomorphC
          d hM0R).source := by
    simpa [q, S, y] using
      sourceFullFrameRealCompatibleChartDomain_gaugeSlice_mem_source hG
  have hprojection_ambient :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
            sourceFullFrameSymmetricBase d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameGaugeSliceMapSymmetric d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal) S y.1 -
            sourceFullFrameSymmetricBase d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) := by
    simpa [q, S, y] using
      sourceFullFrameRealCompatibleChartRaw_projection_eq hG
  have hprojection :
      sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hGvar -
            sourceFullFrameSymmetricBase d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) =
        sourceFullFrameRealCompatibleKernelProjection d hM0R
          (sourceFullFrameGaugeSliceMapSymmetric d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal) S y.1 -
            sourceFullFrameSymmetricBase d
              ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)) := by
    simpa [← hselected_eq] using hprojection_ambient
  change sourceFullFrameGauge_reconstructInvariant d n ι
      ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal) S y = G
  exact
    sourceFullFrameGauge_reconstructInvariant_eq_of_realCompatibleProjection_eq_mixedRows_eq
      d n ι hM0R S hGvar hdet y hG_source hX_source hprojection rfl

/-- The raw chart coordinate of the real base point belongs to the model-side
domain for the open-image shrink. -/
theorem sourceFullFrameRealCompatibleChartRaw_center_mem_modelChartDomain
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    sourceFullFrameRealCompatibleChartRaw ι hM0R F
        (sourceRealOrientedMinkowskiInvariant d n x0) ∈
      sourceFullFrameRealCompatibleModelChartDomain ι hM0R F := by
  constructor
  · simpa [sourceFullFrameRealCompatibleChartRaw] using
      sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
        d hM0R F
  · have hcenter :=
      sourceFullFrameRealCompatibleChartDomain_center_mem ι hM0R F
    rw [sourceFullFrameRealCompatibleChartInvRaw_left_inv hcenter]
    exact hcenter

/-- The raw compatible product chart is right-inverse to reconstruction on its
chart image. -/
theorem sourceFullFrameRealCompatibleChartRaw_right_inv_on_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy : y ∈
      sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartRaw ι hM0R F
        (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y) = y := by
  rcases hy with ⟨G, hG, rfl⟩
  rw [sourceFullFrameRealCompatibleChartInvRaw_left_inv hG]

/-- Reconstructing a point of the raw chart image lands back in the raw
compatible chart domain. -/
theorem sourceFullFrameRealCompatibleChartInvRaw_mem_domain_on_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy : y ∈
      sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartInvRaw ι hM0R F y ∈
      sourceFullFrameRealCompatibleChartDomain ι hM0R F := by
  rcases hy with ⟨G, hG, rfl⟩
  rw [sourceFullFrameRealCompatibleChartInvRaw_left_inv hG]
  exact hG

set_option maxHeartbeats 500000 in
/-- Points in the raw chart image correspond to gauge-model coordinates with
invertible reconstructed selected frame. -/
theorem sourceFullFrameRealCompatibleChartRaw_modelDetNonzero_on_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R}
    {y : sourceFullFrameRealCompatibleChartModel ι F.realModelDim}
    (hy : y ∈
      sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) :
    sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y ∈
      sourceFullFrameGaugeModelDetNonzero d n ι
        ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)) := by
  rcases hy with ⟨G, hG, rfl⟩
  have hleft := sourceFullFrameRealCompatibleChartInvRaw_left_inv hG
  have hdet : G.det ι ≠ 0 :=
    sourceFullFrameRealCompatibleChartDomain_det_ne_zero hG
  rw [mem_sourceFullFrameGaugeModelDetNonzero]
  have hdet_eq :
      (sourceFullFrameGauge_reconstructInvariant d n ι
        ((sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        (sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F
          (sourceFullFrameRealCompatibleChartRaw ι hM0R F G))).det ι =
        G.det ι := by
    simpa [sourceFullFrameRealCompatibleChartInvRaw] using
      congrArg (fun H : SourceOrientedGramData d n => H.det ι) hleft
  rw [← sourceFullFrameGauge_reconstructInvariant_selectedDet]
  rw [hdet_eq]
  exact hdet

/-- The raw compatible chart is continuous on the shrunken domain. -/
theorem continuousOn_sourceFullFrameRealCompatibleChartRaw
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    ContinuousOn (sourceFullFrameRealCompatibleChartRaw ι hM0R F)
      (sourceFullFrameRealCompatibleChartDomain ι hM0R F) := by
  have hfst : ContinuousOn
      (fun G : SourceOrientedGramData d n =>
        sourceFullFrameRealCompatibleSelectedKernelSourceCoordC ι hM0R F G)
      (sourceFullFrameRealCompatibleChartDomain ι hM0R F) := by
    unfold sourceFullFrameRealCompatibleSelectedKernelSourceCoordC
    exact
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).continuousOn_symm.comp
        (continuous_sourceFullFrameRealCompatibleSelectedKernelCoordAmbientC
          ι hM0R F).continuousOn
        (fun _G hG =>
          sourceFullFrameRealCompatibleChartDomain_selectedKernel_mem_target hG)
  have hsnd : ContinuousOn (sourceSelectedMixedRows d n ι)
      (sourceFullFrameRealCompatibleChartDomain ι hM0R F) :=
    (continuous_sourceSelectedMixedRows d n ι).continuousOn
  simpa [sourceFullFrameRealCompatibleChartRaw] using hfst.prodMk hsnd

/-- The raw compatible reconstruction inverse is continuous on the raw chart
image. -/
theorem continuousOn_sourceFullFrameRealCompatibleChartInvRaw_on_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    ContinuousOn (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F)
      (sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) := by
  let M0 := (sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal
  let S := sourceFullFrameExplicitGaugeSliceData d
    (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hrec : ContinuousOn
      (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) :=
    continuousOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
      d n ι M0 S
  have hmodel :
      Continuous (sourceFullFrameRealCompatibleChartModelToGaugeModel
        ι hM0R F) :=
    continuous_sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F
  have hsubset :
      ∀ y ∈ sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
          sourceFullFrameRealCompatibleChartDomain ι hM0R F,
        sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y ∈
          sourceFullFrameGaugeModelDetNonzero d n ι M0 S := by
    intro y hy
    simpa [M0, S] using
      sourceFullFrameRealCompatibleChartRaw_modelDetNonzero_on_image hy
  simpa [sourceFullFrameRealCompatibleChartInvRaw, M0, S] using
    hrec.comp hmodel.continuousOn hsubset

/-- The raw compatible reconstruction inverse is complex differentiable on the
raw chart image. -/
theorem differentiableOn_sourceFullFrameRealCompatibleChartInvRaw_on_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det}
    {F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R} :
    DifferentiableOn ℂ (sourceFullFrameRealCompatibleChartInvRaw ι hM0R F)
      (sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
        sourceFullFrameRealCompatibleChartDomain ι hM0R F) := by
  let M0 := (sourceRealFullFrameMatrix d n ι x0).map Complex.ofReal
  let S := sourceFullFrameExplicitGaugeSliceData d
    (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hrec : DifferentiableOn ℂ
      (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) :=
    differentiableOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
      d n ι M0 S
  have hmodel :
      Differentiable ℂ (sourceFullFrameRealCompatibleChartModelToGaugeModel
        ι hM0R F) :=
    differentiable_sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F
  have hsubset :
      ∀ y ∈ sourceFullFrameRealCompatibleChartRaw ι hM0R F ''
          sourceFullFrameRealCompatibleChartDomain ι hM0R F,
        sourceFullFrameRealCompatibleChartModelToGaugeModel ι hM0R F y ∈
          sourceFullFrameGaugeModelDetNonzero d n ι M0 S := by
    intro y hy
    simpa [M0, S] using
      sourceFullFrameRealCompatibleChartRaw_modelDetNonzero_on_image hy
  simpa [sourceFullFrameRealCompatibleChartInvRaw, M0, S] using
    hrec.comp (hmodel.differentiableOn) hsubset

/-- Local biholomorphic inverse data for the raw determinant-direction
compatible product chart.  The separate max-rank chart packet still needs the
open-image shrink which turns this raw local inverse into a
`SourceOrientedMaxRankChartData`. -/
noncomputable def sourceFullFrameRealCompatibleLocalBiholomorphRaw
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    LocalBiholomorphOnSourceOrientedVariety d n
      (sourceFullFrameRealCompatibleChartDomain ι hM0R F)
      (sourceFullFrameRealCompatibleChartRaw ι hM0R F) where
  inv := sourceFullFrameRealCompatibleChartInvRaw ι hM0R F
  left_inv_on := by
    intro G hG
    exact sourceFullFrameRealCompatibleChartInvRaw_left_inv hG
  right_inv_on := by
    intro y hy
    exact sourceFullFrameRealCompatibleChartRaw_right_inv_on_image hy
  inv_mem_on := by
    intro y hy
    exact sourceFullFrameRealCompatibleChartInvRaw_mem_domain_on_image hy
  chart_continuousOn :=
    continuousOn_sourceFullFrameRealCompatibleChartRaw
  inv_differentiableOn :=
    differentiableOn_sourceFullFrameRealCompatibleChartInvRaw_on_image
  inv_continuousOn :=
    continuousOn_sourceFullFrameRealCompatibleChartInvRaw_on_image

/-- Complex derivative of the frame-level target coordinate used by the
selected-frame product-chart construction. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetDerivC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
      (Fin F.realModelDim → ℂ) :=
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  ((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm :
      K →L[ℂ] (Fin F.realModelDim → ℂ)).comp
    ((sourceFullFrameRealCompatibleKernelProjection d hM0R).comp
      ((sourceFullFrameSymmetrizeCoordCLM d).comp
        (sourceFullFrameOrientedDifferentialCLM d (M0R.map Complex.ofReal))))

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The complex frame-level target coordinate has the explicit derivative
obtained by differentiating the oriented full-frame invariant, symmetrizing,
projecting to the real-compatible tangent kernel, and applying finite kernel
coordinates. -/
theorem sourceFullFrameRealCompatibleFrameTargetCoordC_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F)
      (sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F)
      (M0R.map Complex.ofReal) := by
  let M0C := M0R.map Complex.ofReal
  let Lsym := sourceFullFrameSymmetrizeCoordCLM d
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0C)).ker
  let P : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ] K :=
    sourceFullFrameRealCompatibleKernelProjection d hM0R
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let Es : K →L[ℂ] (Fin F.realModelDim → ℂ) := E.symm
  have hGram : HasStrictFDerivAt
      (sourceFullFrameOrientedGramCoord d)
      (sourceFullFrameOrientedDifferentialCLM d M0C) M0C := by
    simpa [M0C] using sourceFullFrameOrientedGram_hasStrictFDerivAt
      (d := d) (M0 := M0C)
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hL : HasStrictFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => Lsym H)
      Lsym (sourceFullFrameOrientedGramCoord d M0C) :=
    Lsym.hasStrictFDerivAt
  have hSymm : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Lsym (sourceFullFrameOrientedGramCoord d M))
      (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)) M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := fun H : SourceFullFrameOrientedCoord d => Lsym H)
        (f := sourceFullFrameOrientedGramCoord d) hL hGram)
  let base := sourceFullFrameSymmetricBase d M0C
  have hSub : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Lsym (sourceFullFrameOrientedGramCoord d M) - base)
      (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)) M0C := by
    exact hSymm.sub_const base
  have hP : HasStrictFDerivAt
      (P : sourceFullFrameSymmetricCoordSubmodule d → K)
      P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ _
      K _ _ _
      P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base)
  have hPcomp : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        P (Lsym (sourceFullFrameOrientedGramCoord d M) - base))
      (P.comp (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)))
      M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := (P : sourceFullFrameSymmetricCoordSubmodule d → K))
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          Lsym (sourceFullFrameOrientedGramCoord d M) - base) hP hSub)
  have hE : HasStrictFDerivAt
      (Es : K → Fin F.realModelDim → ℂ)
      Es (P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base)) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      K _ _ _
      (Fin F.realModelDim → ℂ) _ _ _
      Es (P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base))
  have hcomp : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Es (P (Lsym (sourceFullFrameOrientedGramCoord d M) - base)))
      (Es.comp (P.comp (Lsym.comp
        (sourceFullFrameOrientedDifferentialCLM d M0C)))) M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := (Es : K → Fin F.realModelDim → ℂ))
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          P (Lsym (sourceFullFrameOrientedGramCoord d M) - base))
        hE hPcomp)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with M
  simp [sourceFullFrameRealCompatibleFrameTargetCoordC,
    M0C, Lsym, P, E, Es, K, base, sourceFullFrameSymmetrizeCoordCLM]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- On the explicit complex slice coordinates, the complex frame-target
derivative recovers the finite coordinate vector. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivC_complexCoordEquiv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℂ) :
    sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (F.complexCoordEquiv q :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = q := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let X : S.slice := F.complexCoordEquiv q
  have hsymm :
      (sourceFullFrameSymmetrizeCoordCLM d)
          (sourceFullFrameOrientedDifferentialCLM d (M0R.map Complex.ofReal)
            (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) =
        sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X := by
    apply Subtype.ext
    change
      (sourceFullFrameSymmetrizeCoord d
          (sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
            (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :
          SourceFullFrameOrientedCoord d) =
        sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    exact sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X).property
  have hproj :
      (sourceFullFrameRealCompatibleKernelProjection d hM0R)
          (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X) =
        sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X := by
    have hp := sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X)
    simpa [sourceFullFrameGaugeSliceKernelDerivCLM] using hp
  calc
    sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (F.complexCoordEquiv q :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
        = E.symm ((sourceFullFrameRealCompatibleKernelProjection d hM0R)
            ((sourceFullFrameSymmetrizeCoordCLM d)
              (sourceFullFrameOrientedDifferentialCLM d
                (M0R.map Complex.ofReal)
                (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)))) := by
          simp [sourceFullFrameRealCompatibleFrameTargetDerivC, E, X]
    _ = E.symm (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X) := by
          rw [hsymm, hproj]
    _ = q := by
          rw [← sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
          let e :=
            sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv
              d hM0C S
          change F.complexCoordEquiv.symm
              (e.symm (e (F.complexCoordEquiv q))) = q
          rw [ContinuousLinearEquiv.symm_apply_apply]
          exact ContinuousLinearEquiv.symm_apply_apply F.complexCoordEquiv q

/-- Complexification of real full-frame matrices as a continuous real-linear
map. -/
noncomputable def sourceFullFrameRealMatrixComplexifyCLM
    (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j =>
      Complex.ofRealCLM.comp
        ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.proj i :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
              Fin (d + 1) → ℝ))

@[simp]
theorem sourceFullFrameRealMatrixComplexifyCLM_apply
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameRealMatrixComplexifyCLM d M = M.map Complex.ofReal := by
  ext i j
  change Complex.ofRealCLM (M i j) = (M i j : ℂ)
  simp

/-- Real frame-level target coordinate, obtained by restricting the complex
target coordinate to complexified real frames and taking coordinatewise real
part. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
      Fin F.realModelDim → ℝ :=
  fun M =>
    sourceFullFrameComplexCoordinateReCLM F.realModelDim
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
        (M.map Complex.ofReal))

/-- The real frame-level target coordinate is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleFrameTargetCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordR
  apply (sourceFullFrameComplexCoordinateReCLM F.realModelDim).continuous.comp
  apply
    (continuous_sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F).comp
  fun_prop

@[simp]
theorem sourceFullFrameRealCompatibleFrameTargetCoordR_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M0R = 0 := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordR
  rw [sourceFullFrameRealCompatibleFrameTargetCoordC_base d hM0R F]
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- Real derivative of the frame-level target coordinate used by the
selected-frame product-chart construction. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetDerivR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
      (Fin F.realModelDim → ℝ) :=
  (sourceFullFrameComplexCoordinateReCLM F.realModelDim).comp
    (((sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F).restrictScalars ℝ).comp
      (sourceFullFrameRealMatrixComplexifyCLM d))

set_option synthInstance.maxHeartbeats 140000 in
set_option maxHeartbeats 500000 in
/-- The real frame-level target coordinate has the real derivative obtained by
restricting the complex derivative to complexified real matrices and taking
coordinatewise real part. -/
theorem sourceFullFrameRealCompatibleFrameTargetCoordR_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F)
      (sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F)
      M0R := by
  let fC := sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
  let LC := sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
  let incl := sourceFullFrameRealMatrixComplexifyCLM d
  let re := sourceFullFrameComplexCoordinateReCLM F.realModelDim
  have hC : HasStrictFDerivAt fC LC (M0R.map Complex.ofReal) := by
    simpa [fC, LC] using
      sourceFullFrameRealCompatibleFrameTargetCoordC_hasStrictFDerivAt
        d hM0R F
  have hC_R : HasStrictFDerivAt fC (LC.restrictScalars ℝ)
      (M0R.map Complex.ofReal) :=
    hC.restrictScalars ℝ
  have hC_at_incl : HasStrictFDerivAt fC (LC.restrictScalars ℝ)
      (incl M0R) := by
    simpa [incl] using hC_R
  have hincl : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => incl M)
      incl M0R :=
    ContinuousLinearMap.hasStrictFDerivAt incl (x := M0R)
  have hcomp1 : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => fC (incl M))
      ((LC.restrictScalars ℝ).comp incl) M0R := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := M0R)
        (g := fC)
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => incl M)
        hC_at_incl hincl)
  have hre : HasStrictFDerivAt
      (fun q : Fin F.realModelDim → ℂ => re q)
      re (fC (incl M0R)) :=
    ContinuousLinearMap.hasStrictFDerivAt re (x := fC (incl M0R))
  have hcomp2 : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
        re (fC (incl M)))
      (re.comp ((LC.restrictScalars ℝ).comp incl)) M0R := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := M0R)
        (g := fun q : Fin F.realModelDim → ℂ => re q)
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
          fC (incl M)) hre hcomp1)
  simpa [sourceFullFrameRealCompatibleFrameTargetCoordR,
    sourceFullFrameRealCompatibleFrameTargetDerivR, fC, LC, incl, re]
    using hcomp2

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- On the explicit real slice coordinates, the real frame-target derivative
recovers the finite coordinate vector. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivR_realCoordEquiv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F
        ((F.realCoordEquiv q :
            sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) = q := by
  let XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    (F.realCoordEquiv q :
      sourceFullFrameRealDifferentialRightInverseRange d hM0R)
  have hcomplex :
      (F.complexCoordEquiv (fun i => (q i : ℂ)) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
        XR.map Complex.ofReal := by
    have h := F.complexCoordEquiv_real_eq q
    exact congrArg Subtype.val h
  change sourceFullFrameComplexCoordinateReCLM F.realModelDim
      (sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (XR.map Complex.ofReal)) = q
  rw [← hcomplex]
  rw [sourceFullFrameRealCompatibleFrameTargetDerivC_complexCoordEquiv]
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- The real frame-target derivative is surjective. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivR_range_eq_top
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    LinearMap.range
        (sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F).toLinearMap =
      ⊤ := by
  rw [LinearMap.range_eq_top]
  intro q
  exact
    ⟨((F.realCoordEquiv q :
        sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      sourceFullFrameRealCompatibleFrameTargetDerivR_realCoordEquiv
        d hM0R F q⟩

/-- Frame matrices whose real-compatible target coordinate lies in the local
real inverse-function target and whose determinant remains nonzero. -/
def sourceFullFrameRealCompatibleFrameDomain
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  {M |
    sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).target ∧
    M.det ≠ 0}

/-- The real-compatible frame domain is open. -/
theorem sourceFullFrameRealCompatibleFrameDomain_open
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    IsOpen (sourceFullFrameRealCompatibleFrameDomain d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameDomain
  refine
    ((sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).open_target.preimage
        (continuous_sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F)
      ).inter ?_
  exact
    isOpen_ne_fun
      (continuous_id.matrix_det :
        Continuous
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M.det))
      continuous_const

/-- The base real frame lies in the real-compatible frame domain. -/
theorem sourceFullFrameRealCompatibleFrameDomain_base_mem
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    M0R ∈ sourceFullFrameRealCompatibleFrameDomain d hM0R F := by
  constructor
  · rw [sourceFullFrameRealCompatibleFrameTargetCoordR_base d hM0R F]
    exact
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
        d hM0R F
  · exact hM0R.ne_zero

/-- Every matrix in the real-compatible frame domain has nonzero determinant. -/
theorem sourceFullFrameRealCompatibleFrameDomain_det_nonzero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameDomain d hM0R F ⊆ {M | M.det ≠ 0} := by
  intro M hM
  exact hM.2

/-- The real selected-frame slice coordinate obtained by applying the inverse
of the real normalized kernel chart to the frame-level target coordinate. -/
noncomputable def sourceFullFrameRealCompatibleFrameKernelCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
      Fin F.realModelDim → ℝ :=
  fun M =>
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).symm
        (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M)

/-- The real selected-frame slice coordinate is continuous on the local
real-compatible frame domain. -/
theorem continuousOn_sourceFullFrameRealCompatibleFrameKernelCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    ContinuousOn
      (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F)
      (sourceFullFrameRealCompatibleFrameDomain d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameKernelCoordR
  exact
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).continuousOn_symm.comp
        (continuous_sourceFullFrameRealCompatibleFrameTargetCoordR
          d hM0R F).continuousOn
        (by
          intro M hM
          exact hM.1)

@[simp]
theorem sourceFullFrameRealCompatibleFrameKernelCoordR_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M0R = 0 := by
  let e :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F
  have hsource :
      (0 : Fin F.realModelDim → ℝ) ∈ e.source := by
    simpa [e] using
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
        d hM0R F
  have htarget :
      (0 : Fin F.realModelDim → ℝ) ∈ e.target := by
    simpa [e] using
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
        d hM0R F
  have he0 : e (0 : Fin F.realModelDim → ℝ) =
      (0 : Fin F.realModelDim → ℝ) := by
    rw [sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph_coe]
    exact sourceFullFrameRealCompatibleNormalizedKernelMapReal_zero d hM0R F
  unfold sourceFullFrameRealCompatibleFrameKernelCoordR
  rw [sourceFullFrameRealCompatibleFrameTargetCoordR_base d hM0R F]
  exact ((e.eq_symm_apply hsource htarget).mpr he0).symm

/-- A total complex selected-frame coordinate obtained from the real coordinate
on complexified real frames.  Away from the real locus it is an arbitrary
zero extension; the full implicit-chart producer later proves that the actual
complex max-rank chart agrees with this coordinate on the real source patch
where it is used. -/
noncomputable def sourceFullFrameRealCompatibleComplexKernelCoordFromReal
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice :=
  fun M =>
    if h : ∃ MR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        M = MR.map Complex.ofReal then
      F.complexCoordEquiv
        (SCV.realToComplex
          (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F
            (Classical.choose h)))
    else 0

/-- On complexified real frames, the total complex selected-frame coordinate
is exactly the complexification of the real selected-frame coordinate. -/
theorem sourceFullFrameRealCompatibleComplexKernelCoordFromReal_real_eq
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameRealCompatibleComplexKernelCoordFromReal d hM0R F
        (M.map Complex.ofReal) =
      F.complexCoordEquiv
        (SCV.realToComplex
          (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M)) := by
  unfold sourceFullFrameRealCompatibleComplexKernelCoordFromReal
  let h : ∃ MR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      M.map Complex.ofReal = MR.map Complex.ofReal := ⟨M, rfl⟩
  have hchoose : Classical.choose h = M := by
    have hspec := Classical.choose_spec h
    ext i j
    exact Complex.ofReal_injective (congrFun (congrFun hspec i) j).symm
  rw [dif_pos h]
  rw [hchoose]

/-- Mechanical constructor for the real gauge-slice packet once a compatible
complex selected-frame coordinate is supplied.  The gauge-slice packet records
the local frame domain, determinant control, continuity, and real/complex
compatibility; the open-image obligation belongs to the final shrunken source
chart, not to this frame-domain-wide packet. -/
noncomputable def sourceFullFrameRealGaugeSliceData_of_frameKernelCoord
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (complexKernelCoord :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice)
    (complexKernelCoord_real_eq :
      ∀ M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        complexKernelCoord (M.map Complex.ofReal) =
          F.complexCoordEquiv
            (SCV.realToComplex
              (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M))) :
    SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero where
  M0_det_unit := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  complexSlice :=
    sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  realModelDim := F.realModelDim
  realModelToComplexSlice := F.complexCoordEquiv
  realKernelCoord :=
    sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F
  complexKernelCoord := complexKernelCoord
  complexKernelCoord_real_eq := complexKernelCoord_real_eq
  frameDomain := sourceFullFrameRealCompatibleFrameDomain d hM0R F
  frameDomain_open :=
    sourceFullFrameRealCompatibleFrameDomain_open d hM0R F
  center_mem_frameDomain :=
    sourceFullFrameRealCompatibleFrameDomain_base_mem d hM0R F
  frameDomain_det_nonzero :=
    sourceFullFrameRealCompatibleFrameDomain_det_nonzero d hM0R F
  realKernelCoord_continuousOn :=
    continuousOn_sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F

/-- Mechanical real gauge-slice constructor in the common case where the
complex selected-frame coordinate is the canonical real-locus extension above.
This is the direct constructor for `SourceFullFrameRealGaugeSliceData` from the
checked real-compatible IFT frame-domain packet. -/
noncomputable def sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero :=
  sourceFullFrameRealGaugeSliceData_of_frameKernelCoord d hM0R F
    (sourceFullFrameRealCompatibleComplexKernelCoordFromReal d hM0R F)
    (sourceFullFrameRealCompatibleComplexKernelCoordFromReal_real_eq
      d hM0R F)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 700000 in
/-- The real-compatible selected-frame slice supplies the local product chart
whose first coordinate is the checked real selected-frame kernel coordinate. -/
noncomputable def sourceFullFrameRealSelectedFrameProductChartData_of_realCompatibleSlice
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Sigma fun O : Type =>
      Sigma fun instO : TopologicalSpace O =>
        @SourceFullFrameRealSelectedFrameProductChartData
          d n ι x0 hM0R.ne_zero
          (sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
            d hM0R F)
          O instO := by
  let M0R := sourceRealFullFrameMatrix d n ι x0
  let S :=
    sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
      d hM0R F
  let f := sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F
  let f' := sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F
  let O := f'.ker
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F
  have hf : HasStrictFDerivAt f f' M0R := by
    simpa [f, f', M0R] using
      sourceFullFrameRealCompatibleFrameTargetCoordR_hasStrictFDerivAt
        d hM0R F
  have hsurj : LinearMap.range f'.toLinearMap = ⊤ := by
    simpa [f'] using
      sourceFullFrameRealCompatibleFrameTargetDerivR_range_eq_top d hM0R F
  let eT : OpenPartialHomeomorph
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      ((Fin F.realModelDim → ℝ) × O) :=
    hf.implicitToOpenPartialHomeomorph f f' hsurj
  let eProd : OpenPartialHomeomorph
      ((Fin F.realModelDim → ℝ) × O)
      ((Fin F.realModelDim → ℝ) × O) :=
    eK.symm.prod (OpenPartialHomeomorph.refl O)
  let sourceOpen : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
    S.frameDomain ∩ {M | M.det ≠ 0}
  have hsourceOpen : IsOpen sourceOpen := by
    exact S.frameDomain_open.inter
      (isOpen_ne_fun
        (continuous_id.matrix_det :
          Continuous
            (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
              M.det))
        continuous_const)
  let frameChart := (eT.trans eProd).restrOpen sourceOpen hsourceOpen
  refine ⟨O, ?_⟩
  letI : TopologicalSpace O := inferInstance
  refine ⟨inferInstance, ?_⟩
  refine
    { frameChart := frameChart
      center_mem_source := ?_
      source_det := ?_
      source_frameDomain := ?_
      first_eq_realKernelCoord := ?_ }
  · have hTsource : M0R ∈ eT.source :=
      hf.mem_implicitToOpenPartialHomeomorph_source hsurj
    have hTself : eT M0R = (f M0R, (0 : O)) := by
      exact hf.implicitToOpenPartialHomeomorph_self hsurj
    have hKtarget : (0 : Fin F.realModelDim → ℝ) ∈ eK.target := by
      simpa [eK] using
        sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
          d hM0R F
    have hProdSource : eT M0R ∈ eProd.source := by
      have hf0 : f M0R = 0 := by
        simp [f, M0R]
      rw [hTself]
      simpa [eProd, hf0] using hKtarget
    have hTrans : M0R ∈ (eT.trans eProd).source :=
      ⟨hTsource, hProdSource⟩
    have hOpen : M0R ∈ sourceOpen :=
      ⟨S.center_mem_frameDomain, hM0R.ne_zero⟩
    exact ⟨hTrans, hOpen⟩
  · intro M hM
    exact hM.2.2
  · intro M hM
    exact hM.2.1
  · intro M _hM
    have hfirstT : (eT M).1 = f M := by
      exact hf.implicitToOpenPartialHomeomorph_fst hsurj M
    change (eProd (eT M)).1 = eK.symm (f M)
    simp [eProd, hfirstT]

/-- The checked real-compatible full-frame gauge-slice packet at a real
determinant-nonzero base. -/
theorem sourceFullFrameRealGaugeSliceData
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Nonempty (SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero) := by
  rcases sourceFullFrameRealSliceFiniteCoordData d hM0R with ⟨F⟩
  exact
    ⟨sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
      d hM0R F⟩

end BHW
