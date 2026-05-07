import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHolomorphicSection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart

/-!
# Full-frame support for source-oriented holomorphic sections

This file starts the producer side of the max-rank holomorphic-section route.
The lemmas here are the mechanical coordinate-differentiability layer for the
full-frame branch; the remaining inverse-regular target shrink is kept as the
next honest theorem target.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Symmetrization of full-frame oriented coordinates, bundled as a continuous
linear map into the symmetric-coordinate submodule. -/
noncomputable def sourceFullFrameSymmetrizeCoordCLM
    (d : ℕ) :
    SourceFullFrameOrientedCoord d →L[ℂ]
      sourceFullFrameSymmetricCoordSubmodule d where
  toFun := sourceFullFrameSymmetrizeCoord d
  map_add' := by
    intro H K
    apply Subtype.ext
    ext a b <;> simp [sourceFullFrameSymmetrizeCoord]
    ring
  map_smul' := by
    intro c H
    apply Subtype.ext
    ext a b <;> simp [sourceFullFrameSymmetrizeCoord]
    ring
  cont := continuous_sourceFullFrameSymmetrizeCoord d

theorem differentiable_sourceFullFrameSymmetrizeCoord
    (d : ℕ) :
    Differentiable ℂ (sourceFullFrameSymmetrizeCoord d) := by
  simpa [sourceFullFrameSymmetrizeCoordCLM] using
    (sourceFullFrameSymmetrizeCoordCLM d).differentiable

/-- Selecting full-frame oriented coordinates from ambient oriented source data
is complex differentiable. -/
theorem differentiable_sourceFullFrameOrientedCoordOfSource
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    Differentiable ℂ (sourceFullFrameOrientedCoordOfSource d n ι) := by
  unfold sourceFullFrameOrientedCoordOfSource
  have hgram : Differentiable ℂ
      (fun G : SourceOrientedGramData d n =>
        fun a b : Fin (d + 1) => G.gram (ι a) (ι b)) := by
    refine differentiable_pi.mpr ?_
    intro a
    refine differentiable_pi.mpr ?_
    intro b
    exact
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (ι b)).differentiable.comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) (ι a)).differentiable.comp
          (by
            simp))
  have hdet : Differentiable ℂ
      (fun G : SourceOrientedGramData d n => G.det ι) := by
    exact
      (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : (Fin (d + 1) ↪ Fin n) => ℂ) ι).differentiable.comp
        (by
          simp)
  simpa [SourceOrientedGramData.gram, SourceOrientedGramData.det] using
    Differentiable.prodMk hgram hdet

/-- The total ambient selected symmetric coordinate is complex differentiable. -/
theorem differentiable_sourceFullFrameSelectedSymmetricCoordAmbient
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    Differentiable ℂ (sourceFullFrameSelectedSymmetricCoordAmbient d n ι) := by
  unfold sourceFullFrameSelectedSymmetricCoordAmbient
  exact (differentiable_sourceFullFrameSymmetrizeCoord d).comp
    (differentiable_sourceFullFrameOrientedCoordOfSource d n ι)

/-- The ambient selected kernel coordinate is just the fixed kernel projection
of the selected symmetric coordinate displacement.  This avoids using
differentiability of the symmetric implicit chart. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_eq_kernelProjection
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (G : SourceOrientedGramData d n) :
    sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G =
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
          sourceFullFrameSymmetricBase d M0) := by
  unfold sourceFullFrameSelectedKernelCoordAmbient
  exact sourceFullFrameSymmetricEquation_implicitChart_snd d M0 hM0
    (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G)

/-- The nonlinear gauge-slice kernel-coordinate map is also the fixed kernel
projection of the symmetric gauge-slice displacement. -/
theorem sourceFullFrameGaugeSliceImplicitKernelMap_eq_kernelProjection
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X =
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
          sourceFullFrameSymmetricBase d M0) := by
  unfold sourceFullFrameGaugeSliceImplicitKernelMap
  exact sourceFullFrameSymmetricEquation_implicitChart_snd d M0 hM0
    (sourceFullFrameGaugeSliceMapSymmetric d M0 S X)

set_option synthInstance.maxHeartbeats 100000 in
/-- The ambient selected kernel coordinate is complex differentiable. -/
theorem differentiable_sourceFullFrameSelectedKernelCoordAmbient
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    Differentiable ℂ (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0) := by
  letI : AddCommGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (inferInstance : NormedAddCommGroup
      (sourceFullFrameSymmetricCoordSubmodule d)).toAddCommGroup
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  letI : AddCommGroup K :=
    (inferInstance : NormedAddCommGroup K).toAddCommGroup
  have hsymm := differentiable_sourceFullFrameSelectedSymmetricCoordAmbient d n ι
  have hsub : Differentiable ℂ
      (fun G : SourceOrientedGramData d n =>
        sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
          sourceFullFrameSymmetricBase d M0) := by
    exact hsymm.sub (differentiable_const (c := sourceFullFrameSymmetricBase d M0))
  have hproj : Differentiable ℂ
      (fun G : SourceOrientedGramData d n =>
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
            sourceFullFrameSymmetricBase d M0)) := by
    exact
      (ContinuousLinearMap.differentiable
        (𝕜 := ℂ)
        (E := sourceFullFrameSymmetricCoordSubmodule d)
        (F := K)
        (sourceFullFrameSymmetricEquationKernelProjection d M0)).comp hsub
  convert hproj using 1

/-- The mixed-row coordinate projection used in the full-frame chart candidate
is complex differentiable. -/
theorem differentiable_sourceSelectedMixedRows
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    Differentiable ℂ (sourceSelectedMixedRows d n ι) := by
  unfold sourceSelectedMixedRows
  refine differentiable_pi.mpr ?_
  intro k
  refine differentiable_pi.mpr ?_
  intro a
  exact
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (ι a)).differentiable.comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) k.1).differentiable.comp
        (by
          simp))

namespace SourceFullFrameMaxRankChartAmbientShrink

set_option synthInstance.maxHeartbeats 120000 in
/-- Once the inverse kernel chart is differentiable on a selected target set,
the full-frame chart candidate is differentiable on any ambient shrink whose
selected kernel coordinates land in that set. -/
theorem chartCandidate_differentiableOn_Ωamb_of_kernelSymmOn
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    {D : Set ((sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker)}
    (hsymm : DifferentiableOn ℂ
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm D)
    (hΩD : ∀ G ∈ T.Ωamb,
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ D) :
    DifferentiableOn ℂ
      (chartCandidate (d := d) (n := n) (ι := ι) hM0 S)
      T.Ωamb := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  have hK : DifferentiableOn ℂ
      (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0) T.Ωamb :=
    (differentiable_sourceFullFrameSelectedKernelCoordAmbient d n ι hM0).differentiableOn
  have hfst : DifferentiableOn ℂ
      (fun G : SourceOrientedGramData d n =>
        e.symm (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G))
      T.Ωamb := by
    exact hsymm.comp hK hΩD
  have hsnd : DifferentiableOn ℂ (sourceSelectedMixedRows d n ι) T.Ωamb :=
    (differentiable_sourceSelectedMixedRows d n ι).differentiableOn
  simpa [chartCandidate, e] using DifferentiableOn.prodMk hfst hsnd

end SourceFullFrameMaxRankChartAmbientShrink

end BHW
