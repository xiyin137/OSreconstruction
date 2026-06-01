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

/-- The symmetric-codomain gauge-slice map is the ambient polynomial
gauge-slice map followed by the fixed full-frame symmetrization. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_eq_symmetrize
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    sourceFullFrameGaugeSliceMapSymmetric d M0 S X =
      sourceFullFrameSymmetrizeCoord d
        (sourceFullFrameGaugeSliceMap d M0 S X) := by
  apply Subtype.ext
  symm
  exact sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d
    (sourceFullFrameGaugeSliceMap_mem_hypersurface d M0 S X).1

/-- The symmetric-codomain gauge-slice map is smooth. -/
theorem contDiff_sourceFullFrameGaugeSliceMapSymmetric
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0) :
    ContDiff ℂ ⊤ (sourceFullFrameGaugeSliceMapSymmetric d M0 S) := by
  have h : sourceFullFrameGaugeSliceMapSymmetric d M0 S =
      (sourceFullFrameSymmetrizeCoord d) ∘
        (sourceFullFrameGaugeSliceMap d M0 S) := by
    funext X
    exact sourceFullFrameGaugeSliceMapSymmetric_eq_symmetrize d S X
  rw [h]
  exact (sourceFullFrameSymmetrizeCoordCLM d).contDiff.comp
    (contDiff_sourceFullFrameGaugeSliceMap d M0 S)

set_option synthInstance.maxHeartbeats 100000 in
/-- The nonlinear implicit-kernel coordinate map is smooth; it is a fixed
linear projection of the smooth symmetric gauge-slice displacement. -/
theorem contDiff_sourceFullFrameGaugeSliceImplicitKernelMap
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ContDiff ℂ ⊤ (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S) := by
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  letI : AddCommGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (inferInstance : NormedAddCommGroup
      (sourceFullFrameSymmetricCoordSubmodule d)).toAddCommGroup
  letI : AddCommGroup K :=
    (inferInstance : NormedAddCommGroup K).toAddCommGroup
  have hsymm :
      ContDiff ℂ ⊤ (sourceFullFrameGaugeSliceMapSymmetric d M0 S) :=
    contDiff_sourceFullFrameGaugeSliceMapSymmetric d S
  have hsub : ContDiff ℂ ⊤ (fun X : S.slice =>
        sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
          sourceFullFrameSymmetricBase d M0) := by
    exact hsymm.sub contDiff_const
  have hproj : ContDiff ℂ ⊤ (fun X : S.slice =>
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (sourceFullFrameGaugeSliceMapSymmetric d M0 S X -
            sourceFullFrameSymmetricBase d M0)) := by
    exact
      (sourceFullFrameSymmetricEquationKernelProjection d M0).contDiff.comp
        hsub
  convert hproj using 1

set_option synthInstance.maxHeartbeats 100000 in
/-- At the origin, the implicit-kernel coordinate derivative is the checked
continuous-linear equivalence from the gauge slice to the kernel. -/
theorem sourceFullFrameGaugeSliceImplicitKernelMap_base_fderiv_isInvertible
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (fderiv ℂ (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S)
      0).IsInvertible := by
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  let e0 := sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv
    d hM0 S
  have hderiv :
      fderiv ℂ (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S) 0 =
        (e0 : S.slice →L[ℂ] K) := by
    rw [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
    exact
      (sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt
        d hM0 S).hasFDerivAt.fderiv
  exact ⟨e0, hderiv.symm⟩

set_option synthInstance.maxHeartbeats 100000 in
/-- Source-side shrink on which the implicit-kernel coordinate derivative
remains invertible. -/
theorem sourceFullFrameGaugeSliceImplicitKernelMap_local_invertible_nhds
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ∃ U : Set S.slice,
      IsOpen U ∧ (0 : S.slice) ∈ U ∧
        U ⊆
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).source ∧
        ∀ X ∈ U,
          (fderiv ℂ
            (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S)
            X).IsInvertible := by
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  letI : AddCommGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (inferInstance : NormedAddCommGroup
      (sourceFullFrameSymmetricCoordSubmodule d)).toAddCommGroup
  letI : AddCommGroup K :=
    (inferInstance : NormedAddCommGroup K).toAddCommGroup
  letI : IsUniformAddGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (sourceFullFrameSymmetricCoordSubmodule d).toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup S.slice :=
    S.slice.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace S.slice :=
    sourceFullFrameGaugeSliceData_slice_completeSpace d S
  letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
  let f := sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
    d hM0 S
  let InvSet : Set (S.slice →L[ℂ] K) :=
    Set.range ((↑) : (S.slice ≃L[ℂ] K) → S.slice →L[ℂ] K)
  have hInvOpen : IsOpen InvSet := by
    dsimp [InvSet]
    exact @ContinuousLinearEquiv.isOpen ℂ _ S.slice _ _ K _ _
      (sourceFullFrameGaugeSliceData_slice_completeSpace d S)
  have hderivCont : Continuous (fun X : S.slice => fderiv ℂ f X) := by
    exact
      (contDiff_sourceFullFrameGaugeSliceImplicitKernelMap
        d hM0 S).continuous_fderiv (by simp)
  let U : Set S.slice := e.source ∩ {X | fderiv ℂ f X ∈ InvSet}
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · exact e.open_source.inter (hInvOpen.preimage hderivCont)
  · refine
      ⟨sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource
        d hM0 S, ?_⟩
    exact
      sourceFullFrameGaugeSliceImplicitKernelMap_base_fderiv_isInvertible
        d hM0 S
  · intro X hX
    exact hX.1
  · intro X hX
    exact hX.2

set_option synthInstance.maxHeartbeats 120000 in
/-- Target-side regularity shrink for the inverse implicit-kernel chart. -/
structure SourceFullFrameImplicitKernelTargetRegularityData
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) where
  D : Set ((sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker)
  D_open : IsOpen D
  zero_mem : 0 ∈ D
  D_subset_target :
    D ⊆
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
        d hM0 S).target
  has_deriv_equiv :
    ∀ K ∈ D,
      ∃ e' : S.slice ≃L[ℂ]
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d M0)).ker,
        HasFDerivAt
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S)
          (e' : S.slice →L[ℂ]
            (sourceFullFrameSymmetricEquationDerivCLM d
              (sourceFullFrameOrientedGramCoord d M0)).ker)
          ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).symm K)
  forward_smooth :
    ∀ K ∈ D,
      ContDiffAt ℂ ⊤
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S)
        ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).symm K)
  symm_differentiableOn :
    DifferentiableOn ℂ
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
        d hM0 S).symm D

set_option synthInstance.maxHeartbeats 120000 in
/-- Construct the target-side regularity shrink from derivative continuity and
openness of the continuous-linear equivalence locus. -/
noncomputable def sourceFullFrameImplicitKernelTargetRegularityData
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    SourceFullFrameImplicitKernelTargetRegularityData d hM0 S := by
  classical
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  letI : AddCommGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (inferInstance : NormedAddCommGroup
      (sourceFullFrameSymmetricCoordSubmodule d)).toAddCommGroup
  letI : AddCommGroup K :=
    (inferInstance : NormedAddCommGroup K).toAddCommGroup
  letI : IsUniformAddGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
    (sourceFullFrameSymmetricCoordSubmodule d).toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup S.slice :=
    S.slice.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace S.slice :=
    sourceFullFrameGaugeSliceData_slice_completeSpace d S
  letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
  let f := sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
    d hM0 S
  let hex :=
    sourceFullFrameGaugeSliceImplicitKernelMap_local_invertible_nhds
      d hM0 S
  let U : Set S.slice := Classical.choose hex
  have hU_spec := Classical.choose_spec hex
  have hU_open : IsOpen U := hU_spec.1
  have hU_zero : (0 : S.slice) ∈ U := hU_spec.2.1
  have hU_inv : ∀ X ∈ U, (fderiv ℂ f X).IsInvertible := by
    intro X hX
    exact hU_spec.2.2.2 X hX
  let D : Set K := e.target ∩ e.symm ⁻¹' U
  have hD_open : IsOpen D := by
    exact e.isOpen_inter_preimage_symm hU_open
  have hsymm_zero : e.symm (0 : K) = (0 : S.slice) := by
    have hsource0 :=
      sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S
    have hleft := e.left_inv hsource0
    have he0 : e (0 : S.slice) = (0 : K) := by
      simp [e,
        sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe]
    simpa [he0] using hleft
  have hD_zero : (0 : K) ∈ D := by
    refine
      ⟨sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget
        d hM0 S, ?_⟩
    simpa [hsymm_zero] using hU_zero
  have hD_subset_target : D ⊆ e.target := by
    intro Y hY
    exact hY.1
  have hcont : ContDiff ℂ ⊤ f :=
    contDiff_sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
  have hderiv :
      ∀ Y ∈ D,
        ∃ e' : S.slice ≃L[ℂ] K,
          HasFDerivAt e (e' : S.slice →L[ℂ] K) (e.symm Y) := by
    intro Y hY
    rcases hU_inv (e.symm Y) hY.2 with ⟨e', he'⟩
    refine ⟨e', ?_⟩
    have hf_at :
        HasFDerivAt f (fderiv ℂ f (e.symm Y)) (e.symm Y) :=
      ((hcont.differentiable (by simp)) (e.symm Y)).hasFDerivAt
    simpa [e, f,
      sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe,
      he'] using hf_at
  have hsmooth :
      ∀ Y ∈ D, ContDiffAt ℂ ⊤ e (e.symm Y) := by
    intro Y hY
    simpa [e, f,
      sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe]
      using (hcont.contDiffAt (x := e.symm Y))
  have hsymm_diff : DifferentiableOn ℂ e.symm D := by
    exact @SCV.openPartialHomeomorph_symm_differentiableOn_of_hasFDerivAt
      ℂ S.slice K _ _ _
      (sourceFullFrameGaugeSliceData_slice_completeSpace d S) _ _
      e D hD_subset_target hderiv hsmooth
  exact
    { D := D
      D_open := hD_open
      zero_mem := hD_zero
      D_subset_target := hD_subset_target
      has_deriv_equiv := hderiv
      forward_smooth := hsmooth
      symm_differentiableOn := hsymm_diff }

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

/-- The regularity packet supplies the inverse-kernel differentiability
hypothesis needed by the full-frame chart candidate. -/
theorem chartCandidate_differentiableOn_Ωamb
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (R : SourceFullFrameImplicitKernelTargetRegularityData d hM0 S)
    (hΩD : ∀ G ∈ T.Ωamb,
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ R.D) :
    DifferentiableOn ℂ
      (chartCandidate (d := d) (n := n) (ι := ι) hM0 S)
      T.Ωamb :=
  chartCandidate_differentiableOn_Ωamb_of_kernelSymmOn T
    R.symm_differentiableOn hΩD

/-- Restrict an ambient full-frame shrink so every selected kernel coordinate
lands in the inverse-regular target set. -/
noncomputable def restrict_kernelRegularity
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (R : SourceFullFrameImplicitKernelTargetRegularityData d hM0 S)
    (hcenterKernel :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0) :
    SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 := by
  let ΩD : Set (SourceOrientedGramData d n) :=
    {G | sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ R.D}
  let Ωamb := T.Ωamb ∩ ΩD
  have hΩD_open : IsOpen ΩD := by
    exact R.D_open.preimage
      (differentiable_sourceFullFrameSelectedKernelCoordAmbient
        d n ι hM0).continuous
  have hΩamb_open : IsOpen Ωamb := T.Ωamb_open.inter hΩD_open
  have hcenter : G0 ∈ Ωamb := by
    exact ⟨T.center_mem, by simpa [ΩD, hcenterKernel] using R.zero_mem⟩
  exact
    { Ωamb := Ωamb
      Ωamb_open := hΩamb_open
      center_mem := hcenter
      selectedSymmetric_mem_implicitSource := by
        intro G hG
        exact T.selectedSymmetric_mem_implicitSource hG.1
      selectedKernel_mem_target := by
        intro G hG
        exact R.D_subset_target hG.2
      gaugeSlice_mem_implicitSource := by
        intro G hG
        exact T.gaugeSlice_mem_implicitSource hG.1
      selectedDetNonzero := by
        intro G hG
        exact T.selectedDetNonzero hG.1 }

/-- Membership in the restricted shrink records the selected-kernel
regularity condition. -/
theorem restrict_kernelRegularity_mem_D
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (R : SourceFullFrameImplicitKernelTargetRegularityData d hM0 S)
    (hcenterKernel :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ (restrict_kernelRegularity T R hcenterKernel).Ωamb) :
    sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ R.D := by
  exact hG.2

/-- On the regularity-restricted shrink, the full-frame chart candidate is
complex differentiable. -/
theorem chartCandidate_differentiableOn_restrict_kernelRegularity
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (R : SourceFullFrameImplicitKernelTargetRegularityData d hM0 S)
    (hcenterKernel :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0) :
    DifferentiableOn ℂ
      (chartCandidate (d := d) (n := n) (ι := ι) hM0 S)
      (restrict_kernelRegularity T R hcenterKernel).Ωamb := by
  exact chartCandidate_differentiableOn_Ωamb
    (restrict_kernelRegularity T R hcenterKernel) R
    (by
      intro G hG
      exact restrict_kernelRegularity_mem_D T R hcenterKernel hG)

end SourceFullFrameMaxRankChartAmbientShrink

set_option maxHeartbeats 1000000 in
/-- Full-frame max-rank points have an ambient holomorphic local section of
the source-oriented invariant map through the extended tube. -/
noncomputable def sourceOrientedMaxRank_localSection_fullFrame
    {d n : ℕ}
    [NeZero d]
    (_hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (ι : Fin (d + 1) ↪ Fin n)
    (hdet : sourceFullFrameDet d n ι z0 ≠ 0) :
    SourceOrientedLocalHolomorphicSectionData (d := d) n
      (sourceOrientedMinkowskiInvariant d n z0) := by
  classical
  let G0 : SourceOrientedGramData d n := sourceOrientedMinkowskiInvariant d n z0
  let M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z0
  have hM0 : IsUnit M0.det := by
    exact isUnit_iff_ne_zero.mpr
      (by simpa [M0, sourceFullFrameDet] using hdet)
  let S := sourceFullFrameGaugeSlice_exists d hM0
  have hG0 : G0 ∈ sourceOrientedGramVariety d n := by
    exact ⟨z0, rfl⟩
  have hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0 := by
    simpa [G0, M0] using
      (sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant
        d n ι z0).symm
  let T0 : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    sourceFullFrameMaxRankChart_ambientShrink
      d n ι hM0 S hG0 hM0_oriented
  let R := sourceFullFrameImplicitKernelTargetRegularityData d hM0 S
  have hcenterKernel :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 :=
    sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
      d n ι hM0 hG0 hM0_oriented
  let Treg : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    SourceFullFrameMaxRankChartAmbientShrink.restrict_kernelRegularity
      T0 R hcenterKernel
  let chart : SourceOrientedGramData d n →
      sourceFullFrameMaxRankChartModel d n ι M0 S :=
    SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
      (d := d) (n := n) (ι := ι) hM0 S
  let f : sourceFullFrameMaxRankChartModel d n ι M0 S →
      Fin n → Fin (d + 1) → ℂ :=
    sourceFullFrameGauge_reconstructVector d n ι M0 S
  let modelDet : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    sourceFullFrameGaugeModelDetNonzero d n ι M0 S
  have hf_cont : ContinuousOn f modelDet := by
    exact
      (differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
        d n ι M0 S).continuousOn
  let preSpec :=
    (continuousOn_iff'.mp hf_cont)
      (ExtendedTube d n) (isOpen_extendedTube (d := d) (n := n))
  let Umodel : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    Classical.choose preSpec
  have hUmodel_spec :
      IsOpen Umodel ∧
        f ⁻¹' ExtendedTube d n ∩ modelDet = Umodel ∩ modelDet :=
    Classical.choose_spec preSpec
  have hUmodel_open : IsOpen Umodel := hUmodel_spec.1
  have hpre_eq :
      f ⁻¹' ExtendedTube d n ∩ modelDet = Umodel ∩ modelDet :=
    hUmodel_spec.2
  let y0 : sourceFullFrameMaxRankChartModel d n ι M0 S := chart G0
  have hframe0 :
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y0 =
        sourceFullFrameMatrix d n ι z0 := by
    simpa [chart, y0, G0, M0] using
      SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_reconstructFrame_center_eq
          (d := d) (n := n) (ι := ι) hM0 S hG0 hM0_oriented
  have hdetG0 : G0.det ι ≠ 0 := by
    simpa [G0, sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det,
      sourceFullFrameDet] using hdet
  have hf_y0 : f y0 = z0 := by
    simpa [f, y0, chart, G0] using
      sourceFullFrameGauge_reconstructVector_eq_of_frame_eq_mixedRows_eq
        d n ι M0 S y0 z0 hframe0 rfl hdetG0
  have hy0_model : y0 ∈ Treg.modelChartDomain := by
    simpa [Treg, y0, chart] using
      Treg.chartCandidate_center_mem_modelChartDomain hG0 hM0_oriented
  have hy0_Umodel : y0 ∈ Umodel := by
    have hy0_pre : y0 ∈ f ⁻¹' ExtendedTube d n ∩ modelDet := by
      exact
        ⟨by simpa [hf_y0] using hz0,
          by simpa [modelDet] using hy0_model.2.2⟩
    have hy0_U_det : y0 ∈ Umodel ∩ modelDet := by
      rw [← hpre_eq]
      exact hy0_pre
    exact hy0_U_det.1
  let V : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    Umodel ∩ Treg.modelChartDomain
  have hV_open : IsOpen V := hUmodel_open.inter Treg.modelChartDomain_open
  have hy0V : y0 ∈ V := ⟨hy0_Umodel, hy0_model⟩
  have hmodelDet_of_mem_V : ∀ y ∈ V, y ∈ modelDet := by
    intro y hy
    exact hy.2.2.2
  have hV_ET : ∀ y ∈ V, f y ∈ ExtendedTube d n := by
    intro y hy
    have hy_pre : y ∈ f ⁻¹' ExtendedTube d n ∩ modelDet := by
      rw [hpre_eq]
      exact ⟨hy.1, hmodelDet_of_mem_V y hy⟩
    exact hy_pre.1
  have hchart_cont : ContinuousOn chart Treg.Ωamb := by
    simpa [chart] using Treg.chartCandidate_continuousOn_Ωamb
  let chartPreSpec := (continuousOn_iff'.mp hchart_cont) V hV_open
  let UΩ : Set (SourceOrientedGramData d n) := Classical.choose chartPreSpec
  have hchart_pre_spec :
      IsOpen UΩ ∧ chart ⁻¹' V ∩ Treg.Ωamb = UΩ ∩ Treg.Ωamb :=
    Classical.choose_spec chartPreSpec
  have hUΩ_open : IsOpen UΩ := hchart_pre_spec.1
  have hchart_pre_eq :
      chart ⁻¹' V ∩ Treg.Ωamb = UΩ ∩ Treg.Ωamb :=
    hchart_pre_spec.2
  let Ω : Set (SourceOrientedGramData d n) := UΩ ∩ Treg.Ωamb
  have hΩ_open : IsOpen Ω := hUΩ_open.inter Treg.Ωamb_open
  have hcenter_pre : G0 ∈ chart ⁻¹' V ∩ Treg.Ωamb :=
    ⟨by simpa [y0, chart] using hy0V, Treg.center_mem⟩
  have hcenterΩ : G0 ∈ Ω := by
    have htmp : G0 ∈ chart ⁻¹' V ∩ Treg.Ωamb := hcenter_pre
    rw [hchart_pre_eq] at htmp
    exact htmp
  have hchart_mem_V : ∀ G ∈ Ω, chart G ∈ V := by
    intro G hG
    have hG_U : G ∈ UΩ ∩ Treg.Ωamb := hG
    have hpre : G ∈ chart ⁻¹' V ∩ Treg.Ωamb := by
      rw [hchart_pre_eq]
      exact hG_U
    exact hpre.1
  have hchart_diff_Treg : DifferentiableOn ℂ chart Treg.Ωamb := by
    simpa [chart, Treg] using
      SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_differentiableOn_restrict_kernelRegularity
          T0 R hcenterKernel
  have hchart_diff_Ω : DifferentiableOn ℂ chart Ω :=
    hchart_diff_Treg.mono (by
      intro G hG
      exact hG.2)
  have htoVec_diff :
      DifferentiableOn ℂ (fun G : SourceOrientedGramData d n =>
        f (chart G)) Ω := by
    exact
      (differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
        d n ι M0 S).comp hchart_diff_Ω (by
          intro G hG
          exact hmodelDet_of_mem_V (chart G) (hchart_mem_V G hG))
  refine
    { Ω := Ω
      Ω_open := hΩ_open
      center_mem := by simpa [G0] using hcenterΩ
      toVec := fun G => f (chart G)
      toVec_mem := ?_
      toVec_right_inv := ?_
      toVec_holomorphic := by simpa [f, chart] using htoVec_diff }
  · intro G hG
    exact hV_ET (chart G) (hchart_mem_V G hG)
  · intro G hG
    have hrel : G ∈ Treg.relDomain := ⟨hG.1.2, hG.2⟩
    have hrec := Treg.reconstructInvariant_chartCandidate_eq_of_mem_relDomain hrel
    simpa [f, chart, sourceFullFrameGauge_reconstructInvariant_eq] using hrec

end BHW
