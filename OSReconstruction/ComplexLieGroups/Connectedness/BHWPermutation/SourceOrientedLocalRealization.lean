import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameMaxRankProducer

/-!
# Local realization for the oriented extended-tube image

This file isolates the purely topological part of relative openness for the
oriented extended-tube image.  The hard Hall-Wightman Lemma-3 content remains
the local vector-realization datum at each extended-tube point.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Local vector-realization data for the oriented extended-tube image near an
extended-tube source tuple.  The `realizes` field is the mathematical content:
nearby oriented-variety points in the ambient neighborhood must be realized by
actual source tuples still lying in `ExtendedTube`. -/
structure SourceOrientedExtendedTubeLocalRealizationData
    (d n : ℕ)
    (z0 : Fin n → Fin (d + 1) → ℂ) where
  Ω : Set (SourceOrientedGramData d n)
  Ω_open : IsOpen Ω
  center_mem : sourceOrientedMinkowskiInvariant d n z0 ∈ Ω
  realizes :
    Ω ∩ sourceOrientedGramVariety d n ⊆
      sourceOrientedExtendedTubeDomain d n

/-- The local-realization theorem is exactly the missing geometric input for
relative openness of the oriented extended-tube image. -/
def SourceOrientedExtendedTubeLocalRealizationProducer
    (d n : ℕ) : Type :=
  ∀ {z0 : Fin n → Fin (d + 1) → ℂ},
    z0 ∈ ExtendedTube d n →
      SourceOrientedExtendedTubeLocalRealizationData d n z0

/-- The explicit reconstructed vector map is continuous on the model
determinant-nonzero locus. -/
theorem continuousOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ContinuousOn (sourceFullFrameGauge_reconstructVector d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) :=
  (differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
    d n ι M0 S).continuousOn

/-- Full-frame, selected-determinant-nonzero local realization of nearby
oriented source data by actual extended-tube source tuples.

This is the max-rank tube-shrink step: start with the source-centered
full-frame chart, shrink its model domain so the explicit reconstructed vector
stays in the open extended tube, then pull that model shrink back to an
ambient source-variety neighborhood. -/
noncomputable def sourceOrientedExtendedTubeLocalRealizationData_of_fullFrameDetNonzero
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hdet : sourceFullFrameDet d n ι z0 ≠ 0) :
    SourceOrientedExtendedTubeLocalRealizationData d n z0 := by
  classical
  let G0 : SourceOrientedGramData d n :=
    sourceOrientedMinkowskiInvariant d n z0
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
  let T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    sourceFullFrameMaxRankChart_ambientShrink
      d n ι hM0 S hG0 hM0_oriented
  let f : sourceFullFrameMaxRankChartModel d n ι M0 S →
      Fin n → Fin (d + 1) → ℂ :=
    sourceFullFrameGauge_reconstructVector d n ι M0 S
  let modelDet : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    sourceFullFrameGaugeModelDetNonzero d n ι M0 S
  have hf_cont : ContinuousOn f modelDet := by
    simpa [f, modelDet] using
      continuousOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
        d n ι M0 S
  let preSpec :=
    (continuousOn_iff'.mp hf_cont)
      (ExtendedTube d n) (isOpen_extendedTube (d := d) (n := n))
  let U : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    Classical.choose preSpec
  have hU_spec :
      IsOpen U ∧ f ⁻¹' ExtendedTube d n ∩ modelDet = U ∩ modelDet :=
    Classical.choose_spec preSpec
  have hU_open : IsOpen U := hU_spec.1
  have hpre_eq :
      f ⁻¹' ExtendedTube d n ∩ modelDet = U ∩ modelDet :=
    hU_spec.2
  let y0 : sourceFullFrameMaxRankChartModel d n ι M0 S :=
    SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
      (d := d) (n := n) (ι := ι) hM0 S G0
  have hframe0 :
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y0 =
        sourceFullFrameMatrix d n ι z0 := by
    simpa [y0, G0, M0] using
      SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_reconstructFrame_center_eq
        (d := d) (n := n) (ι := ι) hM0 S hG0 hM0_oriented
  have hdetG0 : G0.det ι ≠ 0 := by
    simpa [G0, sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det,
      sourceFullFrameDet] using hdet
  have hf_y0 : f y0 = z0 := by
    simpa [f, y0, G0] using
      sourceFullFrameGauge_reconstructVector_eq_of_frame_eq_mixedRows_eq
        d n ι M0 S y0 z0 hframe0 rfl hdetG0
  have hy0_model : y0 ∈ T.modelChartDomain :=
    T.chartCandidate_center_mem_modelChartDomain hG0 hM0_oriented
  have hy0_U : y0 ∈ U := by
    have hy0_pre : y0 ∈ f ⁻¹' ExtendedTube d n ∩ modelDet := by
      exact ⟨by simpa [hf_y0] using hz0, by simpa [modelDet] using hy0_model.2.2⟩
    have hy0_U_det : y0 ∈ U ∩ modelDet := by
      rw [← hpre_eq]
      exact hy0_pre
    exact hy0_U_det.1
  let V : Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
    U ∩ T.modelChartDomain
  have hV_open : IsOpen V := by
    exact hU_open.inter T.modelChartDomain_open
  have hcenterV : y0 ∈ V := by
    exact ⟨hy0_U, hy0_model⟩
  have hsource :
      ∀ y ∈ V,
        y.1 ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).source := by
    intro y hy
    exact hy.2.1
  have hmodelDet_of_mem_V : ∀ y ∈ V, y ∈ modelDet := by
    intro y hy
    exact hy.2.2.2
  have hdetV :
      ∀ y ∈ V,
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0 := by
    intro y hy
    simpa [modelDet] using hmodelDet_of_mem_V y hy
  have hreconstruct :
      ∀ y ∈ V,
        sourceFullFrameGauge_reconstructInvariant d n ι M0 S y ∈
          T.relDomain := by
    intro y hy
    exact
      ⟨hy.2.2.1,
        sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y⟩
  have hV_ET :
      ∀ y ∈ V, f y ∈ ExtendedTube d n := by
    intro y hy
    have hy_pre : y ∈ f ⁻¹' ExtendedTube d n ∩ modelDet := by
      rw [hpre_eq]
      exact ⟨hy.1, hmodelDet_of_mem_V y hy⟩
    exact hy_pre.1
  let hex :=
    T.exists_restrict_modelOpen_image_eq
      hV_open hcenterV hsource hdetV hreconstruct
  let T' : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    Classical.choose hex
  have hT'_image :
      (SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
        (d := d) (n := n) (ι := ι) hM0 S) '' T'.relDomain = V :=
    (Classical.choose_spec hex).2
  refine
    { Ω := T'.Ωamb
      Ω_open := T'.Ωamb_open
      center_mem := by
        simpa [G0] using T'.center_mem
      realizes := ?_ }
  intro G hG
  let y : sourceFullFrameMaxRankChartModel d n ι M0 S :=
    SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
      (d := d) (n := n) (ι := ι) hM0 S G
  have hG_rel : G ∈ T'.relDomain := ⟨hG.1, hG.2⟩
  have hyV : y ∈ V := by
    have hy_image :
        y ∈
          (SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
            (d := d) (n := n) (ι := ι) hM0 S) '' T'.relDomain := by
      exact ⟨G, hG_rel, rfl⟩
    simpa [y, hT'_image] using hy_image
  let z : Fin n → Fin (d + 1) → ℂ := f y
  have hzET : z ∈ ExtendedTube d n := hV_ET y hyV
  have hrec :
      sourceFullFrameGauge_reconstructInvariant d n ι M0 S y = G := by
    simpa [y] using
      T'.reconstructInvariant_chartCandidate_eq_of_mem_relDomain hG_rel
  refine ⟨z, hzET, ?_⟩
  simpa [z, f, sourceFullFrameGauge_reconstructInvariant_eq] using hrec

/-- In the hard range, max rank supplies a nonzero full-frame determinant, so
the checked full-frame tube shrink gives local realization. -/
noncomputable def sourceOrientedExtendedTubeLocalRealizationData_of_fullFrameMaxRank
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hmax :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    SourceOrientedExtendedTubeLocalRealizationData d n z0 := by
  classical
  have hHW : HWSourceGramMaxRankAt d n z0 :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt d n z0).1
      hmax
  have hreg : SourceComplexGramRegularAt d n z0 :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn hHW
  let hex := exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
    d n hn hreg
  let ι : Fin (d + 1) ↪ Fin n := Classical.choose hex
  have hdet : sourceFullFrameDet d n ι z0 ≠ 0 :=
    Classical.choose_spec hex
  exact
    sourceOrientedExtendedTubeLocalRealizationData_of_fullFrameDetNonzero
      ι hz0 hdet

/-- Relative openness of the oriented extended-tube image, once local
realization is supplied at every extended-tube source tuple. -/
theorem sourceOrientedExtendedTubeDomain_relOpen_of_localRealization
    (localRealization :
      SourceOrientedExtendedTubeLocalRealizationProducer d n) :
    IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedExtendedTubeDomain d n) := by
  classical
  let I : Type := {z : Fin n → Fin (d + 1) → ℂ // z ∈ ExtendedTube d n}
  let Ω : Set (SourceOrientedGramData d n) :=
    ⋃ p : I, (localRealization p.2).Ω
  refine ⟨Ω, ?_, ?_⟩
  · exact isOpen_iUnion fun p => (localRealization p.2).Ω_open
  · ext G
    constructor
    · intro hG
      rcases hG with ⟨z, hz, rfl⟩
      constructor
      · exact Set.mem_iUnion.2
          ⟨⟨z, hz⟩, (localRealization hz).center_mem⟩
      · exact ⟨z, rfl⟩
    · rintro ⟨hGΩ, hGvar⟩
      rcases Set.mem_iUnion.1 hGΩ with ⟨p, hp⟩
      exact (localRealization p.2).realizes ⟨hp, hGvar⟩

/-- Relative openness plus connectedness of the oriented extended-tube image,
with the geometric work isolated in the local-realization producer. -/
theorem sourceOrientedExtendedTubeDomain_relOpen_connected_of_localRealization
    (localRealization :
      SourceOrientedExtendedTubeLocalRealizationProducer d n) :
    IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedExtendedTubeDomain d n) ∧
      IsConnected (sourceOrientedExtendedTubeDomain d n) := by
  exact
    ⟨sourceOrientedExtendedTubeDomain_relOpen_of_localRealization
        (d := d) (n := n) localRealization,
      sourceOrientedExtendedTubeDomain_connected d n⟩

end BHW
