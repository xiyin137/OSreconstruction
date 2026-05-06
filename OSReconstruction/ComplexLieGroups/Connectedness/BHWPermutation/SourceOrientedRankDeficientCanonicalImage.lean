import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientSchurWindowShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeNormal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurReconstruct
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurGraph

/-!
# Canonical extracted Schur image for rank-deficient source charts

This file exposes the honest extracted-image set for the remaining
rank-deficient local-image producer.  The set is cut out by the local
head-gauge chart, the extracted Schur mixed coordinate, and target-shaped
shifted-tail residual bounds.  The finite-coordinate continuity proof, both
algebraic inclusions, and the head-gauge canonical-image/local-image wrappers
are checked here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected Schur head block is a continuous finite-coordinate projection
of the oriented source Gram data. -/
theorem continuous_sourceOrientedSchurHeadBlock
    (d n r : ℕ)
    (hrn : r ≤ n) :
    Continuous
      (fun G : SourceOrientedGramData d n =>
        sourceOrientedSchurHeadBlock n r hrn G) := by
  unfold sourceOrientedSchurHeadBlock
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  exact
    (continuous_apply (finSourceHead hrn b)).comp
      ((continuous_apply (finSourceHead hrn a)).comp
        (continuous_sourceOrientedGramData_gram (d := d) (n := n)))

/-- The selected Schur mixed block is a continuous finite-coordinate
projection of the oriented source Gram data. -/
theorem continuous_sourceOrientedSchurMixedBlock
    (d n r : ℕ)
    (hrn : r ≤ n) :
    Continuous
      (fun G : SourceOrientedGramData d n =>
        sourceOrientedSchurMixedBlock n r hrn G) := by
  unfold sourceOrientedSchurMixedBlock
  apply continuous_pi
  intro u
  apply continuous_pi
  intro a
  exact
    (continuous_apply (finSourceHead hrn a)).comp
      ((continuous_apply (finSourceTail hrn u)).comp
        (continuous_sourceOrientedGramData_gram (d := d) (n := n)))

/-- The selected Schur tail block is a continuous finite-coordinate projection
of the oriented source Gram data. -/
theorem continuous_sourceOrientedSchurTailBlock
    (d n r : ℕ)
    (hrn : r ≤ n) :
    Continuous
      (fun G : SourceOrientedGramData d n =>
        sourceOrientedSchurTailBlock n r hrn G) := by
  unfold sourceOrientedSchurTailBlock
  apply continuous_pi
  intro u
  apply continuous_pi
  intro v
  exact
    (continuous_apply (finSourceTail hrn v)).comp
      ((continuous_apply (finSourceTail hrn u)).comp
        (continuous_sourceOrientedGramData_gram (d := d) (n := n)))

/-- Subtype-valued continuity of the selected symmetric Schur head coordinate
on the source-oriented variety. -/
theorem continuous_sourceOrientedSchurHeadBlockSymm_on_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (fun Gv : SourceOrientedVariety d n =>
        sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2) := by
  apply Continuous.subtype_mk
  exact
    (continuous_sourceOrientedSchurHeadBlock d n r hrn).comp
      continuous_subtype_val

/-- The source-variety points whose selected head lies in the head gauge and
whose gauge factor lies in a prescribed head-coordinate window form an open
subtype set. -/
theorem isOpen_sourceOrientedHeadGaugeSchurHeadWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius : ℝ) :
    IsOpen
      {Gv : SourceOrientedVariety d n |
        let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
        Acoord ∈ Head.U ∧
          Head.factor Acoord ∈ sourceOrientedHeadCoordinateWindow r headRadius} := by
  let Amap : SourceOrientedVariety d n → SourceSymmetricMatrixCoord r :=
    fun Gv => sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  have hAmap_cont : Continuous Amap :=
    continuous_sourceOrientedSchurHeadBlockSymm_on_variety d n r hrD hrn
  have htarget_open :
      IsOpen
        (Head.U ∩ Head.factor ⁻¹'
          sourceOrientedHeadCoordinateWindow r headRadius) := by
    exact
      Head.factor_continuousOn.isOpen_inter_preimage
        Head.U_open (isOpen_sourceOrientedHeadCoordinateWindow r headRadius)
  have hpre :
      IsOpen
        (Amap ⁻¹'
          (Head.U ∩ Head.factor ⁻¹'
            sourceOrientedHeadCoordinateWindow r headRadius)) :=
    htarget_open.preimage hAmap_cont
  simpa [Amap, Set.preimage_setOf_eq, and_assoc] using hpre

/-- On the open head-gauge patch, the extracted Schur mixed coefficient is
continuous.  The only non-polynomial operation is inversion of the selected
head block, and the head-gauge determinant-unit theorem supplies its unit
patch. -/
theorem continuousOn_sourceSchurMixedCoeff_headGaugePatch
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    ContinuousOn
      (fun Gv : SourceOrientedVariety d n =>
        sourceSchurMixedCoeff n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1))
      {Gv : SourceOrientedVariety d n |
        sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U} := by
  let S : Set (SourceOrientedVariety d n) :=
    {Gv | sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U}
  let Amap : SourceOrientedVariety d n → Matrix (Fin r) (Fin r) ℂ :=
    fun Gv => sourceOrientedSchurHeadBlock n r hrn Gv.1
  let Mmap : SourceOrientedVariety d n → Matrix (Fin (n - r)) (Fin r) ℂ :=
    fun Gv => sourceOrientedSchurMixedBlock n r hrn Gv.1
  have hA_cont : Continuous Amap :=
    (continuous_sourceOrientedSchurHeadBlock d n r hrn).comp
      continuous_subtype_val
  have hM_cont : Continuous Mmap :=
    (continuous_sourceOrientedSchurMixedBlock d n r hrn).comp
      continuous_subtype_val
  have hmaps :
      Set.MapsTo Amap S
        {A : Matrix (Fin r) (Fin r) ℂ | IsUnit A.det} := by
    intro Gv hGv
    exact
      sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
        d n r hrD hrn Gv.2 Head hGv
  have hInv_on : ContinuousOn (fun Gv => (Amap Gv)⁻¹) S := by
    intro Gv hGv
    have hA_unit : IsUnit (Amap Gv).det := hmaps hGv
    have hA_within : ContinuousWithinAt Amap S Gv :=
      hA_cont.continuousAt.continuousWithinAt
    have hInv_base : ContinuousWithinAt
        (fun A : Matrix (Fin r) (Fin r) ℂ => A⁻¹)
        {A : Matrix (Fin r) (Fin r) ℂ | IsUnit A.det} (Amap Gv) :=
      continuousOn_matrix_inv_of_isUnit_det (Amap Gv) hA_unit
    exact hInv_base.comp hA_within hmaps
  change ContinuousOn
    (fun Gv : SourceOrientedVariety d n =>
      Mmap Gv * (Amap Gv)⁻¹) S
  change ContinuousOn
    (fun Gv : SourceOrientedVariety d n =>
      fun u a => (Mmap Gv * (Amap Gv)⁻¹) u a) S
  rw [continuousOn_pi]
  intro u
  rw [continuousOn_pi]
  intro a
  simp [Matrix.mul_apply]
  apply continuousOn_finset_sum
  intro b _hb
  have hM_entry : ContinuousOn (fun Gv => Mmap Gv u b) S := by
    exact
      ((continuous_apply b).comp
        ((continuous_apply u).comp hM_cont)).continuousOn
  have hInv_entry : ContinuousOn (fun Gv => (Amap Gv)⁻¹ b a) S := by
    exact
      (continuous_apply a).comp_continuousOn
        ((continuous_apply b).comp_continuousOn hInv_on)
  exact hM_entry.mul hInv_entry

/-- The head-gauge/factor-window patch further cut by the extracted mixed
Schur-coordinate window is open. -/
theorem isOpen_sourceOrientedHeadGaugeSchurHeadMixedWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ) :
    IsOpen
      {Gv : SourceOrientedVariety d n |
        let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
        Acoord ∈ Head.U ∧
          Head.factor Acoord ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
          sourceSchurMixedCoeff n r hrn Gv.1
              (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
            sourceOrientedMixedCoordinateWindow n r mixedRadius} := by
  let baseSet : Set (SourceOrientedVariety d n) :=
    {Gv |
      let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
      Acoord ∈ Head.U ∧
        Head.factor Acoord ∈ sourceOrientedHeadCoordinateWindow r headRadius}
  let mixedMap : SourceOrientedVariety d n →
      Matrix (Fin (n - r)) (Fin r) ℂ :=
    fun Gv =>
      sourceSchurMixedCoeff n r hrn Gv.1
        (sourceOrientedSchurHeadBlock n r hrn Gv.1)
  have hbase_open : IsOpen baseSet := by
    simpa [baseSet] using
      isOpen_sourceOrientedHeadGaugeSchurHeadWindow
        d n r hrD hrn Head headRadius
  have hmixed_cont_base : ContinuousOn mixedMap baseSet := by
    exact
      (continuousOn_sourceSchurMixedCoeff_headGaugePatch
        d n r hrD hrn Head).mono (by
          intro Gv hGv
          simpa [baseSet] using hGv.1)
  have hopen :
      IsOpen
        (baseSet ∩ mixedMap ⁻¹'
          sourceOrientedMixedCoordinateWindow n r mixedRadius) := by
    exact
      hmixed_cont_base.isOpen_inter_preimage hbase_open
        (isOpen_sourceOrientedMixedCoordinateWindow n r mixedRadius)
  convert hopen using 1
  ext Gv
  simp [baseSet, mixedMap, and_assoc]

/-- On the head-gauge patch, the extracted residual Schur-complement Gram
block is continuous. -/
theorem continuousOn_sourceSchurComplement_headGaugePatch
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    ContinuousOn
      (fun Gv : SourceOrientedVariety d n =>
        sourceSchurComplement n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1))
      {Gv : SourceOrientedVariety d n |
        sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U} := by
  let S : Set (SourceOrientedVariety d n) :=
    {Gv | sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U}
  let Amap : SourceOrientedVariety d n → Matrix (Fin r) (Fin r) ℂ :=
    fun Gv => sourceOrientedSchurHeadBlock n r hrn Gv.1
  let Lmap : SourceOrientedVariety d n → Matrix (Fin (n - r)) (Fin r) ℂ :=
    fun Gv =>
      sourceSchurMixedCoeff n r hrn Gv.1
        (sourceOrientedSchurHeadBlock n r hrn Gv.1)
  let Cmap : SourceOrientedVariety d n →
      Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
    fun Gv => sourceOrientedSchurTailBlock n r hrn Gv.1
  have hA_cont : Continuous Amap :=
    (continuous_sourceOrientedSchurHeadBlock d n r hrn).comp
      continuous_subtype_val
  have hC_cont : Continuous Cmap :=
    (continuous_sourceOrientedSchurTailBlock d n r hrn).comp
      continuous_subtype_val
  have hL_on : ContinuousOn Lmap S :=
    continuousOn_sourceSchurMixedCoeff_headGaugePatch d n r hrD hrn Head
  change ContinuousOn
    (fun Gv : SourceOrientedVariety d n =>
      Cmap Gv - Lmap Gv * Amap Gv * (Lmap Gv).transpose) S
  fun_prop

/-- On the head-gauge patch, each extracted residual determinant coordinate is
continuous. -/
theorem continuousOn_sourceSchurResidualDeterminant_headGaugePatch
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (ι : Fin (d + 1 - r) ↪ Fin (n - r)) :
    ContinuousOn
      (fun Gv : SourceOrientedVariety d n =>
        sourceSchurResidualDeterminants d n r hrD hrn Gv.1
          (Head.factor
            (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2)) ι)
      {Gv : SourceOrientedVariety d n |
        sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U} := by
  let S : Set (SourceOrientedVariety d n) :=
    {Gv | sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U}
  let Acoord : SourceOrientedVariety d n → SourceSymmetricMatrixCoord r :=
    fun Gv => sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  let Hmap : SourceOrientedVariety d n → Matrix (Fin r) (Fin r) ℂ :=
    fun Gv => Head.factor (Acoord Gv)
  have hAcoord_cont : Continuous Acoord :=
    continuous_sourceOrientedSchurHeadBlockSymm_on_variety d n r hrD hrn
  have hAcoord_on : ContinuousOn Acoord S :=
    hAcoord_cont.continuousOn
  have hAcoord_maps : Set.MapsTo Acoord S Head.U := by
    intro Gv hGv
    simpa [S, Acoord] using hGv
  have hH_on : ContinuousOn Hmap S := by
    simpa [Hmap] using
      Head.factor_continuousOn.comp' hAcoord_on hAcoord_maps
  have hnum_on : ContinuousOn
      (fun Gv : SourceOrientedVariety d n =>
        Gv.1.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn ι)) S := by
    exact
      ((continuous_apply
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn ι)).comp
        ((continuous_sourceOrientedGramData_det (d := d) (n := n)).comp
          continuous_subtype_val)).continuousOn
  have hden_on : ContinuousOn (fun Gv : SourceOrientedVariety d n =>
      (Hmap Gv).det) S := by
    have hdet : Continuous (fun H : Matrix (Fin r) (Fin r) ℂ => H.det) := by
      fun_prop
    exact hdet.comp_continuousOn hH_on
  have hden_ne : ∀ Gv ∈ S, (Hmap Gv).det ≠ 0 := by
    intro Gv hGv
    exact (Head.factor_det_unit (Acoord Gv) (hAcoord_maps hGv)).ne_zero
  simpa [sourceSchurResidualDeterminants, Hmap, Acoord, S] using
    hnum_on.div hden_on hden_ne

/-- The subtype normal-image candidate cut out by head-gauge Schur extraction.
It is the set that should be open in `SourceOrientedVariety d n`: the selected
head lies in the gauge domain, the gauge factor and mixed Schur coefficient
lie in the chosen coordinate windows, and the gauge-selected shifted residual
tail satisfies the target-shaped tail-radius bounds. -/
def sourceOrientedHeadGaugeSchurExtractedImage
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedVariety d n) :=
  {Gv |
    let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
    let H := Head.factor Acoord
    let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
    Acoord ∈ Head.U ∧
      H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
      sourceSchurMixedCoeff n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
        sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
      (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
      (∀ ι, ‖T.det ι‖ < Tail.tailEta)}

/-- The extracted Schur image set is open in the source-oriented variety
subtype. -/
theorem isOpen_sourceOrientedHeadGaugeSchurExtractedImage
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen
      (sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail) := by
  let baseSet : Set (SourceOrientedVariety d n) :=
    {Gv |
      let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
      Acoord ∈ Head.U ∧
        Head.factor Acoord ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
        sourceSchurMixedCoeff n r hrn Gv.1
            (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
          sourceOrientedMixedCoordinateWindow n r mixedRadius}
  let gramMap : SourceOrientedVariety d n →
      Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
    fun Gv =>
      sourceSchurComplement n r hrn Gv.1
        (sourceOrientedSchurHeadBlock n r hrn Gv.1)
  let detMap : SourceOrientedVariety d n →
      ((Fin (d + 1 - r) ↪ Fin (n - r)) → ℂ) :=
    fun Gv ι =>
      sourceSchurResidualDeterminants d n r hrD hrn Gv.1
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2)) ι
  let gramWindow : Set (Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :=
    {C | ∀ u v, ‖C u v‖ < Tail.tailEta}
  let detWindow : Set ((Fin (d + 1 - r) ↪ Fin (n - r)) → ℂ) :=
    {D | ∀ ι, ‖D ι‖ < Tail.tailEta}
  have hbase_open : IsOpen baseSet := by
    simpa [baseSet] using
      isOpen_sourceOrientedHeadGaugeSchurHeadMixedWindow
        d n r hrD hrn Head headRadius mixedRadius
  have hbase_sub_head :
      baseSet ⊆
        {Gv : SourceOrientedVariety d n |
          sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2 ∈ Head.U} := by
    intro Gv hGv
    simpa [baseSet] using hGv.1
  have hgram_cont_base : ContinuousOn gramMap baseSet :=
    (continuousOn_sourceSchurComplement_headGaugePatch
      d n r hrD hrn Head).mono hbase_sub_head
  have hdet_cont_base : ContinuousOn detMap baseSet := by
    rw [continuousOn_pi]
    intro ι
    exact
      (continuousOn_sourceSchurResidualDeterminant_headGaugePatch
        d n r hrD hrn Head ι).mono hbase_sub_head
  have hgramWindow_open : IsOpen gramWindow := by
    have h :=
      isOpen_sourceMatrixCoordinateWindow
        (0 : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) Tail.tailEta
    simpa [gramWindow, sourceMatrixCoordinateWindow, sub_zero] using h
  have hdetWindow_open : IsOpen detWindow := by
    simp only [detWindow, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun ι =>
      isOpen_lt (by fun_prop) continuous_const
  have hgram_open :
      IsOpen (baseSet ∩ gramMap ⁻¹' gramWindow) := by
    exact
      hgram_cont_base.isOpen_inter_preimage hbase_open hgramWindow_open
  have hdet_cont_gram : ContinuousOn detMap
      (baseSet ∩ gramMap ⁻¹' gramWindow) :=
    hdet_cont_base.mono Set.inter_subset_left
  have hfinal :
      IsOpen
        ((baseSet ∩ gramMap ⁻¹' gramWindow) ∩
          detMap ⁻¹' detWindow) := by
    exact
      hdet_cont_gram.isOpen_inter_preimage hgram_open hdetWindow_open
  convert hfinal using 1
  ext Gv
  simp [sourceOrientedHeadGaugeSchurExtractedImage, baseSet, gramMap, detMap,
    gramWindow, detWindow, sourceOrientedSchurResidualTailData, and_assoc]

/-- Forward inclusion for the extracted image: a normal parameter in a
head-gauge-compatible Schur window satisfies exactly the extracted
head/mixed/residual-tail conditions. -/
theorem sourceOrientedNormalParameterVarietyPoint_mem_headGaugeSchurExtractedImage
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p ∈
      sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail := by
  let Gv := sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  let H := Head.factor Acoord
  let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
  have hpDomain : p.head ∈ Head.factorDomain := hdomain hp.1
  have hAeq :
      Acoord = sourceHeadFactorGramSymmCoord d r hrD p.head := by
    simpa [Gv, Acoord] using
      sourceOrientedSchurHeadBlockSymm_normalParameter d n r hrD hrn p
  have hHeadU : Acoord ∈ Head.U := by
    rw [hAeq]
    exact Head.factorDomain_mem p.head hpDomain
  have hfactor : H = p.head := by
    dsimp [H]
    rw [hAeq]
    exact Head.factor_left_inverse p.head hpDomain
  have hmixed :
      sourceSchurMixedCoeff n r hrn Gv.1
          (sourceOrientedSchurHeadBlock n r hrn Gv.1) =
        p.mixed := by
    simpa [Gv] using
      SourceOrientedRankDeficientAlgebraicNormalFormData.schurWindow_normalParameter_headGauge_mixedCoeff_eq
        Head hdomain p hp
  have htail :
      T = sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
    simpa [Gv, Acoord, H, T] using
      SourceOrientedRankDeficientAlgebraicNormalFormData.schurWindow_normalParameter_headGauge_residualTail_eq
        Head hdomain p hp
  have hfactor' :
      Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2) =
        p.head := by
    simpa [Acoord, H] using hfactor
  have htail' :
      sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1
          (Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2)) =
        sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
    simpa [Acoord, H, T] using htail
  change
    (let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
     let H := Head.factor Acoord
     let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
     Acoord ∈ Head.U ∧
       H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
       sourceSchurMixedCoeff n r hrn Gv.1
           (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
         sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
       (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
       (∀ ι, ‖T.det ι‖ < Tail.tailEta))
  dsimp only
  refine ⟨hHeadU, ?_, ?_, ?_, ?_⟩
  · simpa [hfactor'] using hp.1
  · simpa [hmixed] using hp.2.1
  · intro u v
    have h := hp.2.2.2.1 u v
    simpa [htail'] using h
  · intro ι
    have h := hp.2.2.2.2 ι
    simpa [htail'] using h

/-- Reverse inclusion for the extracted image.  A source-variety point whose
head-gauge Schur extraction lies in the target-shaped windows is reconstructed
by a normal parameter in the corresponding Schur window. -/
theorem sourceOrientedHeadGaugeSchurExtractedImage_subset_normalParameter_image
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (headRadius mixedRadius : ℝ)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail ⊆
      sourceOrientedNormalParameterVarietyPoint d n r hrD hrn ''
        sourceOrientedRankDeficientSchurParameterWindow
          d n r hrD hrn headRadius mixedRadius Tail := by
  intro Gv hGv
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
  let H := Head.factor Acoord
  let L := sourceSchurMixedCoeff n r hrn Gv.1
    (sourceOrientedSchurHeadBlock n r hrn Gv.1)
  let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
  change
    (let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2
     let H := Head.factor Acoord
     let T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H
     Acoord ∈ Head.U ∧
       H ∈ sourceOrientedHeadCoordinateWindow r headRadius ∧
       sourceSchurMixedCoeff n r hrn Gv.1
           (sourceOrientedSchurHeadBlock n r hrn Gv.1) ∈
         sourceOrientedMixedCoordinateWindow n r mixedRadius ∧
       (∀ u v, ‖T.gram u v‖ < Tail.tailEta) ∧
       (∀ ι, ‖T.det ι‖ < Tail.tailEta)) at hGv
  dsimp only at hGv
  rcases hGv with ⟨hHeadU, hH_window, hL_window, hT_gram, hT_det⟩
  let R : SourceOrientedSchurResidualData d n r hrD hrn Gv.1 :=
    sourceOriented_schurResidualData_of_headGauge
      hd hrD hrn Head Gv.2 hHeadU
  have hT_mem :
      T ∈ sourceShiftedTailOrientedVariety d r hrD (n - r) := by
    simpa [T, H, Acoord] using
      sourceOrientedSchurResidualTailData_mem_variety
        hd hrD hrn Head Gv.2 hHeadU
  rcases Tail.tailRealize T hT_mem hT_gram hT_det with
    ⟨q, hq_coord, hqT⟩
  have hqR :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) q = R.tail := by
    simpa [R, T, H, Acoord,
      sourceOriented_schurResidualData_of_headGauge,
      sourceOriented_schurResidualData_of_tail_mem] using hqT
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := R.headFactor
      mixed := R.L
      tail := q }
  have hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [p, R, H, Acoord,
        sourceOriented_schurResidualData_of_headGauge,
        sourceOriented_schurResidualData_of_tail_mem] using hH_window
    · simpa [p, R, L, H, Acoord,
        sourceOriented_schurResidualData_of_headGauge,
        sourceOriented_schurResidualData_of_tail_mem] using hL_window
    · refine ⟨?_, ?_, ?_⟩
      · simpa [p] using hq_coord
      · intro u v
        have hproj :
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v =
              T.gram u v := by
          exact congrFun (congrFun (congrArg SourceShiftedTailOrientedData.gram hqT) u) v
        rw [hproj]
        exact hT_gram u v
      · intro ι
        have hproj :
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι =
              T.det ι := by
          exact congrFun (congrArg SourceShiftedTailOrientedData.det hqT) ι
        rw [hproj]
        exact hT_det ι
  refine ⟨p, hp, ?_⟩
  apply Subtype.ext
  have hrecon :=
    sourceOriented_reconstruct_from_schurResidual
      d n r hn hrD hrn Gv.2 R hqR
  simpa [sourceOrientedNormalParameterVarietyPoint, p] using hrecon

/-- The canonical Schur/residual image theorem for a fixed head-gauge-compatible
Schur window.  The open image is the extracted Schur image set above; openness
and both image inclusions are now checked. -/
theorem sourceOrientedHeadGaugeSchurWindowCanonicalImage
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain) :
    ∃ Ω : Set (SourceOrientedVariety d n),
      IsOpen Ω ∧
        Ω ⊆
          sourceOrientedNormalParameterVarietyPoint d n r hrD hrn ''
            sourceOrientedRankDeficientSchurParameterWindow
              d n r hrD hrn headRadius mixedRadius Tail ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSchurParameterWindow
            d n r hrD hrn headRadius mixedRadius Tail →
          sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p ∈ Ω) := by
  refine
    ⟨sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail,
      isOpen_sourceOrientedHeadGaugeSchurExtractedImage
        d n r hrD hrn Head headRadius mixedRadius Tail,
      ?_, ?_⟩
  · exact
      sourceOrientedHeadGaugeSchurExtractedImage_subset_normalParameter_image
        hd hn hrD hrn Head headRadius mixedRadius Tail
  · intro p hp
    exact
      sourceOrientedNormalParameterVarietyPoint_mem_headGaugeSchurExtractedImage
        Head hdomain p hp

namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- Head-gauge form of the strengthened rank-deficient local-image producer.
Once a local head gauge is supplied at the canonical center, all Schur-window
shrink, canonical-image openness/surjectivity, transported containment, and
max-rank connectedness fields are checked. -/
noncomputable def maxRankLocalImageData_of_headGaugeSchurWindow
    [NeZero d]
    (hd : 2 ≤ d)
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (Head : SourceRankDeficientHeadGaugeData d N.r N.hrD)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    Σ P : Type, Σ _ : TopologicalSpace P,
      SourceOrientedRankDeficientMaxRankLocalImageData
        (d := d) (n := n) (P := P) G0 N0 :=
  N.maxRankLocalImageData_of_headGaugeSchurWindowCanonicalImage
    hn Head hN0_open hG0N0
    (fun {headRadius} {mixedRadius} {Tail} _hhead _hmixed hdomain =>
      sourceOrientedHeadGaugeSchurWindowCanonicalImage
        (d := d) (n := n) hd hn N.hrD N.hrn Head
        (headRadius := headRadius) (mixedRadius := mixedRadius)
        Tail hdomain)

end SourceOrientedRankDeficientAlgebraicNormalFormData

end BHW
