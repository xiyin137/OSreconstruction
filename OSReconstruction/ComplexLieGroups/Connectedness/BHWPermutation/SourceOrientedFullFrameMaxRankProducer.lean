import Mathlib.LinearAlgebra.Basis.Defs
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalBasis
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexDensity

/-!
# Full-frame max-rank chart producer

This file converts the full-frame chart construction into the max-rank chart
producer expected by the oriented local-basis layer in the hard range
`d + 1 <= n`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected nonzero full frame of a source tuple as a basis of complex
spacetime. -/
noncomputable def sourceFullFrameBasis
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    Module.Basis (Fin (d + 1)) ℂ (Fin (d + 1) → ℂ) :=
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let hMdet : IsUnit M.transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (by simpa [M, sourceFullFrameDet] using hι)
  letI hM : Invertible M.transpose :=
    Matrix.invertibleOfIsUnitDet M.transpose hMdet
  (Pi.basisFun ℂ (Fin (d + 1))).map
    (Matrix.toLinearEquiv' M.transpose hM)

/-- The selected full-frame basis evaluates to the selected source vectors. -/
theorem sourceFullFrameBasis_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (a : Fin (d + 1)) :
    sourceFullFrameBasis d n ι z hι a = z (ι a) := by
  ext μ
  unfold sourceFullFrameBasis
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change
    ((((sourceFullFrameMatrix d n ι z).transpose.toLinearEquiv' _) :
        Module.End ℂ (Fin (d + 1) → ℂ)) (Pi.single a 1)) μ =
      z (ι a) μ
  rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  simp [sourceFullFrameMatrix]

/-- In the hard range `d + 1 <= n`, scalar max rank of an actual source
configuration forces maximal complex source span. -/
theorem sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt
    (d n : ℕ)
    (hn : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hmax : HWSourceGramMaxRankAt d n z) :
    SourceComplexGramRegularAt d n z := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n z
  have hrank_ge :
      d + 1 ≤
        (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank := by
    simpa [HWSourceGramMaxRankAt, HWSourceGramMaxRank, sourceGramMatrixRank,
      Nat.min_eq_left hn] using hmax
  have hrank_le :
      (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank ≤
        Module.finrank ℂ S := by
    simpa [S] using
      sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank d n z
  have hge : d + 1 ≤ Module.finrank ℂ S :=
    le_trans hrank_ge hrank_le
  have hle : Module.finrank ℂ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [S, sourceComplexConfigurationSpan, Module.finrank_fin_fun] using h
  unfold SourceComplexGramRegularAt
  rw [Nat.min_eq_right hn]
  exact le_antisymm hle hge

/-- In the hard range, maximal complex source span supplies a selected
full-frame source determinant which is nonzero. -/
theorem exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
    (d n : ℕ)
    (hn : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z) :
    ∃ ι : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n ι z ≠ 0 := by
  rcases exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg with
    ⟨I, hI, _J, _hJ, hminor⟩
  let e : Fin (d + 1) ≃ Fin (min n (d + 1)) :=
    finCongr (Nat.min_eq_right hn).symm
  let ι : Fin (d + 1) ↪ Fin n :=
    { toFun := fun a => I (e a)
      inj' := by
        intro a b hab
        exact e.injective (hI hab) }
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  have hli_min :
      LinearIndependent ℂ (fun a : Fin (min n (d + 1)) => z (I a)) :=
    linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
      d n hminor
  have hli :
      LinearIndependent ℂ (fun a : Fin (d + 1) => z (ι a)) := by
    simpa [ι, Function.comp_def] using hli_min.comp e e.injective
  have hrows : LinearIndependent ℂ M.row := by
    simpa [M, sourceFullFrameMatrix, Matrix.row] using hli
  have hMunit : IsUnit M :=
    (Matrix.linearIndependent_rows_iff_isUnit).1 hrows
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).1 hMunit).ne_zero
  exact ⟨ι, by simpa [M, sourceFullFrameDet] using hdet⟩

/-- Same ordinary source Gram preserves nonvanishing of a selected full-frame
determinant. -/
theorem sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    sourceFullFrameDet d n ι w ≠ 0 := by
  let Mz : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let Mw : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι w
  have hsel :
      sourceFullFrameGram d Mz =
        sourceFullFrameGram d Mw := by
    ext a b
    simpa [Mz, Mw, sourceFullFrameGram_sourceFullFrameMatrix] using
      congrFun (congrFun hgram (ι a)) (ι b)
  intro hwzero
  have hdet_eq :
      (Matrix.of (sourceFullFrameGram d Mz)).det =
        (Matrix.of (sourceFullFrameGram d Mw)).det := by
    simpa using
      congrArg (fun G : Fin (d + 1) → Fin (d + 1) → ℂ =>
        (Matrix.of G).det) hsel
  have hzdet : Mz.det ≠ 0 := by
    simpa [Mz, sourceFullFrameDet] using hι
  have hwdet : Mw.det = 0 := by
    simpa [Mw, sourceFullFrameDet] using hwzero
  have hdet_eq' :
      minkowskiMetricDet d * Mz.det ^ 2 =
        minkowskiMetricDet d * Mw.det ^ 2 := by
    calc
      minkowskiMetricDet d * Mz.det ^ 2 =
          (Matrix.of (sourceFullFrameGram d Mz)).det :=
        (sourceFullFrameGram_det_eq d Mz).symm
      _ = (Matrix.of (sourceFullFrameGram d Mw)).det := hdet_eq
      _ = minkowskiMetricDet d * Mw.det ^ 2 :=
        sourceFullFrameGram_det_eq d Mw
  have hright : minkowskiMetricDet d * Mw.det ^ 2 = 0 := by
    rw [hwdet]
    simp
  exact (mul_ne_zero (minkowskiMetricDet_ne_zero d)
    (pow_ne_zero 2 hzdet)) (hdet_eq'.trans hright)

/-- The selected full-frame map carrying the chosen full frame of `z` to the
corresponding full frame of `w`. -/
noncomputable def sourceFullFrameMap
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
  let hιw := sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    d n hgram ι hι
  (sourceFullFrameBasis d n ι z hι).equiv
    (sourceFullFrameBasis d n ι w hιw)
    (Equiv.refl (Fin (d + 1)))

/-- The selected full-frame map sends selected source vectors of `z` to the
corresponding selected source vectors of `w`. -/
theorem sourceFullFrameMap_apply_selected
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (a : Fin (d + 1)) :
    sourceFullFrameMap d n hgram ι hι (z (ι a)) = w (ι a) := by
  let hιw := sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    d n hgram ι hι
  calc
    sourceFullFrameMap d n hgram ι hι (z (ι a)) =
        sourceFullFrameMap d n hgram ι hι
          ((sourceFullFrameBasis d n ι z hι) a) := by
          rw [sourceFullFrameBasis_apply]
    _ = (sourceFullFrameBasis d n ι w hιw) a := by
          rw [sourceFullFrameMap]
          simp
    _ = w (ι a) := sourceFullFrameBasis_apply d n ι w hιw a

/-- Full scalar Gram rank supplies a nonzero ordered full-frame determinant. -/
theorem exists_sourceFullFrameDet_ne_zero_of_sourceGramRank_eq_spacetime
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1) :
    ∃ ι : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n ι z ≠ 0 := by
  have hrank_le_n :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤ n :=
    by
      simpa [sourceGramMatrixRank] using
        (Matrix.rank_le_width
          (A := Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j))
  have hn : d + 1 ≤ n := by
    simpa [hfull] using hrank_le_n
  have hmax : HWSourceGramMaxRankAt d n z := by
    simp [HWSourceGramMaxRankAt, HWSourceGramMaxRank, hfull,
      Nat.min_eq_left hn]
  have hreg : SourceComplexGramRegularAt d n z :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn hmax
  exact exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
    d n hn hreg

/-- In the hard range, every oriented max-rank source-variety point lies on
some selected full-frame determinant-nonzero sheet. -/
theorem exists_selectedDetNonzero_of_sourceOrientedMaxRankAt
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hmax : SourceOrientedMaxRankAt d n G0) :
    ∃ ι : Fin (d + 1) ↪ Fin n, G0.det ι ≠ 0 := by
  let z : Fin n → Fin (d + 1) → ℂ := Classical.choose hG0
  have hz : sourceOrientedMinkowskiInvariant d n z = G0 :=
    Classical.choose_spec hG0
  have hmax_z :
      SourceOrientedMaxRankAt d n (sourceOrientedMinkowskiInvariant d n z) := by
    simpa [hz] using hmax
  have hHW : HWSourceGramMaxRankAt d n z :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt d n z).1 hmax_z
  have hreg : SourceComplexGramRegularAt d n z :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn hHW
  rcases exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
      d n hn hreg with
    ⟨ι, hdetz⟩
  refine ⟨ι, ?_⟩
  have hdetz' : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0 := by
    simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det] using hdetz
  simpa [hz] using hdetz'

/-- In the hard range, oriented max rank supplies the finite-coordinate
max-rank chart packet expected by the local connected-basis layer. -/
noncomputable def sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hmax : SourceOrientedMaxRankAt d n G0) :
    Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0 := by
  let hex := exists_selectedDetNonzero_of_sourceOrientedMaxRankAt hn hG0 hmax
  let ι : Fin (d + 1) ↪ Fin n := Classical.choose hex
  have hdet : G0.det ι ≠ 0 := Classical.choose_spec hex
  exact sourceOrientedMaxRankChartData_of_selectedDetNonzero ι hG0 hdet

/-- Hard-range local connected-basis adapter: the full-frame producer closes
the max-rank chart input, leaving only the exceptional-rank local-image
producer. -/
theorem sourceOrientedGramVariety_local_connectedRelOpen_basis_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  exact
    sourceOrientedGramVariety_local_connectedRelOpen_basis_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hG0 hN0_open hG0N0

/-- Hard-range connected-component adapter using the full-frame max-rank
producer and the supplied exceptional-rank local-image producer. -/
theorem sourceOrientedGramVariety_connectedComponentIn_relOpen_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {G0 : SourceOrientedGramData d n}
    (hG0D : G0 ∈ D) :
    IsRelOpenInSourceOrientedGramVariety d n
      (connectedComponentIn D G0) := by
  exact
    sourceOrientedGramVariety_connectedComponentIn_relOpen_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hD_rel hG0D

/-- Hard-range compact-path tube adapter using the full-frame max-rank
producer and the supplied exceptional-rank local-image producer. -/
theorem sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {γ : unitInterval → SourceOrientedGramData d n}
    (hγ_cont : Continuous γ)
    (hγD : ∀ t, γ t ∈ D)
    {W0 : Set (SourceOrientedGramData d n)}
    (hW0_rel : IsRelOpenInSourceOrientedGramVariety d n W0)
    (hW0_conn : IsConnected W0)
    (hW0_nonempty : W0.Nonempty)
    (hW0D : W0 ⊆ D)
    (hstart : γ (0 : unitInterval) ∈ W0) :
    ∃ Wtube : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n Wtube ∧
      IsConnected Wtube ∧
      W0 ⊆ Wtube ∧
      Wtube ⊆ D ∧
      (∀ t, γ t ∈ Wtube) := by
  exact
    sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hD_rel hγ_cont hγD hW0_rel hW0_conn
      hW0_nonempty hW0D hstart

end BHW
