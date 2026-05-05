import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexZeroSection

/-!
# Local selected source Gram chart assembly

This file contains the final local shrink/assembly lemmas built on the checked
selected zero-section packet.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- The complex and real base selected flat coordinates agree under the real
slice. -/
theorem sourceSelectedComplexGramBaseCoord_real_slice
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    SCV.realToComplex
        ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI)
          (sourceSelectedRealGramMap d n (min n (d + 1)) I x0)) =
      (sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I
          (realEmbed x0)) := by
  let m := min n (d + 1)
  rw [← sourceSelectedComplexSymCoordFinEquiv_real_slice n m hI
    (sourceSelectedRealGramMap d n m I x0)]
  congr 1
  ext i a
  simp [sourceSelectedSymCoordRealComplexify_apply,
    sourceSelectedRealGramMap_apply,
    sourceSelectedComplexGramMap_apply,
    sourceRealGramComplexify,
    sourceMinkowskiGram_realEmbed]

/-- Real-side coordinate-ball shrink compatible with a prescribed complex flat
coordinate neighborhood.  The real zero-section stays in the canonical real
chart target and in the nonzero selected-minor patch. -/
theorem exists_sourceSelectedRealGramZeroSection_good_ball
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_open : IsOpen D)
    (hq0D :
      SCV.realToComplex
        ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI)
          (sourceSelectedRealGramMap d n (min n (d + 1)) I x0)) ∈ D) :
    ∃ Vre : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ),
      IsOpen Vre ∧ Vre.Nonempty ∧
      ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedRealGramMap d n (min n (d + 1)) I x0)) ∈ Vre ∧
      (∀ q ∈ Vre, SCV.realToComplex q ∈ D) ∧
      (∀ q ∈ Vre,
        sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedRealGramImplicitChart d n hI hJ hminor).target) ∧
      (∀ q ∈ Vre,
        sourceRegularMinor d n I J
          ((sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q)) ≠ 0) ∧
      (∀ q ∈ Vre,
        SourceGramRegularAt d n
          ((sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q))) := by
  let m := min n (d + 1)
  let eR := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  let q0 :=
    (sourceSelectedRealSymCoordFinEquiv n m hI)
      (sourceSelectedRealGramMap d n m I x0)
  let y0 := sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q0
  have hx0e : x0 ∈ eR.source :=
    sourceSelectedRealGramImplicitChart_mem_source d n hI hJ hminor
  have hy0_eq : y0 = eR x0 := by
    rw [sourceSelectedRealGramImplicitChart_self]
    simp [q0, y0, m]
  have hy0_target : y0 ∈ eR.target := by
    rw [hy0_eq]
    exact eR.map_source hx0e
  have hrealToComplex_cont :
      Continuous
        (SCV.realToComplex :
          (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℝ) →
            Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) := by
    exact continuous_pi fun k =>
      Complex.continuous_ofReal.comp (continuous_apply k)
  have hD_nhds : {q | SCV.realToComplex q ∈ D} ∈ 𝓝 q0 := by
    exact hrealToComplex_cont.continuousAt.preimage_mem_nhds
      (hD_open.mem_nhds hq0D)
  have hzero_target_nhds :
      {q |
        sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          eR.target} ∈ 𝓝 q0 := by
    exact
      (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI).continuous
        |>.continuousAt
        |>.preimage_mem_nhds (eR.open_target.mem_nhds hy0_target)
  have hsection_cont :
      ContinuousAt
        (fun q =>
          eR.symm (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q))
        q0 := by
    have hsymm0 :
        ContinuousAt eR.symm
          (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q0) := by
      simpa [y0] using eR.continuousAt_symm hy0_target
    exact hsymm0.comp
      (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI).continuous.continuousAt
  let Rminor : Set (Fin n → Fin (d + 1) → ℝ) :=
    {x | sourceRegularMinor d n I J x ≠ 0}
  have hRminor_open : IsOpen Rminor := by
    exact isOpen_ne_fun (continuous_sourceRegularMinor d n I J) continuous_const
  have hbase_minor : eR.symm y0 ∈ Rminor := by
    rw [hy0_eq]
    rw [eR.left_inv hx0e]
    exact hminor
  have hminor_nhds :
      {q |
        eR.symm (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q) ∈
          Rminor} ∈ 𝓝 q0 := by
    exact hsection_cont.preimage_mem_nhds (hRminor_open.mem_nhds hbase_minor)
  have hgood_nhds :
      ({q | SCV.realToComplex q ∈ D} ∩
        {q |
          sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
            eR.target} ∩
        {q |
          eR.symm
              (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q) ∈
            Rminor}) ∈ 𝓝 q0 :=
    inter_mem (inter_mem hD_nhds hzero_target_nhds) hminor_nhds
  rcases Metric.mem_nhds_iff.mp hgood_nhds with ⟨ε, hεpos, hεsub⟩
  let Vre : Set
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℝ) :=
    Metric.ball q0 ε
  refine ⟨Vre, Metric.isOpen_ball, ⟨q0, Metric.mem_ball_self hεpos⟩,
    Metric.mem_ball_self hεpos, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (hεsub hq).1.1
  · intro q hq
    exact (hεsub hq).1.2
  · intro q hq
    exact (hεsub hq).2
  · intro q hq
    exact sourceGramRegularAt_of_exists_nonzero_minor d n
      ⟨I, hI, J, hJ, (hεsub hq).2⟩

/-- Local selected-coordinate chart on the complex source Gram variety at a
regular real source point, with a compatible real slice. -/
theorem sourceComplexGramVariety_selectedChart_of_realRegular
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hx0V : realEmbed x0 ∈ V) :
    ∃ (N : ℕ)
      (D : Set (Fin N → ℂ))
      (Vre : Set (Fin N → ℝ))
      (Γ : (Fin N → ℂ) → (Fin n → Fin n → ℂ))
      (γre : (Fin N → ℝ) → (Fin n → Fin (d + 1) → ℝ)),
      IsOpen D ∧ IsConnected D ∧
      IsOpen Vre ∧ Vre.Nonempty ∧
      (∀ q ∈ Vre, SCV.realToComplex q ∈ D) ∧
      Γ '' D ⊆ sourceComplexGramVariety d n ∧
      Γ '' D ⊆ sourceMinkowskiGram d n '' V ∧
      IsRelOpenInSourceComplexGramVariety d n (Γ '' D) ∧
      sourceRealGramComplexify n (sourceRealMinkowskiGram d n x0) ∈ Γ '' D ∧
      (∀ z ∈ D, ∃ w ∈ V, Γ z = sourceMinkowskiGram d n w) ∧
      ContinuousOn γre Vre ∧
      (∃ q0 ∈ Vre, γre q0 = x0 ∧
        Γ (SCV.realToComplex q0) =
          sourceRealGramComplexify n (sourceRealMinkowskiGram d n x0)) ∧
      (∀ q ∈ Vre,
        SourceGramRegularAt d n (γre q) ∧
        sourceRealMinkowskiGram d n (γre q) ∈
          sourceRealGramVariety d n ∧
        Γ (SCV.realToComplex q) =
          sourceRealGramComplexify n
            (sourceRealMinkowskiGram d n (γre q))) ∧
      DifferentiableOn ℂ Γ D := by
  rcases exists_nonzero_minor_of_sourceGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  let m := min n (d + 1)
  let N := Fintype.card (sourceSelectedSymCoordKey n m I)
  let eC := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let eR := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  let Γ : (Fin N → ℂ) → (Fin n → Fin n → ℂ) :=
    fun q =>
      sourceMinkowskiGram d n
        (eC.symm (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
  let γre : (Fin N → ℝ) → (Fin n → Fin (d + 1) → ℝ) :=
    fun q =>
      eR.symm (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q)
  let q0C : Fin N → ℂ :=
    (sourceSelectedComplexSymCoordFinEquiv n m hI)
      (sourceSelectedComplexGramMap d n m I (realEmbed x0))
  let q0R : Fin N → ℝ :=
    (sourceSelectedRealSymCoordFinEquiv n m hI)
      (sourceSelectedRealGramMap d n m I x0)
  rcases exists_sourceSelectedComplexGramZeroSection_good_ball
      d n hI hJ hminor hV_open hx0V with
    ⟨D, hD_open, hD_conn, hq0CD, hD_target, hD_sourceV, hD_minor, hD_inv⟩
  have hq0RD : SCV.realToComplex q0R ∈ D := by
    rw [sourceSelectedComplexGramBaseCoord_real_slice d n hI]
    exact hq0CD
  rcases exists_sourceSelectedRealGramZeroSection_good_ball
      d n hI hJ hminor hD_open hq0RD with
    ⟨Vre, hVre_open, hVre_nonempty, hq0RVre, hVreD, hVre_target,
      hVre_minor, hVre_regular⟩
  have hbaseCsrc :
      eC.symm (sourceSelectedComplexGramMap d n m I (realEmbed x0), 0) =
        realEmbed x0 := by
    have hx0eC : realEmbed x0 ∈ eC.source :=
      sourceSelectedComplexGramImplicitChart_mem_source d n hI hJ hminor
    rw [← sourceSelectedComplexGramImplicitChart_self d n hI hJ hminor]
    exact eC.left_inv hx0eC
  have hbaseRsrc :
      eR.symm (sourceSelectedRealGramMap d n m I x0, 0) = x0 := by
    have hx0eR : x0 ∈ eR.source :=
      sourceSelectedRealGramImplicitChart_mem_source d n hI hJ hminor
    rw [← sourceSelectedRealGramImplicitChart_self d n hI hJ hminor]
    exact eR.left_inv hx0eR
  refine ⟨N, D, Vre, Γ, γre, hD_open, hD_conn, hVre_open, hVre_nonempty,
    hVreD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro G ⟨q, hqD, rfl⟩
    exact ⟨eC.symm
      (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q), rfl⟩
  · rintro G ⟨q, hqD, rfl⟩
    exact ⟨eC.symm
      (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q),
      hD_sourceV q hqD, rfl⟩
  · simpa [Γ, eC, m, N] using
      sourceSelectedComplexGramZeroSection_image_relOpen
        d n hI hJ hminor hD_open hD_target hD_minor
  · refine ⟨q0C, hq0CD, ?_⟩
    simp [Γ, q0C, eC, m, N]
    rw [hbaseCsrc]
    exact sourceMinkowskiGram_realEmbed d n x0
  · intro z hzD
    exact ⟨eC.symm
      (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI z),
      hD_sourceV z hzD, rfl⟩
  · simpa [γre, eR, m, N] using
      sourceSelectedRealGramZeroSection_continuousOn
        d n hI hJ hminor hVre_target
  · refine ⟨q0R, hq0RVre, ?_, ?_⟩
    · simp [γre, q0R, eR, m, N]
      exact hbaseRsrc
    · have hslice :
          SCV.realToComplex q0R = q0C :=
        sourceSelectedComplexGramBaseCoord_real_slice d n hI
      rw [hslice]
      simp [Γ, q0C, eC, m, N]
      rw [hbaseCsrc]
      exact sourceMinkowskiGram_realEmbed d n x0
  · intro q hqVre
    refine ⟨hVre_regular q hqVre, ?_, ?_⟩
    · exact ⟨γre q, rfl⟩
    · simpa [Γ, γre, eC, eR, m, N] using
        sourceSelectedComplexGramZeroSection_real_slice_gram
          d n hI hJ hminor q (hD_target (SCV.realToComplex q) (hVreD q hqVre))
          (hVre_target q hqVre) (hVre_minor q hqVre)
  · simpa [Γ, eC, m, N] using
      sourceSelectedComplexGramZeroSection_gram_differentiableOn
        d n hI hJ hminor hD_target hD_inv

/-- Pull back a variety-holomorphic scalar function along a differentiable
chart whose image lies in the variety domain. -/
theorem SourceVarietyHolomorphicOn.comp_differentiableOn_chart
    (d n N : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    {D : Set (Fin N → ℂ)}
    {Γ : (Fin N → ℂ) → (Fin n → Fin n → ℂ)}
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hΓU : Γ '' D ⊆ U)
    (hΓdiff : DifferentiableOn ℂ Γ D) :
    DifferentiableOn ℂ (fun z => H (Γ z)) D := by
  intro z hzD
  have hΓzU : Γ z ∈ U := hΓU ⟨z, hzD, rfl⟩
  rcases hH (Γ z) hΓzU with
    ⟨U0, hU0_open, hΓzU0, hHdiffU0, _hU0sub⟩
  have hHat : DifferentiableAt ℂ H (Γ z) :=
    (hHdiffU0 (Γ z) hΓzU0).differentiableAt
      (hU0_open.mem_nhds hΓzU0)
  simpa [Function.comp_def] using
    DifferentiableAt.comp_differentiableWithinAt
      (f := Γ) (g := H) (x := z) hHat (hΓdiff z hzD)

/-- A local totally-real zero theorem on the source complex Gram variety:
vanishing on a Hall-Wightman real environment gives a nonempty relatively open
complex-variety neighborhood on which the same variety-holomorphic scalar
representative vanishes. -/
theorem sourceVariety_localChart_totallyReal_zero
    (d n : ℕ)
    {O : Set (Fin n → Fin n → ℝ)}
    (hO : IsHWRealEnvironment d n O)
    {U : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hO_sub : ∀ G ∈ O, sourceRealGramComplexify n G ∈ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (h_zero : ∀ G ∈ O, H (sourceRealGramComplexify n G) = 0) :
    ∃ W : Set (Fin n → Fin n → ℂ),
      IsRelOpenInSourceComplexGramVariety d n W ∧
      W.Nonempty ∧ W ⊆ U ∧ Set.EqOn H 0 W := by
  rcases hO.nonempty with ⟨G0, hG0O⟩
  rcases hO.realized_by_jost G0 hG0O with
    ⟨x0, _hx0Jost, hx0reg, hx0Gram⟩
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  rcases hO.relOpen with ⟨O0, hO0_open, hO_eq⟩
  have hG0U : sourceRealGramComplexify n G0 ∈ U := hO_sub G0 hG0O
  have hG0U0 : sourceRealGramComplexify n G0 ∈ U0 := by
    rw [hU_eq] at hG0U
    exact hG0U.1
  have hG0O0 : G0 ∈ O0 := by
    rw [hO_eq] at hG0O
    exact hG0O.1
  let V : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | sourceMinkowskiGram d n z ∈ U0}
  have hV_open : IsOpen V := by
    exact hU0_open.preimage (contDiff_sourceMinkowskiGram d n).continuous
  have hx0V : realEmbed x0 ∈ V := by
    dsimp [V]
    rw [sourceMinkowskiGram_realEmbed, hx0Gram]
    exact hG0U0
  rcases sourceComplexGramVariety_selectedChart_of_realRegular
      d n hx0reg hV_open hx0V with
    ⟨N, D, Vre, Γ, γre, hD_open, hD_conn, hVre_open, hVre_nonempty,
      hVreD, hΓvar, hΓsource, hΓrel, hbaseΓ, _hΓrealizer, hγcont,
      hbase, hreal, hΓdiff⟩
  have hΓU : Γ '' D ⊆ U := by
    intro Z hZ
    have hZvar : Z ∈ sourceComplexGramVariety d n := hΓvar hZ
    rcases hΓsource hZ with ⟨w, hwV, hZw⟩
    rw [hU_eq]
    refine ⟨?_, hZvar⟩
    rw [← hZw]
    exact hwV
  let VreO : Set (Fin N → ℝ) :=
    Vre ∩ {q | sourceRealMinkowskiGram d n (γre q) ∈ O0}
  have hrealGram_cont : Continuous (sourceRealMinkowskiGram d n) :=
    (contDiff_sourceRealMinkowskiGram d n).continuous
  have hVreO_open : IsOpen VreO := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hγ_at : ContinuousAt γre q :=
      hγcont.continuousAt (hVre_open.mem_nhds hq.1)
    have hcomp_at :
        ContinuousAt (fun q => sourceRealMinkowskiGram d n (γre q)) q :=
      hrealGram_cont.continuousAt.comp hγ_at
    exact inter_mem (hVre_open.mem_nhds hq.1)
      (hcomp_at.preimage_mem_nhds (hO0_open.mem_nhds hq.2))
  have hVreO_nonempty : VreO.Nonempty := by
    rcases hbase with ⟨q0, hq0Vre, hγq0, _hΓq0⟩
    refine ⟨q0, hq0Vre, ?_⟩
    change sourceRealMinkowskiGram d n (γre q0) ∈ O0
    rw [hγq0, hx0Gram]
    exact hG0O0
  have hVreO_subD : ∀ q ∈ VreO, SCV.realToComplex q ∈ D := by
    intro q hq
    exact hVreD q hq.1
  have hcoord_diff :
      DifferentiableOn ℂ (fun z => H (Γ z)) D :=
    SourceVarietyHolomorphicOn.comp_differentiableOn_chart
      d n N hH hΓU hΓdiff
  have hcoord_zero :
      ∀ q ∈ VreO, H (Γ (SCV.realToComplex q)) = 0 := by
    intro q hq
    rcases hreal q hq.1 with ⟨_hregq, hGvar, hslice⟩
    let Gq := sourceRealMinkowskiGram d n (γre q)
    have hGqO : Gq ∈ O := by
      rw [hO_eq]
      exact ⟨hq.2, hGvar⟩
    have hz := h_zero Gq hGqO
    simpa [Gq, hslice] using hz
  have hident :
      ∀ z ∈ D, H (Γ z) = 0 :=
    SCV.identity_theorem_totally_real
      hD_open hD_conn hcoord_diff hVreO_open hVreO_nonempty
      hVreO_subD hcoord_zero
  refine ⟨Γ '' D, hΓrel, ?_, hΓU, ?_⟩
  · exact ⟨sourceRealGramComplexify n (sourceRealMinkowskiGram d n x0), hbaseΓ⟩
  · intro Z hZ
    rcases hZ with ⟨z, hzD, rfl⟩
    exact hident z hzD

end BHW
