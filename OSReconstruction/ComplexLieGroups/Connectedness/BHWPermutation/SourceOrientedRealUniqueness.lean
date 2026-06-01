import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealMaxRank
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedBHWFiniteOverlap

/-!
# Oriented real uniqueness from finite real chart data

This file contains the generic SCV consumer for the oriented real-patch route.
Given a finite-coordinate max-rank chart whose real source slice is in standard
`SCV.realToComplex` form, agreement on a real source environment produces a
nonempty relatively open max-rank seed and then propagates across a connected
oriented source-variety domain by the checked max-rank identity principle.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A finite-coordinate local chart around a real source point, together with
real coordinates whose complexification agrees with the oriented source chart
on a real source neighborhood. -/
structure SourceOrientedLocalRealChartData
    (d n : ℕ)
    (x0 : Fin n → Fin (d + 1) → ℝ) where
  m : ℕ
  C :
    SourceOrientedMaxRankChartData d n
      (M := Fin m → ℂ)
      (sourceRealOrientedMinkowskiInvariant d n x0)
  E0 : Set (Fin n → Fin (d + 1) → ℝ)
  E0_open : IsOpen E0
  center_mem : x0 ∈ E0
  invariant_mem_chart :
    ∀ x ∈ E0, sourceRealOrientedMinkowskiInvariant d n x ∈ C.Ω
  realCoord : (Fin n → Fin (d + 1) → ℝ) → (Fin m → ℝ)
  realCoord_continuousOn : ContinuousOn realCoord E0
  realCoord_image_open :
    ∀ {S : Set (Fin n → Fin (d + 1) → ℝ)},
      IsOpen S → S ⊆ E0 → IsOpen (realCoord '' S)
  chart_real_eq :
    ∀ x ∈ E0,
      C.chart (sourceRealOrientedMinkowskiInvariant d n x) =
        SCV.realToComplex (realCoord x)

/-- A Hall-Wightman oriented real environment: a nonempty open Jost real patch
with finite-coordinate local real chart data at every point. -/
structure IsHWOrientedRealEnvironment
    (d n : ℕ)
    (E : Set (Fin n → Fin (d + 1) → ℝ)) : Prop where
  nonempty : E.Nonempty
  open_real : IsOpen E
  realized_by_jost : E ⊆ JostSet d n
  local_real_chart :
    ∀ x ∈ E, Nonempty (SourceOrientedLocalRealChartData d n x)

/-- Package a source-open Jost real patch with local real chart data at every
point as a Hall-Wightman oriented real environment. -/
theorem sourceOrientedRealEnvironment_of_localRealCharts
    (d n : ℕ)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E)
    (hE_nonempty : E.Nonempty)
    (hE_jost : E ⊆ JostSet d n)
    (hCharts :
      ∀ x ∈ E, Nonempty (SourceOrientedLocalRealChartData d n x)) :
    IsHWOrientedRealEnvironment d n E where
  nonempty := hE_nonempty
  open_real := hE_open
  realized_by_jost := hE_jost
  local_real_chart := hCharts

/-- A fixed determinant-nonzero real patch is an oriented real environment once
the pointwise full-frame local real chart producer is available. -/
theorem sourceOrientedRealEnvironment_of_fullFrameDetNonzero_localCharts
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E)
    (hE_nonempty : E.Nonempty)
    (hE_jost : E ⊆ JostSet d n)
    (hdet :
      ∀ x ∈ E, sourceRealFullFrameDet d n ι x ≠ 0)
    (hLocal :
      ∀ {x : Fin n → Fin (d + 1) → ℝ},
        sourceRealFullFrameDet d n ι x ≠ 0 →
          Nonempty (SourceOrientedLocalRealChartData d n x)) :
    IsHWOrientedRealEnvironment d n E :=
  sourceOrientedRealEnvironment_of_localRealCharts d n
    hE_open hE_nonempty hE_jost
    (fun x hx => hLocal (hdet x hx))

/-- In the hard range, a checked OS45 real patch has a determinant-regular
permuted subpatch which becomes an oriented real environment as soon as the
pointwise full-frame local real chart producer is available. -/
theorem os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_localCharts
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (hn : d + 1 ≤ n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (E0 : Set (Fin n → Fin (d + 1) → ℝ))
    (hE0 : IsOS45Figure24CheckedRealPatch (d := d) n π i hi E0)
    (hLocal :
      ∀ (ι : Fin (d + 1) ↪ Fin n)
        {y : Fin n → Fin (d + 1) → ℝ},
        sourceRealFullFrameDet d n ι y ≠ 0 →
          Nonempty (SourceOrientedLocalRealChartData d n y)) :
    ∃ E : Set (Fin n → Fin (d + 1) → ℝ),
      E ⊆ E0 ∧
      IsOpen E ∧
      E.Nonempty ∧
      IsHWOrientedRealEnvironment d n
        {y | ∃ x ∈ E, y = fun k => x (π k)} := by
  rcases os45Figure24_checkedRealPatch_fullFrameGramEnvironmentSubpatch
      (d := d) hd n hn π i hi E0 hE0 with
    ⟨ι, E, _O, hE_sub, hE_open, hE_ne, hEperm_open, hEperm_ne,
      hdet, hEperm_jost, _hO_sub, _hO_env⟩
  refine ⟨E, hE_sub, hE_open, hE_ne, ?_⟩
  exact
    sourceOrientedRealEnvironment_of_fullFrameDetNonzero_localCharts
      d n ι hEperm_open hEperm_ne hEperm_jost hdet
      (fun {y} hy => hLocal ι hy)

namespace SourceOrientedLocalRealChartData

/-- Shrink a local real chart simultaneously inside a relatively open oriented
domain and inside a real source patch. -/
theorem shrink_to_domain_and_realPatch
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (R : SourceOrientedLocalRealChartData d n x0)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    {U : Set (SourceOrientedGramData d n)}
    (hE_open : IsOpen E)
    (hx0E : x0 ∈ E)
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hx0U : sourceRealOrientedMinkowskiInvariant d n x0 ∈ U) :
    ∃ (Ω : Set (SourceOrientedGramData d n))
      (Eseed : Set (Fin n → Fin (d + 1) → ℝ)),
      sourceRealOrientedMinkowskiInvariant d n x0 ∈ Ω ∧
      IsRelOpenInSourceOrientedGramVariety d n Ω ∧
      Ω ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Ω ⊆ R.C.Ω ∧
      IsOpen (R.C.chart '' Ω) ∧
      IsConnected (R.C.chart '' Ω) ∧
      IsOpen Eseed ∧
      x0 ∈ Eseed ∧
      Eseed ⊆ E ∧
      Eseed ⊆ R.E0 ∧
      (∀ x ∈ Eseed, sourceRealOrientedMinkowskiInvariant d n x ∈ Ω) := by
  obtain ⟨Ω, hcenter, hΩ_rel, hΩ_sub_Umax, hΩ_sub_C,
      hΩ_chart_open, hΩ_chart_conn⟩ :=
    R.C.shrink_to_relOpen hU_rel hx0U
  have hrealToComplex_cont :
      Continuous (fun q : Fin R.m → ℝ => SCV.realToComplex q) := by
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp (continuous_apply i)
  have hcoord_complex_contOn :
      ContinuousOn
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          SCV.realToComplex (R.realCoord x)) R.E0 :=
    hrealToComplex_cont.comp_continuousOn R.realCoord_continuousOn
  obtain ⟨Vcoord, hVcoord_open, hVcoord_eq⟩ :=
    (continuousOn_iff'.mp hcoord_complex_contOn)
      (R.C.chart '' Ω) hΩ_chart_open
  let Eseed : Set (Fin n → Fin (d + 1) → ℝ) :=
    E ∩ R.E0 ∩ Vcoord
  have hEseed_open : IsOpen Eseed :=
    (hE_open.inter R.E0_open).inter hVcoord_open
  have hx0Eseed : x0 ∈ Eseed := by
    refine ⟨⟨hx0E, R.center_mem⟩, ?_⟩
    have hxpre :
        x0 ∈
          {x : Fin n → Fin (d + 1) → ℝ |
            SCV.realToComplex (R.realCoord x) ∈ R.C.chart '' Ω} ∩
            R.E0 := by
      exact ⟨⟨sourceRealOrientedMinkowskiInvariant d n x0,
        hcenter, R.chart_real_eq x0 R.center_mem⟩, R.center_mem⟩
    have hxV : x0 ∈ Vcoord ∩ R.E0 := by
      rw [← hVcoord_eq]
      exact hxpre
    exact hxV.1
  have hEseed_sub_E : Eseed ⊆ E := by
    intro x hx
    exact hx.1.1
  have hEseed_sub_R : Eseed ⊆ R.E0 := by
    intro x hx
    exact hx.1.2
  have hEseed_maps :
      ∀ x ∈ Eseed, sourceRealOrientedMinkowskiInvariant d n x ∈ Ω := by
    intro x hx
    let G := sourceRealOrientedMinkowskiInvariant d n x
    have hxR : x ∈ R.E0 := hEseed_sub_R hx
    have hGΩbig : G ∈ R.C.Ω := R.invariant_mem_chart x hxR
    have hxpre :
        x ∈
          {x : Fin n → Fin (d + 1) → ℝ |
            SCV.realToComplex (R.realCoord x) ∈ R.C.chart '' Ω} ∩
            R.E0 := by
      have hxV : x ∈ Vcoord ∩ R.E0 := ⟨hx.2, hxR⟩
      change x ∈
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          SCV.realToComplex (R.realCoord x)) ⁻¹' (R.C.chart '' Ω) ∩ R.E0
      rw [hVcoord_eq]
      exact hxV
    have hchart_mem : R.C.chart G ∈ R.C.chart '' Ω := by
      simpa [G, R.chart_real_eq x hxR] using hxpre.1
    have hinvΩ :
        R.C.chart_biholomorphic.inv (R.C.chart G) ∈ Ω :=
      LocalBiholomorphOnSourceOrientedVariety.inv_mem_restrict
        (d := d) (n := n) R.C.chart_biholomorphic hΩ_sub_C
        (R.C.chart G) hchart_mem
    simpa [R.C.chart_biholomorphic.left_inv_on G hGΩbig] using hinvΩ
  exact
    ⟨Ω, Eseed, hcenter, hΩ_rel, hΩ_sub_Umax, hΩ_sub_C,
      hΩ_chart_open, hΩ_chart_conn, hEseed_open, hx0Eseed,
      hEseed_sub_E, hEseed_sub_R, hEseed_maps⟩

end SourceOrientedLocalRealChartData

/-- A Hall-Wightman oriented real environment supplies a nonempty relatively
open max-rank seed on which a germ-holomorphic scalar vanishes, provided it
vanishes on the real environment. -/
theorem sourceOrientedLocalTotallyReal_zero_seed
    (d n : ℕ)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE : IsHWOrientedRealEnvironment d n E)
    {U : Set (SourceOrientedGramData d n)}
    {H : SourceOrientedGramData d n → ℂ}
    (hU_rel : IsRelOpenInSourceOrientedGramVariety d n U)
    (hE_U :
      ∀ x ∈ E, sourceRealOrientedMinkowskiInvariant d n x ∈ U)
    (hH : SourceOrientedVarietyGermHolomorphicOn d n H U)
    (h_zero :
      ∀ x ∈ E, H (sourceRealOrientedMinkowskiInvariant d n x) = 0) :
    ∃ W : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n W ∧
      W.Nonempty ∧
      W ⊆ U ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn H 0 W := by
  obtain ⟨x0, hx0E⟩ := hE.nonempty
  let R : SourceOrientedLocalRealChartData d n x0 :=
    Classical.choice (hE.local_real_chart x0 hx0E)
  obtain ⟨Ω, Eseed, hcenter, hΩ_rel, hΩ_sub_Umax, hΩ_sub_C,
      hΩ_chart_open, hΩ_chart_conn, hEseed_open, hx0Eseed,
      hEseed_sub_E, hEseed_sub_R, hEseed_maps⟩ :=
    R.shrink_to_domain_and_realPatch
      (d := d) (n := n) hE.open_real hx0E hU_rel (hE_U x0 hx0E)
  obtain ⟨φc, hφc_holo, hφc_eq⟩ :=
    SourceOrientedVarietyGermHolomorphicOn.to_maxRank_chart
      (d := d) (n := n) hH R.C hΩ_rel
      (by intro G hG; exact (hΩ_sub_Umax hG).1) hΩ_sub_C
  let Vre : Set (Fin R.m → ℝ) := R.realCoord '' Eseed
  have hVre_open : IsOpen Vre :=
    R.realCoord_image_open hEseed_open hEseed_sub_R
  have hVre_ne : Vre.Nonempty :=
    ⟨R.realCoord x0, x0, hx0Eseed, rfl⟩
  have hVre_sub :
      ∀ q ∈ Vre, SCV.realToComplex q ∈ R.C.chart '' Ω := by
    rintro q ⟨x, hxSeed, rfl⟩
    have hxR : x ∈ R.E0 := hEseed_sub_R hxSeed
    exact
      ⟨sourceRealOrientedMinkowskiInvariant d n x,
        hEseed_maps x hxSeed, R.chart_real_eq x hxR⟩
  have hVre_zero :
      ∀ q ∈ Vre, φc (SCV.realToComplex q) = 0 := by
    rintro q ⟨x, hxSeed, rfl⟩
    have hxR : x ∈ R.E0 := hEseed_sub_R hxSeed
    have hxΩ :
        sourceRealOrientedMinkowskiInvariant d n x ∈ Ω :=
      hEseed_maps x hxSeed
    calc
      φc (SCV.realToComplex (R.realCoord x)) =
          φc (R.C.chart (sourceRealOrientedMinkowskiInvariant d n x)) := by
            rw [← R.chart_real_eq x hxR]
      _ = H (sourceRealOrientedMinkowskiInvariant d n x) :=
            hφc_eq (sourceRealOrientedMinkowskiInvariant d n x) hxΩ
      _ = 0 := h_zero x (hEseed_sub_E hxSeed)
  have hcoord_zero :
      ∀ z ∈ R.C.chart '' Ω, φc z = 0 :=
    SCV.identity_theorem_totally_real
      hΩ_chart_open hΩ_chart_conn hφc_holo
      hVre_open hVre_ne hVre_sub hVre_zero
  refine
    ⟨Ω, hΩ_rel, ⟨sourceRealOrientedMinkowskiInvariant d n x0, hcenter⟩,
      hΩ_sub_Umax, ?_⟩
  intro G hGΩ
  have hφ := hφc_eq G hGΩ
  have hz : φc (R.C.chart G) = 0 :=
    hcoord_zero (R.C.chart G) ⟨G, hGΩ, rfl⟩
  simpa [hφ] using hz

/-- Hard-range oriented distributional uniqueness from a Hall-Wightman
oriented real environment. -/
theorem sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment
    {d n : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE : IsHWOrientedRealEnvironment d n E) :
    sourceOrientedDistributionalUniquenessPatch d n E := by
  refine ⟨hE.nonempty, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hE_U hΦ hΨ hEq_real
  let H : SourceOrientedGramData d n → ℂ := fun G => Φ G - Ψ G
  have hH : SourceOrientedVarietyGermHolomorphicOn d n H U :=
    SourceOrientedVarietyGermHolomorphicOn.sub (d := d) (n := n) hΦ hΨ
  have hzero_real :
      ∀ x ∈ E, H (sourceRealOrientedMinkowskiInvariant d n x) = 0 := by
    intro x hx
    exact sub_eq_zero.mpr (hEq_real x hx)
  obtain ⟨W, hW_rel, hW_ne, hW_sub_Umax, hW_zero⟩ :=
    sourceOrientedLocalTotallyReal_zero_seed
      (d := d) (n := n) hE hU_rel hE_U hH hzero_real
  have hUmax_conn :
      IsConnected (U ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT
      (d := d) (n := n) hd hn hU_rel hU_conn
  have hW_eq : Set.EqOn Φ Ψ W := by
    intro G hGW
    exact sub_eq_zero.mp (hW_zero hGW)
  exact
    sourceOrientedGramVariety_eqOn_of_connected_maxRank_fullFrame
      (d := d) (n := n) hn hU_rel hUmax_conn hW_rel hW_ne
      (by intro G hGW; exact (hW_sub_Umax hGW).1)
      hΦ hΨ hW_eq

end BHW
