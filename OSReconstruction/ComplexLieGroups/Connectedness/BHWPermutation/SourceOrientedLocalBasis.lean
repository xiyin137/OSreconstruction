import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedConnected
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientLocalImage

/-!
# Local connected basis assembly for the oriented source variety

This file assembles the local connected basis from two geometric producers:
finite-coordinate max-rank charts and rank-deficient local-image patches.  The
rank-deficient producer is still an explicit input; the theorem here only
performs the checked stratum dispatch and connected-component/tube assembly.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- A finite-coordinate max-rank chart producer plus a rank-deficient patch
producer gives the local connected relatively open basis of the oriented source
variety. -/
theorem sourceOrientedGramVariety_local_connectedRelOpen_basis_of_stratum_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
    (rankDeficientPatchAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G0 ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            IsConnected V ∧
            V ⊆ N0 ∩ sourceOrientedGramVariety d n)
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
  by_cases hmax : SourceOrientedMaxRankAt d n G0
  · rcases maxRankChartAt hG0 hmax with ⟨_m, C⟩
    rcases C.connectedPatch_inside_open hN0_open hG0N0 with ⟨P, hP_sub⟩
    exact ⟨P.V, P.center_mem, P.V_relOpen, P.V_connected, hP_sub⟩
  · have hex : SourceOrientedExceptionalRank d n G0 := ⟨hG0, hmax⟩
    exact rankDeficientPatchAt hG0 hex hN0_open hG0N0

/-- Connected components of relatively open oriented domains are relatively
open once the max-rank and rank-deficient local producers are supplied. -/
theorem sourceOrientedGramVariety_connectedComponentIn_relOpen_of_stratum_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
    (rankDeficientPatchAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G0 ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            IsConnected V ∧
            V ⊆ N0 ∩ sourceOrientedGramVariety d n)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {G0 : SourceOrientedGramData d n}
    (hG0D : G0 ∈ D) :
    IsRelOpenInSourceOrientedGramVariety d n (connectedComponentIn D G0) := by
  exact
    sourceOrientedGramVariety_connectedComponentIn_relOpen_of_local_connectedRelOpen_basis
      (d := d) (n := n)
      (localBasis := by
        intro G hG N hN_open hGN
        exact
          sourceOrientedGramVariety_local_connectedRelOpen_basis_of_stratum_producers
            (d := d) (n := n) maxRankChartAt rankDeficientPatchAt
            hG hN_open hGN)
      hD_rel hG0D

/-- A connected relatively open oriented-source tube follows a continuous path
once the max-rank and rank-deficient local producers are supplied. -/
theorem sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_stratum_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
    (rankDeficientPatchAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          ∃ V : Set (SourceOrientedGramData d n),
            G0 ∈ V ∧
            IsRelOpenInSourceOrientedGramVariety d n V ∧
            IsConnected V ∧
            V ⊆ N0 ∩ sourceOrientedGramVariety d n)
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
    sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_local_connectedRelOpen_basis
      (d := d) (n := n)
      (localBasis := by
        intro G hG N hN_open hGN
        exact
          sourceOrientedGramVariety_local_connectedRelOpen_basis_of_stratum_producers
            (d := d) (n := n) maxRankChartAt rankDeficientPatchAt
            hG hN_open hGN)
      hD_rel hγ_cont hγD hW0_rel hW0_conn hW0_nonempty hW0D hstart

/-- Final local-basis adapter: finite-coordinate max-rank charts and
rank-deficient local-image packets are the two producer inputs needed for the
oriented source-variety local connected basis. -/
theorem sourceOrientedGramVariety_local_connectedRelOpen_basis_of_chart_and_localImage_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
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
    sourceOrientedGramVariety_local_connectedRelOpen_basis_of_stratum_producers
      (d := d) (n := n) maxRankChartAt
      (fun {G} hG hex {N0} hOpen hMem =>
        sourceOrientedRankDeficientPatchAt_of_localImageProducer
          (d := d) (n := n) rankDeficientLocalImageAt
          (G0 := G) (N0 := N0) hG hex hOpen hMem)
      hG0 hN0_open hG0N0

/-- Connected components of relatively open oriented domains are relatively
open once the final max-rank chart and rank-deficient local-image producers are
supplied. -/
theorem sourceOrientedGramVariety_connectedComponentIn_relOpen_of_chart_and_localImage_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
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
    IsRelOpenInSourceOrientedGramVariety d n (connectedComponentIn D G0) := by
  exact
    sourceOrientedGramVariety_connectedComponentIn_relOpen_of_stratum_producers
      (d := d) (n := n) maxRankChartAt
      (fun {G} hG hex {N0} hOpen hMem =>
        sourceOrientedRankDeficientPatchAt_of_localImageProducer
          (d := d) (n := n) rankDeficientLocalImageAt
          (G0 := G) (N0 := N0) hG hex hOpen hMem)
      hD_rel hG0D

/-- A connected relatively open oriented-source tube follows a continuous path
once the final max-rank chart and rank-deficient local-image producers are
supplied. -/
theorem sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_chart_and_localImage_producers
    (maxRankChartAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedMaxRankAt d n G0 →
        Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0)
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
    sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_stratum_producers
      (d := d) (n := n) maxRankChartAt
      (fun {G} hG hex {N0} hOpen hMem =>
        sourceOrientedRankDeficientPatchAt_of_localImageProducer
          (d := d) (n := n) rankDeficientLocalImageAt
          (G0 := G) (N0 := N0) hG hex hOpen hMem)
      hD_rel hγ_cont hγD hW0_rel hW0_conn hW0_nonempty hW0D hstart

end BHW
