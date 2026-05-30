import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJostLocal

/-!
# OS45 Pair-Data Producers

This file contains the small carrier assembly step between the local
`S'_n` BHW/Jost branch and the compact Figure-2-4 Wick-pairing packets used in
the theorem-2 locality route.
-/

noncomputable section

open Complex Topology MeasureTheory Filter Matrix LorentzLieGroup

namespace BHW

variable {d : ℕ} [NeZero d]

/-- Zero-height common-edge EOW pairings produce the OS45 source-patch
BHW/Jost pair carrier.

This is the checked Stage C -> Stage D bridge in the OS I §4.5 route: the
flat common-edge pairing equality supplies the local EOW seed, the authorized
local `S'_n` BHW theorem supplies a single branch on the selected hull, and
the stored trace fields turn that branch into the pair carrier used by the
compact Wick-pairing constructors. -/
noncomputable def os45_BHWJostPairData_of_zeroHeight_pairingsCLM
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V := by
  let H : BHW.OS45BHWJostHullData (d := d) hd n i hi P :=
    BHW.os45_BHWJostHullData_of_figure24 (d := d) hd i hi P
  let zseed : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P
  have hzseed :
      zseed ∈ H.ΩJ ∩ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [zseed] using H.commonEdgeSPrimeSeed_mem_ΩJ
    · simpa [zseed] using
        BHW.os45Figure24CommonEdgeSPrimeSeed_mem_extendedTube
          (d := d) hd
    · simpa [zseed] using
        BHW.os45Figure24CommonEdgeSPrimeSeed_mem_permutedExtendedTubeSector
          (d := d) hd
  have hseed :=
    BHW.os45_BHWJost_localSPrimeEOWSeedAt_commonEdge_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc H T hzero_plus hzero_minus
  let S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H :=
    BHW.os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt
      (d := d) hd OS lgc H zseed hzseed hseed
  exact S.toPairData

/-- Zero-height common-edge EOW pairings produce the OS45 source-patch
BHW/Jost pair carrier, using only connectedness of the true two-sector overlap.

This is the axiom-free replacement surface for
`os45_BHWJostPairData_of_zeroHeight_pairingsCLM`: the local EOW seed is first
propagated across `T'_n ∩ τT'_n` by the product identity theorem, then the two
initial-sector branches are glued explicitly on the stored local hull. -/
noncomputable def os45_BHWJostPairData_of_zeroHeight_pairingsCLM_overlapConnected
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap_connected :
      IsConnected
        (BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ))
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi P.V := by
  let H : BHW.OS45BHWJostHullData (d := d) hd n i hi P :=
    BHW.os45_BHWJostHullData_of_figure24 (d := d) hd i hi P
  let zseed : Fin n → Fin (d + 1) → ℂ :=
    BHW.os45Figure24CommonEdgeSPrimeSeed d n P
  have hseed :=
    BHW.os45_BHWJost_localSPrimeEOWSeedAt_commonEdge_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc H T hzero_plus hzero_minus
  let S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H :=
    BHW.OS45BHWJostSPrimeBranchData.of_localEOWSeedAt_overlapConnected
      (d := d) OS lgc (P := P) (H := H)
      zseed hOverlap_connected hseed
  exact S.toPairData

/-- Local `S'_n` branch data whose real patch contains the canonical
Figure-2-4 source patch produces the compact Wick-pairing packet. -/
noncomputable def os45CompactFigure24WickPairingEq_of_sPrimeBranchData
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {H : BHW.OS45BHWJostHullData (d := d) hd n i hi P}
    (S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H)
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ P.V) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical
    (d := d) hd OS lgc n i hi S.toPairData hsource_subset

/-- A BHW/Jost pair carrier is already the direct adjacent EOW difference
envelope on its real source patch.

This is the checked local handoff from the book's two boundary restrictions to
the Lean consumer: the envelope function is `Btau - Bord`, with the Wick and
real trace identities inherited from the pair carrier. -/
noncomputable def adjacentOSEOWDifferenceEnvelope_of_pairData
    (hd : 2 ≤ d)
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (P : BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V) :
    BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n P.τ V := by
  exact
    { U := P.U
      U_open := P.U_open
      U_connected := P.U_connected
      H := P.difference
      H_holo := P.difference_holo
      wick_mem := P.wick_mem
      real_mem := P.real_mem
      wick_diff := by
        intro x hx
        exact P.difference_wick_trace hx
      real_diff := by
        intro x hx
        exact P.difference_real_trace hx }

/-- A local `S'_n` branch supplies the adjacent EOW difference envelope on the
canonical OS45 real patch.

This names the remaining mathematical blocker sharply: construct the local
`S'_n` branch from the OS/Jost/Ruelle edge-of-the-wedge step at the spacelike
point.  Once `S` exists, no further distributional or support wrapper is
needed to obtain the local envelope. -/
noncomputable def adjacentOSEOWDifferenceEnvelope_of_sPrimeBranchData
    (hd : 2 ≤ d)
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {H : BHW.OS45BHWJostHullData (d := d) hd n i hi P}
    (S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H) :
    BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n P.τ P.V :=
  BHW.adjacentOSEOWDifferenceEnvelope_of_pairData
    (d := d) hd S.toPairData

/-- The canonical source-patch version of
`os45_BHWJostPairData_of_zeroHeight_pairingsCLM`. -/
noncomputable def os45_BHWJostPairData_on_figure24SourcePatch_of_zeroHeight_pairingsCLM
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n
            (BHW.os45_adjacent_identity_canonicalSourcePatch
              (d := d) hd i hi)
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n
            (BHW.os45_adjacent_identity_canonicalSourcePatch
              (d := d) hd i hi)
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            ((BHW.os45_adjacent_identity_canonicalSourcePatch
                (d := d) hd i hi).τ.symm *
              (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi
      (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi) := by
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) (n := n) hd i hi
  have hPsource :
      BHW.os45Figure24SourcePatch (d := d) n i hi = P.V := by
    simpa [P] using
      BHW.os45Figure24SourcePatch_eq_canonical (d := d) hd n i hi
  simpa [hPsource, P] using
    BHW.os45_BHWJostPairData_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P) T hzero_plus hzero_minus

/-- Zero-height common-edge EOW pairings produce the compact Figure-2-4
Wick-pairing packet. -/
noncomputable def os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n
            (BHW.os45_adjacent_identity_canonicalSourcePatch
              (d := d) hd i hi)
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n
            (BHW.os45_adjacent_identity_canonicalSourcePatch
              (d := d) hd i hi)
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            ((BHW.os45_adjacent_identity_canonicalSourcePatch
                (d := d) hd i hi).τ.symm *
              (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch
    (d := d) hd OS lgc n i hi
    (BHW.os45_BHWJostPairData_on_figure24SourcePatch_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc n i hi T hzero_plus hzero_minus)

/-- Zero-height common-edge EOW pairings produce the compact Figure-2-4
Wick-pairing packet through the axiom-free connected-overlap local-hull
constructor.

Compared with `os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM`,
this version makes the genuine geometric input explicit and does not route
through `localSPrime_twoSectorBranch_of_EOW_BHW`. -/
noncomputable def os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM_overlapConnected
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hsource_subset :
      BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ⊆ P.V)
    (hOverlap_connected :
      IsConnected
        (BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ))
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ) :
    BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
  BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical
    (d := d) hd OS lgc n i hi
    (BHW.os45_BHWJostPairData_of_zeroHeight_pairingsCLM_overlapConnected
      (d := d) hd OS lgc (P := P) hOverlap_connected T
      hzero_plus hzero_minus)
    hsource_subset

end BHW
