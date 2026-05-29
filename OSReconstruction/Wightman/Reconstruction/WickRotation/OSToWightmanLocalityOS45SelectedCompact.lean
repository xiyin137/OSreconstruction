import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45PairData

/-!
# Selected Jost Data To Compact OS45 Packets

This file contains the small checked carrier bridge from the Ruelle/Jost
selected-data surface to the compact Figure-2-4 Wick-pairing packet used by
the theorem-2 canonical-shell transport.
-/

noncomputable section

open Complex Topology MeasureTheory Filter Matrix LorentzLieGroup

namespace BHW

variable {d : ℕ} [NeZero d]

/-- Direct common-edge zero representations on the canonical Figure-2-4 source
patches produce the selected adjacent Jost anchor packet.

This is the non-circular source-side entry point for the selected-data layer:
the remaining OS I Section 4.5 payload is the concrete zero representation of
the adjacent-minus-ordinary common-edge branch on each canonical source patch.
The theorem below only performs the checked handoff from that representation to
the compact Figure-2-4 packet and then to selected adjacent Jost data. -/
noncomputable def selectedAdjacentDistributionalJostAnchorData_of_canonical_commonEdge_representsZero
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hrep :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        let P :=
          BHW.os45_adjacent_identity_canonicalSourcePatch
            (d := d) (n := n) hd i hi
        SCV.RepresentsDistributionOn
          (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
          (fun u : NPointDomain d n =>
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) P.V) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n := by
  refine
    BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq
      (d := d) OS lgc n ?_
  intro i hi
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) (n := n) hd i hi
  have hzero :=
    BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresents
      (d := d) hd OS lgc (P := P) (hrep i hi)
  exact
    BHW.os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc n i hi
      (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
      hzero.1 hzero.2

/-- Pointwise common-edge equality on the canonical Figure-2-4 source patches
supplies the selected adjacent Jost anchor packet.

This is the sharper source-side entry point for the non-circular OS I §4.5
payload: once the adjacent and ordinary pulled real branches have genuinely
been identified on each canonical source patch, the distributional zero
representation required by
`selectedAdjacentDistributionalJostAnchorData_of_canonical_commonEdge_representsZero`
is immediate by support restriction. -/
noncomputable def selectedAdjacentDistributionalJostAnchorData_of_canonical_sourceCommonEdge_eq
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hsource :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        let P :=
          BHW.os45_adjacent_identity_canonicalSourcePatch
            (d := d) (n := n) hd i hi
        ∀ u ∈ P.V,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n := by
  refine
    BHW.selectedAdjacentDistributionalJostAnchorData_of_canonical_commonEdge_representsZero
      (d := d) hd OS lgc n ?_
  intro i hi
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) (n := n) hd i hi
  exact
    BHW.os45_sourceCommonEdge_representsZero_of_eqOn
      (d := d) OS lgc
      (P := P) (U := P.V)
      (hsource i hi)

/-- Selected adjacent distributional Jost data supplies the compact
Figure-2-4 Wick-pairing packet for the canonical adjacent source patch.

The proof follows the OS I §4.5/Jost route already checked locally:
selected Jost data gives the horizontal-difference germ, the germ represents
zero distributionally on the common edge, and the zero-height CLM bridge
produces the compact packet. -/
noncomputable def os45CompactFigure24WickPairingEq_of_selectedJostData
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    (hOverlap :
      ∀ (j : Fin n) (hj : j.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    BHW.OS45CompactFigure24WickPairingEq (d := d) n i hi OS lgc := by
  classical
  let P :=
    BHW.os45_adjacent_identity_canonicalSourcePatch
      (d := d) (n := n) hd i hi
  let H : BHW.OS45BHWJostHullData (d := d) hd n i hi P :=
    BHW.os45_BHWJostHullData_of_figure24 (d := d) hd i hi P
  let hlocal :=
    BHW.os45_hdiff_of_selectedJostData
      (d := d) hd OS lgc (P := P) H hOverlap hData P.V P.V_open
      P.V_nonempty (by intro u hu; exact hu)
  let Ucx : Set (Fin n → Fin (d + 1) → ℂ) := Classical.choose hlocal
  let hlocalU := Classical.choose_spec hlocal
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    Classical.choose hlocalU
  let hspec := Classical.choose_spec hlocalU
  have hrep :=
    BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
      (d := d) hd OS lgc (P := P) P.V P.V_open P.V_nonempty Ucx Hdiff
      hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.1
      hspec.2.2.2.2.2.1 hspec.2.2.2.2.2.2
  let hzero :=
    BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresents
      (d := d) hd OS lgc (P := P) hrep
  exact
    BHW.os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM
      (d := d) hd OS lgc n i hi
      (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
      hzero.1 hzero.2

end BHW
