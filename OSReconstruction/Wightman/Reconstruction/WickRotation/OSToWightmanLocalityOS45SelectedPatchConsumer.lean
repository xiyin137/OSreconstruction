import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityCanonicalShell
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SelectedCompact

/-!
# Selected Figure-2-4 Patch Consumer

This small companion is the local consumer in the OS I Section 4.5 /
Jost-Ruelle locality route.  Once selected adjacent Jost data supplies the
compact Figure-2-4 Wick-pairing packet, the canonical-shell boundary-value
theorem gives adjacent Wightman equality for tests supported in that packet.
-/

noncomputable section

open scoped Classical NNReal
open BigOperators Filter MeasureTheory Matrix LorentzLieGroup

namespace BHW

variable {d : ℕ} [NeZero d]

/-- Selected adjacent Jost data gives the boundary-value adjacent-swap equality
for compact tests whose topological support lies in the selected local
Figure-2-4 real patch.

Monograph Vol IV Ch 2, Proposition `os-boundary-package-consequences` (b):
after local Jost/EOW equality has produced the compact patch packet, smearing
with tests supported in that patch gives the boundary-value commutativity
identity. -/
theorem bvt_W_eq_of_selectedJostData_at_tsupport
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
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_patch :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        (BHW.os45CompactFigure24WickPairingEq_of_selectedJostData
          (d := d) hd OS lgc hOverlap hData
          : BHW.OS45CompactFigure24WickPairingEq
              (d := d) n i hi OS lgc).realPatch 1)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  classical
  let P : BHW.OS45CompactFigure24WickPairingEq
      (d := d) n i hi OS lgc :=
    BHW.os45CompactFigure24WickPairingEq_of_selectedJostData
      (d := d) hd OS lgc hOverlap hData
  refine
    BHW.bvt_W_eq_of_compactFigure24Patch_at_tsupport
      (d := d) OS lgc n i hi f g hf_compact ?_ hswap
  intro x hx
  exact ⟨P, hf_patch hx⟩

/-- Source-patch form of the selected local consumer.

The compact packet produced from selected Jost data is built from the canonical
Figure-2-4 source patch, so a test supported in that source patch is supported
in the identity-labelled real patch consumed by
`bvt_W_eq_of_selectedJostData_at_tsupport`. -/
theorem bvt_W_eq_of_selectedJostData_on_figure24SourcePatch
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
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_source :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
    (hswap :
      ∀ x : NPointDomain d n,
        g.toFun x =
          f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc n f = bvt_W OS lgc n g := by
  refine
    BHW.bvt_W_eq_of_selectedJostData_at_tsupport
      (d := d) hd OS lgc hOverlap hData f g hf_compact ?_ hswap
  intro x hx
  refine Set.mem_image_of_mem _ (hf_source hx)

end BHW
