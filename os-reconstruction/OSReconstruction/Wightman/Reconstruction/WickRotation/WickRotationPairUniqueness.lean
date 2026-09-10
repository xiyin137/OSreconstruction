import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity

/-!
# Uniqueness from the literal Wick-pair contract

Compact zero-diagonal Euclidean tests identify the holomorphic functions on
the forward tube. Their existing Schwartz boundary limits then identify the
full distributions. No growth, positivity, or reconstructed record is assumed.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace OSReconstruction

theorem wickRotationPair_unique
    {d : Nat} [NeZero d] {S : SchwingerFunctions d}
    {W V : (n : Nat) -> SchwartzNPoint d n -> Complex}
    (hW : IsWickRotationPair S W) (hV : IsWickRotationPair S V) : W = V := by
  funext n f
  obtain ⟨F, hF, hFb, hFe⟩ := hW n
  obtain ⟨G, hG, hGb, hGe⟩ := hV n
  obtain ⟨eta, heta⟩ := forwardConeAbs_nonempty d n
  have heta : InForwardCone d n eta := (inForwardCone_iff_mem_forwardConeAbs eta).mpr heta
  apply tendsto_nhds_unique (hFb f eta heta)
  apply (hGb f eta heta).congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  symm
  exact forwardTube_point_eq_of_zeroDiagonal_distributional_wickSection_eq F G hF hG
    (fun phi _ _ => (hFe (ZeroDiagonalSchwartz.ofClassical phi)).symm.trans
      (hGe (ZeroDiagonalSchwartz.ofClassical phi))) x eta heta epsilon hepsilon

end OSReconstruction
