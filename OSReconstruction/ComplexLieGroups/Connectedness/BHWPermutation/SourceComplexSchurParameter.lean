import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurGraph

/-!
# Parameter-side connectedness for Schur rank slices

The singular Schur-graph proof in `SourceComplexSchurGraph.lean` proves
connectedness after applying the graph map.  The source-oriented exceptional
local-image route also needs the parameter-side version: the max-rank preimage
inside the head/mixed/tail parameter box is exactly such a product slice.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The Schur parameter set with an exact-rank residual coordinate is
connected when the head, mixed, and exact residual pieces are connected. -/
theorem isConnected_sourcePrincipalSchur_rankExact_parameterSet
    (D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_conn : IsConnected Aset)
    (hB_conn : IsConnected Bset)
    (hS_conn :
      IsConnected
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = D - Fintype.card r})) :
    IsConnected
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}} := by
  have hprod : IsConnected
      (Aset ×ˢ (Bset ×ˢ
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = D - Fintype.card r}))) :=
    hA_conn.prod (hB_conn.prod hS_conn)
  simpa [Set.prod] using hprod

/-- The Schur parameter set with a rank-bounded residual coordinate is
connected when the head, mixed, and rank-bounded residual pieces are
connected. -/
theorem isConnected_sourcePrincipalSchur_rankLE_parameterSet
    (D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_conn : IsConnected Aset)
    (hB_conn : IsConnected Bset)
    (hS_conn :
      IsConnected
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank ≤ D - Fintype.card r})) :
    IsConnected
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank ≤ D - Fintype.card r}} := by
  have hprod : IsConnected
      (Aset ×ˢ (Bset ×ˢ
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank ≤ D - Fintype.card r}))) :=
    hA_conn.prod (hB_conn.prod hS_conn)
  simpa [Set.prod] using hprod

end BHW
