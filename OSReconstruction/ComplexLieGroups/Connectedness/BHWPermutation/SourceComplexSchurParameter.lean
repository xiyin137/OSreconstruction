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

/-- Connectedness is transported through the preimage of a continuous linear
equivalence.  This is the finite-coordinate step used after identifying a
Schur parameter slice in product coordinates. -/
theorem isConnected_preimage_continuousLinearEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F)
    {S : Set F}
    (hS : IsConnected S) :
    IsConnected (e ⁻¹' S) := by
  have himage : e.symm '' S = e ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  rw [← himage]
  exact hS.image e.symm e.symm.continuous.continuousOn

/-- Connectedness is transported through the preimage of a homeomorphism.
This is the topology-only replacement for the normal-parameter coordinate
model, whose checked coordinate map is a homeomorphism rather than a
continuous linear equivalence. -/
theorem isConnected_preimage_homeomorph
    {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F)
    {S : Set F}
    (hS : IsConnected S) :
    IsConnected (e ⁻¹' S) := by
  have himage : e.symm '' S = e ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  rw [← himage]
  exact hS.image e.symm e.symm.continuous.continuousOn

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
