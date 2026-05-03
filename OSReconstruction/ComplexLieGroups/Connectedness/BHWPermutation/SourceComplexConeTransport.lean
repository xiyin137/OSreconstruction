import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexCone

/-!
# Rank-exact cone connectedness on arbitrary finite index types

`SourceComplexCone.lean` proves the small connected rank-exact cone
neighborhood theorem on `Fin m`.  The singular Schur chart uses the complement
type supplied by a selected principal minor.  This file transports the checked
cone theorem along `Fintype.equivFin`, without changing the mathematics.
-/

noncomputable section

open Matrix

namespace BHW

/-- The checked rank-exact cone connectedness theorem, transported from
`Fin (Fintype.card q)` to an arbitrary finite index type `q`. -/
theorem matrixSymmetricRankExactCone_small_connected
    {q : Type*} [Fintype q] [DecidableEq q]
    (r : ℕ) (hr : r ≤ Fintype.card q)
    {N : Set (Matrix q q ℂ)}
    (hN_open : IsOpen N)
    (h0N : (0 : Matrix q q ℂ) ∈ N) :
    ∃ C : Set (Matrix q q ℂ),
      (0 : Matrix q q ℂ) ∈ C ∧
      IsOpen C ∧ C ⊆ N ∧
      IsConnected
        (C ∩ {S : Matrix q q ℂ | Sᵀ = S ∧ S.rank = r}) := by
  let e : q ≃ Fin (Fintype.card q) := Fintype.equivFin q
  let Nfin : Set (Matrix (Fin (Fintype.card q)) (Fin (Fintype.card q)) ℂ) :=
    {T | T.reindex e.symm e.symm ∈ N}
  have hNfin_open : IsOpen Nfin := by
    exact hN_open.preimage (by fun_prop)
  have h0Nfin :
      (0 : Matrix (Fin (Fintype.card q)) (Fin (Fintype.card q)) ℂ) ∈ Nfin := by
    simpa [Nfin, e] using h0N
  rcases sourceSymmetricRankExactCone_small_connected
      (Fintype.card q) r hr hNfin_open h0Nfin with
    ⟨Cfin, h0Cfin, hCfin_open, hCfin_sub, hCfin_conn⟩
  let C : Set (Matrix q q ℂ) := {S | S.reindex e e ∈ Cfin}
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · simpa [C, e] using h0Cfin
  · exact hCfin_open.preimage (by fun_prop)
  · intro S hSC
    have hfin : (S.reindex e e).reindex e.symm e.symm ∈ N := hCfin_sub hSC
    simpa [C, Nfin, e] using hfin
  · have himg_conn : IsConnected
        ((fun T : Matrix (Fin (Fintype.card q)) (Fin (Fintype.card q)) ℂ =>
            T.reindex e.symm e.symm) ''
          (Cfin ∩ sourceSymmetricRankExactStratum (Fintype.card q) r)) := by
      exact hCfin_conn.image _ (by fun_prop)
    refine Eq.subst ?_ himg_conn
    ext S
    constructor
    · intro hS
      rcases hS with ⟨T, hT, rfl⟩
      rcases hT with ⟨hTC, hTstr⟩
      rcases hTstr with ⟨hTsym, hTrank⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [C, e] using hTC
      · ext i j
        have hsymMatrix : Tᵀ = T := by
          ext a b
          exact hTsym b a
        have hback : (T.reindex e.symm e.symm)ᵀ = T.reindex e.symm e.symm := by
          ext a b
          simpa [Matrix.transpose] using
            congr_fun (congr_fun hsymMatrix (e a)) (e b)
        exact congr_fun (congr_fun hback i) j
      · simpa [e] using hTrank
    · intro hS
      rcases hS with ⟨hSC, hSsym, hSrank⟩
      refine ⟨S.reindex e e, ?_, ?_⟩
      · refine ⟨hSC, ?_⟩
        constructor
        · intro i j
          have hsym' : (S.reindex e e)ᵀ = S.reindex e e := by
            exact (show Sᵀ = S ↔ (S.reindex e e)ᵀ = S.reindex e e from by
              constructor
              · intro h
                ext i j
                simpa [Matrix.transpose] using
                  congr_fun (congr_fun h (e.symm i)) (e.symm j)
              · intro h
                ext i j
                have := congr_fun (congr_fun h (e i)) (e j)
                simpa [Matrix.transpose] using this).mp hSsym
          simpa [Matrix.transpose] using congr_fun (congr_fun hsym' j) i
        · have hrank' : (S.reindex e e).rank = S.rank := by
            simp [e]
          exact hrank'.trans hSrank
      · simp [e]

end BHW
