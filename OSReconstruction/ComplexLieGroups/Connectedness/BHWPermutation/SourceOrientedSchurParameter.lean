import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurParameter
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankBridge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTransport

/-!
# Oriented max-rank on Schur parameter graphs

This file records the algebraic rewrite used by the exceptional
Schur/residual local-image producer: on a principal Schur graph, hard-range
oriented max-rank is exactly exact rank of the residual Schur-complement
coordinate.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- On a principal Schur graph with invertible symmetric head block, ordinary
source Gram rank `D` is exactly residual Schur-complement rank
`D - card r`. -/
theorem sourcePrincipalSchurGraph_sourceGramMatrixRank_eq_iff_residual_rank
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
    (hA_sym : Aᵀ = A)
    {B : Matrix r q ℂ} {S : Matrix q q ℂ}
    (hS_sym : Sᵀ = S) (hrD : Fintype.card r ≤ D) :
    sourceGramMatrixRank n (sourcePrincipalSchurGraph n e A B S) = D ↔
      S.rank = D - Fintype.card r := by
  have hsym :
      sourcePrincipalSchurGraph n e A B S ∈
        sourceSymmetricMatrixSpace n :=
    sourcePrincipalSchurGraph_mem_symmetric n e B hA_sym hS_sym
  have hiff :=
    sourcePrincipalSchurGraph_mem_rankExact_iff
      n D e hA_unit hA_sym (B := B) hS_sym hrD
  constructor
  · intro hrank
    exact hiff.1 ⟨hsym, by simpa [sourceGramMatrixRank] using hrank⟩
  · intro hS
    have hmem :
        sourcePrincipalSchurGraph n e A B S ∈
          sourceSymmetricRankExactStratum n D :=
      hiff.2 hS
    simpa [sourceGramMatrixRank] using hmem.2

/-- In the hard source range, the oriented max-rank predicate for an oriented
Gram datum whose ordinary coordinate is a principal Schur graph is exactly
exact rank of the residual Schur-complement coordinate.  The determinant
coordinates are irrelevant because `SourceOrientedMaxRankAt` only reads
`G.gram`. -/
theorem sourceOrientedMaxRankAt_sourcePrincipalSchurGraph_iff_residual_rank
    (hn : d + 1 ≤ n)
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
    (hA_sym : Aᵀ = A)
    {B : Matrix r q ℂ} {S : Matrix q q ℂ}
    (hS_sym : Sᵀ = S)
    (hrD : Fintype.card r ≤ d + 1)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ) :
    SourceOrientedMaxRankAt d n
        ((sourcePrincipalSchurGraph n e A B S, δ) :
          SourceOrientedGramData d n) ↔
      S.rank = d + 1 - Fintype.card r := by
  rw [sourceOrientedMaxRankAt_iff_sourceGramMatrixRank_eq_fullFrame
    (d := d) (n := n) hn]
  simpa [SourceOrientedGramData.gram] using
    sourcePrincipalSchurGraph_sourceGramMatrixRank_eq_iff_residual_rank
      n (d + 1) e hA_unit hA_sym hS_sym hrD

/-- The parameter subset on which a principal Schur graph is oriented
max-rank is exactly the product subset whose residual coordinate has exact
rank.  The determinant coordinates may depend on the parameter, but they do
not affect the predicate. -/
theorem sourcePrincipalSchur_orientedMaxRank_parameterSet_eq
    (hn : d + 1 ≤ n)
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ {A : Matrix r r ℂ}, A ∈ Aset → IsUnit A.det)
    (hA_sym : ∀ {A : Matrix r r ℂ}, A ∈ Aset → Aᵀ = A)
    (hS_sym : ∀ {S : Matrix q q ℂ}, S ∈ Sset → Sᵀ = S)
    (hrD : Fintype.card r ≤ d + 1)
    (δ :
      Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ →
        (Fin (d + 1) ↪ Fin n) → ℂ) :
    {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
      p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset ∧
        SourceOrientedMaxRankAt d n
          ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
            SourceOrientedGramData d n)} =
    {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
      p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
        p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = d + 1 - Fintype.card r}} := by
  ext p
  constructor
  · rintro ⟨hA, hB, hS, hmax⟩
    have hrank :
        p.2.2.rank = d + 1 - Fintype.card r :=
      (sourceOrientedMaxRankAt_sourcePrincipalSchurGraph_iff_residual_rank
        (d := d) (n := n) hn e
        (A := p.1) (B := p.2.1) (S := p.2.2)
        (hA_unit hA) (hA_sym hA) (hS_sym hS) hrD (δ p)).1 hmax
    exact ⟨hA, hB, ⟨hS, (hS_sym hS), hrank⟩⟩
  · rintro ⟨hA, hB, hS, hSsym, hrank⟩
    have hmax :
        SourceOrientedMaxRankAt d n
          ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
            SourceOrientedGramData d n) :=
      (sourceOrientedMaxRankAt_sourcePrincipalSchurGraph_iff_residual_rank
        (d := d) (n := n) hn e
        (A := p.1) (B := p.2.1) (S := p.2.2)
        (hA_unit hA) (hA_sym hA) hSsym hrD (δ p)).2 hrank
    exact ⟨hA, hB, hS, hmax⟩

/-- Connectedness of the principal Schur parameter slice whose oriented image
is max-rank.  This is the product-connectedness input for the exceptional
rank-deficient local-image producer after normal coordinates have been
identified with a principal Schur graph. -/
theorem isConnected_sourcePrincipalSchur_orientedMaxRank_parameterSet
    (hn : d + 1 ≤ n)
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ {A : Matrix r r ℂ}, A ∈ Aset → IsUnit A.det)
    (hA_sym : ∀ {A : Matrix r r ℂ}, A ∈ Aset → Aᵀ = A)
    (hS_sym : ∀ {S : Matrix q q ℂ}, S ∈ Sset → Sᵀ = S)
    (hrD : Fintype.card r ≤ d + 1)
    (δ :
      Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ →
        (Fin (d + 1) ↪ Fin n) → ℂ)
    (hA_conn : IsConnected Aset)
    (hB_conn : IsConnected Bset)
    (hS_conn :
      IsConnected
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = d + 1 - Fintype.card r})) :
    IsConnected
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset ∧
          SourceOrientedMaxRankAt d n
            ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
              SourceOrientedGramData d n)} := by
  rw [sourcePrincipalSchur_orientedMaxRank_parameterSet_eq
    (d := d) (n := n) hn e hA_unit hA_sym hS_sym hrD δ]
  exact
    isConnected_sourcePrincipalSchur_rankExact_parameterSet
      (d + 1) hA_conn hB_conn hS_conn

/-- The previous connected parameter-slice theorem is stable under an inverse
oriented invariant transport.  This is the exact shape used by rank-deficient
normal-form local images, where the normal Schur chart is transported back to
the original oriented coordinates by `T.invFun`. -/
theorem isConnected_sourcePrincipalSchur_transported_orientedMaxRank_parameterSet
    (hn : d + 1 ≤ n)
    (T : SourceOrientedInvariantTransportEquiv d n)
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ {A : Matrix r r ℂ}, A ∈ Aset → IsUnit A.det)
    (hA_sym : ∀ {A : Matrix r r ℂ}, A ∈ Aset → Aᵀ = A)
    (hS_sym : ∀ {S : Matrix q q ℂ}, S ∈ Sset → Sᵀ = S)
    (hrD : Fintype.card r ≤ d + 1)
    (δ :
      Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ →
        (Fin (d + 1) ↪ Fin n) → ℂ)
    (hA_conn : IsConnected Aset)
    (hB_conn : IsConnected Bset)
    (hS_conn :
      IsConnected
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = d + 1 - Fintype.card r})) :
    IsConnected
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset ∧
          SourceOrientedMaxRankAt d n
            (T.invFun
              ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
                SourceOrientedGramData d n))} := by
  let normalSet :
      Set (Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ) :=
    {p |
      p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset ∧
        SourceOrientedMaxRankAt d n
          ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
            SourceOrientedGramData d n)}
  have hEq :
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset ∧
          SourceOrientedMaxRankAt d n
            (T.invFun
              ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
                SourceOrientedGramData d n))} = normalSet := by
    ext p
    constructor
    · rintro ⟨hA, hB, hS, hmax⟩
      exact ⟨hA, hB, hS,
        (T.invFun_maxRank_iff
          ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
            SourceOrientedGramData d n)).1 hmax⟩
    · rintro ⟨hA, hB, hS, hmax⟩
      exact ⟨hA, hB, hS,
        (T.invFun_maxRank_iff
          ((sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2, δ p) :
            SourceOrientedGramData d n)).2 hmax⟩
  rw [hEq]
  exact
    isConnected_sourcePrincipalSchur_orientedMaxRank_parameterSet
      (d := d) (n := n) hn e hA_unit hA_sym hS_sym hrD δ
      hA_conn hB_conn hS_conn

end BHW
