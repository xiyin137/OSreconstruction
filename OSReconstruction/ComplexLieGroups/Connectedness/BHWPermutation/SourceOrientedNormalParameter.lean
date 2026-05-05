import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented

/-!
# Head/tail source indices for rank-deficient normal parameters

The rank-deficient Schur normal form splits the source labels into a selected
head block of size `r` and a tail block of size `n - r`.  This file records
the elementary `Fin` bookkeeping for that split.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected head source labels `0, ..., r-1` as labels in `Fin n`. -/
def finSourceHead {r n : ℕ} (hrn : r ≤ n) :
    Fin r → Fin n :=
  Fin.castLE hrn

/-- The tail source labels `r, ..., n-1` as labels in `Fin n`. -/
def finSourceTail {r n : ℕ} (hrn : r ≤ n) :
    Fin (n - r) → Fin n :=
  fun u => Fin.cast (Nat.add_sub_of_le hrn) (Fin.natAdd r u)

@[simp]
theorem finSourceHead_val {r n : ℕ} (hrn : r ≤ n) (a : Fin r) :
    (finSourceHead hrn a).val = a.val := by
  rfl

@[simp]
theorem finSourceTail_val {r n : ℕ} (hrn : r ≤ n) (u : Fin (n - r)) :
    (finSourceTail hrn u).val = r + u.val := by
  simp [finSourceTail]

/-- The head-label inclusion is injective. -/
theorem finSourceHead_injective {r n : ℕ} (hrn : r ≤ n) :
    Function.Injective (finSourceHead hrn) :=
  Fin.castLE_injective hrn

/-- The tail-label inclusion is injective. -/
theorem finSourceTail_injective {r n : ℕ} (hrn : r ≤ n) :
    Function.Injective (finSourceTail hrn) := by
  intro u v huv
  apply Fin.ext
  have hval :
      r + u.val = r + v.val := by
    simpa using congrArg Fin.val huv
  exact Nat.add_left_cancel hval

/-- Head labels and tail labels are disjoint. -/
theorem finSourceHead_ne_finSourceTail {r n : ℕ} (hrn : r ≤ n)
    (a : Fin r) (u : Fin (n - r)) :
    finSourceHead hrn a ≠ finSourceTail hrn u := by
  intro h
  have hval :
      a.val = r + u.val := by
    simpa using congrArg Fin.val h
  omega

/-- Every source label is either in the selected head block or in the tail. -/
theorem finSourceHead_tail_cases {r n : ℕ} (hrn : r ≤ n)
    (i : Fin n) :
    (∃ a : Fin r, i = finSourceHead hrn a) ∨
      (∃ u : Fin (n - r), i = finSourceTail hrn u) := by
  by_cases hi : i.val < r
  · left
    refine ⟨⟨i.val, hi⟩, ?_⟩
    apply Fin.ext
    simp [finSourceHead]
  · right
    have hri : r ≤ i.val := Nat.le_of_not_gt hi
    have htail_lt : i.val - r < n - r := by
      omega
    refine ⟨⟨i.val - r, htail_lt⟩, ?_⟩
    apply Fin.ext
    simp [finSourceTail]
    omega

/-- Finite product coordinates for a rank-deficient source normal form:
an invertible head factor, mixed tail/head coefficients, and residual tail
vectors in the orthogonal complement. -/
structure SourceOrientedRankDeficientNormalParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  head : Matrix (Fin r) (Fin r) ℂ
  mixed : Matrix (Fin (n - r)) (Fin r) ℂ
  tail : Fin (n - r) → Fin (d + 1 - r) → ℂ

/-- The center of the normal parameter chart. -/
def sourceOrientedNormalCenterParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := 1
  mixed := 0
  tail := 0

/-- Embed an orthogonal-tail coordinate vector into the full spacetime
coordinate space by padding the first `r` head coordinates with zero. -/
def sourceTailEmbed
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    if h : r ≤ μ.val then
      q ⟨μ.val - r, by omega⟩
    else
      0

@[simp]
theorem sourceTailEmbed_head
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ)
    (a : Fin r) :
    sourceTailEmbed d r hrD q
      (finSourceHead (Nat.le_of_lt hrD) a) = 0 := by
  simp [sourceTailEmbed]

@[simp]
theorem sourceTailEmbed_tail
    (d r : ℕ)
    (hrD : r < d + 1)
    (q : Fin (d + 1 - r) → ℂ)
    (u : Fin (d + 1 - r)) :
    sourceTailEmbed d r hrD q
      (finSourceTail (Nat.le_of_lt hrD) u) = q u := by
  simp [sourceTailEmbed]

@[simp]
theorem sourceTailEmbed_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceTailEmbed d r hrD 0 = 0 := by
  ext μ
  by_cases h : r ≤ μ.val <;> simp [sourceTailEmbed, h]

/-- Canonical source tuple for the rank-`r` normal form: the first `r`
source vectors are the first `r` coordinate vectors, and all remaining source
vectors vanish.  The definition is total in `r`; the normal-form route uses it
only under `r < d + 1` and `r ≤ n`. -/
def hwLemma3CanonicalSource
    (d n r : ℕ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i μ =>
    if i.val = μ.val ∧ i.val < r then
      1
    else
      0

/-- Head vectors after applying the head-factor coordinate. -/
def sourceOrientedNormalHeadVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    ∑ b : Fin r,
      p.head a b * hwLemma3CanonicalSource d n r (finSourceHead hrn b) μ

/-- At the center parameter, each normal head vector is the corresponding
canonical head source vector. -/
theorem sourceOrientedNormalHeadVector_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (a : Fin r) :
    sourceOrientedNormalHeadVector d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) a =
      hwLemma3CanonicalSource d n r (finSourceHead hrn a) := by
  ext μ
  classical
  rw [sourceOrientedNormalHeadVector, sourceOrientedNormalCenterParameter]
  rw [Finset.sum_eq_single a]
  · simp [hwLemma3CanonicalSource]
  · intro b _ hb
    have hab : a ≠ b := fun h => hb h.symm
    simp [hab]
  · intro ha
    simp at ha

/-- Source tuple associated to a normal-form parameter.  Head source labels use
the head-factor vectors; tail labels are a mixed head combination plus an
embedded orthogonal-tail vector. -/
def sourceOrientedNormalParameterVector
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i =>
    if hi : i.val < r then
      sourceOrientedNormalHeadVector d n r hrD hrn p ⟨i.val, hi⟩
    else
      let u : Fin (n - r) := ⟨i.val - r, by omega⟩
      fun μ =>
        (∑ a : Fin r,
          p.mixed u a *
            sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
        sourceTailEmbed d r hrD (p.tail u) μ

/-- At the center parameter, the normal-parameter vector is the canonical
rank-`r` source. -/
theorem sourceOrientedNormalParameterVector_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterVector d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      hwLemma3CanonicalSource d n r := by
  ext i μ
  by_cases hi : i.val < r
  · simp [sourceOrientedNormalParameterVector, hi,
      sourceOrientedNormalHeadVector_center, hwLemma3CanonicalSource]
  · have hcanon : hwLemma3CanonicalSource d n r i μ = 0 := by
      simp [hwLemma3CanonicalSource, hi]
    simp [sourceOrientedNormalParameterVector, hi,
      sourceOrientedNormalHeadVector, sourceOrientedNormalCenterParameter,
      hcanon]

end BHW
