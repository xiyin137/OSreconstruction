import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexChart

/-!
# Dimension support for source complex selected Gram charts

This file records the finite-dimensional coordinate count for the selected
complex symmetric-coordinate chart used on Hall-Wightman's regular rank
stratum.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- The selected complex symmetric-coordinate subspace has the expected complex
dimension `n*m - m*(m-1)/2`. -/
theorem finrank_sourceSelectedComplexSymCoordSubspace
    (n m : ℕ)
    (I : Fin m → Fin n)
    (hI : Function.Injective I) :
    Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n m I) =
      n * m - (m * (m - 1)) / 2 := by
  let K := sourceSelectedSymCoordKey n m I
  have hkey : Fintype.card K = n * m - (m * (m - 1)) / 2 := by
    have hreal := (sourceSelectedRealSymCoordKeyEquiv n m hI).finrank_eq
    have hformula := finrank_sourceSelectedSymCoordSubspace n m I hI
    calc
      Fintype.card K = Module.finrank ℝ (K → ℝ) := by
        simp [K, Module.finrank_fintype_fun_eq_card]
      _ = Module.finrank ℝ (sourceSelectedSymCoordSubspace n m I) := by
        exact hreal.symm
      _ = n * m - (m * (m - 1)) / 2 := hformula
  have hcomplex := (sourceSelectedComplexSymCoordKeyEquiv n m hI).finrank_eq
  calc
    Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n m I)
        = Module.finrank ℂ (K → ℂ) := by
          exact hcomplex
    _ = Fintype.card K := by
          simp [K, Module.finrank_fintype_fun_eq_card]
    _ = n * m - (m * (m - 1)) / 2 := hkey

/-- The binomial correction term in the rank-stratum dimension formula is
bounded by the ambient rectangular coordinate count. -/
theorem sourceRankExactChartDim_choose_two_le_mul
    (n k : ℕ)
    (hk : k ≤ n) :
    Nat.choose k 2 ≤ n * k := by
  have hchoose_le_mul : Nat.choose k 2 ≤ k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_le_self _ _
  have hkm1 : k * (k - 1) ≤ k * k := by
    exact Nat.mul_le_mul_left k (Nat.sub_le _ _)
  have hkn : k * k ≤ n * k := by
    rw [mul_comm k k, mul_comm n k]
    exact Nat.mul_le_mul_left k hk
  exact hchoose_le_mul.trans (hkm1.trans hkn)

/-- Successive rank-exact chart dimensions differ by `n - k` in binomial
coordinates. -/
theorem sourceRankExactChartDim_succ_sub_choose
    (n k : ℕ)
    (hk : k + 1 ≤ n) :
    n * (k + 1) - Nat.choose (k + 1) 2 -
        (n * k - Nat.choose k 2) =
      n - k := by
  have hchoose : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
    rw [show (2 : ℕ) = 1 + 1 by rfl]
    rw [Nat.choose_succ_succ]
    simp
    omega
  have hk_le : k ≤ n := by omega
  have hC : Nat.choose k 2 ≤ n * k :=
    sourceRankExactChartDim_choose_two_le_mul n k hk_le
  rw [hchoose, Nat.mul_succ]
  omega

/-- The lower-rank codimension calculation in binomial coordinates:
`dim(rankExact D) - dim(rankExact (D-1)) = n - D + 1`. -/
theorem sourceRankExactChartDim_sub_previous_choose
    (n D : ℕ)
    (hD0 : 0 < D)
    (hDle : D ≤ n) :
    n * D - Nat.choose D 2 -
        (n * (D - 1) - Nat.choose (D - 1) 2) =
      n - D + 1 := by
  cases D with
  | zero => omega
  | succ k =>
      calc
        n * (k + 1) - Nat.choose (k + 1) 2 -
            (n * ((k + 1) - 1) - Nat.choose ((k + 1) - 1) 2)
            = n * (k + 1) - Nat.choose (k + 1) 2 -
              (n * k - Nat.choose k 2) := by simp
        _ = n - k := sourceRankExactChartDim_succ_sub_choose n k hDle
        _ = n - (k + 1) + 1 := by omega

/-- The lower-rank codimension calculation in the Hall-Wightman paper's
dimension formula `n*D - D*(D-1)/2`. -/
theorem sourceRankExactChartDim_sub_previous
    (n D : ℕ)
    (hD0 : 0 < D)
    (hDle : D ≤ n) :
    n * D - (D * (D - 1)) / 2 -
        (n * (D - 1) - ((D - 1) * ((D - 1) - 1)) / 2) =
      n - D + 1 := by
  rw [← Nat.choose_two_right D, ← Nat.choose_two_right (D - 1)]
  exact sourceRankExactChartDim_sub_previous_choose n D hD0 hDle

/-- The selected complex rank-`D` and rank-`D-1` chart dimensions differ by
`n - D + 1`. -/
theorem finrank_sourceSelectedComplexSymCoordSubspace_sub_previous
    (n D : ℕ)
    (hD0 : 0 < D)
    (hDle : D ≤ n)
    (I : Fin D → Fin n)
    (hI : Function.Injective I)
    (J : Fin (D - 1) → Fin n)
    (hJ : Function.Injective J) :
    Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n D I) -
        Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n (D - 1) J) =
      n - D + 1 := by
  rw [finrank_sourceSelectedComplexSymCoordSubspace n D I hI,
    finrank_sourceSelectedComplexSymCoordSubspace n (D - 1) J hJ]
  exact sourceRankExactChartDim_sub_previous n D hD0 hDle

/-- In the singular case `D < n`, the lower-rank locus has selected-chart
codimension at least two. -/
theorem finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two
    (n D : ℕ)
    (hD0 : 0 < D)
    (hDlt : D < n)
    (I : Fin D → Fin n)
    (hI : Function.Injective I)
    (J : Fin (D - 1) → Fin n)
    (hJ : Function.Injective J) :
    2 ≤ Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n D I) -
        Module.finrank ℂ (sourceSelectedComplexSymCoordSubspace n (D - 1) J) := by
  rw [finrank_sourceSelectedComplexSymCoordSubspace_sub_previous
    n D hD0 (Nat.le_of_lt hDlt) I hI J hJ]
  omega

end BHW
