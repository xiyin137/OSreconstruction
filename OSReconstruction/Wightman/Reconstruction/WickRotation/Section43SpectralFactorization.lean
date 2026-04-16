import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-!
# Section 4.3 Spectral Factorization Coordinates

This small companion contains the coordinate blocks needed to factor the
full-flat Wightman Fourier kernel on the Section 4.3 spectral region.  The key
point is that the Borchers-reversed left factor uses the total-momentum-shifted
block `section43LeftBorchersBlock`, not the naive reversed left block.
-/

/-- Left flat frequency block of a full `(n + r)`-point flat frequency. -/
def section43SplitLeftFlat (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    ξ (finProdFinEquiv (Fin.castAdd r p.1, p.2))

/-- Right flat frequency block of a full `(n + r)`-point flat frequency. -/
def section43SplitRightFlat (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (r * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    ξ (finProdFinEquiv (Fin.natAdd n p.1, p.2))

/-- Negative chronological reversal of an `n`-point flat frequency block. -/
def section43NegRevFlat (d n : ℕ) [NeZero d]
    (ξL : Fin (n * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i;
    -(ξL (finProdFinEquiv (Fin.rev p.1, p.2)))

/-- The shifted Borchers-left cumulative-tail block.

For `q` in the full `(n + r)` cumulative-tail coordinates, this is
`q_n, q_{n-1}, ..., q_1`.  The `r > 0` hypothesis ensures the first index
`n` exists in the full block.
-/
def section43LeftBorchersBlock (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r)) : NPointDomain d n :=
  fun i μ => q ⟨n - i.val, by omega⟩ μ

@[simp] theorem section43SplitLeftFlat_apply
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (i : Fin n) (μ : Fin (d + 1)) :
    section43SplitLeftFlat d n r ξ (finProdFinEquiv (i, μ)) =
      ξ (finProdFinEquiv (Fin.castAdd r i, μ)) := by
  simp [section43SplitLeftFlat]

@[simp] theorem section43SplitRightFlat_apply
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ)
    (j : Fin r) (μ : Fin (d + 1)) :
    section43SplitRightFlat d n r ξ (finProdFinEquiv (j, μ)) =
      ξ (finProdFinEquiv (Fin.natAdd n j, μ)) := by
  simp [section43SplitRightFlat]

@[simp] theorem section43NegRevFlat_apply
    (d n : ℕ) [NeZero d]
    (ξL : Fin (n * (d + 1)) → ℝ)
    (i : Fin n) (μ : Fin (d + 1)) :
    section43NegRevFlat d n ξL (finProdFinEquiv (i, μ)) =
      -(ξL (finProdFinEquiv (Fin.rev i, μ))) := by
  simp [section43NegRevFlat]

@[simp] theorem section43LeftBorchersBlock_apply
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r))
    (i : Fin n) (μ : Fin (d + 1)) :
    section43LeftBorchersBlock d n r hr q i μ =
      q ⟨n - i.val, by omega⟩ μ := rfl

/-- Spectral-region membership makes the shifted left Borchers block
positive-energy. -/
theorem section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
    (d n r : ℕ) [NeZero d] {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hr : 0 < r)
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r)) :
    section43LeftBorchersBlock d n r hr
        (section43CumulativeTailMomentumCLE d (n + r) ξ) ∈
      section43PositiveEnergyRegion d n := by
  have hq :
      section43CumulativeTailMomentumCLE d (n + r) ξ ∈
        section43PositiveEnergyRegion d (n + r) :=
    section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
      d (n + r) hξ.1
  intro i
  simpa [section43PositiveEnergyRegion, section43LeftBorchersBlock] using
    hq ⟨n - i.val, by omega⟩

/-- Spectral-region membership makes the ordinary right tail block
positive-energy. -/
theorem section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
    (d n r : ℕ) [NeZero d] {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r)) :
    section43RightTailBlock d n r
        (section43CumulativeTailMomentumCLE d (n + r) ξ) ∈
      section43PositiveEnergyRegion d r := by
  have hq :
      section43CumulativeTailMomentumCLE d (n + r) ξ ∈
        section43PositiveEnergyRegion d (n + r) :=
    section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
      d (n + r) hξ.1
  exact section43RightTailBlock_mem_positiveEnergy d n r hq

end OSReconstruction
