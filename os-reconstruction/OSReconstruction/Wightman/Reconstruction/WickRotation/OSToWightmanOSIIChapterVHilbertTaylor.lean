/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGluing



















noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Algebraic Taylor data before any convergence estimate is imposed.

The `homogeneousTerm p` is the total-degree-`p` Hilbert coefficient after the
multi-index sum has been formed.  The scalar Gram kernel records the reflected
Schwinger pairing of two such coefficients.  Unlike
`HilbertTaylorCauchyData`, this structure does not assume a norm-remainder
identity: that identity is proved below from the coefficient pairings. -/
structure HilbertTaylorGramData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  homogeneousTerm : ℕ → H
  scalarGram : ℕ → ℕ → ℂ
  inner_homogeneousTerm_eq_scalarGram :
    ∀ p q,
      @inner ℂ H _ (homogeneousTerm p) (homogeneousTerm q) =
        scalarGram p q

namespace HilbertTaylorGramData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Taylor polynomial containing homogeneous degrees strictly below `N`. -/
def partialSum (D : HilbertTaylorGramData H) (N : ℕ) : H :=
  ∑ p ∈ Finset.range N, D.homogeneousTerm p

/-- Finite homogeneous tail with degrees in `[N, M)`. -/
def tail (D : HilbertTaylorGramData H) (N M : ℕ) : H :=
  ∑ p ∈ Finset.Ico N M, D.homogeneousTerm p

/-- The reflected scalar double tail corresponding to a Hilbert Taylor tail. -/
def scalarTail (D : HilbertTaylorGramData H) (N M : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ico N M,
    ∑ p ∈ Finset.Ico N M, D.scalarGram p q

theorem tail_eq_partialSum_sub
    (D : HilbertTaylorGramData H)
    {N M : ℕ} (hNM : N ≤ M) :
    D.tail N M = D.partialSum M - D.partialSum N := by
  simpa only [tail, partialSum] using
    Finset.sum_Ico_eq_sub D.homogeneousTerm hNM

/-- The norm square of a finite Hilbert Taylor tail is exactly the real part
of its reflected scalar Gram tail.

This is the finite-sum algebra at the heart of OS II equation (5.21).  The
remaining OS-specific obligation is to identify each Gram coefficient with
the corresponding derivative of the continued reflected Schwinger function;
the norm expansion itself is no longer an assumed field. -/
theorem norm_tail_sq_eq_re_scalarTail
    (D : HilbertTaylorGramData H)
    (N M : ℕ) :
    ‖D.tail N M‖ ^ 2 = (D.scalarTail N M).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (D.tail N M)]
  simp only [tail, scalarTail, sum_inner, inner_sum,
    D.inner_homogeneousTerm_eq_scalarGram, RCLike.re_to_complex]

theorem norm_partialSum_sub_sq_eq_re_scalarTail
    (D : HilbertTaylorGramData H)
    {N M : ℕ} (hNM : N ≤ M) :
    ‖D.partialSum M - D.partialSum N‖ ^ 2 =
      (D.scalarTail N M).re := by
  rw [← D.tail_eq_partialSum_sub hNM]
  exact D.norm_tail_sq_eq_re_scalarTail N M

/-- The norm square of a finite Hilbert Taylor polynomial is the real part of
the corresponding square partial sum of its scalar Gram matrix. -/
theorem norm_partialSum_sq_eq_re_squareSum
    (D : HilbertTaylorGramData H) (N : ℕ) :
    ‖D.partialSum N‖ ^ 2 =
      (∑ pq ∈ Finset.range N ×ˢ Finset.range N,
        D.scalarGram pq.1 pq.2).re := by
  have h := D.norm_tail_sq_eq_re_scalarTail 0 N
  have htail : D.tail 0 N = D.partialSum N := by
    simp only [tail, partialSum, Nat.Ico_zero_eq_range]
  rw [htail] at h
  rw [Finset.sum_product, Finset.sum_comm]
  simpa only [scalarTail, Nat.Ico_zero_eq_range] using h

/-- If Hilbert Taylor polynomials and their square scalar Gram sums converge,
the real part of the scalar limit is the squared norm of the Hilbert limit. -/
theorem norm_limit_sq_eq_re_of_tendsto_squareSum
    (D : HilbertTaylorGramData H) (Ψ : H) (value : ℂ)
    (hΨ : Filter.Tendsto D.partialSum Filter.atTop (nhds Ψ))
    (hscalar :
      Filter.Tendsto
        (fun N =>
          ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
            D.scalarGram pq.1 pq.2)
        Filter.atTop (nhds value)) :
    ‖Ψ‖ ^ 2 = value.re := by
  have hnorm :
      Filter.Tendsto (fun N => ‖D.partialSum N‖ ^ 2)
        Filter.atTop (nhds (‖Ψ‖ ^ 2)) :=
    hΨ.norm.pow 2
  have hreal :
      Filter.Tendsto
        (fun N =>
          (∑ pq ∈ Finset.range N ×ˢ Finset.range N,
            D.scalarGram pq.1 pq.2).re)
        Filter.atTop (nhds value.re) :=
    (Complex.continuous_re.tendsto value).comp hscalar
  exact tendsto_nhds_unique hnorm
    (hreal.congr' (Filter.Eventually.of_forall fun N =>
      (D.norm_partialSum_sq_eq_re_squareSum N).symm))

/-- One summable point-independent majorant for a family of scalar Gram
matrices makes every sufficiently late square tail uniformly small. -/
theorem scalarTail_small_uniform_of_norm_scalarGram_le
    {X : Type*}
    (D : X → HilbertTaylorGramData H)
    (s : Set X)
    (majorant : ℕ × ℕ → ℝ)
    (hmajorant_nonneg : ∀ pq, 0 ≤ majorant pq)
    (hmajorant_sum : Summable majorant)
    (hmajorant :
      ∀ x ∈ s, ∀ p q,
        ‖(D x).scalarGram p q‖ ≤ majorant (p, q)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ x ∈ s, ∀ M, N ≤ M →
        ((D x).scalarTail N M).re < ε ^ 2 := by
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨t, ht⟩ :=
    summable_iff_vanishing_norm.mp hmajorant_sum (ε ^ 2) hεsq
  obtain ⟨N, hN⟩ := (t.image Prod.fst).exists_nat_subset_range
  refine ⟨N, fun x hx M hNM => ?_⟩
  let u : Finset (ℕ × ℕ) := Finset.Ico N M ×ˢ Finset.Ico N M
  have hdisjoint : Disjoint u t := by
    rw [Finset.disjoint_left]
    intro pq hpqu hpqt
    have hpN : N ≤ pq.1 :=
      (Finset.mem_Ico.mp (Finset.mem_product.mp hpqu).1).1
    have hp_lt : pq.1 < N := by
      rw [← Finset.mem_range]
      exact hN (Finset.mem_image.mpr ⟨pq, hpqt, rfl⟩)
    omega
  have htail :
      (∑ pq ∈ u, (D x).scalarGram pq.1 pq.2) =
        (D x).scalarTail N M := by
    calc
      (∑ pq ∈ u, (D x).scalarGram pq.1 pq.2) =
          ∑ p ∈ Finset.Ico N M,
            ∑ q ∈ Finset.Ico N M,
              (D x).scalarGram p q := by
                simp only [u, Finset.sum_product]
      _ = ∑ q ∈ Finset.Ico N M,
            ∑ p ∈ Finset.Ico N M,
              (D x).scalarGram p q := by
                rw [Finset.sum_comm]
      _ = (D x).scalarTail N M := rfl
  have hmajorant_tail :
      (∑ pq ∈ u, majorant pq) < ε ^ 2 := by
    have hnorm := ht u hdisjoint
    rw [Real.norm_of_nonneg] at hnorm
    · exact hnorm
    · exact Finset.sum_nonneg fun pq _ => hmajorant_nonneg pq
  calc
    ((D x).scalarTail N M).re ≤
        ‖(D x).scalarTail N M‖ :=
      Complex.re_le_norm _
    _ = ‖∑ pq ∈ u, (D x).scalarGram pq.1 pq.2‖ := by
      rw [htail]
    _ ≤ ∑ pq ∈ u, ‖(D x).scalarGram pq.1 pq.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ pq ∈ u, majorant pq := by
      exact Finset.sum_le_sum fun pq _ =>
        hmajorant x hx pq.1 pq.2
    _ < ε ^ 2 := hmajorant_tail

/-- A summable point-independent scalar Gram majorant makes a family of
Hilbert Taylor polynomials uniformly Cauchy. -/
theorem uniformCauchySeqOn_partialSum_of_norm_scalarGram_le
    {X : Type*}
    (D : X → HilbertTaylorGramData H)
    (s : Set X)
    (majorant : ℕ × ℕ → ℝ)
    (hmajorant_nonneg : ∀ pq, 0 ≤ majorant pq)
    (hmajorant_sum : Summable majorant)
    (hmajorant :
      ∀ x ∈ s, ∀ p q,
        ‖(D x).scalarGram p q‖ ≤ majorant (p, q)) :
    UniformCauchySeqOn
      (fun N x => (D x).partialSum N) Filter.atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ :=
    scalarTail_small_uniform_of_norm_scalarGram_le
      D s majorant hmajorant_nonneg hmajorant_sum hmajorant
      (ε / 2) hhalf
  refine ⟨N, fun M hNM L hNL x hx => ?_⟩
  have hM_sq :
      ‖(D x).partialSum M - (D x).partialSum N‖ ^ 2 <
        (ε / 2) ^ 2 := by
    rw [(D x).norm_partialSum_sub_sq_eq_re_scalarTail hNM]
    exact hN x hx M hNM
  have hL_sq :
      ‖(D x).partialSum L - (D x).partialSum N‖ ^ 2 <
        (ε / 2) ^ 2 := by
    rw [(D x).norm_partialSum_sub_sq_eq_re_scalarTail hNL]
    exact hN x hx L hNL
  have hM :
      ‖(D x).partialSum M - (D x).partialSum N‖ < ε / 2 := by
    nlinarith [norm_nonneg ((D x).partialSum M - (D x).partialSum N)]
  have hL :
      ‖(D x).partialSum L - (D x).partialSum N‖ < ε / 2 := by
    nlinarith [norm_nonneg ((D x).partialSum L - (D x).partialSum N)]
  rw [dist_eq_norm]
  calc
    ‖(D x).partialSum M - (D x).partialSum L‖ =
        ‖((D x).partialSum M - (D x).partialSum N) -
          ((D x).partialSum L - (D x).partialSum N)‖ := by
            congr 1
            abel
    _ ≤ ‖(D x).partialSum M - (D x).partialSum N‖ +
          ‖(D x).partialSum L - (D x).partialSum N‖ :=
      norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hM hL
    _ = ε := by ring

end HilbertTaylorGramData

namespace HilbertTaylorCauchyData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end HilbertTaylorCauchyData

end OSIIChapterV
end OSReconstruction
