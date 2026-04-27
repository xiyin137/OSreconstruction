import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity

/-!
# Density support for source complex regular configurations

This file proves the complex analogue of the real dense-regular source
configuration theorem.  It is a source-side input for the Hall-Wightman
regular-stratum density argument.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- The complex full-span template obtained by embedding the real template. -/
def sourceComplexFullSpanTemplate
    (d n : ℕ) :
    Fin n → Fin (d + 1) → ℂ :=
  realEmbed (sourceFullSpanTemplate d n)

/-- The complex full-span template contains the canonical coordinate basis
block. -/
theorem sourceComplexFullSpanTemplate_basisVector
    (d n : ℕ)
    (a : Fin (min n (d + 1))) :
    sourceComplexFullSpanTemplate d n (sourceTemplateDomainIndex d n a) =
      Pi.single (sourceTemplateCoordIndex d n a) (1 : ℂ) := by
  ext μ
  unfold sourceComplexFullSpanTemplate realEmbed
  by_cases hμ : μ = sourceTemplateCoordIndex d n a
  · subst μ
    have h := congrFun (sourceFullSpanTemplate_basisVector d n a)
      (sourceTemplateCoordIndex d n a)
    simpa using congrArg (fun x : ℝ => (x : ℂ)) h
  · have h := congrFun (sourceFullSpanTemplate_basisVector d n a) μ
    rw [h]
    simp [Pi.single_eq_of_ne hμ]

/-- The canonical maximal complex regular minor of the template is one. -/
theorem sourceComplexFullSpanTemplate_regularMinor_eq_one
    (d n : ℕ) :
    sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) (sourceComplexFullSpanTemplate d n) = 1 := by
  rw [sourceComplexFullSpanTemplate, sourceComplexRegularMinor_realEmbed]
  exact_mod_cast sourceFullSpanTemplate_regularMinor_eq_one d n

/-- The canonical maximal complex regular minor of the template is nonzero. -/
theorem sourceComplexFullSpanTemplate_regularMinor_ne_zero
    (d n : ℕ) :
    sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) (sourceComplexFullSpanTemplate d n) ≠ 0 := by
  rw [sourceComplexFullSpanTemplate_regularMinor_eq_one]
  norm_num

/-- Determinant polynomial of the canonical regular minor along the complex
line `z + t • sourceComplexFullSpanTemplate`. -/
def sourceComplexCanonicalRegularMinorLinePolynomial
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Polynomial ℂ :=
  let B : Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) ℂ :=
    fun a b =>
      z (sourceTemplateDomainIndex d n a) (sourceTemplateCoordIndex d n b)
  Matrix.det ((Polynomial.X : Polynomial ℂ) •
      (1 : Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) (Polynomial ℂ)) +
    B.map Polynomial.C)

/-- The canonical line-minor determinant polynomial has leading coefficient
one. -/
theorem sourceComplexCanonicalRegularMinorLinePolynomial_leadingCoeff
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Polynomial.leadingCoeff
      (sourceComplexCanonicalRegularMinorLinePolynomial d n z) = 1 := by
  simpa [sourceComplexCanonicalRegularMinorLinePolynomial] using
    Polynomial.leadingCoeff_det_X_one_add_C
      (A := (fun a b : Fin (min n (d + 1)) =>
        z (sourceTemplateDomainIndex d n a) (sourceTemplateCoordIndex d n b) :
        Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) ℂ))

/-- The canonical line-minor determinant polynomial is not zero. -/
theorem sourceComplexCanonicalRegularMinorLinePolynomial_ne_zero
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceComplexCanonicalRegularMinorLinePolynomial d n z ≠ 0 := by
  intro hp
  have hlead :=
    sourceComplexCanonicalRegularMinorLinePolynomial_leadingCoeff d n z
  have hlead0 := congrArg Polynomial.leadingCoeff hp
  rw [hlead] at hlead0
  norm_num at hlead0

/-- Evaluating the canonical line-minor polynomial gives the canonical complex
regular minor of `z + t • sourceComplexFullSpanTemplate`. -/
theorem sourceComplexCanonicalRegularMinorLinePolynomial_eval
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (t : ℂ) :
    (sourceComplexCanonicalRegularMinorLinePolynomial d n z).eval t =
      sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n)
        (z + t • sourceComplexFullSpanTemplate d n) := by
  unfold sourceComplexCanonicalRegularMinorLinePolynomial sourceComplexRegularMinor
  rw [Matrix.det_apply', Polynomial.eval_finset_sum, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.eval_mul, Polynomial.eval_intCast]
  congr 1
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : σ i = i
  · have hcoord :
        sourceTemplateCoordIndex d n i =
          sourceTemplateCoordIndex d n (σ i) := by rw [h]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      sourceComplexFullSpanTemplate_basisVector, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, h, hcoord, add_comm]
  · have hcoord :
        sourceTemplateCoordIndex d n i ≠
          sourceTemplateCoordIndex d n (σ i) := by
      intro hcoord
      exact h ((sourceTemplateCoordIndex_injective d n) hcoord).symm
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      sourceComplexFullSpanTemplate_basisVector, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, h, hcoord, add_comm]

/-- The nonvanishing locus of the canonical complex regular minor is dense. -/
theorem sourceComplexCanonicalRegularMinor_nonzero_dense
    (d n : ℕ) :
    Dense {z : Fin n → Fin (d + 1) → ℂ |
      sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) z ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hU_nonempty
  rcases hU_nonempty with ⟨z, hzU⟩
  let line : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t => z + t • sourceComplexFullSpanTemplate d n
  let p := sourceComplexCanonicalRegularMinorLinePolynomial d n z
  have hp_ne : p ≠ 0 := by
    simpa [p] using
      sourceComplexCanonicalRegularMinorLinePolynomial_ne_zero d n z
  have hroots_finite : ({t : ℂ | p.eval t = 0}).Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro t ht
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset] at ht ⊢
    exact (Polynomial.mem_roots hp_ne).mpr ht
  have hdense : Dense (Set.univ \ {t : ℂ | p.eval t = 0}) := by
    simpa using
      (Dense.diff_finite (s := (Set.univ : Set ℂ)) dense_univ hroots_finite)
  have hline_cont : Continuous line := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre_open : IsOpen (line ⁻¹' U) := hU.preimage hline_cont
  have hpre_nonempty : (line ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [line] using hzU
  obtain ⟨t, htgood, htU⟩ :=
    hdense.exists_mem_open hpre_open hpre_nonempty
  have hp_eval_ne : p.eval t ≠ 0 := by
    have ht_not : t ∉ {t : ℂ | p.eval t = 0} := by
      simpa [Set.mem_diff, p] using htgood
    simpa using ht_not
  refine ⟨line t, ?_, ?_⟩
  · exact htU
  · have hminor :
        sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
          (sourceTemplateCoordIndex d n) (line t) ≠ 0 := by
      have heval : p.eval t =
          sourceComplexRegularMinor d n (sourceTemplateDomainIndex d n)
            (sourceTemplateCoordIndex d n) (line t) := by
        simpa [p, line] using
          sourceComplexCanonicalRegularMinorLinePolynomial_eval d n z t
      exact fun h => hp_eval_ne (by rwa [heval])
    exact hminor

/-- Complex regular source configurations form a dense subset of complex source
configuration space. -/
theorem dense_sourceComplexGramRegularAt
    (d n : ℕ) :
    Dense {z : Fin n → Fin (d + 1) → ℂ | SourceComplexGramRegularAt d n z} := by
  apply (sourceComplexCanonicalRegularMinor_nonzero_dense d n).mono
  intro z hz
  exact sourceComplexGramRegularAt_of_exists_nonzero_minor d n
    ⟨sourceTemplateDomainIndex d n,
      sourceTemplateDomainIndex_injective d n,
      sourceTemplateCoordIndex d n,
      sourceTemplateCoordIndex_injective d n,
      hz⟩

/-- In the hard range `d + 1 <= n`, a nonzero complex regular source minor
makes the corresponding selected Gram rows linearly independent. -/
theorem sourceMinkowskiGram_rows_linearIndependent_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0)
    (hD : d + 1 ≤ n) :
    LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) =>
        fun j : Fin n => sourceMinkowskiGram d n z (I a) j) := by
  let m := min n (d + 1)
  have hsrc_li : LinearIndependent ℂ (fun a : Fin m => z (I a)) := by
    simpa [m] using
      linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
        d n hminor
  have hspan :
      Submodule.span ℂ
        (Set.range (fun a : Fin m => z (I a))) = ⊤ := by
    simpa [m] using
      sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero
        d n hminor hD
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum a
  have hw_zero :
      (∑ c : Fin m, coeff c • z (I c)) = 0 := by
    apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
      d m hspan
    intro b
    have hrow := congrFun hsum (I b)
    calc
      sourceComplexMinkowskiInner d
          (∑ c : Fin m, coeff c • z (I c)) (z (I b))
          = ∑ c : Fin m,
              coeff c *
                sourceComplexMinkowskiInner d (z (I c)) (z (I b)) := by
            rw [sourceComplexMinkowskiInner_sum_smul_left]
      _ = 0 := by
            simpa [m, Finset.sum_apply, Pi.smul_apply,
              sourceMinkowskiGram_apply_eq_complexInner] using hrow
  exact (Fintype.linearIndependent_iff.mp hsrc_li coeff hw_zero) a

/-- In the hard range `d + 1 <= n`, a nonzero complex regular source minor
forces the source Gram matrix to have rank at least `d + 1`. -/
theorem sourceMinkowskiGram_rank_ge_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0)
    (hD : d + 1 ≤ n) :
    d + 1 ≤
      (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank := by
  let m := min n (d + 1)
  let G : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j
  let R : Matrix (Fin m) (Fin n) ℂ := fun a j => G (I a) j
  have hrows : LinearIndependent ℂ R.row := by
    simpa [R, G, Matrix.row, m] using
      sourceMinkowskiGram_rows_linearIndependent_of_sourceComplexRegularMinor_ne_zero
        d n hminor hD
  have hRrank : R.rank = m := by
    simpa [Fintype.card_fin] using hrows.rank_matrix (M := R)
  have hR_le_G : R.rank ≤ G.rank := by
    simpa [R, G, Matrix.submatrix] using
      Matrix.rank_submatrix_le (A := G) I (Equiv.refl (Fin n))
  calc
    d + 1 = m := by
      simp [m, Nat.min_eq_right hD]
    _ = R.rank := hRrank.symm
    _ ≤ G.rank := hR_le_G

/-- In the hard range `d + 1 <= n`, every complex regular source point maps to
a Gram matrix of rank at least `d + 1`. -/
theorem sourceMinkowskiGram_rank_ge_of_sourceComplexGramRegularAt
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z) :
    d + 1 ≤
      (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank := by
  rcases exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg with
    ⟨I, _hI, J, _hJ, hminor⟩
  exact
    sourceMinkowskiGram_rank_ge_of_sourceComplexRegularMinor_ne_zero
      d n hminor hD

/-- In the hard range `d + 1 <= n`, every complex regular source point maps
into the regular rank-`d+1` stratum of the source complex Gram variety. -/
theorem sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z) :
    sourceMinkowskiGram d n z ∈
      sourceSymmetricRankExactStratum n (d + 1) := by
  have hge :=
    sourceMinkowskiGram_rank_ge_of_sourceComplexGramRegularAt
      d n hD hreg
  have hvar :
      sourceMinkowskiGram d n z ∈ sourceComplexGramVariety d n := by
    exact ⟨z, rfl⟩
  rw [sourceComplexGramVariety_eq_rank_le] at hvar
  exact ⟨hvar.1, le_antisymm hvar.2 hge⟩

/-- In the hard range `d + 1 <= n`, the regular rank-`d+1` stratum is dense
in the source complex Gram variety. -/
theorem sourceComplexGramVariety_subset_closure_sourceSymmetricRankExactStratum
    (d n : ℕ)
    (hD : d + 1 ≤ n) :
    sourceComplexGramVariety d n ⊆
      closure (sourceSymmetricRankExactStratum n (d + 1)) := by
  intro G hG
  rcases hG with ⟨z, rfl⟩
  rw [mem_closure_iff]
  intro O hO hGO
  have hpre_open : IsOpen ((sourceMinkowskiGram d n) ⁻¹' O) := by
    exact hO.preimage (contDiff_sourceMinkowskiGram d n).continuous
  have hpre_nonempty : ((sourceMinkowskiGram d n) ⁻¹' O).Nonempty := by
    exact ⟨z, hGO⟩
  obtain ⟨z', hz'reg, hz'O⟩ :=
    (dense_sourceComplexGramRegularAt d n).exists_mem_open
      hpre_open hpre_nonempty
  exact ⟨sourceMinkowskiGram d n z', hz'O,
    sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt
      d n hD hz'reg⟩

/-- In the hard range `d + 1 <= n`, the ambient closure of the regular
rank-`d+1` stratum is exactly the source complex Gram variety. -/
theorem closure_sourceSymmetricRankExactStratum_eq_sourceComplexGramVariety
    (d n : ℕ)
    (hD : d + 1 ≤ n) :
    closure (sourceSymmetricRankExactStratum n (d + 1)) =
      sourceComplexGramVariety d n := by
  apply Set.Subset.antisymm
  · rw [(isClosed_sourceComplexGramVariety d n).closure_subset_iff]
    exact
      sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
        d n (d + 1) le_rfl
  · exact
      sourceComplexGramVariety_subset_closure_sourceSymmetricRankExactStratum
        d n hD

/-- Every nonempty relatively open subset of the source complex Gram variety
meets the regular rank-`d+1` stratum in the hard range `d + 1 <= n`. -/
theorem sourceComplexGramVariety_relOpen_inter_rankExact_nonempty
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_nonempty : U.Nonempty) :
    (U ∩ sourceSymmetricRankExactStratum n (d + 1)).Nonempty := by
  rcases hU_rel with ⟨U0, hU0_open, rfl⟩
  rcases hU_nonempty with ⟨G, hGU0, hGvar⟩
  have hGcl :
      G ∈ closure (sourceSymmetricRankExactStratum n (d + 1)) :=
    sourceComplexGramVariety_subset_closure_sourceSymmetricRankExactStratum
      d n hD hGvar
  rw [mem_closure_iff] at hGcl
  rcases hGcl U0 hU0_open hGU0 with ⟨G', hG'U0, hG'exact⟩
  have hG'var :
      G' ∈ sourceComplexGramVariety d n :=
    sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
      d n (d + 1) le_rfl hG'exact
  exact ⟨G', ⟨hG'U0, hG'var⟩, hG'exact⟩

/-- In the hard range `d + 1 <= n`, the regular rank-`d+1` stratum is dense
inside every relatively open source-variety domain. -/
theorem sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U) :
    U ⊆ closure (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  rcases hU_rel with ⟨U0, hU0_open, rfl⟩
  rintro G ⟨hGU0, hGvar⟩
  rw [mem_closure_iff]
  intro O hO_open hGO
  have hGcl :
      G ∈ closure (sourceSymmetricRankExactStratum n (d + 1)) :=
    sourceComplexGramVariety_subset_closure_sourceSymmetricRankExactStratum
      d n hD hGvar
  rw [mem_closure_iff] at hGcl
  rcases hGcl (O ∩ U0) (hO_open.inter hU0_open) ⟨hGO, hGU0⟩ with
    ⟨G', hG'OU0, hG'exact⟩
  have hG'var :
      G' ∈ sourceComplexGramVariety d n :=
    sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
      d n (d + 1) le_rfl hG'exact
  exact ⟨G', hG'OU0.1, ⟨⟨hG'OU0.2, hG'var⟩, hG'exact⟩⟩

/-- A continuous scalar-product representative on a relatively open source
variety domain that vanishes on the dense regular rank stratum vanishes on the
whole domain. -/
theorem sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hH_cont : ContinuousOn H U)
    (hzero :
      Set.EqOn H 0
        (U ∩ sourceSymmetricRankExactStratum n (d + 1))) :
    Set.EqOn H 0 U := by
  intro G hGU
  by_contra hH_ne
  have hGcl :
      G ∈ closure (U ∩ sourceSymmetricRankExactStratum n (d + 1)) :=
    sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
      d n hD hU_rel hGU
  rcases (continuousOn_iff.mp hH_cont) G hGU {w : ℂ | w ≠ 0}
      isOpen_ne hH_ne with
    ⟨O, hO_open, hGO, hO_sub⟩
  rw [mem_closure_iff] at hGcl
  rcases hGcl O hO_open hGO with ⟨G', hG'O, hG'reg⟩
  have hG'U : G' ∈ U := hG'reg.1
  have hH_ne' : H G' ≠ 0 := by
    exact hO_sub ⟨hG'O, hG'U⟩
  have hH_zero' : H G' = 0 := hzero hG'reg
  exact hH_ne' hH_zero'

end BHW
