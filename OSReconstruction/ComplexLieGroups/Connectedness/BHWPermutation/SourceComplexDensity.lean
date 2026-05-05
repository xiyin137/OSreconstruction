import Mathlib.Analysis.Normed.Module.Connected
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurGraph

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

/-- The rank of a source Gram matrix is bounded by the dimension of the
complex span of the source rows. -/
theorem sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank ≤
      Module.finrank ℂ (sourceComplexConfigurationSpan d n z) := by
  let G : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n z
  let T : S →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun s j => sourceComplexMinkowskiInner d s.1 (z j)
    map_add' := by
      intro s t
      ext j
      simp [sourceComplexMinkowskiInner_add_left]
    map_smul' := by
      intro c s
      ext j
      simp [sourceComplexMinkowskiInner_smul_left] }
  have hrow_le :
      Submodule.span ℂ (Set.range G.row) ≤ LinearMap.range T := by
    refine Submodule.span_le.mpr ?_
    rintro v ⟨i, rfl⟩
    refine ⟨⟨z i, ?_⟩, ?_⟩
    · exact Submodule.subset_span ⟨i, rfl⟩
    · ext j
      simp [T, G, Matrix.row, sourceMinkowskiGram_apply_eq_complexInner]
  calc
    (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank
        = Module.finrank ℂ (Submodule.span ℂ (Set.range G.row)) := by
          simpa [G] using G.rank_eq_finrank_span_row
    _ ≤ Module.finrank ℂ (LinearMap.range T) :=
          Submodule.finrank_mono hrow_le
    _ ≤ Module.finrank ℂ S :=
          LinearMap.finrank_range_le T

/-- Every rank-exact source scalar-product matrix has a complex regular source
realization. -/
theorem sourceSymmetricRankExactStratum_exists_complexRegular_realization
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n (d + 1)) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      SourceComplexGramRegularAt d n z ∧
        sourceMinkowskiGram d n z = Z := by
  have hZvar :
      Z ∈ sourceComplexGramVariety d n :=
    sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
      d n (d + 1) le_rfl hZ
  rcases hZvar with ⟨z, rfl⟩
  refine ⟨z, ?_, rfl⟩
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n z
  have hrank_le :
      (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank ≤
        Module.finrank ℂ S := by
    simpa [S] using
      sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank d n z
  have hge : d + 1 ≤ Module.finrank ℂ S := by
    simpa [S, hZ.2] using hrank_le
  have hle : Module.finrank ℂ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [S, sourceComplexConfigurationSpan, Module.finrank_fin_fun] using h
  unfold SourceComplexGramRegularAt
  rw [Nat.min_eq_right hD]
  exact le_antisymm hle hge

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

/-- Inside any open complex source neighborhood of a complex regular point,
there is a connected source ball whose Gram image contains a relatively open
rank-exact neighborhood in the source complex Gram variety. -/
theorem sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
    (d n : ℕ)
    (hD : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hz0V : z0 ∈ V) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen U ∧ IsConnected U ∧ z0 ∈ U ∧ U ⊆ V ∧
      ∃ O : Set (Fin n → Fin n → ℂ),
        sourceMinkowskiGram d n z0 ∈ O ∧
        IsRelOpenInSourceComplexGramVariety d n O ∧
        O ⊆ sourceMinkowskiGram d n '' U ∧
        O ⊆ sourceSymmetricRankExactStratum n (d + 1) ∧
        IsConnected O ∧
        ∀ G ∈ O, ∃ z ∈ U,
          sourceMinkowskiGram d n z = G := by
  rcases exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  rcases sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hz0e, _hebase, hefst⟩
  let base : Set (Fin n → Fin (d + 1) → ℂ) :=
    (e.source ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}) ∩ V
  have hbase_open : IsOpen base := by
    exact (e.open_source.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)).inter hV_open
  have hz0base : z0 ∈ base := ⟨⟨hz0e, hminor⟩, hz0V⟩
  rcases Metric.mem_nhds_iff.mp (hbase_open.mem_nhds hz0base) with
    ⟨ε, hεpos, hεsub⟩
  let U : Set (Fin n → Fin (d + 1) → ℂ) := Metric.ball z0 ε
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsConnected U := Metric.isConnected_ball hεpos
  have hz0U : z0 ∈ U := Metric.mem_ball_self hεpos
  have hUbase : U ⊆ base := by
    intro z hz
    exact hεsub hz
  have hUsub : U ⊆ e.source := fun _ hz => (hUbase hz).1.1
  have hUV : U ⊆ V := fun _ hz => (hUbase hz).2
  have hUminor :
      ∀ z ∈ U, sourceComplexRegularMinor d n I J z ≠ 0 :=
    fun _ hz => (hUbase hz).1.2
  let m := min n (d + 1)
  let S := sourceSelectedComplexSymCoordSubspace n m I
  let K := LinearMap.ker
    (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  let T : Set (S × K) := e '' U
  let R : Set S := Prod.fst '' T
  have hTopen : IsOpen T := by
    exact e.isOpen_image_of_subset_source hUopen hUsub
  have hRopen : IsOpen R := by
    exact isOpenMap_fst T hTopen
  rcases isOpen_induced_iff.mp hRopen with
    ⟨R0, hR0open, hR0pre⟩
  let E0 : Set (Fin n → Fin n → ℂ) :=
    {G | sourceSelectedComplexGramCoord n m I G ∈ R0}
  let O : Set (Fin n → Fin n → ℂ) :=
    E0 ∩ sourceComplexGramVariety d n
  have hPcont : Continuous (sourceSelectedComplexGramCoord n m I) :=
    LinearMap.continuous_of_finiteDimensional
      (sourceSelectedComplexGramCoord n m I)
  have hE0open : IsOpen E0 := by
    exact hR0open.preimage hPcont
  have hbaseR :
      sourceSelectedComplexGramMap d n m I z0 ∈ R := by
    refine ⟨e z0, ?_, ?_⟩
    · exact ⟨z0, hz0U, rfl⟩
    · exact hefst z0 hz0e
  have hbaseR0 :
      (sourceSelectedComplexGramMap d n m I z0 :
          Fin n → Fin m → ℂ) ∈ R0 := by
    have hpre :
        sourceSelectedComplexGramMap d n m I z0 ∈
          Subtype.val ⁻¹' R0 := by
      rw [hR0pre]
      exact hbaseR
    exact hpre
  have hbaseO :
      sourceMinkowskiGram d n z0 ∈ O := by
    refine ⟨?_, ?_⟩
    · exact hbaseR0
    · exact ⟨z0, rfl⟩
  have hOcomplex :
      ∀ G ∈ O, ∃ z ∈ U,
        sourceComplexRegularMinor d n I J z ≠ 0 ∧
          sourceMinkowskiGram d n z = G := by
    intro G hGO
    rcases hGO with ⟨hGE0, hGvar⟩
    have hGsym : ∀ i j : Fin n, G i j = G j i := by
      rcases hGvar with ⟨z, rfl⟩
      intro i j
      exact sourceMinkowskiGram_symm d n z i j
    let A : S :=
      ⟨sourceSelectedComplexGramCoord n m I G, by
        intro a b
        change G (I a) (I b) = G (I b) (I a)
        exact hGsym (I a) (I b)⟩
    have hAR : A ∈ R := by
      have hpre : A ∈ Subtype.val ⁻¹' R0 := hGE0
      rw [hR0pre] at hpre
      exact hpre
    rcases hAR with ⟨p, hpT, hpA⟩
    rcases hpT with ⟨u, huU, rfl⟩
    have hselSubtype :
        sourceSelectedComplexGramMap d n m I u = A := by
      exact (hefst u (hUsub huU)).symm.trans hpA
    have hsel :
        sourceSelectedComplexGramCoord n m I
            (sourceMinkowskiGram d n u) =
          sourceSelectedComplexGramCoord n m I G := by
      exact congrArg Subtype.val hselSubtype
    have hGram :
        sourceMinkowskiGram d n u = G :=
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
        d n hI (hUminor u huU) hGvar hsel
    exact ⟨u, huU, hUminor u huU, hGram⟩
  have hOsubset :
      O ⊆ sourceMinkowskiGram d n '' U := by
    intro G hG
    rcases hOcomplex G hG with ⟨u, huU, _hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩
  have hImageSubset :
      sourceMinkowskiGram d n '' U ⊆ O := by
    rintro G ⟨u, huU, rfl⟩
    refine ⟨?_, ⟨u, rfl⟩⟩
    have hAR : sourceSelectedComplexGramMap d n m I u ∈ R := by
      refine ⟨e u, ?_, ?_⟩
      · exact ⟨u, huU, rfl⟩
      · exact hefst u (hUsub huU)
    have hpre :
        sourceSelectedComplexGramMap d n m I u ∈
          Subtype.val ⁻¹' R0 := by
      rw [hR0pre]
      exact hAR
    simpa [sourceSelectedComplexGramMap] using hpre
  have hOreg :
      O ⊆ sourceSymmetricRankExactStratum n (d + 1) := by
    intro G hG
    rcases hOcomplex G hG with ⟨u, huU, hminoru, hGram⟩
    rw [← hGram]
    exact
      sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt
        d n hD
        (sourceComplexGramRegularAt_of_exists_nonzero_minor d n
          ⟨I, hI, J, hJ, hminoru⟩)
  have hOconn : IsConnected O := by
    have hOeq : O = sourceMinkowskiGram d n '' U :=
      Set.Subset.antisymm hOsubset hImageSubset
    rw [hOeq]
    exact hUconn.image (sourceMinkowskiGram d n)
      (contDiff_sourceMinkowskiGram d n).continuous.continuousOn
  refine ⟨U, hUopen, hUconn, hz0U, hUV, O, hbaseO, ?_,
    hOsubset, hOreg, hOconn, ?_⟩
  · exact ⟨E0, hE0open, rfl⟩
  · intro G hG
    rcases hOcomplex G hG with ⟨u, huU, _hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩

/-- Regular-rank points of the source complex Gram variety have relatively
open connected rank-exact neighborhoods inside any prescribed ambient
neighborhood. -/
theorem sourceComplexGramVariety_local_rankExact_connected_basis_regular
    (d n : ℕ)
    (hD : d + 1 < n)
    {Z0 : Fin n → Fin n → ℂ}
    (hZ0reg : Z0 ∈ sourceSymmetricRankExactStratum n (d + 1))
    {N0 : Set (Fin n → Fin n → ℂ)}
    (hN0_open : IsOpen N0)
    (hZ0N0 : Z0 ∈ N0) :
    ∃ V : Set (Fin n → Fin n → ℂ),
      Z0 ∈ V ∧
      IsRelOpenInSourceComplexGramVariety d n V ∧
      V ⊆ N0 ∩ sourceComplexGramVariety d n ∧
      IsConnected (V ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  have hDle : d + 1 ≤ n := Nat.le_of_lt hD
  rcases sourceSymmetricRankExactStratum_exists_complexRegular_realization
      d n hDle hZ0reg with
    ⟨z0, hz0reg, hz0Gram⟩
  let Vsrc : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | sourceMinkowskiGram d n z ∈ N0}
  have hVsrc_open : IsOpen Vsrc :=
    hN0_open.preimage (contDiff_sourceMinkowskiGram d n).continuous
  have hz0Vsrc : z0 ∈ Vsrc := by
    simpa [Vsrc, hz0Gram] using hZ0N0
  rcases sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
      d n hDle hz0reg hVsrc_open hz0Vsrc with
    ⟨Usrc, _hUsrc_open, _hUsrc_conn, _hz0Usrc, hUsrc_sub,
      O, hZ0O, hO_rel, _hO_image, hO_rank, hO_conn, hO_surj⟩
  have hZ0O' : Z0 ∈ O := by
    simpa [hz0Gram] using hZ0O
  refine ⟨O, hZ0O', hO_rel, ?_, ?_⟩
  · intro G hGO
    rcases hO_surj G hGO with ⟨z, hzU, hzG⟩
    refine ⟨?_, ?_⟩
    · rw [← hzG]
      exact hUsrc_sub hzU
    · exact sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
        d n (d + 1) le_rfl (hO_rank hGO)
  · have hO_inter :
        O ∩ sourceSymmetricRankExactStratum n (d + 1) = O := by
      ext G
      constructor
      · intro hG
        exact hG.1
      · intro hG
        exact ⟨hG, hO_rank hG⟩
    rw [hO_inter]
    exact hO_conn

/-- Every source complex Gram-variety point has arbitrarily small relatively
open neighborhoods whose rank-`d+1` part is connected.  This is the local
Hall-Wightman source-variety connectedness input: regular points use the
checked source-Gram implicit chart, and singular points use the Schur product
chart. -/
theorem sourceComplexGramVariety_local_rankExact_connected_basis
    (d n : ℕ)
    (hD : d + 1 < n)
    {Z0 : Fin n → Fin n → ℂ}
    (hZ0 : Z0 ∈ sourceComplexGramVariety d n)
    {N0 : Set (Fin n → Fin n → ℂ)}
    (hN0_open : IsOpen N0)
    (hZ0N0 : Z0 ∈ N0) :
    ∃ V : Set (Fin n → Fin n → ℂ),
      Z0 ∈ V ∧
      IsRelOpenInSourceComplexGramVariety d n V ∧
      V ⊆ N0 ∩ sourceComplexGramVariety d n ∧
      IsConnected (V ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  let M0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z0 i j
  have hZ0_rank_le : Z0 ∈ sourceSymmetricMatrixSpace n ∧
      M0.rank ≤ d + 1 := by
    have h := hZ0
    rw [sourceComplexGramVariety_eq_rank_le] at h
    simpa [M0] using h
  by_cases hreg : M0.rank = d + 1
  · have hZ0reg : Z0 ∈ sourceSymmetricRankExactStratum n (d + 1) := by
      exact ⟨hZ0_rank_le.1, by simpa [M0] using hreg⟩
    exact
      sourceComplexGramVariety_local_rankExact_connected_basis_regular
        d n hD hZ0reg hN0_open hZ0N0
  · have hsing : M0.rank < d + 1 := by
      omega
    exact
      sourceComplexGramVariety_local_rankExact_connected_basis_singular
        d n hD hZ0 (by simpa [M0] using hsing) hN0_open hZ0N0

/-- Pull back a variety-holomorphic scalar along the source complex Gram map. -/
theorem SourceVarietyHolomorphicOn.comp_sourceMinkowskiGram
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hGramU : sourceMinkowskiGram d n '' V ⊆ U) :
    DifferentiableOn ℂ (fun z => H (sourceMinkowskiGram d n z)) V := by
  intro z hzV
  have hG : sourceMinkowskiGram d n z ∈ U :=
    hGramU ⟨z, hzV, rfl⟩
  rcases hH (sourceMinkowskiGram d n z) hG with
    ⟨U0, hU0_open, hGU0, hHdiffU0, _hU0_sub⟩
  have hHat : DifferentiableAt ℂ H (sourceMinkowskiGram d n z) :=
    (hHdiffU0 (sourceMinkowskiGram d n z) hGU0).differentiableAt
      (hU0_open.mem_nhds hGU0)
  have hgram : Differentiable ℂ (sourceMinkowskiGram d n) :=
    (contDiff_sourceMinkowskiGram d n).differentiable (by simp)
  exact (hHat.comp z hgram.differentiableAt).differentiableWithinAt

/-- Local identity propagation on the regular rank stratum of the source
complex Gram variety. -/
theorem sourceComplexGramVariety_rankExact_local_identity_near_point
    (d n : ℕ)
    (hD : d + 1 < n)
    {U : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    {Z0 : Fin n → Fin n → ℂ}
    (hZ0U : Z0 ∈ U)
    (hZ0reg : Z0 ∈ sourceSymmetricRankExactStratum n (d + 1))
    {A : Set (Fin n → Fin n → ℂ)}
    (hA_rel :
      ∃ A0, IsOpen A0 ∧
        A = A0 ∩ (U ∩ sourceSymmetricRankExactStratum n (d + 1)))
    (hZ0_closure : Z0 ∈ closure A)
    (hA_zero : Set.EqOn H 0 A) :
    ∃ V : Set (Fin n → Fin n → ℂ),
      Z0 ∈ V ∧
      (∃ V0, IsOpen V0 ∧
        V = V0 ∩ (U ∩ sourceSymmetricRankExactStratum n (d + 1))) ∧
      Set.EqOn H 0 V := by
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  rcases hA_rel with ⟨A0, hA0_open, hA_eq⟩
  have hDle : d + 1 ≤ n := Nat.le_of_lt hD
  rcases sourceSymmetricRankExactStratum_exists_complexRegular_realization
      d n hDle hZ0reg with
    ⟨z0, hz0reg, hz0Gram⟩
  let Vsrc : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | sourceMinkowskiGram d n z ∈ U0}
  have hVsrc_open : IsOpen Vsrc := by
    exact hU0_open.preimage (contDiff_sourceMinkowskiGram d n).continuous
  have hz0Vsrc : z0 ∈ Vsrc := by
    have hZ0U0 : Z0 ∈ U0 := by
      rw [hU_eq] at hZ0U
      exact hZ0U.1
    simpa [Vsrc, hz0Gram] using hZ0U0
  rcases sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
      d n hDle hz0reg hVsrc_open hz0Vsrc with
    ⟨Usrc, hUsrc_open, hUsrc_conn, _hz0Usrc, hUsrc_subVsrc,
      O, hbaseO, hO_rel, hO_image, hO_rank, _hO_conn, hO_surj⟩
  have hZ0O : Z0 ∈ O := by
    simpa [hz0Gram] using hbaseO
  rcases hO_rel with ⟨O0, hO0_open, hO_eq⟩
  have hZ0O0 : Z0 ∈ O0 := by
    rw [hO_eq] at hZ0O
    exact hZ0O.1
  rw [mem_closure_iff] at hZ0_closure
  rcases hZ0_closure O0 hO0_open hZ0O0 with
    ⟨G1, hG1O0, hG1A⟩
  have hG1A_decomp :
      G1 ∈ A0 ∩ (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
    simpa [hA_eq] using hG1A
  have hG1var : G1 ∈ sourceComplexGramVariety d n :=
    sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
      d n (d + 1) le_rfl hG1A_decomp.2.2
  have hG1O : G1 ∈ O := by
    rw [hO_eq]
    exact ⟨hG1O0, hG1var⟩
  rcases hO_surj G1 hG1O with ⟨z1, hz1Usrc, hz1Gram⟩
  let P : Set (Fin n → Fin (d + 1) → ℂ) :=
    Usrc ∩ {z | sourceMinkowskiGram d n z ∈ A0 ∩ O0}
  have hP_open : IsOpen P := by
    exact hUsrc_open.inter
      ((hA0_open.inter hO0_open).preimage
        (contDiff_sourceMinkowskiGram d n).continuous)
  have hz1P : z1 ∈ P := by
    refine ⟨hz1Usrc, ?_⟩
    change sourceMinkowskiGram d n z1 ∈ A0 ∩ O0
    rw [hz1Gram]
    exact ⟨hG1A_decomp.1, hG1O0⟩
  have hGramU : sourceMinkowskiGram d n '' Usrc ⊆ U := by
    rintro G ⟨z, hzUsrc, rfl⟩
    rw [hU_eq]
    exact ⟨hUsrc_subVsrc hzUsrc, ⟨z, rfl⟩⟩
  have hdiff :
      DifferentiableOn ℂ
        (fun z => H (sourceMinkowskiGram d n z)) Usrc :=
    SourceVarietyHolomorphicOn.comp_sourceMinkowskiGram
      d n hH hGramU
  have hagree :
      (fun z => H (sourceMinkowskiGram d n z)) =ᶠ[nhds z1]
        (fun _ => 0) := by
    filter_upwards [hP_open.mem_nhds hz1P] with z hzP
    have hzUsrc : z ∈ Usrc := hzP.1
    have hzA0 : sourceMinkowskiGram d n z ∈ A0 := hzP.2.1
    have hzO0 : sourceMinkowskiGram d n z ∈ O0 := hzP.2.2
    have hGvar : sourceMinkowskiGram d n z ∈ sourceComplexGramVariety d n :=
      ⟨z, rfl⟩
    have hGO : sourceMinkowskiGram d n z ∈ O := by
      rw [hO_eq]
      exact ⟨hzO0, hGvar⟩
    have hGrank :
        sourceMinkowskiGram d n z ∈
          sourceSymmetricRankExactStratum n (d + 1) :=
      hO_rank hGO
    have hGU : sourceMinkowskiGram d n z ∈ U := by
      rw [hU_eq]
      exact ⟨hUsrc_subVsrc hzUsrc, hGvar⟩
    have hGA : sourceMinkowskiGram d n z ∈ A := by
      rw [hA_eq]
      exact ⟨hzA0, hGU, hGrank⟩
    exact hA_zero hGA
  have hzero_src :
      Set.EqOn (fun z => H (sourceMinkowskiGram d n z)) (fun _ => 0) Usrc :=
    identity_theorem_product hUsrc_open hUsrc_conn hdiff
      (differentiableOn_const (c := (0 : ℂ))) hz1Usrc hagree
  have hO_subU : O ⊆ U := by
    intro G hGO
    rcases hO_surj G hGO with ⟨z, hzUsrc, hGram⟩
    rw [hU_eq]
    have hGvar : G ∈ sourceComplexGramVariety d n := by
      rw [hO_eq] at hGO
      exact hGO.2
    refine ⟨?_, hGvar⟩
    rw [← hGram]
    exact hUsrc_subVsrc hzUsrc
  refine ⟨O, hZ0O, ?_, ?_⟩
  · refine ⟨O0 ∩ U0, hO0_open.inter hU0_open, ?_⟩
    ext G
    constructor
    · intro hGO
      have hGO' := hGO
      rw [hO_eq] at hGO'
      have hGU := hO_subU hGO
      have hGU' := hGU
      rw [hU_eq] at hGU'
      exact ⟨⟨hGO'.1, hGU'.1⟩, hGU, hO_rank hGO⟩
    · intro hG
      have hGvar : G ∈ sourceComplexGramVariety d n := by
        have hGU := hG.2.1
        rw [hU_eq] at hGU
        exact hGU.2
      rw [hO_eq]
      exact ⟨hG.1.1, hGvar⟩
  · intro G hGO
    rcases hO_surj G hGO with ⟨z, hzUsrc, hGram⟩
    have hz_zero := hzero_src hzUsrc
    simpa [hGram] using hz_zero

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

/-- Topological assembly for the connected regular-locus theorem.  If the
rank-exact locus is dense in a connected source-variety domain and every point
has arbitrarily small relatively open neighborhoods with connected rank-exact
part, then the whole rank-exact locus in the domain is connected. -/
theorem sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_conn : IsConnected U)
    (hdense :
      U ⊆ closure
        (U ∩ sourceSymmetricRankExactStratum n (d + 1)))
    (hlocal :
      ∀ Z, Z ∈ U →
        ∀ N0 : Set (Fin n → Fin n → ℂ), IsOpen N0 → Z ∈ N0 →
          ∃ V : Set (Fin n → Fin n → ℂ),
            Z ∈ V ∧
            IsRelOpenInSourceComplexGramVariety d n V ∧
            V ⊆ U ∩ N0 ∧
            IsConnected
              (V ∩ sourceSymmetricRankExactStratum n (d + 1))) :
    IsConnected
      (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  let R : Set (Fin n → Fin n → ℂ) :=
    sourceSymmetricRankExactStratum n (d + 1)
  let S : Set (Fin n → Fin n → ℂ) := U ∩ R
  refine ⟨?_, ?_⟩
  · rcases hU_conn.1 with ⟨Z, hZU⟩
    rcases hlocal Z hZU Set.univ isOpen_univ trivial with
      ⟨V, _hZV, _hV_rel, hV_sub, hVreg_conn⟩
    rcases hVreg_conn.1 with ⟨Y, hYV, hYR⟩
    exact ⟨Y, (hV_sub hYV).1, hYR⟩
  · intro O1 O2 hO1 hO2 hS_cover hS_O1 hS_O2
    let A : Set (Fin n → Fin n → ℂ) := S ∩ O1
    let B : Set (Fin n → Fin n → ℂ) := S ∩ O2
    have hS_subset_AB : S ⊆ A ∪ B := by
      intro Y hYS
      rcases hS_cover hYS with hYO1 | hYO2
      · exact Or.inl ⟨hYS, hYO1⟩
      · exact Or.inr ⟨hYS, hYO2⟩
    have hU_subset_closure_AB : U ⊆ closure A ∪ closure B := by
      intro Z hZU
      have hZclS : Z ∈ closure S := by
        simpa [S, R] using hdense hZU
      have hZclUnion : Z ∈ closure (A ∪ B) :=
        closure_mono hS_subset_AB hZclS
      simpa [closure_union] using hZclUnion
    have hclosure_inter_nonempty :
        (U ∩ closure A ∩ closure B).Nonempty := by
      by_cases hinter : (U ∩ closure A ∩ closure B).Nonempty
      · exact hinter
      · have hno : ∀ Z, Z ∈ U → Z ∈ closure A → Z ∈ closure B → False := by
          intro Z hZU hZA hZB
          exact hinter ⟨Z, ⟨hZU, hZA⟩, hZB⟩
        let OA : Set (Fin n → Fin n → ℂ) := (closure B)ᶜ
        let OB : Set (Fin n → Fin n → ℂ) := (closure A)ᶜ
        have hOA_open : IsOpen OA := isClosed_closure.isOpen_compl
        have hOB_open : IsOpen OB := isClosed_closure.isOpen_compl
        have hU_sub_open : U ⊆ OA ∪ OB := by
          intro Z hZU
          rcases hU_subset_closure_AB hZU with hZA | hZB
          · have hZnotB : Z ∉ closure B :=
              fun hZB => hno Z hZU hZA hZB
            exact Or.inl hZnotB
          · have hZnotA : Z ∉ closure A :=
              fun hZA => hno Z hZU hZA hZB
            exact Or.inr hZnotA
        have hU_OA_nonempty : (U ∩ OA).Nonempty := by
          rcases hS_O1 with ⟨Y, hYS, hYO1⟩
          have hYA : Y ∈ A := ⟨hYS, hYO1⟩
          have hYclA : Y ∈ closure A := subset_closure hYA
          have hYnotB : Y ∉ closure B :=
            fun hYB => hno Y hYS.1 hYclA hYB
          exact ⟨Y, hYS.1, hYnotB⟩
        have hU_OB_nonempty : (U ∩ OB).Nonempty := by
          rcases hS_O2 with ⟨Y, hYS, hYO2⟩
          have hYB : Y ∈ B := ⟨hYS, hYO2⟩
          have hYclB : Y ∈ closure B := subset_closure hYB
          have hYnotA : Y ∉ closure A :=
            fun hYA => hno Y hYS.1 hYA hYclB
          exact ⟨Y, hYS.1, hYnotA⟩
        exfalso
        rcases hU_conn.2 OA OB hOA_open hOB_open hU_sub_open
            hU_OA_nonempty hU_OB_nonempty with
          ⟨Z, hZU, hZOA, hZOB⟩
        rcases hU_subset_closure_AB hZU with hZA | hZB
        · exact hZOB hZA
        · exact hZOA hZB
    rcases hclosure_inter_nonempty with ⟨Z0, hZ0U_clA, hZ0clB⟩
    have hZ0U : Z0 ∈ U := hZ0U_clA.1
    have hZ0clA : Z0 ∈ closure A := hZ0U_clA.2
    rcases hlocal Z0 hZ0U Set.univ isOpen_univ trivial with
      ⟨V, hZ0V, hV_rel, hV_sub, hVreg_conn⟩
    rcases hV_rel with ⟨V0, hV0_open, hV_eq⟩
    have hZ0V0 : Z0 ∈ V0 := by
      rw [hV_eq] at hZ0V
      exact hZ0V.1
    have hVreg_sub_S : V ∩ R ⊆ S := by
      intro Y hY
      exact ⟨(hV_sub hY.1).1, hY.2⟩
    have hVreg_cover : V ∩ R ⊆ O1 ∪ O2 :=
      hVreg_sub_S.trans hS_cover
    have hVreg_O1_nonempty : ((V ∩ R) ∩ O1).Nonempty := by
      rw [mem_closure_iff] at hZ0clA
      rcases hZ0clA V0 hV0_open hZ0V0 with ⟨Y, hYV0, hYA⟩
      have hYR : Y ∈ R := hYA.1.2
      have hYvar : Y ∈ sourceComplexGramVariety d n :=
        sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
          d n (d + 1) le_rfl (by simpa [R] using hYR)
      have hYV : Y ∈ V := by
        rw [hV_eq]
        exact ⟨hYV0, hYvar⟩
      exact ⟨Y, ⟨hYV, hYR⟩, hYA.2⟩
    have hVreg_O2_nonempty : ((V ∩ R) ∩ O2).Nonempty := by
      rw [mem_closure_iff] at hZ0clB
      rcases hZ0clB V0 hV0_open hZ0V0 with ⟨Y, hYV0, hYB⟩
      have hYR : Y ∈ R := hYB.1.2
      have hYvar : Y ∈ sourceComplexGramVariety d n :=
        sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
          d n (d + 1) le_rfl (by simpa [R] using hYR)
      have hYV : Y ∈ V := by
        rw [hV_eq]
        exact ⟨hYV0, hYvar⟩
      exact ⟨Y, ⟨hYV, hYR⟩, hYB.2⟩
    rcases hVreg_conn.2 O1 O2 hO1 hO2 hVreg_cover
        hVreg_O1_nonempty hVreg_O2_nonempty with
      ⟨Y, hYVreg, hYO1O2⟩
    exact ⟨Y, hVreg_sub_S hYVreg, hYO1O2⟩

/-- Rank-exact source-variety identity principle once the regular rank stratum
inside the domain is connected.  This is the global topological propagation
step after the local analytic continuation theorem: the remaining geometric
input for the strict source branch is the connectedness of
`U ∩ sourceSymmetricRankExactStratum n (d + 1)`. -/
theorem sourceComplexGramVariety_rankExact_identity_principle_of_connected
    (d n : ℕ)
    (hD : d + 1 < n)
    {U W : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hUreg_conn :
      IsConnected (U ∩ sourceSymmetricRankExactStratum n (d + 1)))
    (hW_rel : IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0
      (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  let R : Set (Fin n → Fin n → ℂ) :=
    sourceSymmetricRankExactStratum n (d + 1)
  let Ureg : Set (Fin n → Fin n → ℂ) := U ∩ R
  let A0 : Set (Fin n → Fin n → ℂ) :=
    {Z | ∃ O : Set (Fin n → Fin n → ℂ),
      IsOpen O ∧ Z ∈ O ∧ Set.EqOn H 0 (O ∩ Ureg)}
  let A : Set (Fin n → Fin n → ℂ) := A0 ∩ Ureg
  have hA0_open : IsOpen A0 := by
    rw [isOpen_iff_forall_mem_open]
    intro Z hZA0
    rcases hZA0 with ⟨O, hO_open, hZO, hO_zero⟩
    refine ⟨O, ?_, hO_open, hZO⟩
    intro Y hYO
    exact ⟨O, hO_open, hYO, hO_zero⟩
  have hA_rel :
      ∃ A0', IsOpen A0' ∧
        A = A0' ∩ (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
    refine ⟨A0, hA0_open, ?_⟩
    rfl
  have hA_zero : Set.EqOn H 0 A := by
    intro Z hZA
    rcases hZA.1 with ⟨O, _hO_open, hZO, hO_zero⟩
    exact hO_zero ⟨hZO, hZA.2⟩
  have hA_nonempty : A.Nonempty := by
    have hDle : d + 1 ≤ n := Nat.le_of_lt hD
    rcases hW_rel with ⟨W0, hW0_open, hW_eq⟩
    rcases sourceComplexGramVariety_relOpen_inter_rankExact_nonempty
        d n hDle ⟨W0, hW0_open, hW_eq⟩ hW_ne with
      ⟨Z, hZW, hZR⟩
    have hZW0 : Z ∈ W0 := by
      rw [hW_eq] at hZW
      exact hZW.1
    have hZU : Z ∈ U := hW_sub hZW
    refine ⟨Z, ?_⟩
    refine ⟨?_, ⟨hZU, by simpa [R] using hZR⟩⟩
    refine ⟨W0, hW0_open, hZW0, ?_⟩
    intro Y hY
    have hYvar : Y ∈ sourceComplexGramVariety d n :=
      sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
        d n (d + 1) le_rfl (by simpa [Ureg, R] using hY.2.2)
    have hYW : Y ∈ W := by
      rw [hW_eq]
      exact ⟨hY.1, hYvar⟩
    exact hW_zero hYW
  let Asub : Set Ureg := {x | (x : Fin n → Fin n → ℂ) ∈ A}
  have hAsub_open : IsOpen Asub := by
    have hpre : Asub = Subtype.val ⁻¹' A0 := by
      ext x
      simp [Asub, A]
    rw [hpre]
    exact hA0_open.preimage continuous_subtype_val
  have hAsub_nonempty : Asub.Nonempty := by
    rcases hA_nonempty with ⟨Z, hZA⟩
    exact ⟨⟨Z, hZA.2⟩, hZA⟩
  have hAsub_compl_open : IsOpen (Asubᶜ) := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx_not
    have hx_not_A : (x : Fin n → Fin n → ℂ) ∉ A := by
      simpa [Asub] using hx_not
    have hx_not_closure : (x : Fin n → Fin n → ℂ) ∉ closure A := by
      intro hx_closure
      rcases sourceComplexGramVariety_rankExact_local_identity_near_point
          d n hD hU_rel hH x.property.1
          (by simpa [Ureg, R] using x.property.2)
          hA_rel hx_closure hA_zero with
        ⟨V, hxV, hV_rel, hV_zero⟩
      rcases hV_rel with ⟨V0, hV0_open, hV_eq⟩
      have hxV0 : (x : Fin n → Fin n → ℂ) ∈ V0 := by
        rw [hV_eq] at hxV
        exact hxV.1
      have hxA0 : (x : Fin n → Fin n → ℂ) ∈ A0 := by
        refine ⟨V0, hV0_open, hxV0, ?_⟩
        intro Y hY
        exact hV_zero (by simpa [hV_eq] using hY)
      have hxA : (x : Fin n → Fin n → ℂ) ∈ A := ⟨hxA0, x.property⟩
      exact hx_not_A hxA
    let Nsub : Set Ureg := Subtype.val ⁻¹' ((closure A)ᶜ)
    refine ⟨Nsub, ?_, ?_, ?_⟩
    · intro y hyN hyA
      have hyA_ambient : (y : Fin n → Fin n → ℂ) ∈ A := by
        simpa [Asub] using hyA
      exact hyN (subset_closure hyA_ambient)
    · exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
    · exact hx_not_closure
  have hAsub_clopen : IsClopen Asub :=
    ⟨⟨hAsub_compl_open⟩, hAsub_open⟩
  haveI : ConnectedSpace Ureg :=
    isConnected_iff_connectedSpace.mp hUreg_conn
  have hAsub_univ : Asub = Set.univ :=
    IsClopen.eq_univ hAsub_clopen hAsub_nonempty
  intro Z hZUreg
  have hZA : Z ∈ A := by
    have hx : (⟨Z, by simpa [Ureg, R] using hZUreg⟩ : Ureg) ∈ Asub := by
      rw [hAsub_univ]
      trivial
    simpa [Asub] using hx
  exact hA_zero hZA

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

/-- The regular rank stratum is connected inside every connected relatively
open source complex Gram-variety domain in the strict range. -/
theorem sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
    (d n : ℕ)
    (hD : d + 1 < n)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U) :
    IsConnected (U ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  exact
    sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis
      d n hU_conn
      (sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
        d n (Nat.le_of_lt hD) hU_rel)
      (by
        intro Z hZU N0 hN0_open hZN0
        rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
        have hZU0 : Z ∈ U0 := by
          rw [hU_eq] at hZU
          exact hZU.1
        have hZvar : Z ∈ sourceComplexGramVariety d n := by
          rw [hU_eq] at hZU
          exact hZU.2
        rcases sourceComplexGramVariety_local_rankExact_connected_basis
            d n hD hZvar (hU0_open.inter hN0_open) ⟨hZU0, hZN0⟩ with
          ⟨V, hZV, hV_rel, hV_sub, hV_conn⟩
        refine ⟨V, hZV, hV_rel, ?_, hV_conn⟩
        intro G hGV
        rcases hV_sub hGV with ⟨hGU0N0, hGvar⟩
        exact ⟨by
          rw [hU_eq]
          exact ⟨hGU0N0.1, hGvar⟩, hGU0N0.2⟩)

/-- Strict-range rank-exact source-variety identity principle, with the
connectedness of the regular rank stratum supplied by the local-basis theorem. -/
theorem sourceComplexGramVariety_rankExact_identity_principle
    (d n : ℕ)
    (hD : d + 1 < n)
    {U W : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U)
    (hW_rel : IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0
      (U ∩ sourceSymmetricRankExactStratum n (d + 1)) :=
  sourceComplexGramVariety_rankExact_identity_principle_of_connected
    d n hD hU_rel
    (sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
      d n hD hU_rel hU_conn)
    hW_rel hW_ne hW_sub hH hW_zero

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

/-- Full hard-range source-variety identity principle once the regular rank
stratum inside the connected domain is connected.  The remaining theorem-2
source-side geometric input is the connectedness of
`U ∩ sourceSymmetricRankExactStratum n (d + 1)`. -/
theorem sourceComplexGramVariety_identity_principle_of_connected_rankExact
    (d n : ℕ)
    (hD : d + 1 < n)
    {U W : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hUreg_conn :
      IsConnected (U ∩ sourceSymmetricRankExactStratum n (d + 1)))
    (hW_rel : IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U := by
  have hDle : d + 1 ≤ n := Nat.le_of_lt hD
  have hzero_rankExact :
      Set.EqOn H 0
        (U ∩ sourceSymmetricRankExactStratum n (d + 1)) :=
    sourceComplexGramVariety_rankExact_identity_principle_of_connected
      d n hD hU_rel hUreg_conn hW_rel hW_ne hW_sub hH hW_zero
  exact
    sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
      d n hDle hU_rel (SourceVarietyHolomorphicOn.continuousOn d n hH)
      hzero_rankExact

/-- Source complex Gram-variety identity principle in all arities.  The easy
branch uses full symmetric coordinates; the strict branch uses the connected
regular-rank theorem proved from the local Hall-Wightman Schur chart. -/
theorem sourceComplexGramVariety_identity_principle
    (d n : ℕ)
    {U W : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U)
    (hW_rel : IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U := by
  by_cases hn : n ≤ d + 1
  · exact
      sourceComplexGramVariety_identity_principle_easy
        d n hn hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_zero
  · have hD : d + 1 < n := by omega
    exact
      sourceComplexGramVariety_identity_principle_of_connected_rankExact
        d n hD hU_rel
        (sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
          d n hD hU_rel hU_conn)
        hW_rel hW_ne hW_sub hH hW_zero

end BHW
