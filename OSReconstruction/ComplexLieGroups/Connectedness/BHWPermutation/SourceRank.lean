import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceCoefficient

/-!
# Source Gram rank predicates

This file contains the scalar-rank predicates used to split the
Hall-Wightman same-source-Gram analysis.  These predicates live on scalar Gram
matrices; they are not local regularity predicates for the Gram map.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Rank of a source Gram matrix in Hall-Wightman's scalar-product
coordinates. -/
def sourceGramMatrixRank
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ) : ℕ :=
  Matrix.rank Z

/-- Rank of the scalar Gram matrix attached to a source configuration. -/
def sourceConfigGramMatrixRank
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : ℕ :=
  sourceGramMatrixRank n (sourceMinkowskiGram d n z)

/-- Hall-Wightman's orbit-rank branch for Lemma 2. -/
def HWSourceGramOrbitRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  min d n ≤ sourceGramMatrixRank n Z

/-- Hall-Wightman's low-rank branch for Lemma 2. -/
def HWSourceGramLowRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  sourceGramMatrixRank n Z < min d n

/-- Orbit-rank branch at a source configuration. -/
def HWSourceGramOrbitRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramOrbitRank d n (sourceMinkowskiGram d n z)

/-- Low-rank branch at a source configuration. -/
def HWSourceGramLowRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramLowRank d n (sourceMinkowskiGram d n z)

/-- Maximal scalar rank for the local source-variety chart branch.  This is
the maximal possible rank in spacetime dimension `d + 1`, not the Lemma-2
orbit threshold. -/
def HWSourceGramMaxRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  min (d + 1) n ≤ sourceGramMatrixRank n Z

/-- Exceptional scalar rank for the local source-variety chart branch. -/
def HWSourceGramExceptionalRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  sourceGramMatrixRank n Z < min (d + 1) n

/-- Maximal scalar rank at a source configuration. -/
def HWSourceGramMaxRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramMaxRank d n (sourceMinkowskiGram d n z)

/-- Exceptional scalar rank at a source configuration. -/
def HWSourceGramExceptionalRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramExceptionalRank d n (sourceMinkowskiGram d n z)

/-- The left-adjoint map of the complex Minkowski form restricted to a source
subspace. -/
def restrictedMinkowskiLeftMap
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    M →ₗ[ℂ] (M →ₗ[ℂ] ℂ) where
  toFun x :=
    { toFun := fun y =>
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)
      map_add' := by
        intro y z
        exact sourceComplexMinkowskiInner_add_right
          d (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)
          (z : Fin (d + 1) → ℂ)
      map_smul' := by
        intro c y
        exact sourceComplexMinkowskiInner_smul_right
          d c (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) }
  map_add' := by
    intro x y
    ext z
    exact sourceComplexMinkowskiInner_add_left
      d (x : Fin (d + 1) → ℂ)
      (y : Fin (d + 1) → ℂ)
      (z : Fin (d + 1) → ℂ)
  map_smul' := by
    intro c x
    ext y
    exact sourceComplexMinkowskiInner_smul_left
      d c (x : Fin (d + 1) → ℂ)
      (y : Fin (d + 1) → ℂ)

/-- Radical of the complex Minkowski form restricted to a source subspace. -/
def restrictedMinkowskiRadical
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    Submodule ℂ M :=
  LinearMap.ker (restrictedMinkowskiLeftMap d M)

/-- Rank of the complex Minkowski form restricted to a source subspace. -/
def restrictedMinkowskiRank
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) : ℕ :=
  Module.finrank ℂ M - Module.finrank ℂ (restrictedMinkowskiRadical d M)

/-- Nondegeneracy of the complex Minkowski form after restriction to a source
subspace. -/
def ComplexMinkowskiNondegenerateSubspace
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) : Prop :=
  ∀ x : M,
    (∀ y : M,
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (y : Fin (d + 1) → ℂ) = 0) →
      x = 0

/-- On a nondegenerate restricted source subspace, the restricted radical is
trivial. -/
theorem restrictedMinkowskiRadical_eq_bot_of_nondegenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hndeg : ComplexMinkowskiNondegenerateSubspace d M) :
    restrictedMinkowskiRadical d M = ⊥ := by
  ext x
  constructor
  · intro hx
    have hxmap : restrictedMinkowskiLeftMap d M x = 0 := by
      simpa [restrictedMinkowskiRadical] using hx
    have horth :
        ∀ y : M,
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ) = 0 := by
      intro y
      have h :=
        congrArg (fun L : M →ₗ[ℂ] ℂ => L y) hxmap
      simpa [restrictedMinkowskiLeftMap] using h
    have hx0 : x = 0 := hndeg x horth
    simp [hx0]
  · intro hx
    rw [restrictedMinkowskiRadical, LinearMap.mem_ker]
    ext y
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp [restrictedMinkowskiLeftMap, sourceComplexMinkowskiInner]

/-- On a nondegenerate restricted source subspace, restricted rank is the
dimension of the subspace. -/
theorem restrictedMinkowskiRank_eq_finrank_of_nondegenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hndeg : ComplexMinkowskiNondegenerateSubspace d M) :
    restrictedMinkowskiRank d M = Module.finrank ℂ M := by
  rw [restrictedMinkowskiRank,
    restrictedMinkowskiRadical_eq_bot_of_nondegenerate d hndeg]
  simp

/-- The ambient vector-to-dual map induced by the complex Minkowski pairing on a
source subspace.  Its kernel is the Minkowski orthogonal complement. -/
def complexMinkowskiToSubmoduleDual
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] Module.Dual ℂ M where
  toFun v :=
    { toFun := fun x => sourceComplexMinkowskiInner d v (x : Fin (d + 1) → ℂ)
      map_add' := by
        intro x y
        exact sourceComplexMinkowskiInner_add_right
          d v (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ)
      map_smul' := by
        intro c x
        exact sourceComplexMinkowskiInner_smul_right
          d c v (x : Fin (d + 1) → ℂ) }
  map_add' := by
    intro u v
    ext x
    exact sourceComplexMinkowskiInner_add_left
      d u v (x : Fin (d + 1) → ℂ)
  map_smul' := by
    intro c v
    ext x
    exact sourceComplexMinkowskiInner_smul_left
      d c v (x : Fin (d + 1) → ℂ)

/-- The complex Minkowski orthogonal complement of a source subspace. -/
def complexMinkowskiOrthogonalSubmodule
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  LinearMap.ker (complexMinkowskiToSubmoduleDual d M)

@[simp]
theorem mem_complexMinkowskiOrthogonalSubmodule_iff
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ))
    (v : Fin (d + 1) → ℂ) :
    v ∈ complexMinkowskiOrthogonalSubmodule d M ↔
      ∀ x : M,
        sourceComplexMinkowskiInner d v (x : Fin (d + 1) → ℂ) = 0 := by
  rw [complexMinkowskiOrthogonalSubmodule, LinearMap.mem_ker]
  constructor
  · intro hv x
    have h := congrArg (fun f : Module.Dual ℂ M => f x) hv
    simpa [complexMinkowskiToSubmoduleDual] using h
  · intro hv
    ext x
    simpa [complexMinkowskiToSubmoduleDual] using hv x

/-- If a source subspace has dimension below the ambient spacetime dimension,
then its complex Minkowski orthogonal complement is nontrivial. -/
theorem complexMinkowskiOrthogonalSubmodule_ne_bot_of_finrank_lt
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hfin : Module.finrank ℂ M < d + 1) :
    complexMinkowskiOrthogonalSubmodule d M ≠ ⊥ := by
  let L := complexMinkowskiToSubmoduleDual d M
  have hrange_le_dual :
      Module.finrank ℂ (LinearMap.range L) ≤
        Module.finrank ℂ (Module.Dual ℂ M) :=
    Submodule.finrank_le (LinearMap.range L)
  have hrange_le :
      Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ M := by
    simpa [Subspace.dual_finrank_eq] using hrange_le_dual
  have hrange_lt :
      Module.finrank ℂ (LinearMap.range L) < d + 1 :=
    lt_of_le_of_lt hrange_le hfin
  have hsum :
      Module.finrank ℂ (LinearMap.range L) +
          Module.finrank ℂ (LinearMap.ker L) =
        d + 1 := by
    simpa [L, Module.finrank_fin_fun] using
      LinearMap.finrank_range_add_finrank_ker L
  have hker_pos : 0 < Module.finrank ℂ (LinearMap.ker L) := by
    omega
  have hker_ne : LinearMap.ker L ≠ ⊥ :=
    (Submodule.one_le_finrank_iff).1 (Nat.succ_le_of_lt hker_pos)
  simpa [complexMinkowskiOrthogonalSubmodule, L] using hker_ne

/-- A coefficient-evaluated source vector lies in the restricted radical
exactly when it pairs to zero with every coefficient-evaluated source vector. -/
theorem sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → ℂ) :
    let evalZ := sourceCoefficientEval d n z
    let M := LinearMap.range evalZ
    (⟨evalZ a, ⟨a, rfl⟩⟩ : M) ∈
        restrictedMinkowskiRadical d M ↔
      ∀ b : Fin n → ℂ,
        sourceComplexMinkowskiInner d (evalZ a) (evalZ b) = 0 := by
  intro evalZ M
  rw [restrictedMinkowskiRadical, LinearMap.mem_ker]
  constructor
  · intro h b
    have hlin :
        restrictedMinkowskiLeftMap d M
          (⟨evalZ a, ⟨a, rfl⟩⟩ : M) = 0 := h
    have happ :=
      congrArg
        (fun L : M →ₗ[ℂ] ℂ => L (⟨evalZ b, ⟨b, rfl⟩⟩ : M))
        hlin
    simpa [restrictedMinkowskiLeftMap] using happ
  · intro h
    ext y
    rcases y with ⟨yv, b, rfl⟩
    simpa [restrictedMinkowskiLeftMap] using h b

/-- The scalar Gram kernel is the preimage of the restricted Minkowski
radical under coefficient evaluation. -/
theorem sourceCoefficientGramKernel_eq_eval_preimage_radical
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceCoefficientGramKernel n (sourceMinkowskiGram d n z) =
      ((restrictedMinkowskiRadical d
          (LinearMap.range (sourceCoefficientEval d n z))).map
        (Submodule.subtype
          (LinearMap.range (sourceCoefficientEval d n z)))).comap
        (sourceCoefficientEval d n z) := by
  let evalZ := sourceCoefficientEval d n z
  let M := LinearMap.range evalZ
  let rad := restrictedMinkowskiRadical d M
  ext a
  have hmap :
      evalZ a ∈ rad.map (Submodule.subtype M) ↔
        (⟨evalZ a, ⟨a, rfl⟩⟩ : M) ∈ rad := by
    constructor
    · rintro ⟨x, hx, hxval⟩
      have hx_eq : x = (⟨evalZ a, ⟨a, rfl⟩⟩ : M) :=
        Subtype.ext hxval
      simpa [hx_eq] using hx
    · intro hx
      exact ⟨(⟨evalZ a, ⟨a, rfl⟩⟩ : M), hx, rfl⟩
  change
    a ∈ LinearMap.ker
        (sourceCoefficientGramMap n (sourceMinkowskiGram d n z)) ↔
      evalZ a ∈ rad.map (Submodule.subtype M)
  rw [LinearMap.mem_ker, hmap,
    sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero]
  simpa [evalZ, M, rad] using
    (sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff d n z a).symm

/-- The scalar Gram matrix rank is the finrank of the range of the associated
coefficient Gram map. -/
theorem sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap
    (n : ℕ)
    (G : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n G =
      Module.finrank ℂ (LinearMap.range (sourceCoefficientGramMap n G)) := by
  rw [sourceGramMatrixRank]
  rw [← Matrix.rank_transpose G]
  rw [Matrix.rank_eq_finrank_range_toLin (Gᵀ)
    (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))]
  rw [Matrix.toLin_eq_toLin']
  rw [← sourceCoefficientGramMap_eq_toLin_transpose]

/-- The range rank of the scalar Gram map is the rank of the complex
Minkowski form restricted to the source span. -/
theorem finrank_range_sourceCoefficientGramMap_eq_restrictedRank
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Module.finrank ℂ
        (LinearMap.range
          (sourceCoefficientGramMap n (sourceMinkowskiGram d n z))) =
      restrictedMinkowskiRank d
        (LinearMap.range (sourceCoefficientEval d n z)) := by
  let evalZ : (Fin n → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    sourceCoefficientEval d n z
  let M := LinearMap.range evalZ
  let rad := restrictedMinkowskiRadical d M
  let gramMap : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    sourceCoefficientGramMap n (sourceMinkowskiGram d n z)
  have hK_le : LinearMap.ker evalZ ≤ LinearMap.ker gramMap := by
    simpa [evalZ, gramMap, sourceCoefficientGramKernel] using
      sourceCoefficientEval_ker_le_gramKernel d n z
  let liftGram : ((Fin n → ℂ) ⧸ LinearMap.ker evalZ) →ₗ[ℂ] (Fin n → ℂ) :=
    (LinearMap.ker evalZ).liftQ gramMap hK_le
  have hrange_lift :
      LinearMap.range liftGram = LinearMap.range gramMap := by
    simpa [liftGram] using
      Submodule.range_liftQ
        (p := LinearMap.ker evalZ) (f := gramMap) hK_le
  have hker_eq :
      LinearMap.ker liftGram =
        rad.comap
          (evalZ.quotKerEquivRange :
            ((Fin n → ℂ) ⧸ LinearMap.ker evalZ) →ₗ[ℂ] M) := by
    ext q
    induction q using Quotient.inductionOn with
    | h a =>
        change liftGram (Submodule.Quotient.mk a) = 0 ↔
          evalZ.quotKerEquivRange (Submodule.Quotient.mk a) ∈ rad
        simp only [liftGram, Submodule.liftQ_apply]
        rw [sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero]
        simpa [evalZ, M, rad] using
          (sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff d n z a).symm
  have hker_finrank :
      Module.finrank ℂ (LinearMap.ker liftGram) =
        Module.finrank ℂ rad := by
    rw [hker_eq]
    exact (LinearEquiv.ofSubmodule' evalZ.quotKerEquivRange rad).finrank_eq
  have hquot_finrank :
      Module.finrank ℂ ((Fin n → ℂ) ⧸ LinearMap.ker evalZ) =
        Module.finrank ℂ M :=
    evalZ.quotKerEquivRange.finrank_eq
  have hnullity :
      Module.finrank ℂ (LinearMap.range liftGram) +
          Module.finrank ℂ (LinearMap.ker liftGram) =
        Module.finrank ℂ ((Fin n → ℂ) ⧸ LinearMap.ker evalZ) :=
    LinearMap.finrank_range_add_finrank_ker liftGram
  have hsum :
      Module.finrank ℂ (LinearMap.range gramMap) +
          Module.finrank ℂ rad =
        Module.finrank ℂ M := by
    calc
      Module.finrank ℂ (LinearMap.range gramMap) +
          Module.finrank ℂ rad
          = Module.finrank ℂ (LinearMap.range liftGram) +
              Module.finrank ℂ (LinearMap.ker liftGram) := by
                rw [hrange_lift, hker_finrank]
      _ = Module.finrank ℂ ((Fin n → ℂ) ⧸ LinearMap.ker evalZ) := hnullity
      _ = Module.finrank ℂ M := hquot_finrank
  change
    Module.finrank ℂ (LinearMap.range gramMap) =
      Module.finrank ℂ M - Module.finrank ℂ rad
  omega

/-- The scalar Gram rank is the restricted Minkowski rank of the source
span. -/
theorem sourceGramMatrixRank_eq_restrictedMinkowskiRank_range
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) =
      restrictedMinkowskiRank d
        (LinearMap.range (sourceCoefficientEval d n z)) := by
  rw [sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap]
  exact finrank_range_sourceCoefficientGramMap_eq_restrictedRank d n z

/-- If the restricted source span is nondegenerate, scalar Gram rank is the
dimension of the coefficient span. -/
theorem sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_range_nondegenerate
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hndeg :
      ComplexMinkowskiNondegenerateSubspace d
        (LinearMap.range (sourceCoefficientEval d n z))) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) =
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) := by
  rw [sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
  exact restrictedMinkowskiRank_eq_finrank_of_nondegenerate d hndeg

/-- Degeneracy of the restricted form is witnessed by a nonzero restricted
radical. -/
theorem restrictedMinkowskiRadical_nontrivial_of_degenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdeg : ¬ ComplexMinkowskiNondegenerateSubspace d M) :
    0 < Module.finrank ℂ (restrictedMinkowskiRadical d M) := by
  have hrad_ne : restrictedMinkowskiRadical d M ≠ ⊥ := by
    intro hbot
    apply hdeg
    intro x horth
    have hx_rad : x ∈ restrictedMinkowskiRadical d M := by
      rw [restrictedMinkowskiRadical, LinearMap.mem_ker]
      ext y
      simpa [restrictedMinkowskiLeftMap] using horth y
    have hx_bot : x ∈ (⊥ : Submodule ℂ M) := by
      simpa [hbot] using hx_rad
    simpa using hx_bot
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    ((Submodule.one_le_finrank_iff).2 hrad_ne)

/-- If the restricted form is degenerate, its restricted rank is strictly
smaller than the subspace dimension. -/
theorem restrictedMinkowskiRank_lt_finrank_of_degenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdeg : ¬ ComplexMinkowskiNondegenerateSubspace d M) :
    restrictedMinkowskiRank d M < Module.finrank ℂ M := by
  have hrad_pos :
      0 < Module.finrank ℂ (restrictedMinkowskiRadical d M) :=
    restrictedMinkowskiRadical_nontrivial_of_degenerate (d := d) hdeg
  have hrad_le :
      Module.finrank ℂ (restrictedMinkowskiRadical d M) ≤
        Module.finrank ℂ M :=
    Submodule.finrank_le (restrictedMinkowskiRadical d M)
  simp [restrictedMinkowskiRank]
  omega

/-- The source coefficient span is generated by at most `n` source vectors. -/
theorem finrank_range_sourceCoefficientEval_le
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) ≤ n := by
  have h := LinearMap.finrank_range_le (sourceCoefficientEval d n z)
  simpa [Module.finrank_fin_fun] using h

/-- A degenerate restricted source subspace is a proper subspace of the
ambient nondegenerate complex Minkowski space, hence has dimension at most
`d`. -/
theorem finrank_restrictedSpan_le_d_of_degenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdeg : ¬ ComplexMinkowskiNondegenerateSubspace d M) :
    Module.finrank ℂ M ≤ d := by
  have hM_ne_top : M ≠ ⊤ := by
    intro htop
    apply hdeg
    intro x horth
    apply Subtype.ext
    apply sourceComplexMinkowskiInner_left_nonDegenerate d
    intro v
    have hvM : v ∈ M := by
      rw [htop]
      exact Submodule.mem_top
    exact horth ⟨v, hvM⟩
  have hlt :
      Module.finrank ℂ M <
        Module.finrank ℂ (Fin (d + 1) → ℂ) :=
    Submodule.finrank_lt hM_ne_top
  have hlt' : Module.finrank ℂ M < d + 1 := by
    simpa [Module.finrank_fin_fun] using hlt
  exact Nat.lt_succ_iff.mp hlt'

/-- Degeneracy of the restricted source span forces Hall-Wightman's scalar
rank below the orbit-rank threshold. -/
theorem sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hdeg :
      ¬ ComplexMinkowskiNondegenerateSubspace d
        (LinearMap.range (sourceCoefficientEval d n z))) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) < min d n := by
  let M := LinearMap.range (sourceCoefficientEval d n z)
  have hM_le_n : Module.finrank ℂ M ≤ n :=
    finrank_range_sourceCoefficientEval_le d n z
  have hM_le_d : Module.finrank ℂ M ≤ d :=
    finrank_restrictedSpan_le_d_of_degenerate (d := d) hdeg
  have hrank_lt_M :
      restrictedMinkowskiRank d M < Module.finrank ℂ M :=
    restrictedMinkowskiRank_lt_finrank_of_degenerate (d := d) hdeg
  have hrank_lt_d : restrictedMinkowskiRank d M < d :=
    lt_of_lt_of_le hrank_lt_M hM_le_d
  have hrank_lt_n : restrictedMinkowskiRank d M < n :=
    lt_of_lt_of_le hrank_lt_M hM_le_n
  rw [sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
  exact lt_min hrank_lt_d hrank_lt_n

/-- In Hall-Wightman's high-rank branch, the source span is nondegenerate for
the restricted complex Minkowski form. -/
theorem hw_highRank_eval_range_nondegenerate
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z) :
    ComplexMinkowskiNondegenerateSubspace d
      (LinearMap.range (sourceCoefficientEval d n z)) := by
  by_contra hdeg
  have hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < min d n :=
    sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate d n z hdeg
  have hge :
      min d n ≤ sourceGramMatrixRank n (sourceMinkowskiGram d n z) := by
    simpa [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank] using hzRank
  exact (not_lt_of_ge hge) hlt

/-- In Hall-Wightman's high-rank branch, scalar Gram rank is the dimension of
the source coefficient span. -/
theorem sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_orbitRank
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) =
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) :=
  sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_range_nondegenerate
    d n (hw_highRank_eval_range_nondegenerate (d := d) (n := n) (z := z) hzRank)

/-- In the high-rank branch, if the scalar Gram rank is still below ambient
spacetime rank, then the source coefficient span is a proper-dimensional
subspace. -/
theorem sourceCoefficientEval_range_finrank_lt_spacetime_of_orbitRank_rank_lt_spacetime
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z)
    (hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) < d + 1 := by
  rw [sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_orbitRank
    d n hzRank] at hlt
  exact hlt

/-- In the high-rank but non-full-rank branch, the source coefficient span is a
proper subspace of complex spacetime. -/
theorem sourceCoefficientEval_range_ne_top_of_orbitRank_rank_lt_spacetime
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z)
    (hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    LinearMap.range (sourceCoefficientEval d n z) ≠ ⊤ := by
  intro htop
  have hfin_lt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) < d + 1 :=
    sourceCoefficientEval_range_finrank_lt_spacetime_of_orbitRank_rank_lt_spacetime
      d n hzRank hlt
  have hfin_top :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) = d + 1 := by
    rw [htop]
    simp
  rw [hfin_top] at hfin_lt
  exact (Nat.lt_irrefl (d + 1)) hfin_lt

/-- In the high-rank but non-full-rank branch, the Minkowski orthogonal
complement of the source span is nontrivial. -/
theorem sourceSpan_orthogonalComplement_nontrivial_of_orbitRank_rank_lt_spacetime
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z)
    (hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    complexMinkowskiOrthogonalSubmodule d
        (LinearMap.range (sourceCoefficientEval d n z)) ≠ ⊥ :=
  complexMinkowskiOrthogonalSubmodule_ne_bot_of_finrank_lt d
    (sourceCoefficientEval_range_finrank_lt_spacetime_of_orbitRank_rank_lt_spacetime
      d n hzRank hlt)

/-- If a source subspace has dimension below the ambient spacetime dimension,
then its complex Minkowski orthogonal complement contains a nonzero vector. -/
theorem exists_nonzero_mem_complexMinkowskiOrthogonalSubmodule_of_finrank_lt
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hfin : Module.finrank ℂ M < d + 1) :
    ∃ v : Fin (d + 1) → ℂ,
      v ∈ complexMinkowskiOrthogonalSubmodule d M ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot
    (complexMinkowskiOrthogonalSubmodule_ne_bot_of_finrank_lt d hfin)

/-- In the high-rank but non-full-rank branch, the source-span orthogonal
complement contains a nonzero vector. -/
theorem exists_nonzero_mem_sourceSpan_orthogonalComplement_of_orbitRank_rank_lt_spacetime
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z)
    (hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    ∃ v : Fin (d + 1) → ℂ,
      v ∈ complexMinkowskiOrthogonalSubmodule d
          (LinearMap.range (sourceCoefficientEval d n z)) ∧
        v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot
    (sourceSpan_orthogonalComplement_nontrivial_of_orbitRank_rank_lt_spacetime
      d n hzRank hlt)

/-- In the high-rank branch, the coefficient-evaluation kernel is exactly the
scalar Gram kernel. -/
theorem hw_highRank_eval_ker_eq_gramKernel
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z) :
    LinearMap.ker (sourceCoefficientEval d n z) =
      sourceCoefficientGramKernel n (sourceMinkowskiGram d n z) := by
  let evalZ := sourceCoefficientEval d n z
  apply le_antisymm
  · simpa [evalZ] using sourceCoefficientEval_ker_le_gramKernel d n z
  · intro a ha
    have ha0 :
        sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a = 0 := by
      simpa [sourceCoefficientGramKernel] using
        (LinearMap.mem_ker.mp ha)
    have hNondeg :
        ComplexMinkowskiNondegenerateSubspace d
          (LinearMap.range evalZ) :=
      hw_highRank_eval_range_nondegenerate (d := d) (n := n)
        (z := z) hzRank
    have horth :
        ∀ v : LinearMap.range evalZ,
          sourceComplexMinkowskiInner d
            ((⟨evalZ a, ⟨a, rfl⟩⟩ :
              LinearMap.range evalZ) : Fin (d + 1) → ℂ)
            (v : Fin (d + 1) → ℂ) = 0 := by
      intro v
      rcases v with ⟨_, b, rfl⟩
      exact
        (sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero
          d n z a).1 ha0 b
    have hEval_zero :
        (⟨evalZ a, ⟨a, rfl⟩⟩ : LinearMap.range evalZ) = 0 :=
      hNondeg ⟨evalZ a, ⟨a, rfl⟩⟩ horth
    have hval : evalZ a = 0 :=
      congrArg Subtype.val hEval_zero
    simpa [evalZ, LinearMap.mem_ker] using hval

/-- Same-source-Gram high-rank configurations have identical coefficient
evaluation kernels. -/
theorem hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (hzRank : HWSourceGramOrbitRankAt d n z) :
    LinearMap.ker (sourceCoefficientEval d n z) =
      LinearMap.ker (sourceCoefficientEval d n w) := by
  have hwRank : HWSourceGramOrbitRankAt d n w :=
    by
      simpa [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hgram] using
        hzRank
  calc
    LinearMap.ker (sourceCoefficientEval d n z)
        =
      sourceCoefficientGramKernel n (sourceMinkowskiGram d n z) :=
        hw_highRank_eval_ker_eq_gramKernel (d := d) (n := n)
          (z := z) hzRank
    _ =
      sourceCoefficientGramKernel n (sourceMinkowskiGram d n w) := by
        rw [hgram]
    _ = LinearMap.ker (sourceCoefficientEval d n w) :=
        (hw_highRank_eval_ker_eq_gramKernel (d := d) (n := n)
          (z := w) hwRank).symm

/-- The coefficient-quotient isometry induced by equality of coefficient
evaluation kernels. -/
noncomputable def hwHighRankSpanIsometryOfKernelEq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hker :
      LinearMap.ker (sourceCoefficientEval d n z) =
        LinearMap.ker (sourceCoefficientEval d n w)) :
    LinearMap.range (sourceCoefficientEval d n z) ≃ₗ[ℂ]
      LinearMap.range (sourceCoefficientEval d n w) :=
  let evalZ := sourceCoefficientEval d n z
  let evalW := sourceCoefficientEval d n w
  evalZ.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq
      (LinearMap.ker evalZ) (LinearMap.ker evalW) hker).trans
        evalW.quotKerEquivRange)

/-- The quotient-induced high-rank span isometry sends each coefficient
evaluation for `z` to the matching coefficient evaluation for `w`. -/
theorem hwHighRankSpanIsometry_apply_eval
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hker :
      LinearMap.ker (sourceCoefficientEval d n z) =
        LinearMap.ker (sourceCoefficientEval d n w))
    (a : Fin n → ℂ) :
    hwHighRankSpanIsometryOfKernelEq (d := d) (n := n)
        (z := z) (w := w) hker
      (⟨sourceCoefficientEval d n z a, ⟨a, rfl⟩⟩ :
        LinearMap.range (sourceCoefficientEval d n z)) =
      (⟨sourceCoefficientEval d n w a, ⟨a, rfl⟩⟩ :
        LinearMap.range (sourceCoefficientEval d n w)) := by
  apply Subtype.ext
  simp [hwHighRankSpanIsometryOfKernelEq,
    LinearMap.quotKerEquivRange_symm_apply_image,
    LinearMap.quotKerEquivRange_apply_mk,
    Submodule.quotEquivOfEq_mk]

/-- The well-defined span isometry in Hall-Wightman's high-rank branch.
The map is induced from the common coefficient quotient; it is not the
informal assignment `z i ↦ w i` until the coefficient kernels have been
proved equal. -/
structure HWHighRankSpanIsometryData
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) where
  M : Submodule ℂ (Fin (d + 1) → ℂ)
  N : Submodule ℂ (Fin (d + 1) → ℂ)
  M_eq_range :
    M = LinearMap.range (sourceCoefficientEval d n z)
  N_eq_range :
    N = LinearMap.range (sourceCoefficientEval d n w)
  M_nondegenerate :
    ComplexMinkowskiNondegenerateSubspace d M
  N_nondegenerate :
    ComplexMinkowskiNondegenerateSubspace d N
  z_mem : ∀ i, z i ∈ M
  w_mem : ∀ i, w i ∈ N
  T : M ≃ₗ[ℂ] N
  T_preserves :
    ∀ x y : M,
      sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (T x : Fin (d + 1) → ℂ)
          (T y : Fin (d + 1) → ℂ)
  T_z :
    ∀ i, T ⟨z i, z_mem i⟩ = ⟨w i, w_mem i⟩

/-- Same-source-Gram high-rank configurations have a well-defined
pairing-preserving isometry between their source spans. -/
noncomputable def hw_highRank_spanIsometryData_of_sameSourceGram
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hzRank : HWSourceGramOrbitRankAt d n z)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWHighRankSpanIsometryData d n z w := by
  let evalZ := sourceCoefficientEval d n z
  let evalW := sourceCoefficientEval d n w
  have hker : LinearMap.ker evalZ = LinearMap.ker evalW :=
    hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram
      (d := d) (n := n) (z := z) (w := w) hgram hzRank
  let T : LinearMap.range evalZ ≃ₗ[ℂ] LinearMap.range evalW :=
    hwHighRankSpanIsometryOfKernelEq (d := d) (n := n)
      (z := z) (w := w) hker
  have hwRank : HWSourceGramOrbitRankAt d n w := by
    simpa [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hgram] using
      hzRank
  refine
    { M := LinearMap.range evalZ
      N := LinearMap.range evalW
      M_eq_range := rfl
      N_eq_range := rfl
      M_nondegenerate :=
        hw_highRank_eval_range_nondegenerate (d := d) (n := n)
          (z := z) hzRank
      N_nondegenerate :=
        hw_highRank_eval_range_nondegenerate (d := d) (n := n)
          (z := w) hwRank
      z_mem := ?_
      w_mem := ?_
      T := T
      T_preserves := ?_
      T_z := ?_ }
  · intro i
    exact ⟨Pi.single i (1 : ℂ), by
      simpa [evalZ] using sourceCoefficientEval_single d n z i⟩
  · intro i
    exact ⟨Pi.single i (1 : ℂ), by
      simpa [evalW] using sourceCoefficientEval_single d n w i⟩
  · intro x y
    rcases x with ⟨xv, hxv⟩
    rcases hxv with ⟨ax, hax⟩
    rcases y with ⟨yv, hyv⟩
    rcases hyv with ⟨ay, hay⟩
    subst xv
    subst yv
    have hTx :
        T (⟨evalZ ax, ⟨ax, rfl⟩⟩ : LinearMap.range evalZ) =
          (⟨evalW ax, ⟨ax, rfl⟩⟩ : LinearMap.range evalW) := by
      simpa [T] using
        hwHighRankSpanIsometry_apply_eval (d := d) (n := n)
          (z := z) (w := w) hker ax
    have hTy :
        T (⟨evalZ ay, ⟨ay, rfl⟩⟩ : LinearMap.range evalZ) =
          (⟨evalW ay, ⟨ay, rfl⟩⟩ : LinearMap.range evalW) := by
      simpa [T] using
        hwHighRankSpanIsometry_apply_eval (d := d) (n := n)
          (z := z) (w := w) hker ay
    rw [hTx, hTy]
    rw [sourceCoefficientEval_pair_eq_sum_gram d n z ax ay]
    rw [sourceCoefficientEval_pair_eq_sum_gram d n w ax ay]
    apply Finset.sum_congr rfl
    intro j _
    simp [sourceCoefficientGramMap, hgram]
  · intro i
    have hsingle :
        T
          (⟨evalZ (Pi.single i (1 : ℂ)), ⟨Pi.single i (1 : ℂ), rfl⟩⟩ :
            LinearMap.range evalZ) =
          (⟨evalW (Pi.single i (1 : ℂ)), ⟨Pi.single i (1 : ℂ), rfl⟩⟩ :
            LinearMap.range evalW) := by
      simpa [T] using
        hwHighRankSpanIsometry_apply_eval (d := d) (n := n)
          (z := z) (w := w) hker (Pi.single i (1 : ℂ))
    simpa [evalZ, evalW, sourceCoefficientEval_single d n z i,
      sourceCoefficientEval_single d n w i] using hsingle

/-- The span-isometry data preserves the source Gram matrix. -/
theorem HWHighRankSpanIsometryData_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w) :
    sourceMinkowskiGram d n z = sourceMinkowskiGram d n w := by
  ext i j
  have hpres :=
    S.T_preserves ⟨z i, S.z_mem i⟩ ⟨z j, S.z_mem j⟩
  have hTi := S.T_z i
  have hTj := S.T_z j
  rw [sourceMinkowskiGram_apply_eq_complexInner,
    sourceMinkowskiGram_apply_eq_complexInner]
  simpa [hTi, hTj] using hpres

namespace HWHighRankSpanIsometryData

/-- The stored source span `M` has dimension equal to the scalar Gram rank of
the original configuration. -/
theorem M_finrank_eq_sourceGramRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w) :
    Module.finrank ℂ S.M =
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) := by
  have hndeg :
      ComplexMinkowskiNondegenerateSubspace d
        (LinearMap.range (sourceCoefficientEval d n z)) := by
    simpa [S.M_eq_range] using S.M_nondegenerate
  rw [S.M_eq_range]
  exact
    (sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_range_nondegenerate
      d n (z := z) hndeg).symm

/-- The stored target span `N` has dimension equal to the scalar Gram rank of the
target configuration. -/
theorem N_finrank_eq_sourceGramRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w) :
    Module.finrank ℂ S.N =
      sourceGramMatrixRank n (sourceMinkowskiGram d n w) := by
  have hndeg :
      ComplexMinkowskiNondegenerateSubspace d
        (LinearMap.range (sourceCoefficientEval d n w)) := by
    simpa [S.N_eq_range] using S.N_nondegenerate
  rw [S.N_eq_range]
  exact
    (sourceGramMatrixRank_eq_finrank_range_sourceCoefficientEval_of_range_nondegenerate
      d n (z := w) hndeg).symm

end HWHighRankSpanIsometryData

/-- In the high-rank but non-full-rank branch, the stored source span in the
span-isometry packet has nontrivial complex Minkowski orthogonal complement. -/
theorem sourceSpan_orthogonalComplement_nontrivial_of_proper
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w)
    (hproper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    complexMinkowskiOrthogonalSubmodule d S.M ≠ ⊥ := by
  apply complexMinkowskiOrthogonalSubmodule_ne_bot_of_finrank_lt d
  rw [HWHighRankSpanIsometryData.M_finrank_eq_sourceGramRank d n S]
  exact hproper

/-- In the high-rank but non-full-rank branch, the stored source span in the
span-isometry packet has a nonzero complex Minkowski orthogonal vector. -/
theorem exists_nonzero_mem_sourceSpan_orthogonalComplement_of_proper
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w)
    (hproper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    ∃ v : Fin (d + 1) → ℂ,
      v ∈ complexMinkowskiOrthogonalSubmodule d S.M ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot
    (sourceSpan_orthogonalComplement_nontrivial_of_proper d n S hproper)

/-- A nontrivial nondegenerate complex Minkowski subspace contains a vector
with nonzero self-pairing. -/
theorem exists_nonisotropic_in_nondegenerate_subspace
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ))
    [Nontrivial M]
    (hM : ComplexMinkowskiNondegenerateSubspace d M) :
    ∃ u : M,
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0 := by
  by_contra hnone
  have hdiag :
      ∀ u : M,
        sourceComplexMinkowskiInner d
          (u : Fin (d + 1) → ℂ)
          (u : Fin (d + 1) → ℂ) = 0 := by
    intro u
    by_contra hu
    exact hnone ⟨u, hu⟩
  obtain ⟨x, hx_ne⟩ := exists_ne (0 : M)
  have hx_zero : x = 0 := by
    apply hM x
    intro y
    have hsum := hdiag (x + y)
    have hx := hdiag x
    have hy := hdiag y
    have hxy2 :
        (2 : ℂ) * sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) = 0 := by
      change
        sourceComplexMinkowskiInner d
          ((x : Fin (d + 1) → ℂ) + (y : Fin (d + 1) → ℂ))
          ((x : Fin (d + 1) → ℂ) + (y : Fin (d + 1) → ℂ)) = 0 at hsum
      rw [sourceComplexMinkowskiInner_add_left,
        sourceComplexMinkowskiInner_add_right,
        sourceComplexMinkowskiInner_add_right] at hsum
      rw [hx, hy,
        sourceComplexMinkowskiInner_comm d
          (y : Fin (d + 1) → ℂ)
          (x : Fin (d + 1) → ℂ)] at hsum
      linear_combination hsum
    exact (mul_eq_zero.mp hxy2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  exact hx_ne hx_zero

/-- The complex Minkowski orthogonal complement of a nondegenerate subspace is
nondegenerate. -/
theorem complexMinkowskiOrthogonalSubmodule_nondegenerate
    (d : ℕ)
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M) :
    ComplexMinkowskiNondegenerateSubspace d
      (complexMinkowskiOrthogonalSubmodule d M) := by
  let O := complexMinkowskiOrthogonalSubmodule d M
  intro x horth
  apply Subtype.ext
  apply sourceComplexMinkowskiInner_left_nonDegenerate d
  intro v
  let R := restrictedMinkowskiLeftMap d M
  have hR_inj : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot]
    exact restrictedMinkowskiRadical_eq_bot_of_nondegenerate d hM
  have hdim :
      Module.finrank ℂ M = Module.finrank ℂ (Module.Dual ℂ M) := by
    rw [Subspace.dual_finrank_eq]
  have hR_surj : Function.Surjective R :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hR_inj
  obtain ⟨m, hm⟩ := hR_surj (complexMinkowskiToSubmoduleDual d M v)
  have hvm_orth : v - (m : Fin (d + 1) → ℂ) ∈ O := by
    rw [mem_complexMinkowskiOrthogonalSubmodule_iff]
    intro y
    have hmy :
        sourceComplexMinkowskiInner d
          (m : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d v
          (y : Fin (d + 1) → ℂ) := by
      have h := congrArg (fun f : Module.Dual ℂ M => f y) hm
      simpa [R, restrictedMinkowskiLeftMap, complexMinkowskiToSubmoduleDual]
        using h
    rw [sourceComplexMinkowskiInner_sub_left, hmy, sub_self]
  have hxm :
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (m : Fin (d + 1) → ℂ) = 0 :=
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M
      (x : Fin (d + 1) → ℂ)).1 x.property m
  have hxvm :
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (v - (m : Fin (d + 1) → ℂ)) = 0 :=
    horth ⟨v - (m : Fin (d + 1) → ℂ), hvm_orth⟩
  rw [sourceComplexMinkowskiInner_sub_right, hxm, sub_zero] at hxvm
  exact hxvm

/-- In the high-rank but non-full-rank branch, the stored source span has a
nonisotropic vector in its complex Minkowski orthogonal complement. -/
theorem exists_nonisotropic_mem_sourceSpan_orthogonalComplement_of_proper
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (S : HWHighRankSpanIsometryData d n z w)
    (hproper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    ∃ u : complexMinkowskiOrthogonalSubmodule d S.M,
      sourceComplexMinkowskiInner d
        (u : Fin (d + 1) → ℂ)
        (u : Fin (d + 1) → ℂ) ≠ 0 := by
  have hcomp_ne : complexMinkowskiOrthogonalSubmodule d S.M ≠ ⊥ :=
    sourceSpan_orthogonalComplement_nontrivial_of_proper d n S hproper
  letI : Nontrivial (complexMinkowskiOrthogonalSubmodule d S.M) :=
    (Submodule.nontrivial_iff_ne_bot).2 hcomp_ne
  exact
    exists_nonisotropic_in_nondegenerate_subspace d
      (complexMinkowskiOrthogonalSubmodule d S.M)
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d S.M_nondegenerate)

/-- The low-rank branch is exactly the complement of the orbit-rank branch. -/
theorem hwSourceGram_lowRank_iff_not_orbitRank
    (d n : ℕ)
    {Z : Fin n → Fin n → ℂ} :
    HWSourceGramLowRank d n Z ↔
      ¬ HWSourceGramOrbitRank d n Z := by
  constructor
  · intro hlow horbit
    exact (not_lt_of_ge horbit) hlow
  · intro hnot
    exact Nat.lt_of_not_ge hnot

/-- The exceptional-rank branch is exactly the complement of the maximal-rank
branch. -/
theorem hwSourceGram_exceptionalRank_iff_not_maxRank
    (d n : ℕ)
    {Z : Fin n → Fin n → ℂ} :
    HWSourceGramExceptionalRank d n Z ↔
      ¬ HWSourceGramMaxRank d n Z := by
  constructor
  · intro hex hmax
    exact (not_lt_of_ge hmax) hex
  · intro hnot
    exact Nat.lt_of_not_ge hnot

/-- The orbit-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramOrbitRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramOrbitRankAt d n z ↔
      HWSourceGramOrbitRankAt d n w := by
  simp [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hgram]

/-- The low-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramLowRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramLowRankAt d n z ↔
      HWSourceGramLowRankAt d n w := by
  simp [HWSourceGramLowRankAt, HWSourceGramLowRank, hgram]

/-- The maximal-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramMaxRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramMaxRankAt d n z ↔
      HWSourceGramMaxRankAt d n w := by
  simp [HWSourceGramMaxRankAt, HWSourceGramMaxRank, hgram]

/-- The exceptional-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramExceptionalRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramExceptionalRankAt d n z ↔
      HWSourceGramExceptionalRankAt d n w := by
  simp [HWSourceGramExceptionalRankAt, HWSourceGramExceptionalRank, hgram]

end BHW
