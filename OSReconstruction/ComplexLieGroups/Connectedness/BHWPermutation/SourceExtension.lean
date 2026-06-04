import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeGluing
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.SCV.DistributionalUniqueness

/-!
# Source BHW extension on the permuted extended tube

This file contains the theorem-2-facing, source-coordinate Hall-Wightman data
and local support lemmas in PET language.

The unresolved Hall-Wightman/BHW branch-law theorem is deliberately kept in
the proof docs until it has a checked proof or an explicitly approved source
import boundary.  This production module only exposes the scalar-product
domains, the distributional adjacent anchor, the scalar representative data
shape, and checked local translations of compact-test equality into adjacent
scalar Gram seed equality.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

/-- Complex Minkowski Gram matrix of an ordered tuple of complex spacetime
vectors.  This is the scalar-product coordinate used by Hall-Wightman. -/
def sourceMinkowskiGram (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) * x i μ * x j μ

/-- Complex source Gram matrices are symmetric. -/
theorem sourceMinkowskiGram_symm
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℂ)
    (i j : Fin n) :
    sourceMinkowskiGram d n x i j =
      sourceMinkowskiGram d n x j i := by
  simp [sourceMinkowskiGram, mul_comm, mul_left_comm]

/-- Real Minkowski Gram matrix of an ordered tuple of real spacetime vectors. -/
def sourceRealMinkowskiGram (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ * x i μ * x j μ

/-- Real source Gram matrices are symmetric. -/
theorem sourceRealMinkowskiGram_symm
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (i j : Fin n) :
    sourceRealMinkowskiGram d n x i j =
      sourceRealMinkowskiGram d n x j i := by
  simp [sourceRealMinkowskiGram, mul_comm, mul_left_comm]

/-- The complex Hall-Wightman scalar-product variety, represented as the range
of the complex Minkowski Gram map.  For arity above the spacetime vector
dimension this is a rank-bounded algebraic variety, not an open subset of the
full matrix coordinate space. -/
def sourceComplexGramVariety (d n : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  Set.range (sourceMinkowskiGram d n)

/-- The real Hall-Wightman scalar-product variety, represented as the range of
the real Minkowski Gram map. -/
def sourceRealGramVariety (d n : ℕ) :
    Set (Fin n → Fin n → ℝ) :=
  Set.range (sourceRealMinkowskiGram d n)

/-- Coordinate permutation on complex Gram matrices. -/
def sourcePermuteComplexGram (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j => Z (σ i) (σ j)

/-- Successive source Gram coordinate permutations compose by permutation
multiplication. -/
theorem sourcePermuteComplexGram_mul
    (n : ℕ)
    (α β : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    sourcePermuteComplexGram n (α * β) Z =
      sourcePermuteComplexGram n β
        (sourcePermuteComplexGram n α Z) := by
  ext i j
  rfl

/-- The identity permutation acts trivially on source Gram coordinates. -/
theorem sourcePermuteComplexGram_one
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ) :
    sourcePermuteComplexGram n 1 Z = Z := by
  ext i j
  rfl

/-- Permuting source Gram coordinates and then permuting back by the inverse
recovers the original Gram matrix. -/
theorem sourcePermuteComplexGram_inv_mul
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    sourcePermuteComplexGram n σ⁻¹ (sourcePermuteComplexGram n σ Z) = Z := by
  calc
    sourcePermuteComplexGram n σ⁻¹ (sourcePermuteComplexGram n σ Z)
        = sourcePermuteComplexGram n (σ * σ⁻¹) Z := by
            rw [sourcePermuteComplexGram_mul]
    _ = Z := by
          simpa using sourcePermuteComplexGram_one n Z

/-- Permuting source vectors permutes the complex source Gram matrix. -/
theorem sourceMinkowskiGram_perm
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n (fun k => z (σ k)) =
      sourcePermuteComplexGram n σ (sourceMinkowskiGram d n z) := by
  ext i j
  rfl

/-- Coordinate permutation preserves the Hall-Wightman scalar-product
variety. -/
theorem sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    sourcePermuteComplexGram n σ Z ∈ sourceComplexGramVariety d n ↔
      Z ∈ sourceComplexGramVariety d n := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨fun k => z (σ⁻¹ k), ?_⟩
    calc
      sourceMinkowskiGram d n (fun k => z (σ⁻¹ k))
          = sourcePermuteComplexGram n σ⁻¹ (sourceMinkowskiGram d n z) := by
              simpa using sourceMinkowskiGram_perm d n σ⁻¹ z
      _ = sourcePermuteComplexGram n σ⁻¹
            (sourcePermuteComplexGram n σ Z) := by
              rw [hz]
      _ = Z := by
              ext i j
              simp [sourcePermuteComplexGram]
  · rintro ⟨z, rfl⟩
    exact ⟨fun k => z (σ k), sourceMinkowskiGram_perm d n σ z⟩

/-- The scalar-product image of the ordinary extended tube. -/
def sourceExtendedTubeGramDomain (d n : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  sourceMinkowskiGram d n '' ExtendedTube d n

/-- Domain where both a Gram matrix and a coordinate-permuted Gram matrix
come from ordinary extended-tube configurations. -/
def sourceDoublePermutationGramDomain (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin n → ℂ) :=
  {Z | Z ∈ sourceExtendedTubeGramDomain d n ∧
    sourcePermuteComplexGram n σ Z ∈ sourceExtendedTubeGramDomain d n}

/-- A point of the double scalar-product domain admits ordinary extended-tube
realizations both before and after the coordinate permutation.  This is the
concrete realization data needed by the witness-construction route for the
Hall-Wightman source overlap theorem. -/
theorem exists_sourceExtendedTube_realizations_of_mem_doubleDomain
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceDoublePermutationGramDomain d n σ) :
    ∃ z w : Fin n → Fin (d + 1) → ℂ,
      z ∈ ExtendedTube d n ∧
      w ∈ ExtendedTube d n ∧
      sourceMinkowskiGram d n z = Z ∧
      sourceMinkowskiGram d n w = sourcePermuteComplexGram n σ Z := by
  rcases hZ with ⟨hLeft, hRight⟩
  rcases hLeft with ⟨z, hz, rfl⟩
  rcases hRight with ⟨w, hw, hwGram⟩
  exact ⟨z, w, hz, hw, rfl, hwGram⟩

/-- Realization data in the ordinary extended tube characterizes membership in
the double scalar-product domain. -/
theorem mem_sourceDoublePermutationGramDomain_iff_exists_realizations
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    Z ∈ sourceDoublePermutationGramDomain d n σ ↔
      ∃ z w : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n ∧
        w ∈ ExtendedTube d n ∧
        sourceMinkowskiGram d n z = Z ∧
        sourceMinkowskiGram d n w = sourcePermuteComplexGram n σ Z := by
  constructor
  · exact exists_sourceExtendedTube_realizations_of_mem_doubleDomain d n σ
  · rintro ⟨z, w, hz, hw, hzGram, hwGram⟩
    refine ⟨?_, ?_⟩
    · exact ⟨z, hz, hzGram⟩
    · exact ⟨w, hw, hwGram⟩

/-- Legacy full-domain Hall-Wightman overlap helper for one adjacent swap.

This is definitionally the whole adjacent double scalar-product domain.  The
theorem-2-facing local overlap is the `overlap` field of
`SourceAdjacentOverlapWitness`, which also carries connectedness and
real-environment membership data. -/
def sourceAdjacentPermutationGramOverlap (d n : ℕ)
    (_π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    Set (Fin n → Fin n → ℂ) :=
  sourceDoublePermutationGramDomain d n (Equiv.swap i ⟨i.val + 1, hi⟩)

/-- Expected dimension of the regular Hall-Wightman scalar-product variety.
For spacetime vector dimension `D = d + 1` and `m = min n D`, this is
`n * m - m * (m - 1) / 2`.  In four spacetime dimensions this is
`1, 3, 6, 10, 4n - 6`, the dimension count used by Hall-Wightman. -/
def sourceGramExpectedDim (d n : ℕ) : ℕ :=
  let m := min n (d + 1)
  n * m - (m * (m - 1)) / 2

/-- Real span of the source vectors in spacetime. -/
def sourceConfigurationSpan (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Submodule ℝ (Fin (d + 1) → ℝ) :=
  Submodule.span ℝ (Set.range x)

/-- Complex span of the source vectors in complexified spacetime. -/
def sourceComplexConfigurationSpan (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  Submodule.span ℂ (Set.range z)

/-- Regular real configurations are maximal-span configurations.  For the
nondegenerate Minkowski form this is the regular stratum of the source Gram
map onto the Hall-Wightman scalar-product variety. -/
def SourceGramRegularAt (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) : Prop :=
  Module.finrank ℝ (sourceConfigurationSpan d n x) = min n (d + 1)

/-- Regular complex configurations are maximal-span configurations. -/
def SourceComplexGramRegularAt (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  Module.finrank ℂ (sourceComplexConfigurationSpan d n z) = min n (d + 1)

/-- Differential of the real source Gram map at `x`. -/
def sourceRealGramDifferential
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h i μ * x j μ + x i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
    apply Finset.sum_congr rfl
    intro μ _
    ring

/-- Differential of the complex source Gram map at `z`. -/
def sourceComplexGramDifferential
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        (h i μ * z j μ + z i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
    apply Finset.sum_congr rfl
    intro μ _
    ring

/-- The real source Gram map has Frechet derivative
`sourceRealGramDifferential`. -/
theorem sourceRealMinkowskiGram_hasFDerivAt
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    HasFDerivAt (sourceRealMinkowskiGram d n)
      (LinearMap.toContinuousLinearMap (sourceRealGramDifferential d n x)) x := by
  let rowProj : Fin n →
      ((Fin n → Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ)) :=
    fun i =>
      ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n => Fin (d + 1) → ℝ) i
  let coordProj : Fin (d + 1) →
      ((Fin (d + 1) → ℝ) →L[ℝ] ℝ) :=
    fun μ =>
      ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (d + 1) => ℝ) μ
  let coord : Fin n → Fin (d + 1) →
      ((Fin n → Fin (d + 1) → ℝ) →L[ℝ] ℝ) :=
    fun i μ => (coordProj μ).comp (rowProj i)
  let L : (Fin n → Fin (d + 1) → ℝ) →L[ℝ]
      (Fin n → Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (sourceRealGramDifferential d n x)
  change HasFDerivAt (sourceRealMinkowskiGram d n) L x
  have hL : L =
      ContinuousLinearMap.pi
        (fun i : Fin n =>
          (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin n => Fin n → ℝ) i).comp L) := by
    ext y i j
    rfl
  rw [hL]
  rw [hasFDerivAt_pi]
  intro i
  let Li : (Fin n → Fin (d + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => Fin n → ℝ) i).comp L
  change HasFDerivAt
    (fun y : Fin n → Fin (d + 1) → ℝ =>
      sourceRealMinkowskiGram d n y i) Li x
  have hLi : Li =
      ContinuousLinearMap.pi
        (fun j : Fin n =>
          (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin n => ℝ) j).comp Li) := by
    ext y j
    rfl
  rw [hLi]
  rw [hasFDerivAt_pi]
  intro j
  let component : (Fin n → Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) j).comp Li
  change HasFDerivAt
    (fun y : Fin n → Fin (d + 1) → ℝ =>
      sourceRealMinkowskiGram d n y i j) component x
  have hsum : HasFDerivAt
      (fun y : Fin n → Fin (d + 1) → ℝ =>
        ∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * y i μ * y j μ)
      (∑ μ : Fin (d + 1),
        (MinkowskiSpace.metricSignature d μ) •
          (ContinuousLinearMap.smulRight (coord i μ) (x j μ) +
            ContinuousLinearMap.smulRight (coord j μ) (x i μ))) x := by
    apply HasFDerivAt.fun_sum
    intro μ _
    have hi :
        HasFDerivAt
          (fun y : Fin n → Fin (d + 1) → ℝ => y i μ)
          (coord i μ) x := by
      simpa [coord, rowProj, coordProj] using
        (coord i μ).hasFDerivAt (x := x)
    have hj :
        HasFDerivAt
          (fun y : Fin n → Fin (d + 1) → ℝ => y j μ)
          (coord j μ) x := by
      simpa [coord, rowProj, coordProj] using
        (coord j μ).hasFDerivAt (x := x)
    convert (hi.mul hj).const_mul (MinkowskiSpace.metricSignature d μ) using 1
    · ext y
      simp
      ring
    · ext h
      simp [coord, rowProj, coordProj, ContinuousLinearMap.smulRight]
      ring
  convert hsum using 1
  ext h
  change (sourceRealGramDifferential d n x h) i j =
    (∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ) •
        (ContinuousLinearMap.smulRight (coord i μ) (x j μ) +
          ContinuousLinearMap.smulRight (coord j μ) (x i μ))) h
  simp [coord, rowProj, coordProj, sourceRealGramDifferential,
    Finset.sum_apply, ContinuousLinearMap.smulRight]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- A concrete maximal-span template used in the source Gram regular-locus
geometry: the available coordinate basis vectors appear among the first
`min n (d + 1)` source vectors, and later source vectors are zero. -/
def sourceFullSpanTemplate (d n : ℕ) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ.val = k.val then 1 else 0

/-- The selected source-vector indices in the concrete full-span template. -/
def sourceTemplateDomainIndex
    (d n : ℕ) :
    Fin (min n (d + 1)) → Fin n :=
  fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.min_le_left n (d + 1))⟩

/-- The selected spacetime-coordinate indices in the concrete full-span
template. -/
def sourceTemplateCoordIndex
    (d n : ℕ) :
    Fin (min n (d + 1)) → Fin (d + 1) :=
  fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.min_le_right n (d + 1))⟩

/-- The coordinate-index inclusion for the full-span template is injective. -/
theorem sourceTemplateDomainIndex_injective
    (d n : ℕ) :
    Function.Injective (sourceTemplateDomainIndex d n) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun c : Fin n => c.val) h

/-- The coordinate-index inclusion for the full-span template is injective. -/
theorem sourceTemplateCoordIndex_injective
    (d n : ℕ) :
    Function.Injective (sourceTemplateCoordIndex d n) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun c : Fin (d + 1) => c.val) h

/-- The selected rows of the full-span template are the corresponding standard
coordinate vectors. -/
theorem sourceFullSpanTemplate_basisVector
    (d n : ℕ)
    (a : Fin (min n (d + 1))) :
    sourceFullSpanTemplate d n
        (sourceTemplateDomainIndex d n a) =
      Pi.single (M := fun _ : Fin (d + 1) => ℝ)
        (sourceTemplateCoordIndex d n a) (1 : ℝ) := by
  ext μ
  by_cases hEq : μ = sourceTemplateCoordIndex d n a
  · subst μ
    simp [sourceFullSpanTemplate, sourceTemplateDomainIndex,
      sourceTemplateCoordIndex]
  · have hμ : μ.val ≠ a.val := by
      intro hval
      exact hEq (Fin.ext hval)
    have hNe :
        μ ≠ (⟨a.val,
          lt_of_lt_of_le a.isLt
            (Nat.min_le_right n (d + 1))⟩ : Fin (d + 1)) := by
      simpa [sourceTemplateCoordIndex] using hEq
    simp [sourceFullSpanTemplate, sourceTemplateDomainIndex,
      sourceTemplateCoordIndex, hμ, hNe]

/-- The selected rows of the full-span template are linearly independent. -/
theorem linearIndependent_sourceFullSpanTemplate_basisBlock
    (d n : ℕ) :
    LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        sourceFullSpanTemplate d n (sourceTemplateDomainIndex d n a)) := by
  have hcoord : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        Pi.single (M := fun _ : Fin (d + 1) => ℝ)
          (sourceTemplateCoordIndex d n a) (1 : ℝ)) :=
    by
      have hbasis :
          LinearIndependent ℝ (Pi.basisFun ℝ (Fin (d + 1))) :=
        (Pi.basisFun ℝ (Fin (d + 1))).linearIndependent
      have hcoord :=
        hbasis.comp (sourceTemplateCoordIndex d n)
          (sourceTemplateCoordIndex_injective d n)
      simpa [Function.comp_def, Pi.basisFun_apply] using hcoord
  have hfun :
      (fun a : Fin (min n (d + 1)) =>
        sourceFullSpanTemplate d n (sourceTemplateDomainIndex d n a)) =
      (fun a : Fin (min n (d + 1)) =>
        Pi.single (M := fun _ : Fin (d + 1) => ℝ)
          (sourceTemplateCoordIndex d n a) (1 : ℝ)) := by
    funext a
    exact sourceFullSpanTemplate_basisVector d n a
  rw [hfun]
  exact hcoord

/-- The full-span template is a regular source configuration. -/
theorem sourceFullSpanTemplate_regular
    (d n : ℕ) :
    SourceGramRegularAt d n (sourceFullSpanTemplate d n) := by
  unfold SourceGramRegularAt
  let S : Submodule ℝ (Fin (d + 1) → ℝ) :=
    sourceConfigurationSpan d n (sourceFullSpanTemplate d n)
  have hli : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        sourceFullSpanTemplate d n (sourceTemplateDomainIndex d n a)) :=
    linearIndependent_sourceFullSpanTemplate_basisBlock d n
  have hliS : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        (⟨sourceFullSpanTemplate d n (sourceTemplateDomainIndex d n a),
          by
            change sourceFullSpanTemplate d n
                (sourceTemplateDomainIndex d n a) ∈
              Submodule.span ℝ (Set.range (sourceFullSpanTemplate d n))
            exact Submodule.subset_span
              ⟨sourceTemplateDomainIndex d n a, rfl⟩⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype
    simpa [Function.comp_def, S] using hli
  have hlower : min n (d + 1) ≤ Module.finrank ℝ S := by
    simpa using hliS.fintype_card_le_finrank
  have hupper_n : Module.finrank ℝ S ≤ n := by
    simpa [S, sourceConfigurationSpan] using
      (finrank_range_le_card (R := ℝ) (b := sourceFullSpanTemplate d n))
  have hupper_d : Module.finrank ℝ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [Module.finrank_fin_fun] using h
  have hupper : Module.finrank ℝ S ≤ min n (d + 1) :=
    le_min hupper_n hupper_d
  exact le_antisymm hupper hlower

/-- A maximal coordinate minor of a source configuration. -/
def sourceRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) → Fin n)
    (J : Fin (min n (d + 1)) → Fin (d + 1))
    (x : Fin n → Fin (d + 1) → ℝ) : ℝ :=
  Matrix.det (fun a b => x (I a) (J b))

/-- Coordinate minors vary continuously with the source configuration. -/
theorem continuous_sourceRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) → Fin n)
    (J : Fin (min n (d + 1)) → Fin (d + 1)) :
    Continuous (sourceRegularMinor d n I J) := by
  unfold sourceRegularMinor
  exact (continuous_matrix fun a b =>
    (continuous_apply (J b)).comp (continuous_apply (I a))).matrix_det

/-- A linearly independent family of vectors in a coordinate space has a
nonzero square coordinate minor. -/
theorem exists_nonzero_coordinate_minor_of_linearIndependent
    {m D : ℕ}
    {v : Fin m → Fin D → ℝ}
    (hli : LinearIndependent ℝ v) :
    ∃ J : Fin m → Fin D,
      Function.Injective J ∧
      Matrix.det (fun a b => v a (J b)) ≠ 0 := by
  let A : Matrix (Fin m) (Fin D) ℝ := fun a j => v a j
  have hrowspan :
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) = m := by
    have hspan := finrank_span_eq_card (R := ℝ) (b := v) hli
    simpa [A, Matrix.row, Fintype.card_fin] using hspan
  have hcolrank :
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) = m := by
    have hrank_rows := Matrix.rank_eq_finrank_span_row (R := ℝ) A
    have hrank_cols := Matrix.rank_eq_finrank_span_cols (R := ℝ) A
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) = A.rank := by
        exact hrank_cols.symm
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by
        exact hrank_rows
      _ = m := hrowspan
  obtain ⟨c, hc_mem, _hc_span, hc_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℝ) (s := Set.range A.col)
  let e : Fin m ≃
      Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range A.col))) :=
    finCongr hcolrank.symm
  let J : Fin m → Fin D := fun b => Classical.choose (hc_mem (e b))
  have hJcol : ∀ b : Fin m, A.col (J b) = c (e b) := by
    intro b
    exact Classical.choose_spec (hc_mem (e b))
  have hcols : LinearIndependent ℝ (fun b : Fin m => A.col (J b)) := by
    have hc' : LinearIndependent ℝ (fun b : Fin m => c (e b)) :=
      hc_li.comp e e.injective
    convert hc' using 1
    ext b a
    exact congr_fun (hJcol b) a
  have hJinj : Function.Injective J := by
    intro b₁ b₂ h
    apply hcols.injective
    ext a
    simp [A, Matrix.col, h]
  let B : Matrix (Fin m) (Fin m) ℝ := fun a b => v a (J b)
  have hcolsB : LinearIndependent ℝ B.col := by
    simpa [A, Matrix.col] using hcols
  have hunit : IsUnit B :=
    (Matrix.linearIndependent_cols_iff_isUnit).1 hcolsB
  have hunitdet : IsUnit B.det := B.isUnit_iff_isUnit_det.mp hunit
  exact ⟨J, hJinj, by simpa [B] using hunitdet.ne_zero⟩

/-- A nonzero maximal coordinate minor witnesses regularity of the source
configuration. -/
theorem sourceGramRegularAt_of_exists_nonzero_minor
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hminor :
      ∃ I : Fin (min n (d + 1)) → Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
          sourceRegularMinor d n I J x ≠ 0) :
    SourceGramRegularAt d n x := by
  rcases hminor with ⟨I, _hI, J, _hJ, hdet⟩
  let restrictJ : (Fin (d + 1) → ℝ) →ₗ[ℝ]
      (Fin (min n (d + 1)) → ℝ) := {
    toFun := fun v b => v (J b)
    map_add' := by
      intro v w
      ext b
      simp
    map_smul' := by
      intro c v
      ext b
      simp }
  have hrows : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        fun b : Fin (min n (d + 1)) => x (I a) (J b)) := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hxI : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) => x (I a)) := by
    apply LinearIndependent.of_comp restrictJ
    simpa [Function.comp_def, restrictJ] using hrows
  unfold SourceGramRegularAt
  let S : Submodule ℝ (Fin (d + 1) → ℝ) :=
    sourceConfigurationSpan d n x
  have hxIS : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        (⟨x (I a), by
          change x (I a) ∈ Submodule.span ℝ (Set.range x)
          exact Submodule.subset_span ⟨I a, rfl⟩⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype
    simpa [Function.comp_def, S] using hxI
  have hlower : min n (d + 1) ≤ Module.finrank ℝ S := by
    simpa using hxIS.fintype_card_le_finrank
  have hupper_n : Module.finrank ℝ S ≤ n := by
    simpa [S, sourceConfigurationSpan] using
      (finrank_range_le_card (R := ℝ) (b := x))
  have hupper_d : Module.finrank ℝ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [Module.finrank_fin_fun] using h
  have hupper : Module.finrank ℝ S ≤ min n (d + 1) :=
    le_min hupper_n hupper_d
  exact le_antisymm hupper hlower

/-- Regularity of a source configuration supplies a nonzero maximal coordinate
minor. -/
theorem exists_nonzero_minor_of_sourceGramRegularAt
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    ∃ I : Fin (min n (d + 1)) → Fin n,
      Function.Injective I ∧
      ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
        Function.Injective J ∧
        sourceRegularMinor d n I J x ≠ 0 := by
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range x)) =
      min n (d + 1) := by
    simpa [SourceGramRegularAt, sourceConfigurationSpan] using hreg
  obtain ⟨v, hv_mem, _hv_span, hv_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℝ) (s := Set.range x)
  let e : Fin (min n (d + 1)) ≃
      Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range x))) :=
    finCongr hfin.symm
  let w : Fin (min n (d + 1)) → Fin (d + 1) → ℝ :=
    fun a => v (e a)
  have hw_li : LinearIndependent ℝ w := hv_li.comp e e.injective
  let I : Fin (min n (d + 1)) → Fin n :=
    fun a => Classical.choose (hv_mem (e a))
  have hIrow : ∀ a : Fin (min n (d + 1)), x (I a) = w a := by
    intro a
    exact Classical.choose_spec (hv_mem (e a))
  have hxI_li :
      LinearIndependent ℝ
        (fun a : Fin (min n (d + 1)) => x (I a)) := by
    convert hw_li using 1
    ext a μ
    exact congr_fun (hIrow a) μ
  have hIinj : Function.Injective I := by
    intro a b h
    apply hxI_li.injective
    ext μ
    simp [h]
  obtain ⟨J, hJinj, hdet⟩ :=
    exists_nonzero_coordinate_minor_of_linearIndependent
      (v := fun a => x (I a)) hxI_li
  exact ⟨I, hIinj, J, hJinj, by simpa [sourceRegularMinor] using hdet⟩

/-- Maximal source span is equivalent to the existence of a nonzero maximal
coordinate minor. -/
theorem sourceGramRegularAt_iff_exists_nonzero_minor
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    SourceGramRegularAt d n x ↔
      ∃ I : Fin (min n (d + 1)) → Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
          sourceRegularMinor d n I J x ≠ 0 :=
  ⟨exists_nonzero_minor_of_sourceGramRegularAt d n,
    sourceGramRegularAt_of_exists_nonzero_minor d n⟩

/-- The regular source configurations form an open subset of source
configuration space. -/
theorem isOpen_sourceGramRegularAt
    (d n : ℕ) :
    IsOpen {x : Fin n → Fin (d + 1) → ℝ | SourceGramRegularAt d n x} := by
  classical
  rw [show {x : Fin n → Fin (d + 1) → ℝ | SourceGramRegularAt d n x} =
      ⋃ I : Fin (min n (d + 1)) → Fin n,
        ⋃ _hI : Function.Injective I,
          ⋃ J : Fin (min n (d + 1)) → Fin (d + 1),
            ⋃ _hJ : Function.Injective J,
              {x : Fin n → Fin (d + 1) → ℝ |
                sourceRegularMinor d n I J x ≠ 0} by
    ext x
    simp [sourceGramRegularAt_iff_exists_nonzero_minor]]
  apply isOpen_iUnion
  intro I
  apply isOpen_iUnion
  intro _hI
  apply isOpen_iUnion
  intro J
  apply isOpen_iUnion
  intro _hJ
  exact isOpen_ne_fun (continuous_sourceRegularMinor d n I J) continuous_const

/-- The canonical full-span template has unit determinant on its canonical
maximal minor. -/
theorem sourceFullSpanTemplate_regularMinor_eq_one
    (d n : ℕ) :
    sourceRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) (sourceFullSpanTemplate d n) = 1 := by
  unfold sourceRegularMinor
  rw [show (fun a b : Fin (min n (d + 1)) =>
      sourceFullSpanTemplate d n (sourceTemplateDomainIndex d n a)
        (sourceTemplateCoordIndex d n b)) =
        (1 : Matrix (Fin (min n (d + 1)))
          (Fin (min n (d + 1))) ℝ) by
    ext a b
    have hidx :
        sourceTemplateCoordIndex d n a = sourceTemplateCoordIndex d n b ↔
          a = b :=
      (sourceTemplateCoordIndex_injective d n).eq_iff
    have hidx' :
        sourceTemplateCoordIndex d n b = sourceTemplateCoordIndex d n a ↔
          a = b := by
      rw [eq_comm, hidx]
    simp [sourceFullSpanTemplate_basisVector, Matrix.one_apply,
      Pi.single_apply, hidx']]
  simp

/-- The canonical full-span template minor is nonzero. -/
theorem sourceFullSpanTemplate_regularMinor_ne_zero
    (d n : ℕ) :
    sourceRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) (sourceFullSpanTemplate d n) ≠ 0 := by
  rw [sourceFullSpanTemplate_regularMinor_eq_one]
  norm_num

/-- The determinant polynomial of the canonical regular minor along the line
`x + t • sourceFullSpanTemplate`. -/
def sourceCanonicalRegularMinorLinePolynomial
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) : Polynomial ℝ :=
  let B : Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) ℝ :=
    fun a b =>
      x (sourceTemplateDomainIndex d n a) (sourceTemplateCoordIndex d n b)
  Matrix.det ((Polynomial.X : Polynomial ℝ) •
      (1 : Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) (Polynomial ℝ)) +
    B.map Polynomial.C)

/-- The canonical line-minor determinant polynomial has leading coefficient
one. -/
theorem sourceCanonicalRegularMinorLinePolynomial_leadingCoeff
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Polynomial.leadingCoeff
      (sourceCanonicalRegularMinorLinePolynomial d n x) = 1 := by
  simpa [sourceCanonicalRegularMinorLinePolynomial] using
    Polynomial.leadingCoeff_det_X_one_add_C
      (A := (fun a b : Fin (min n (d + 1)) =>
        x (sourceTemplateDomainIndex d n a) (sourceTemplateCoordIndex d n b) :
        Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) ℝ))

/-- The canonical line-minor determinant polynomial is not the zero
polynomial. -/
theorem sourceCanonicalRegularMinorLinePolynomial_ne_zero
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceCanonicalRegularMinorLinePolynomial d n x ≠ 0 := by
  intro hp
  have hlead :=
    sourceCanonicalRegularMinorLinePolynomial_leadingCoeff d n x
  have hlead0 := congrArg Polynomial.leadingCoeff hp
  rw [hlead] at hlead0
  norm_num at hlead0

/-- Evaluating the canonical line-minor polynomial gives the canonical
coordinate minor of `x + t • sourceFullSpanTemplate`. -/
theorem sourceCanonicalRegularMinorLinePolynomial_eval
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (t : ℝ) :
    (sourceCanonicalRegularMinorLinePolynomial d n x).eval t =
      sourceRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n)
        (x + t • sourceFullSpanTemplate d n) := by
  unfold sourceCanonicalRegularMinorLinePolynomial sourceRegularMinor
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
      sourceFullSpanTemplate_basisVector, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, h, hcoord, add_comm]
  · have hcoord :
        sourceTemplateCoordIndex d n i ≠
          sourceTemplateCoordIndex d n (σ i) := by
      intro hcoord
      exact h ((sourceTemplateCoordIndex_injective d n) hcoord).symm
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      sourceFullSpanTemplate_basisVector, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, h, hcoord, add_comm]

/-- The nonvanishing locus of the canonical regular minor is dense. -/
theorem sourceCanonicalRegularMinor_nonzero_dense
    (d n : ℕ) :
    Dense {x : Fin n → Fin (d + 1) → ℝ |
      sourceRegularMinor d n (sourceTemplateDomainIndex d n)
        (sourceTemplateCoordIndex d n) x ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hU_nonempty
  rcases hU_nonempty with ⟨x, hxU⟩
  let line : ℝ → Fin n → Fin (d + 1) → ℝ :=
    fun t => x + t • sourceFullSpanTemplate d n
  let p := sourceCanonicalRegularMinorLinePolynomial d n x
  have hp_ne : p ≠ 0 := by
    simpa [p] using
      sourceCanonicalRegularMinorLinePolynomial_ne_zero d n x
  have hroots_finite : ({t : ℝ | p.eval t = 0}).Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro t ht
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset] at ht ⊢
    exact (Polynomial.mem_roots hp_ne).mpr ht
  have hdense : Dense (Set.univ \ {t : ℝ | p.eval t = 0}) := by
    simpa using
      (Dense.diff_finite (s := (Set.univ : Set ℝ)) dense_univ hroots_finite)
  have hline_cont : Continuous line := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre_open : IsOpen (line ⁻¹' U) := hU.preimage hline_cont
  have hpre_nonempty : (line ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [line] using hxU
  obtain ⟨t, htgood, htU⟩ :=
    hdense.exists_mem_open hpre_open hpre_nonempty
  have hp_eval_ne : p.eval t ≠ 0 := by
    have ht_not : t ∉ {t : ℝ | p.eval t = 0} := by
      simpa [Set.mem_diff, p] using htgood
    simpa using ht_not
  refine ⟨line t, ?_, ?_⟩
  · exact htU
  · have hminor :
        sourceRegularMinor d n (sourceTemplateDomainIndex d n)
          (sourceTemplateCoordIndex d n) (line t) ≠ 0 := by
      have heval : p.eval t =
          sourceRegularMinor d n (sourceTemplateDomainIndex d n)
            (sourceTemplateCoordIndex d n) (line t) := by
        simpa [p, line] using
          sourceCanonicalRegularMinorLinePolynomial_eval d n x t
      exact fun h => hp_eval_ne (by rwa [heval])
    exact hminor

/-- Regular source configurations form a dense subset of source configuration
space. -/
theorem dense_sourceGramRegularAt
    (d n : ℕ) :
    Dense {x : Fin n → Fin (d + 1) → ℝ | SourceGramRegularAt d n x} := by
  apply (sourceCanonicalRegularMinor_nonzero_dense d n).mono
  intro x hx
  exact sourceGramRegularAt_of_exists_nonzero_minor d n
    ⟨sourceTemplateDomainIndex d n,
      sourceTemplateDomainIndex_injective d n,
      sourceTemplateCoordIndex d n,
      sourceTemplateCoordIndex_injective d n,
      hx⟩

/-- Coordinate permutation on real Gram matrices. -/
def sourcePermuteGram (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (G : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => G (σ i) (σ j)

/-- Permuting source vectors permutes the real source Gram matrix. -/
theorem sourceRealMinkowskiGram_perm
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealMinkowskiGram d n (fun k => x (σ k)) =
      sourcePermuteGram n σ (sourceRealMinkowskiGram d n x) := by
  ext i j
  rfl

/-- The canonical complexification of a real Gram matrix. -/
def sourceRealGramComplexify (n : ℕ)
    (G : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℂ :=
  fun i j => (G i j : ℂ)

/-- The complex Gram differential at a real point extends the real Gram
differential by complexification on real tangent vectors. -/
theorem sourceComplexGramDifferential_realEmbed
    (d n : ℕ)
    (x h : Fin n → Fin (d + 1) → ℝ) :
    sourceComplexGramDifferential d n (realEmbed x) (realEmbed h) =
      sourceRealGramComplexify n ((sourceRealGramDifferential d n x) h) := by
  ext i j
  simp [sourceComplexGramDifferential, sourceRealGramDifferential,
    sourceRealGramComplexify, realEmbed]

/-- Real tangent space to the source Gram image at a real Gram matrix,
represented by regular real configurations mapping to that matrix. -/
def sourceRealGramTangentSpaceAt
    (d n : ℕ)
    (G : Fin n → Fin n → ℝ) :
    Set (Fin n → Fin n → ℝ) :=
  {δG | ∃ x : Fin n → Fin (d + 1) → ℝ,
    SourceGramRegularAt d n x ∧
    sourceRealMinkowskiGram d n x = G ∧
    δG ∈ LinearMap.range (sourceRealGramDifferential d n x)}

/-- Complex tangent space to the source Gram image at a complex Gram matrix,
represented by regular complex configurations mapping to that matrix. -/
def sourceComplexGramTangentSpaceAt
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) :
    Set (Fin n → Fin n → ℂ) :=
  {δZ | ∃ z : Fin n → Fin (d + 1) → ℂ,
    SourceComplexGramRegularAt d n z ∧
    sourceMinkowskiGram d n z = Z ∧
    δZ ∈ LinearMap.range (sourceComplexGramDifferential d n z)}

/-- Hall-Wightman's maximal-totally-real tangent condition at a real Gram
matrix: the complex span of real Gram tangent vectors equals the complex
tangent space of the scalar-product variety. -/
def SourceComplexifiedRealTangentEqualsComplexTangent
    (d n : ℕ)
    (G : Fin n → Fin n → ℝ) : Prop :=
  Submodule.span ℂ
      (sourceRealGramComplexify n '' sourceRealGramTangentSpaceAt d n G) =
    Submodule.span ℂ
      (sourceComplexGramTangentSpaceAt d n (sourceRealGramComplexify n G))

/-- Complexifying a permuted real Gram matrix agrees with permuting the
complexified Gram matrix. -/
theorem sourceRealGramComplexify_perm
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (G : Fin n → Fin n → ℝ) :
    sourceRealGramComplexify n (sourcePermuteGram n σ G) =
      sourcePermuteComplexGram n σ (sourceRealGramComplexify n G) := by
  ext i j
  rfl

/-- Complexifying a real source Gram matrix agrees with the complex source Gram
matrix of the real embedding. -/
theorem sourceMinkowskiGram_realEmbed
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceMinkowskiGram d n (realEmbed x) =
      sourceRealGramComplexify n (sourceRealMinkowskiGram d n x) := by
  ext i j
  simp [sourceMinkowskiGram, sourceRealMinkowskiGram,
    sourceRealGramComplexify, realEmbed]

/-- The complexification of any realized real Gram matrix lies in the complex
Hall-Wightman scalar-product variety. -/
theorem sourceRealGramComplexify_mem_sourceComplexGramVariety
    (d n : ℕ)
    {G : Fin n → Fin n → ℝ}
    (hG : G ∈ sourceRealGramVariety d n) :
    sourceRealGramComplexify n G ∈ sourceComplexGramVariety d n := by
  rcases hG with ⟨x, rfl⟩
  exact ⟨realEmbed x, sourceMinkowskiGram_realEmbed d n x⟩

/-- Relative openness in the complex Hall-Wightman scalar-product variety. -/
def IsRelOpenInSourceComplexGramVariety
    (d n : ℕ)
    (U : Set (Fin n → Fin n → ℂ)) : Prop :=
  ∃ U0 : Set (Fin n → Fin n → ℂ),
    IsOpen U0 ∧ U = U0 ∩ sourceComplexGramVariety d n

/-- Coordinate permutation on complex Gram matrices is continuous. -/
theorem continuous_sourcePermuteComplexGram
    (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Continuous (sourcePermuteComplexGram n σ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (σ j)).comp (continuous_apply (σ i))

/-- Coordinate permutation on complex Gram matrices is complex differentiable. -/
theorem differentiable_sourcePermuteComplexGram
    (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Differentiable ℂ (sourcePermuteComplexGram n σ) := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro j
  have hi : Differentiable ℂ
      (fun Z : Fin n → Fin n → ℂ => Z (σ i)) :=
    differentiable_apply (σ i)
  have hj : Differentiable ℂ (fun r : Fin n → ℂ => r (σ j)) :=
    differentiable_apply (σ j)
  exact hj.comp hi

/-- Relative openness in the Hall-Wightman scalar-product variety is preserved
under precomposition by a coordinate permutation. -/
theorem IsRelOpenInSourceComplexGramVariety.preimage_sourcePermuteComplexGram
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU : IsRelOpenInSourceComplexGramVariety d n U)
    (σ : Equiv.Perm (Fin n)) :
    IsRelOpenInSourceComplexGramVariety d n
      {Z | sourcePermuteComplexGram n σ Z ∈ U} := by
  rcases hU with ⟨U0, hU0_open, rfl⟩
  refine ⟨{Z | sourcePermuteComplexGram n σ Z ∈ U0},
    hU0_open.preimage (continuous_sourcePermuteComplexGram n σ), ?_⟩
  ext Z
  constructor
  · intro h
    constructor
    · exact h.1
    · exact (sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff
        d n σ Z).1 h.2
  · intro h
    constructor
    · exact h.1
    · exact (sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff
        d n σ Z).2 h.2

/-- Relative openness in the Hall-Wightman scalar-product variety is stable
under intersection. -/
theorem IsRelOpenInSourceComplexGramVariety.inter
    (d n : ℕ)
    {U V : Set (Fin n → Fin n → ℂ)}
    (hU : IsRelOpenInSourceComplexGramVariety d n U)
    (hV : IsRelOpenInSourceComplexGramVariety d n V) :
    IsRelOpenInSourceComplexGramVariety d n (U ∩ V) := by
  rcases hU with ⟨U0, hU0_open, rfl⟩
  rcases hV with ⟨V0, hV0_open, rfl⟩
  refine ⟨U0 ∩ V0, hU0_open.inter hV0_open, ?_⟩
  ext Z
  simp [Set.inter_left_comm, Set.inter_comm]

/-- If the ordinary extended-tube scalar Gram domain is relatively open in the
Hall-Wightman scalar-product variety, then every double-permutation domain is
too. -/
theorem sourceDoublePermutationGramDomain_relOpen_of_sourceExtendedTubeGramDomain
    (d n : ℕ)
    (hU : IsRelOpenInSourceComplexGramVariety d n
      (sourceExtendedTubeGramDomain d n))
    (σ : Equiv.Perm (Fin n)) :
    IsRelOpenInSourceComplexGramVariety d n
      (sourceDoublePermutationGramDomain d n σ) := by
  have hpre :
      IsRelOpenInSourceComplexGramVariety d n
        {Z | sourcePermuteComplexGram n σ Z ∈ sourceExtendedTubeGramDomain d n} :=
    IsRelOpenInSourceComplexGramVariety.preimage_sourcePermuteComplexGram
      d n hU σ
  simpa [sourceDoublePermutationGramDomain] using
    IsRelOpenInSourceComplexGramVariety.inter d n hU hpre

/-- The legacy full adjacent scalar overlap domain is relatively open provided
the ordinary extended-tube scalar Gram domain is. -/
theorem sourceAdjacentPermutationGramOverlap_relOpen_of_sourceExtendedTubeGramDomain
    (d n : ℕ)
    (hU : IsRelOpenInSourceComplexGramVariety d n
      (sourceExtendedTubeGramDomain d n))
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    IsRelOpenInSourceComplexGramVariety d n
      (sourceAdjacentPermutationGramOverlap d n π i hi) := by
  simpa [sourceAdjacentPermutationGramOverlap] using
    sourceDoublePermutationGramDomain_relOpen_of_sourceExtendedTubeGramDomain
      d n hU (Equiv.swap i ⟨i.val + 1, hi⟩)

/-- Relative openness in the real Hall-Wightman scalar-product variety. -/
def IsRelOpenInSourceRealGramVariety
    (d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  ∃ E0 : Set (Fin n → Fin n → ℝ),
    IsOpen E0 ∧ E = E0 ∩ sourceRealGramVariety d n

/-- Hall-Wightman's real-environment condition on the scalar-product variety.

The environment is relatively open in the real scalar-product variety, is
realized by regular real Jost configurations, and is maximal totally real in
the complex scalar-product variety. -/
structure IsHWRealEnvironment
    (d n : ℕ)
    (O : Set (Fin n → Fin n → ℝ)) : Prop where
  nonempty : O.Nonempty
  relOpen : IsRelOpenInSourceRealGramVariety d n O
  realized_by_jost :
    ∀ G ∈ O, ∃ x : Fin n → Fin (d + 1) → ℝ,
      x ∈ JostSet d n ∧
      SourceGramRegularAt d n x ∧
      sourceRealMinkowskiGram d n x = G
  maximal_totally_real :
    ∀ G ∈ O, SourceComplexifiedRealTangentEqualsComplexTangent d n G

/-- Local ambient holomorphicity for scalar-product representatives on the
Hall-Wightman scalar-product variety.  This is the analytic-set style surface
needed beyond the small-arity full-matrix case. -/
def SourceVarietyHolomorphicOn
    (d n : ℕ)
    (Φ : (Fin n → Fin n → ℂ) → ℂ)
    (U : Set (Fin n → Fin n → ℂ)) : Prop :=
  ∀ Z ∈ U, ∃ U0 : Set (Fin n → Fin n → ℂ),
    IsOpen U0 ∧ Z ∈ U0 ∧ DifferentiableOn ℂ Φ U0 ∧
      U0 ∩ sourceComplexGramVariety d n ⊆ U

/-- Local ambient source-variety holomorphic representatives are continuous on
their variety domain. -/
theorem SourceVarietyHolomorphicOn.continuousOn
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    (hΦ : SourceVarietyHolomorphicOn d n Φ U) :
    ContinuousOn Φ U := by
  rw [continuousOn_iff]
  intro Z hZU T hT_open hΦZT
  rcases hΦ Z hZU with ⟨U0, hU0_open, hZU0, hDiffU0, _hU0_sub⟩
  have hContU0 : ContinuousOn Φ U0 := hDiffU0.continuousOn
  rcases (continuousOn_iff.mp hContU0) Z hZU0 T hT_open hΦZT with
    ⟨V, hV_open, hZV, hV_sub⟩
  refine ⟨V ∩ U0, hV_open.inter hU0_open, ⟨hZV, hZU0⟩, ?_⟩
  intro W hW
  exact hV_sub ⟨hW.1.1, hW.1.2⟩

/-- Restrict variety-holomorphicity from a set to a relatively open subset. -/
theorem SourceVarietyHolomorphicOn.of_subset_relOpen
    (d n : ℕ)
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    {U V : Set (Fin n → Fin n → ℂ)}
    (hΦ : SourceVarietyHolomorphicOn d n Φ U)
    (hV_rel : IsRelOpenInSourceComplexGramVariety d n V)
    (hVU : V ⊆ U) :
    SourceVarietyHolomorphicOn d n Φ V := by
  intro Z hZV
  rcases hΦ Z (hVU hZV) with ⟨U0, hU0_open, hZU0, hDiffU0, hU0_sub⟩
  rcases hV_rel with ⟨V0, hV0_open, hV0_eq⟩
  refine ⟨U0 ∩ V0, hU0_open.inter hV0_open, ⟨hZU0, ?_⟩, ?_, ?_⟩
  · rw [hV0_eq] at hZV
    exact hZV.1
  · exact hDiffU0.mono (by intro W hW; exact hW.1)
  · intro W hW
    rw [hV0_eq]
    exact ⟨hW.1.2, hW.2⟩

/-- Source-variety holomorphicity is stable under subtraction. -/
theorem SourceVarietyHolomorphicOn.sub
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {Φ Ψ : (Fin n → Fin n → ℂ) → ℂ}
    (hΦ : SourceVarietyHolomorphicOn d n Φ U)
    (hΨ : SourceVarietyHolomorphicOn d n Ψ U) :
    SourceVarietyHolomorphicOn d n (fun Z => Φ Z - Ψ Z) U := by
  intro Z hZU
  rcases hΦ Z hZU with ⟨UΦ, hUΦ_open, hZUΦ, hDiffΦ, hUΦ_sub⟩
  rcases hΨ Z hZU with ⟨UΨ, hUΨ_open, hZUΨ, hDiffΨ, _hUΨ_sub⟩
  refine ⟨UΦ ∩ UΨ, hUΦ_open.inter hUΨ_open, ⟨hZUΦ, hZUΨ⟩, ?_, ?_⟩
  · exact (hDiffΦ.mono (by intro W hW; exact hW.1)).sub
      (hDiffΨ.mono (by intro W hW; exact hW.2))
  · intro W hW
    exact hUΦ_sub ⟨hW.1.1, hW.2⟩

/-- Source-variety holomorphicity is stable under a source Gram coordinate
permutation. -/
theorem SourceVarietyHolomorphicOn.precomp_sourcePermuteComplexGram
    (d n : ℕ)
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    {U : Set (Fin n → Fin n → ℂ)}
    (hΦ : SourceVarietyHolomorphicOn d n Φ U)
    (σ : Equiv.Perm (Fin n)) :
    SourceVarietyHolomorphicOn d n
      (fun Z => Φ (sourcePermuteComplexGram n σ Z))
      {Z | sourcePermuteComplexGram n σ Z ∈ U} := by
  intro Z hZ
  rcases hΦ (sourcePermuteComplexGram n σ Z) hZ with
    ⟨U0, hU0_open, hZU0, hDiffU0, hU0_sub⟩
  refine ⟨{W | sourcePermuteComplexGram n σ W ∈ U0},
    hU0_open.preimage (continuous_sourcePermuteComplexGram n σ), hZU0, ?_, ?_⟩
  · exact hDiffU0.fun_comp
      (differentiable_sourcePermuteComplexGram n σ).differentiableOn
      (by intro W hW; exact hW)
  · intro W hW
    exact hU0_sub ⟨hW.1,
      (sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff d n σ W).2 hW.2⟩

/-- Germ-style holomorphicity on the source Gram variety.  The local
representative may differ from the global scalar function away from the source
Gram variety; equality is required only on the analytic variety slice. -/
def SourceVarietyGermHolomorphicOn
    (d n : ℕ)
    (Φ : (Fin n → Fin n → ℂ) → ℂ)
    (U : Set (Fin n → Fin n → ℂ)) : Prop :=
  ∀ Z ∈ U, ∃ U0 Ψ,
    IsOpen U0 ∧ Z ∈ U0 ∧ DifferentiableOn ℂ Ψ U0 ∧
      Set.EqOn Φ Ψ (U0 ∩ sourceComplexGramVariety d n) ∧
      U0 ∩ sourceComplexGramVariety d n ⊆ U

/-- Relatively open source-variety domains are subsets of the source Gram
variety. -/
theorem IsRelOpenInSourceComplexGramVariety.subset
    {d n : ℕ}
    {U : Set (Fin n → Fin n → ℂ)}
    (hU : IsRelOpenInSourceComplexGramVariety d n U) :
    U ⊆ sourceComplexGramVariety d n := by
  rcases hU with ⟨U0, _hU0_open, hU_eq⟩
  intro Z hZU
  rw [hU_eq] at hZU
  exact hZU.2

/-- A strong ambient representative is a germ representative, by taking the
local representative to be the function itself. -/
theorem SourceVarietyHolomorphicOn.to_germ
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    (hΦ : SourceVarietyHolomorphicOn d n Φ U) :
    SourceVarietyGermHolomorphicOn d n Φ U := by
  intro Z hZU
  rcases hΦ Z hZU with ⟨U0, hU0_open, hZU0, hDiffU0, hU0_sub⟩
  exact ⟨U0, Φ, hU0_open, hZU0, hDiffU0, (by intro W _; rfl), hU0_sub⟩

/-- Germ-holomorphic scalar representatives are continuous on relatively open
source-variety domains. -/
theorem SourceVarietyGermHolomorphicOn.continuousOn
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    (hΦ : SourceVarietyGermHolomorphicOn d n Φ U)
    (hU_sub : U ⊆ sourceComplexGramVariety d n) :
    ContinuousOn Φ U := by
  rw [continuousOn_iff]
  intro Z hZU T hT_open hΦZT
  rcases hΦ Z hZU with
    ⟨U0, Ψ, hU0_open, hZU0, hDiffU0, hEq, _hU0_sub⟩
  have hΨZT : Ψ Z ∈ T := by
    have hEqZ : Φ Z = Ψ Z := hEq ⟨hZU0, hU_sub hZU⟩
    simpa [hEqZ] using hΦZT
  have hContU0 : ContinuousOn Ψ U0 := hDiffU0.continuousOn
  rcases (continuousOn_iff.mp hContU0) Z hZU0 T hT_open hΨZT with
    ⟨V, hV_open, hZV, hV_sub⟩
  refine ⟨V ∩ U0, hV_open.inter hU0_open, ⟨hZV, hZU0⟩, ?_⟩
  intro W hW
  have hΨWT : Ψ W ∈ T := hV_sub ⟨hW.1.1, hW.1.2⟩
  have hEqW : Φ W = Ψ W := hEq ⟨hW.1.2, hU_sub hW.2⟩
  simpa [hEqW] using hΨWT

/-- Restrict germ holomorphicity from a source-variety domain to a relatively
open subdomain. -/
theorem SourceVarietyGermHolomorphicOn.of_subset_relOpen
    (d n : ℕ)
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    {U V : Set (Fin n → Fin n → ℂ)}
    (hΦ : SourceVarietyGermHolomorphicOn d n Φ U)
    (hV_rel : IsRelOpenInSourceComplexGramVariety d n V)
    (hVU : V ⊆ U) :
    SourceVarietyGermHolomorphicOn d n Φ V := by
  intro Z hZV
  rcases hΦ Z (hVU hZV) with
    ⟨U0, Ψ, hU0_open, hZU0, hDiffU0, hEq, _hU0_sub⟩
  rcases hV_rel with ⟨V0, hV0_open, hV0_eq⟩
  refine ⟨U0 ∩ V0, Ψ, hU0_open.inter hV0_open, ⟨hZU0, ?_⟩, ?_, ?_, ?_⟩
  · rw [hV0_eq] at hZV
    exact hZV.1
  · exact hDiffU0.mono (by intro W hW; exact hW.1)
  · intro W hW
    exact hEq ⟨hW.1.1, hW.2⟩
  · intro W hW
    rw [hV0_eq]
    exact ⟨hW.1.2, hW.2⟩

/-- Germ holomorphicity is stable under subtraction. -/
theorem SourceVarietyGermHolomorphicOn.sub
    (d n : ℕ)
    {U : Set (Fin n → Fin n → ℂ)}
    {Φ Ψ : (Fin n → Fin n → ℂ) → ℂ}
    (hΦ : SourceVarietyGermHolomorphicOn d n Φ U)
    (hΨ : SourceVarietyGermHolomorphicOn d n Ψ U) :
    SourceVarietyGermHolomorphicOn d n (fun Z => Φ Z - Ψ Z) U := by
  intro Z hZU
  rcases hΦ Z hZU with
    ⟨UΦ, Φ0, hUΦ_open, hZUΦ, hDiffΦ, hEqΦ, hUΦ_sub⟩
  rcases hΨ Z hZU with
    ⟨UΨ, Ψ0, hUΨ_open, hZUΨ, hDiffΨ, hEqΨ, _hUΨ_sub⟩
  refine ⟨UΦ ∩ UΨ, (fun W => Φ0 W - Ψ0 W),
    hUΦ_open.inter hUΨ_open, ⟨hZUΦ, hZUΨ⟩, ?_, ?_, ?_⟩
  · exact (hDiffΦ.mono (by intro W hW; exact hW.1)).sub
      (hDiffΨ.mono (by intro W hW; exact hW.2))
  · intro W hW
    have hΦW : Φ W = Φ0 W := hEqΦ ⟨hW.1.1, hW.2⟩
    have hΨW : Ψ W = Ψ0 W := hEqΨ ⟨hW.1.2, hW.2⟩
    simp [hΦW, hΨW]
  · intro W hW
    exact hUΦ_sub ⟨hW.1.1, hW.2⟩

/-- Germ holomorphicity is stable under a source Gram coordinate
permutation. -/
theorem SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram
    (d n : ℕ)
    {Φ : (Fin n → Fin n → ℂ) → ℂ}
    {U : Set (Fin n → Fin n → ℂ)}
    (hΦ : SourceVarietyGermHolomorphicOn d n Φ U)
    (σ : Equiv.Perm (Fin n)) :
    SourceVarietyGermHolomorphicOn d n
      (fun Z => Φ (sourcePermuteComplexGram n σ Z))
      {Z | sourcePermuteComplexGram n σ Z ∈ U} := by
  intro Z hZ
  rcases hΦ (sourcePermuteComplexGram n σ Z) hZ with
    ⟨U0, Ψ, hU0_open, hZU0, hDiffU0, hEq, hU0_sub⟩
  refine ⟨{W | sourcePermuteComplexGram n σ W ∈ U0},
    (fun W => Ψ (sourcePermuteComplexGram n σ W)),
    hU0_open.preimage (continuous_sourcePermuteComplexGram n σ), hZU0, ?_, ?_, ?_⟩
  · exact hDiffU0.fun_comp
      (differentiable_sourcePermuteComplexGram n σ).differentiableOn
      (by intro W hW; exact hW)
  · intro W hW
    exact hEq ⟨hW.1,
      (sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff d n σ W).2 hW.2⟩
  · intro W hW
    exact hU0_sub ⟨hW.1,
      (sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff d n σ W).2 hW.2⟩

/-- A Hall-Wightman real Gram environment which is a uniqueness set for
variety-holomorphic scalar-product representatives.

This is the theorem-2-facing uniqueness predicate: agreement on `E` determines
variety-holomorphic scalar-product representatives on connected relatively
open domains in the scalar-product variety. -/
def sourceDistributionalUniquenessSetOnVariety
    (d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (Fin n → Fin n → ℂ))
      (Φ Ψ : (Fin n → Fin n → ℂ) → ℂ),
      IsRelOpenInSourceComplexGramVariety d n U →
      IsConnected U →
      (∀ G ∈ E, sourceRealGramComplexify n G ∈ U) →
      SourceVarietyGermHolomorphicOn d n Φ U →
      SourceVarietyGermHolomorphicOn d n Ψ U →
      (∀ G ∈ E, Φ (sourceRealGramComplexify n G) =
        Ψ (sourceRealGramComplexify n G)) →
      Set.EqOn Φ Ψ U

/-- Variety-level uniqueness is monotone in the real environment.  This lets
the OS supplier enlarge a small Hall-Wightman real environment to the whole
Gram image of the selected Jost patch without losing uniqueness. -/
theorem sourceDistributionalUniquenessSetOnVariety_mono
    (d n : ℕ)
    {O E : Set (Fin n → Fin n → ℝ)}
    (hO : sourceDistributionalUniquenessSetOnVariety d n O)
    (hOE : O ⊆ E) :
    sourceDistributionalUniquenessSetOnVariety d n E := by
  refine ⟨hO.1.mono hOE, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hE_sub hΦ hΨ h_eq
  exact hO.2 U Φ Ψ hU_rel hU_conn
    (fun G hG => hE_sub G (hOE hG))
    hΦ hΨ
    (fun G hG => h_eq G (hOE hG))

/-- A full-matrix real Gram environment which is a uniqueness set for
holomorphic scalar-product representatives.

This is a sufficient small/full-dimensional criterion, not the general
Hall-Wightman scalar-product-variety predicate needed by the OS supplier in
arbitrary arity. -/
def sourceDistributionalUniquenessSet
    (_d n : ℕ)
    (E : Set (Fin n → Fin n → ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (Fin n → Fin n → ℂ))
      (Φ Ψ : (Fin n → Fin n → ℂ) → ℂ),
      IsOpen U →
      IsConnected U →
      (∀ G ∈ E, sourceRealGramComplexify n G ∈ U) →
      DifferentiableOn ℂ Φ U →
      DifferentiableOn ℂ Ψ U →
      (∀ G ∈ E, Φ (sourceRealGramComplexify n G) =
        Ψ (sourceRealGramComplexify n G)) →
      Set.EqOn Φ Ψ U

/-- Any nonempty open real Gram environment is a uniqueness set for
holomorphic scalar-product representatives. -/
theorem sourceDistributionalUniquenessSet_of_isOpen_nonempty
    (d n : ℕ)
    {E : Set (Fin n → Fin n → ℝ)}
    (hE_open : IsOpen E)
    (hE_ne : E.Nonempty) :
    sourceDistributionalUniquenessSet d n E := by
  refine ⟨hE_ne, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  have hsub :
      ∀ G ∈ E, SCV.realToComplexProduct G ∈ U := by
    intro G hG
    simpa [sourceRealGramComplexify, SCV.realToComplexProduct] using
      hE_sub G hG
  have hzero :
      ∀ G ∈ E, (Φ - Ψ) (SCV.realToComplexProduct G) = 0 := by
    intro G hG
    have hG_eq := h_eq G hG
    simpa [sourceRealGramComplexify, SCV.realToComplexProduct, sub_eq_zero] using hG_eq
  have hident :
      ∀ Z ∈ U, (Φ - Ψ) Z = 0 :=
    SCV.identity_theorem_totally_real_product
      (n := n) (p := n)
      hU_open hU_conn (hΦ.sub hΨ) hE_open hE_ne hsub hzero
  intro Z hZ
  exact sub_eq_zero.mp (hident Z hZ)

/-- A real Gram environment containing a nonempty open real subset is a
uniqueness set for holomorphic scalar-product representatives.

This is a sufficient full-matrix criterion.  The general Hall-Wightman
supplier for arbitrary arity works on the scalar-product variety; a realized
Gram image need not contain an open subset of the full matrix coordinate
space. -/
theorem sourceDistributionalUniquenessSet_of_contains_open
    (d n : ℕ)
    {E O : Set (Fin n → Fin n → ℝ)}
    (hO_open : IsOpen O)
    (hO_ne : O.Nonempty)
    (hO_sub : O ⊆ E) :
    sourceDistributionalUniquenessSet d n E := by
  have hE_ne : E.Nonempty := by
    rcases hO_ne with ⟨G, hG⟩
    exact ⟨G, hO_sub hG⟩
  refine ⟨hE_ne, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  exact
    (sourceDistributionalUniquenessSet_of_isOpen_nonempty
      (d := d) (n := n) hO_open hO_ne).2
      U Φ Ψ hU_open hU_conn
      (fun G hG => hE_sub G (hO_sub hG))
      hΦ hΨ
      (fun G hG => h_eq G (hO_sub hG))

/-- Distributional Euclidean/Jost anchor for adjacent PET branches.

The fields are indexed by a PET sector label `π` and an adjacent transposition.
They record the real Jost patches on which both adjacent branches have boundary
values, the scalar-product uniqueness environments, and the compact-test
equality of the two branch boundary distributions there. -/
structure SourceDistributionalAdjacentTubeAnchor
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  realPatch :
    Equiv.Perm (Fin n) →
    (i : Fin n) →
    (hi : i.val + 1 < n) →
    Set (Fin n → Fin (d + 1) → ℝ)
  realPatch_open :
    ∀ π i hi, IsOpen (realPatch π i hi)
  realPatch_nonempty :
    ∀ π i hi, (realPatch π i hi).Nonempty
  realPatch_jost :
    ∀ π i hi, realPatch π i hi ⊆ JostSet d n
  realPatch_left_sector :
    ∀ π i hi x, x ∈ realPatch π i hi →
      realEmbed x ∈ permutedExtendedTubeSector d n π
  realPatch_right_sector :
    ∀ π i hi x, x ∈ realPatch π i hi →
      realEmbed x ∈
        permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩)
  gramEnvironment :
    Equiv.Perm (Fin n) →
    (i : Fin n) →
    (hi : i.val + 1 < n) →
    Set (Fin n → Fin n → ℝ)
  gramEnvironment_unique :
    ∀ π i hi,
      sourceDistributionalUniquenessSetOnVariety d n
        (gramEnvironment π i hi)
  gram_left_mem :
    ∀ π i hi x, x ∈ realPatch π i hi →
      sourceRealMinkowskiGram d n (fun k => x (π k)) ∈
        gramEnvironment π i hi
  gram_environment_realized :
    ∀ π i hi G, G ∈ gramEnvironment π i hi →
      ∃ x ∈ realPatch π i hi,
        sourceRealMinkowskiGram d n (fun k => x (π k)) = G
  gram_right_eq_perm_left :
    ∀ π i hi x, x ∈ realPatch π i hi →
      sourceRealMinkowskiGram d n
          (fun k => x ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
        sourcePermuteGram n (Equiv.swap i ⟨i.val + 1, hi⟩)
          (sourceRealMinkowskiGram d n (fun k => x (π k)))
  compact_branch_eq :
    ∀ π i hi (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
      HasCompactSupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) →
      tsupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ⊆ realPatch π i hi →
      ∫ x : Fin n → Fin (d + 1) → ℝ,
          extendF F (fun k => realEmbed x (π k)) * φ x
        =
      ∫ x : Fin n → Fin (d + 1) → ℝ,
          extendF F
            (fun k => realEmbed x
              ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) *
            φ x

/-- Every anchor Gram environment is nonempty. -/
theorem SourceDistributionalAdjacentTubeAnchor.gramEnvironment_nonempty
    [NeZero d]
    {n : ℕ}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    (hAnchor.gramEnvironment π i hi).Nonempty := by
  rcases hAnchor.realPatch_nonempty π i hi with ⟨x, hx⟩
  refine ⟨sourceRealMinkowskiGram d n (fun k => x (π k)), ?_⟩
  exact hAnchor.gram_left_mem π i hi x hx

/-- Hall-Wightman scalar-product representative data for the ordinary
extended-tube branch.

The representative lives on the scalar-product image of the ordinary extended
tube.  For arity above the spacetime dimension this is a relatively open
domain in the Hall-Wightman Gram variety, not an open subset of the full
matrix coordinate space. -/
structure SourceScalarRepresentativeData
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  U : Set (Fin n → Fin n → ℂ)
  U_eq : U = sourceExtendedTubeGramDomain d n
  U_relOpen : IsRelOpenInSourceComplexGramVariety d n U
  U_connected : IsConnected U
  Phi : (Fin n → Fin n → ℂ) → ℂ
  Phi_holomorphic : SourceVarietyGermHolomorphicOn d n Phi U
  branch_eq :
    ∀ w : Fin n → Fin (d + 1) → ℂ,
      w ∈ ExtendedTube d n →
      Phi (sourceMinkowskiGram d n w) = extendF F w

/-- Witness data for the local Hall-Wightman scalar overlap attached to one
adjacent source real environment.

This is the final theorem-shape intended by the theorem-2 proof docs: the
overlap is not a bare set determined only by `(d,n,π,i,hi)`, but a chosen
connected relatively open scalar-domain neighbourhood carrying the adjacent
real-environment uniqueness step.  The current placeholder
`sourceAdjacentPermutationGramOverlap d n π i hi` remains in the file for the
legacy route, but new theorem-2 source development should target this witness
package instead. -/
structure SourceAdjacentOverlapWitness
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) where
  U : Set (Fin n → Fin n → ℂ)
  U_relOpen : IsRelOpenInSourceComplexGramVariety d n U
  overlap : Set (Fin n → Fin n → ℂ)
  overlap_relOpen : IsRelOpenInSourceComplexGramVariety d n overlap
  overlap_connected : IsConnected overlap
  overlap_subset :
    overlap ⊆
      sourceDoublePermutationGramDomain d n (Equiv.swap i ⟨i.val + 1, hi⟩) ∩ U
  environment_mem_overlap :
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      sourceRealGramComplexify n G ∈ overlap

/-- Witness-based seed cover for one adjacent transposition.

This is the union of all chosen adjacent overlap components for all permutation
labels whose adjacent swap realizes the given transposition.  It is the
source-side carrier for the Hall-Wightman continuation step from local
real-environment uniqueness to the full adjacent double scalar-product domain. -/
def sourceAdjacentSeedCover
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin n → ℂ) :=
  {Z | ∃ (i : Fin n) (hi : i.val + 1 < n),
      τ = Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ∃ (π : Equiv.Perm (Fin n))
        (data : SourceAdjacentOverlapWitness
          (d := d) n F hRep hAnchor π i hi),
        Z ∈ data.overlap}

/-- Active permutation labels for a witness-based adjacent overlap family. -/
def sourceAdjacentOverlapLabelSet
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (i : Fin n)
    (hi : i.val + 1 < n) :
    Set (Equiv.Perm (Fin n)) :=
  {π | ∃ data : SourceAdjacentOverlapWitness
      (d := d) n F hRep hAnchor π i hi,
      data.overlap.Nonempty}

/-- A chosen adjacent overlap witness activates its permutation label. -/
theorem mem_sourceAdjacentOverlapLabelSet_of_witness
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi) :
    π ∈ sourceAdjacentOverlapLabelSet n F hRep hAnchor i hi := by
  rcases hAnchor.gramEnvironment_nonempty π i hi with ⟨G, hG⟩
  refine ⟨data, ?_⟩
  exact ⟨sourceRealGramComplexify n G, data.environment_mem_overlap G hG⟩

/-- Every chosen adjacent overlap component contributes to the corresponding
witness-based adjacent seed cover. -/
theorem sourceAdjacentPermutationGramOverlap_subset_seedCover
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi) :
    data.overlap ⊆
      sourceAdjacentSeedCover n F hRep hAnchor
        (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  intro Z hZ
  refine ⟨i, hi, rfl, π, data, hZ⟩

/-- Real Gram points from the anchor environment lie in the witness-based
adjacent seed cover attached to the same adjacent swap. -/
theorem gramEnvironment_complexify_mem_adjacentSeedCover
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi) :
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      sourceRealGramComplexify n G ∈
        sourceAdjacentSeedCover n F hRep hAnchor
          (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  intro G hG
  exact sourceAdjacentPermutationGramOverlap_subset_seedCover
      (d := d) n F hRep hAnchor π i hi data
      (data.environment_mem_overlap G hG)

/-- The anchor real Gram environment carried by a witness lies in the chosen
Hall-Wightman local scalar neighbourhood `U`. -/
theorem gramEnvironment_complexify_mem_overlapNeighborhood
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi) :
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      sourceRealGramComplexify n G ∈ data.U := by
  intro G hG
  exact (data.overlap_subset (data.environment_mem_overlap G hG)).2

/-- Any point in a chosen adjacent overlap witness lies in the corresponding
adjacent seed cover.  This is the corollary form of the witness-based route
used by the proof docs before the genuinely geometric cover-reaching theorem is
proved. -/
theorem mem_sourceAdjacentSeedCover_of_mem_overlap
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi)
    {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ data.overlap) :
    Z ∈ sourceAdjacentSeedCover n F hRep hAnchor
      (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  exact sourceAdjacentPermutationGramOverlap_subset_seedCover
    (d := d) n F hRep hAnchor π i hi data hZ

/-- Every point in the witness-based adjacent seed cover lies in the
corresponding adjacent double scalar-product domain. -/
theorem sourceAdjacentSeedCover_subset_doubleDomain
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (τ : Equiv.Perm (Fin n)) :
    sourceAdjacentSeedCover n F hRep hAnchor τ ⊆
      sourceDoublePermutationGramDomain d n τ := by
  intro Z hZ
  rcases hZ with ⟨i, hi, hτ, π, data, hZoverlap⟩
  have hmem :
      Z ∈ sourceDoublePermutationGramDomain d n
        (Equiv.swap i ⟨i.val + 1, hi⟩) :=
    (data.overlap_subset hZoverlap).1
  simpa [hτ] using hmem

/-- The legacy full adjacent scalar overlap domain is relatively open once the
Hall-Wightman scalar representative has supplied relative openness of the
ordinary extended-tube scalar Gram domain. -/
theorem sourceAdjacentPermutationGramOverlap_relOpen
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    IsRelOpenInSourceComplexGramVariety d n
      (sourceAdjacentPermutationGramOverlap d n π i hi) := by
  have hU :
      IsRelOpenInSourceComplexGramVariety d n
        (sourceExtendedTubeGramDomain d n) := by
    simpa [hRep.U_eq] using hRep.U_relOpen
  simpa using
    sourceAdjacentPermutationGramOverlap_relOpen_of_sourceExtendedTubeGramDomain
      d n hU π i hi

 /-- Local adjacent equality on one chosen Hall-Wightman overlap component.

This is the active theorem-2 frontier theorem `(A)` on the witness-based
source overlap route.  It is the correct production stepping stone for
downstream theorem-2 development: the proof transcript is documented in the
blueprint, while the global Hall-Wightman source theorem remains outside the
active production frontier. -/
theorem sourceScalarRepresentative_adjacent_eq_on_overlap_of_realEnvironment
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (data : SourceAdjacentOverlapWitness (d := d) n F hRep hAnchor π i hi)
    (hSeed :
      let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
      ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
        hRep.Phi (sourceRealGramComplexify n G) =
          hRep.Phi
            (sourcePermuteComplexGram n τ
              (sourceRealGramComplexify n G))) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∀ Z, Z ∈ data.overlap →
      hRep.Phi (sourcePermuteComplexGram n τ Z) = hRep.Phi Z := by
  dsimp
  have _hd : 2 <= d := hd
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let Ψ : (Fin n → Fin n → ℂ) → ℂ :=
    fun W => hRep.Phi (sourcePermuteComplexGram n τ W)
  have hOverlap_subset_repU : data.overlap ⊆ hRep.U := by
    intro Z hZ
    have hdouble : Z ∈ sourceDoublePermutationGramDomain d n τ :=
      (data.overlap_subset hZ).1
    simpa [hRep.U_eq, τ] using hdouble.1
  have hPerm_overlap_subset_repU :
      data.overlap ⊆ {Z | sourcePermuteComplexGram n τ Z ∈ hRep.U} := by
    intro Z hZ
    have hdouble : Z ∈ sourceDoublePermutationGramDomain d n τ :=
      (data.overlap_subset hZ).1
    simpa [hRep.U_eq, τ] using hdouble.2
  have hΦ : SourceVarietyGermHolomorphicOn d n hRep.Phi data.overlap :=
    SourceVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n) hRep.Phi_holomorphic
      data.overlap_relOpen hOverlap_subset_repU
  have hΨ : SourceVarietyGermHolomorphicOn d n Ψ data.overlap := by
    have hpre : SourceVarietyGermHolomorphicOn d n Ψ
        {Z | sourcePermuteComplexGram n τ Z ∈ hRep.U} := by
      simpa [Ψ] using
        SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram
          (d := d) (n := n) hRep.Phi_holomorphic τ
    exact SourceVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n) hpre data.overlap_relOpen
      hPerm_overlap_subset_repU
  have hreal :
      ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
        hRep.Phi (sourceRealGramComplexify n G) =
          Ψ (sourceRealGramComplexify n G) := by
    intro G hG
    simpa [Ψ, τ] using hSeed G hG
  have hEqOn : Set.EqOn hRep.Phi Ψ data.overlap :=
    (hAnchor.gramEnvironment_unique π i hi).2
      data.overlap hRep.Phi Ψ data.overlap_relOpen
      data.overlap_connected data.environment_mem_overlap hΦ hΨ hreal
  intro Z hZ
  exact (hEqOn hZ).symm

/- The unresolved Hall-Wightman source existence theorem for this data is kept
in the proof docs until it has a checked proof or an explicitly approved source
import boundary.  This production module contains only checked source data and
support lemmas. -/

/-- Compact-test equality in the adjacent source anchor gives pointwise
equality on the selected real patch. -/
theorem sourceAnchor_compactBranchEq_pointwise_on_realPatch
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    ∀ x, x ∈ hAnchor.realPatch π i hi →
      extendF F (fun k => realEmbed x (π k)) =
        extendF F
          (fun k =>
            realEmbed x
              ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) := by
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExtend_cont : ContinuousOn (extendF F) (ExtendedTube d n) :=
    (extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hleftEmbed_cont :
      Continuous
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          fun k => realEmbed x (π k)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply (π k)))
  have hrightEmbed_cont :
      Continuous
        (fun x : Fin n → Fin (d + 1) → ℝ =>
          fun k => realEmbed x
            ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp
        (continuous_apply ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)))
  let L : (Fin n → Fin (d + 1) → ℝ) → ℂ :=
    fun x => extendF F (fun k => realEmbed x (π k))
  let R : (Fin n → Fin (d + 1) → ℝ) → ℂ :=
    fun x =>
      extendF F
        (fun k => realEmbed x
          ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k))
  have hL_cont : ContinuousOn L (hAnchor.realPatch π i hi) := by
    refine hExtend_cont.comp hleftEmbed_cont.continuousOn ?_
    intro x hx
    simpa [L, permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_left_sector π i hi x hx
  have hR_cont : ContinuousOn R (hAnchor.realPatch π i hi) := by
    refine hExtend_cont.comp hrightEmbed_cont.continuousOn ?_
    intro x hx
    simpa [R, permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_right_sector π i hi x hx
  have hEqOn : Set.EqOn L R (hAnchor.realPatch π i hi) := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      (hAnchor.realPatch_open π i hi) hL_cont hR_cont ?_
    intro φ hφ_compact hφ_tsupport
    exact hAnchor.compact_branch_eq π i hi φ hφ_compact hφ_tsupport
  intro x hx
  exact hEqOn hx

/-- Adjacent compact-test equality rewritten as equality of the
Hall-Wightman scalar-product representative on the real Gram environment. -/
theorem sourceScalarRepresentative_adjacent_seed_eq_on_environment
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hRep : SourceScalarRepresentativeData (d := d) n F)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      hRep.Phi (sourceRealGramComplexify n G) =
        hRep.Phi
          (sourcePermuteComplexGram n τ
            (sourceRealGramComplexify n G)) := by
  dsimp
  intro G hG
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  change
    hRep.Phi (sourceRealGramComplexify n G) =
      hRep.Phi
        (sourcePermuteComplexGram n τ
          (sourceRealGramComplexify n G))
  rcases hAnchor.gram_environment_realized π i hi G hG with
    ⟨x, hxPatch, hGx⟩
  have hpoint :
      extendF F (fun k => realEmbed x (π k)) =
        extendF F (fun k => realEmbed x ((π * τ) k)) := by
    simpa [τ] using
      sourceAnchor_compactBranchEq_pointwise_on_realPatch
        (d := d) n F hF_holo hF_lorentz hAnchor π i hi x hxPatch
  have hleft_ET :
      realEmbed (fun k => x (π k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_left_sector π i hi x hxPatch
  have hright_ET :
      realEmbed (fun k => x ((π * τ) k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed, τ] using
      hAnchor.realPatch_right_sector π i hi x hxPatch
  have hleft :
      hRep.Phi (sourceRealGramComplexify n G) =
        extendF F (fun k => realEmbed x (π k)) := by
    simpa [hGx, sourceMinkowskiGram_realEmbed, realEmbed] using
      hRep.branch_eq (realEmbed (fun k => x (π k))) hleft_ET
  have hrightReal :
      sourceRealMinkowskiGram d n (fun k => x ((π * τ) k)) =
        sourcePermuteGram n τ
          (sourceRealMinkowskiGram d n (fun k => x (π k))) := by
    simpa [τ] using hAnchor.gram_right_eq_perm_left π i hi x hxPatch
  have hrightGram :
      sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k))) =
        sourcePermuteComplexGram n τ (sourceRealGramComplexify n G) := by
    calc
      sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k)))
          = sourceRealGramComplexify n
              (sourceRealMinkowskiGram d n (fun k => x ((π * τ) k))) := by
            exact sourceMinkowskiGram_realEmbed
              (d := d) (n := n) (fun k => x ((π * τ) k))
      _ = sourceRealGramComplexify n
            (sourcePermuteGram n τ
              (sourceRealMinkowskiGram d n (fun k => x (π k)))) := by
            rw [hrightReal]
      _ = sourceRealGramComplexify n (sourcePermuteGram n τ G) := by
            rw [hGx]
      _ = sourcePermuteComplexGram n τ (sourceRealGramComplexify n G) :=
            sourceRealGramComplexify_perm (n := n) τ G
  have hright :
      hRep.Phi
          (sourcePermuteComplexGram n τ (sourceRealGramComplexify n G)) =
        extendF F (fun k => realEmbed x ((π * τ) k)) := by
    rw [← hrightGram]
    simpa [realEmbed, Equiv.Perm.mul_apply] using
      hRep.branch_eq (realEmbed (fun k => x ((π * τ) k))) hright_ET
  exact hleft.trans (hpoint.trans hright.symm)

/-- Real Gram points coming from an adjacent Hall-Wightman environment lie in
the corresponding adjacent double scalar-product domain. -/
theorem sourceRealGramComplexify_mem_sourceDoublePermutationGramDomain_of_environment
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      sourceRealGramComplexify n G ∈ sourceDoublePermutationGramDomain d n τ := by
  dsimp
  intro G hG
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases hAnchor.gram_environment_realized π i hi G hG with ⟨x, hxPatch, hGx⟩
  have hleft_ET :
      realEmbed (fun k => x (π k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed] using
      hAnchor.realPatch_left_sector π i hi x hxPatch
  have hright_ET :
      realEmbed (fun k => x ((π * τ) k)) ∈ ExtendedTube d n := by
    simpa [permutedExtendedTubeSector, realEmbed, τ] using
      hAnchor.realPatch_right_sector π i hi x hxPatch
  have hleftGram :
      sourceRealGramComplexify n G =
        sourceMinkowskiGram d n (realEmbed (fun k => x (π k))) := by
    rw [← hGx]
    symm
    exact sourceMinkowskiGram_realEmbed d n (fun k => x (π k))
  have hrightReal :
      sourceRealMinkowskiGram d n (fun k => x ((π * τ) k)) =
        sourcePermuteGram n τ
          (sourceRealMinkowskiGram d n (fun k => x (π k))) := by
    simpa [τ] using hAnchor.gram_right_eq_perm_left π i hi x hxPatch
  have hrightGram :
      sourcePermuteComplexGram n τ (sourceRealGramComplexify n G) =
        sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k))) := by
    calc
      sourcePermuteComplexGram n τ (sourceRealGramComplexify n G)
          = sourceRealGramComplexify n (sourcePermuteGram n τ G) := by
              simpa using (sourceRealGramComplexify_perm (n := n) τ G).symm
      _ = sourceRealGramComplexify n
            (sourcePermuteGram n τ
              (sourceRealMinkowskiGram d n (fun k => x (π k)))) := by
              rw [hGx]
      _ = sourceRealGramComplexify n
            (sourceRealMinkowskiGram d n (fun k => x ((π * τ) k))) := by
              rw [hrightReal]
      _ = sourceMinkowskiGram d n (realEmbed (fun k => x ((π * τ) k))) := by
              exact (sourceMinkowskiGram_realEmbed
                (d := d) (n := n) (fun k => x ((π * τ) k))).symm
  refine ⟨?_, ?_⟩
  · rw [hleftGram]
    exact ⟨realEmbed (fun k => x (π k)), hleft_ET, rfl⟩
  · rw [hrightGram]
    exact ⟨realEmbed (fun k => x ((π * τ) k)), hright_ET, rfl⟩

/-- Real Gram points from an adjacent Hall-Wightman environment lie in the
legacy full adjacent overlap domain. -/
theorem gramEnvironment_complexify_mem_adjacentOverlap
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    ∀ G, G ∈ hAnchor.gramEnvironment π i hi →
      sourceRealGramComplexify n G ∈
        sourceAdjacentPermutationGramOverlap d n π i hi := by
  intro G hG
  simpa [sourceAdjacentPermutationGramOverlap] using
    sourceRealGramComplexify_mem_sourceDoublePermutationGramDomain_of_environment
      (d := d) (n := n) F hAnchor π i hi G hG

/- The scalar-overlap continuation theorem from adjacent real Gram seeds is
also deliberately not exposed as production Lean yet.  The checked theorem
above is the last local support lemma before that genuine Hall-Wightman source
obligation. -/

private theorem source_lorentz_perm_commute
    (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
      fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ
  simp only [complexLorentzAction]

private theorem source_complexLorentzAction_mem_extendedTube
    (n : ℕ)
    (Λ : ComplexLorentzGroup d)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n) :
    complexLorentzAction Λ z ∈ ExtendedTube d n := by
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  exact Set.mem_iUnion.mpr ⟨Λ * Γ, w, hw, by rw [complexLorentzAction_mul]⟩

private theorem source_permutedExtendedTubeSector_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ z ∈ permutedExtendedTubeSector d n π ↔
      z ∈ permutedExtendedTubeSector d n π := by
  constructor
  · intro h
    have h' : complexLorentzAction Λ⁻¹
        (fun k => (complexLorentzAction Λ z) (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ⁻¹ h
    have hrewrite :
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k)) =
          fun k => z (π k) := by
      calc
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k))
            = complexLorentzAction Λ⁻¹
                (complexLorentzAction Λ (fun k => z (π k))) := by
                simp [source_lorentz_perm_commute]
        _ = fun k => z (π k) := by
                rw [complexLorentzAction_inv]
    rw [hrewrite] at h'
    simpa [permutedExtendedTubeSector] using h'
  · intro h
    have h' : complexLorentzAction Λ (fun k => z (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ h
    have hrewrite :
        (fun k => (complexLorentzAction Λ z) (π k)) =
      complexLorentzAction Λ (fun k => z (π k)) := by
      simp [source_lorentz_perm_commute]
    rw [← hrewrite] at h'
    simpa [permutedExtendedTubeSector] using h'

/-- The raw permuted forward-tube branch is holomorphic on its permuted
forward-tube sector.  This packages the `S'_n` datum before BHW enlargement. -/
private theorem source_permutedForwardBranch_holomorphicOn
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => F (fun k => z (π k)))
      (PermutedForwardTube d n π) := by
  intro z hz
  have hzFT : (fun k => z (π k)) ∈ ForwardTube d n := by
    simpa [PermutedForwardTube] using hz
  have hF_at :
      DifferentiableAt ℂ F (fun k => z (π k)) := by
    exact (hF_holo (fun k => z (π k)) hzFT).differentiableAt
      (isOpen_forwardTube.mem_nhds hzFT)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => F (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hF_at.comp z hperm_diff.differentiableAt
  exact hbranch_at.differentiableWithinAt

/-- Restricted real Lorentz invariance transported to each raw permuted
forward-tube branch. -/
private theorem source_permutedForwardBranch_restrictedLorentzInvariant
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (π : Equiv.Perm (Fin n)) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ PermutedForwardTube d n π →
      (fun z' : Fin n → Fin (d + 1) → ℂ => F (fun k => z' (π k)))
        (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) =
      F (fun k => z (π k)) := by
  intro Λ z hz
  have hzFT : (fun k => z (π k)) ∈ ForwardTube d n := by
    simpa [PermutedForwardTube] using hz
  have hcomm :
      (fun k => (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) (π k)) =
        complexLorentzAction (ComplexLorentzGroup.ofReal Λ) (fun k => z (π k)) := by
    simpa using
      (source_lorentz_perm_commute (d := d) (n := n)
        (ComplexLorentzGroup.ofReal Λ) z π).symm
  calc
    (fun z' : Fin n → Fin (d + 1) → ℂ => F (fun k => z' (π k)))
        (complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z)
        = F (complexLorentzAction (ComplexLorentzGroup.ofReal Λ)
            (fun k => z (π k))) := by
            simpa using congrArg F hcomm
    _ = F (fun k => z (π k)) := hF_lorentz Λ (fun k => z (π k)) hzFT

/-- The permutation symmetry hypothesis identifies all raw permuted
forward-tube branches as one symmetric `S'_n` datum. -/
private theorem source_permutedForwardBranch_symmetric
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        F (fun k => z (σ k)) = F z) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      F (fun k => z (π k)) = F (fun k => z (ρ k)) := by
  intro π ρ z
  exact (hF_perm π z).trans (hF_perm ρ z).symm

/-- Each permuted `extendF` branch is holomorphic on its PET sector.  This is a
local analytic sub-obligation for the source theorem below; it uses only the
forward-tube BHW continuation theorem and derives complex-Lorentz overlap
invariance from restricted real Lorentz invariance. -/
theorem permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => z (π k)))
      (permutedExtendedTubeSector d n π) := by
  intro z hz
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExt_at :
      DifferentiableAt ℂ (extendF F) (fun k => z (π k)) := by
    exact
      ((extendF_holomorphicOn n F hF_holo hF_cinv)
        (fun k => z (π k)) hz).differentiableAt
        (isOpen_extendedTube.mem_nhds hz)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hExt_at.comp z hperm_diff.differentiableAt
  exact hbranch_at.differentiableWithinAt

/- The PET branch law, PET extension theorem, and sector single-valuedness
corollary are likewise proof-doc obligations until the Hall-Wightman source
compatibility theorem is proved. -/

end BHW
