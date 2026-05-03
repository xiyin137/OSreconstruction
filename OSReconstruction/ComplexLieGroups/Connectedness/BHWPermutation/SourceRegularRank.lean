import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Implicit
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension

/-!
# Regular source Gram rank support

This companion file continues the source-coordinate Hall-Wightman regular
stratum development after `SourceExtension.lean`.  The source-extension file
now contains the checked regular-locus/minor package and is intentionally kept
stable; the differential-rank and local-chart support lives here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- The real source Gram map is smooth because each coordinate is a finite sum
of quadratic coordinate monomials. -/
theorem contDiff_sourceRealMinkowskiGram
    (d n : ℕ) :
    ContDiff ℝ ⊤ (sourceRealMinkowskiGram d n) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  unfold sourceRealMinkowskiGram
  apply ContDiff.sum
  intro μ _
  exact ((contDiff_const.mul (contDiff_apply_apply ℝ ℝ i μ)).mul
    (contDiff_apply_apply ℝ ℝ j μ))

/-- A nonzero maximal source coordinate minor makes the selected source rows
linearly independent. -/
theorem linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    LinearIndependent ℝ (fun a : Fin (min n (d + 1)) => x (I a)) := by
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
    exact Matrix.linearIndependent_rows_of_det_ne_zero hminor
  apply LinearIndependent.of_comp restrictJ
  simpa [Function.comp_def, restrictJ] using hrows

/-- A nonzero maximal source coordinate minor selects rows whose span is the
whole source configuration span. -/
theorem span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    Submodule.span ℝ
        (Set.range (fun a : Fin (min n (d + 1)) => x (I a))) =
      sourceConfigurationSpan d n x := by
  let T : Submodule ℝ (Fin (d + 1) → ℝ) :=
    Submodule.span ℝ
      (Set.range (fun a : Fin (min n (d + 1)) => x (I a)))
  let S : Submodule ℝ (Fin (d + 1) → ℝ) := sourceConfigurationSpan d n x
  have hxI : LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) => x (I a)) :=
    linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero d n hminor
  have hTS : T ≤ S := by
    have hrange : Set.range
        (fun a : Fin (min n (d + 1)) => x (I a)) ⊆ Set.range x := by
      rintro _ ⟨a, rfl⟩
      exact ⟨I a, rfl⟩
    simpa [T, S, sourceConfigurationSpan] using
      (Submodule.span_mono (R := ℝ) hrange)
  have hTfin : Module.finrank ℝ T = min n (d + 1) := by
    have hspan := finrank_span_eq_card (R := ℝ)
      (b := fun a : Fin (min n (d + 1)) => x (I a)) hxI
    simpa [T, Fintype.card_fin] using hspan
  have hSfin : Module.finrank ℝ S = min n (d + 1) := by
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
  exact Submodule.eq_of_le_of_finrank_eq hTS (by
    simp [T, S, hTfin, hSfin])

/-- Projection from a full Gram variation to the pairings with a selected
family of source rows. -/
def sourceSelectedGramCoord
    (n m : ℕ) (I : Fin m → Fin n) :
    (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin m → ℝ) where
  toFun := fun δ i a => δ i (I a)
  map_add' := by
    intro δ ε
    ext i a
    rfl
  map_smul' := by
    intro c δ
    ext i a
    rfl

@[simp]
theorem sourceSelectedGramCoord_apply
    (n m : ℕ) (I : Fin m → Fin n)
    (δ : Fin n → Fin n → ℝ)
    (i : Fin n) (a : Fin m) :
    sourceSelectedGramCoord n m I δ i a = δ i (I a) :=
  rfl

/-- Coordinate target for selected Gram variations.  It keeps all pairings
`δG i (I a)` and imposes exactly the symmetry constraints on the selected
block. -/
def sourceSelectedSymCoordSubspace
    (n m : ℕ) (I : Fin m → Fin n) :
    Submodule ℝ (Fin n → Fin m → ℝ) where
  carrier := {A | ∀ a b : Fin m, A (I a) b = A (I b) a}
  zero_mem' := by
    intro a b
    rfl
  add_mem' := by
    intro A B hA hB a b
    change A (I a) b + B (I a) b = A (I b) a + B (I b) a
    rw [hA a b, hB a b]
  smul_mem' := by
    intro c A hA a b
    change c • A (I a) b = c • A (I b) a
    rw [hA a b]

theorem mem_sourceSelectedSymCoordSubspace
    {n m : ℕ} {I : Fin m → Fin n}
    {A : Fin n → Fin m → ℝ} :
    A ∈ sourceSelectedSymCoordSubspace n m I ↔
      ∀ a b : Fin m, A (I a) b = A (I b) a :=
  Iff.rfl

/-- The real Gram differential is symmetric in its target matrix indices. -/
theorem sourceRealGramDifferential_symm
    (d n : ℕ)
    (x h : Fin n → Fin (d + 1) → ℝ)
    (i j : Fin n) :
    sourceRealGramDifferential d n x h i j =
      sourceRealGramDifferential d n x h j i := by
  change (∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h i μ * x j μ + x i μ * h j μ)) =
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h j μ * x i μ + x j μ * h i μ)
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The selected-coordinate projection of the Gram differential satisfies the
selected-block symmetry relations. -/
theorem sourceSelectedGramCoord_differential_mem
    (d n : ℕ)
    (x h : Fin n → Fin (d + 1) → ℝ)
    {m : ℕ} (I : Fin m → Fin n) :
    sourceSelectedGramCoord n m I
        ((sourceRealGramDifferential d n x) h) ∈
      sourceSelectedSymCoordSubspace n m I := by
  intro a b
  exact sourceRealGramDifferential_symm d n x h (I a) (I b)

/-- Each real source Gram entry is the source Minkowski pairing of the
corresponding rows. -/
theorem sourceRealMinkowskiGram_apply_eq_minkowskiInner
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (i j : Fin n) :
    sourceRealMinkowskiGram d n x i j =
      MinkowskiSpace.minkowskiInner d (x i) (x j) :=
  rfl

/-- The selected-coordinate Gram differential with codomain restricted to the
selected symmetric-coordinate subspace. -/
def sourceSelectedGramDifferentialToSym
    (d n m : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (I : Fin m → Fin n) :
    (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ]
      sourceSelectedSymCoordSubspace n m I where
  toFun := fun h =>
    ⟨sourceSelectedGramCoord n m I
        ((sourceRealGramDifferential d n x) h),
      sourceSelectedGramCoord_differential_mem d n x h I⟩
  map_add' := by
    intro h₁ h₂
    ext i a
    simp [sourceSelectedGramCoord_apply]
  map_smul' := by
    intro c h
    ext i a
    simp [sourceSelectedGramCoord_apply]

@[simp]
theorem sourceSelectedGramDifferentialToSym_apply
    (d n m : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ)
    (I : Fin m → Fin n)
    (h : Fin n → Fin (d + 1) → ℝ)
    (i : Fin n) (a : Fin m) :
    (sourceSelectedGramDifferentialToSym d n m x I h :
        Fin n → Fin m → ℝ) i a =
      sourceRealGramDifferential d n x h i (I a) :=
  rfl

/-- Selected real Gram coordinates, with codomain restricted to the symmetric
selected-coordinate subspace. -/
def sourceSelectedRealGramMap
    (d n m : ℕ)
    (I : Fin m → Fin n) :
    (Fin n → Fin (d + 1) → ℝ) →
      sourceSelectedSymCoordSubspace n m I :=
  fun x =>
    ⟨sourceSelectedGramCoord n m I (sourceRealMinkowskiGram d n x), by
      intro a b
      simp [sourceSelectedGramCoord_apply,
        sourceRealMinkowskiGram_symm d n x (I a) (I b)]⟩

@[simp]
theorem sourceSelectedRealGramMap_apply
    (d n m : ℕ)
    (I : Fin m → Fin n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (i : Fin n) (a : Fin m) :
    (sourceSelectedRealGramMap d n m I x : Fin n → Fin m → ℝ) i a =
      sourceRealMinkowskiGram d n x i (I a) :=
  rfl

/-- The selected real Gram coordinate map has strict derivative given by the
codomain-restricted selected Gram differential. -/
theorem sourceSelectedRealGramMap_hasStrictFDerivAt
    (d n m : ℕ)
    (I : Fin m → Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    HasStrictFDerivAt
      (sourceSelectedRealGramMap d n m I)
      (LinearMap.toContinuousLinearMap
        (sourceSelectedGramDifferentialToSym d n m x I)) x := by
  have hfull : HasStrictFDerivAt
      (fun y : Fin n → Fin (d + 1) → ℝ =>
        sourceSelectedGramCoord n m I (sourceRealMinkowskiGram d n y))
      (LinearMap.toContinuousLinearMap
        ((sourceSelectedGramCoord n m I).comp
          (sourceRealGramDifferential d n x))) x := by
    have hfullG : HasStrictFDerivAt (sourceRealMinkowskiGram d n)
        (LinearMap.toContinuousLinearMap (sourceRealGramDifferential d n x)) x := by
      have hcd : ContDiffAt ℝ ⊤ (sourceRealMinkowskiGram d n) x :=
        (contDiff_sourceRealMinkowskiGram d n).contDiffAt
      have hstrict := hcd.hasStrictFDerivAt (by simp)
      have hfderiv := (sourceRealMinkowskiGram_hasFDerivAt d n x).fderiv
      rwa [hfderiv] at hstrict
    exact
      (LinearMap.toContinuousLinearMap
        (sourceSelectedGramCoord n m I)).hasStrictFDerivAt.comp x hfullG
  apply HasStrictFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_norm_left
  have hfullNorm := (Asymptotics.isLittleO_norm_left).2 hfull.isLittleO
  simpa [sourceSelectedRealGramMap, sourceSelectedGramDifferentialToSym,
    sourceSelectedGramCoord_apply] using hfullNorm

/-- The standard coordinate basis vector in the source Minkowski space. -/
def sourceStdBasisVector
    (d : ℕ) (μ : Fin (d + 1)) : Fin (d + 1) → ℝ :=
  Pi.single (M := fun _ : Fin (d + 1) => ℝ) μ (1 : ℝ)

/-- Coordinate expansion in the standard source basis. -/
theorem sourceStdBasis_sum
    (d : ℕ) (v : Fin (d + 1) → ℝ) :
    (∑ μ : Fin (d + 1), v μ • sourceStdBasisVector d μ) = v := by
  simpa [sourceStdBasisVector, Pi.basisFun_apply, Pi.basisFun_repr] using
    ((Pi.basisFun ℝ (Fin (d + 1))).sum_repr v)

/-- The Minkowski-dual vector representing a real linear functional. -/
def minkowskiDualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ) :
    Fin (d + 1) → ℝ :=
  fun μ => MinkowskiSpace.metricSignature d μ *
    ell (sourceStdBasisVector d μ)

/-- Every linear functional on finite-dimensional source Minkowski space is
represented by pairing with its Minkowski-dual vector. -/
theorem minkowskiInner_dualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ)
    (v : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d
      (minkowskiDualVectorOfLinearFunctional d ell) v = ell v := by
  unfold MinkowskiSpace.minkowskiInner minkowskiDualVectorOfLinearFunctional
  calc
    (∑ μ : Fin (d + 1),
        MinkowskiSpace.metricSignature d μ *
          (MinkowskiSpace.metricSignature d μ *
            ell (sourceStdBasisVector d μ)) * v μ)
        = ∑ μ : Fin (d + 1),
            ell (sourceStdBasisVector d μ) * v μ := by
          apply Finset.sum_congr rfl
          intro μ _
          calc
            MinkowskiSpace.metricSignature d μ *
                (MinkowskiSpace.metricSignature d μ *
                  ell (sourceStdBasisVector d μ)) * v μ
                =
              (MinkowskiSpace.metricSignature d μ *
                  MinkowskiSpace.metricSignature d μ) *
                ell (sourceStdBasisVector d μ) * v μ := by
                  ring
            _ = ell (sourceStdBasisVector d μ) * v μ := by
                  by_cases hμ : μ = 0
                  · simp [MinkowskiSpace.metricSignature, hμ]
                  · simp [MinkowskiSpace.metricSignature, hμ]
    _ = ell (∑ μ : Fin (d + 1), v μ • sourceStdBasisVector d μ) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro μ _
          rw [map_smul]
          simp [smul_eq_mul, mul_comm]
    _ = ell v := by
          rw [sourceStdBasis_sum d v]

/-- A linearly independent source family admits Minkowski-dual vectors with
Kronecker pairings. -/
theorem exists_minkowski_dual_family_of_linearIndependent
    (d m : ℕ)
    {e : Fin m → Fin (d + 1) → ℝ}
    (hli : LinearIndependent ℝ e) :
    ∃ u : Fin m → Fin (d + 1) → ℝ,
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0 := by
  let W : Submodule ℝ (Fin (d + 1) → ℝ) :=
    Submodule.span ℝ (Set.range e)
  choose ell hell using
    fun a : Fin m =>
      LinearMap.exists_extend
        ((Finsupp.lapply a).comp hli.repr :
          W →ₗ[ℝ] ℝ)
  refine ⟨fun a => minkowskiDualVectorOfLinearFunctional d (ell a), ?_⟩
  intro a b
  rw [minkowskiInner_dualVectorOfLinearFunctional]
  have hell_apply :
      ell a (e b) =
        ((Finsupp.lapply a).comp hli.repr)
          (⟨e b, by
            change e b ∈ Submodule.span ℝ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) := by
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun L : W →ₗ[ℝ] ℝ =>
          L (⟨e b, by
            change e b ∈ Submodule.span ℝ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W)) (hell a)
  rw [hell_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
  have hrepreq :
      hli.repr
          (⟨e b, by
            change e b ∈ Submodule.span ℝ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) =
        Finsupp.single b (1 : ℝ) := by
    exact hli.repr_eq_single b
      (⟨e b, by
        change e b ∈ Submodule.span ℝ (Set.range e)
        exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) rfl
  rw [hrepreq]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

/-- Selected source rows from a nonzero regular minor admit Minkowski-dual
vectors with Kronecker pairings. -/
theorem exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    ∃ u : Fin (min n (d + 1)) → Fin (d + 1) → ℝ,
      ∀ a b : Fin (min n (d + 1)),
        MinkowskiSpace.minkowskiInner d (u a) (x (I b)) =
          if a = b then 1 else 0 :=
  exists_minkowski_dual_family_of_linearIndependent d (min n (d + 1))
    (linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero d n hminor)

/-- Symmetry of the source Minkowski pairing, with no dimension side
condition. -/
theorem sourceMinkowskiInner_comm
    (d : ℕ) (x y : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d x y =
      MinkowskiSpace.minkowskiInner d y x := by
  unfold MinkowskiSpace.minkowskiInner
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Left scalar linearity of the source Minkowski pairing, with no dimension
side condition. -/
theorem sourceMinkowskiInner_smul_left
    (d : ℕ) (c : ℝ) (x y : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d (c • x) y =
      c * MinkowskiSpace.minkowskiInner d x y := by
  unfold MinkowskiSpace.minkowskiInner
  calc
    (∑ μ : Fin (d + 1),
        MinkowskiSpace.metricSignature d μ * (c • x) μ * y μ)
        = ∑ μ : Fin (d + 1),
            c * (MinkowskiSpace.metricSignature d μ * x μ * y μ) := by
          apply Finset.sum_congr rfl
          intro μ _
          simp [Pi.smul_apply, smul_eq_mul]
          ring
    _ = c * ∑ μ : Fin (d + 1),
          MinkowskiSpace.metricSignature d μ * x μ * y μ := by
          rw [Finset.mul_sum]

/-- The Gram differential is the sum of the two Minkowski pairings obtained by
differentiating each argument. -/
theorem sourceRealGramDifferential_apply_eq_minkowskiInner
    (d n : ℕ)
    (x h : Fin n → Fin (d + 1) → ℝ)
    (i j : Fin n) :
    sourceRealGramDifferential d n x h i j =
      MinkowskiSpace.minkowskiInner d (h i) (x j) +
        MinkowskiSpace.minkowskiInner d (x i) (h j) := by
  change (∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h i μ * x j μ + x i μ * h j μ)) =
    MinkowskiSpace.minkowskiInner d (h i) (x j) +
      MinkowskiSpace.minkowskiInner d (x i) (h j)
  unfold MinkowskiSpace.minkowskiInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Pairing a linear combination of Minkowski-dual vectors against a selected
source row recovers the corresponding coefficient. -/
theorem minkowskiInner_sum_smul_dual_left
    (d m : ℕ)
    {u e : Fin m → Fin (d + 1) → ℝ}
    (hdual :
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0)
    (coeff : Fin m → ℝ) (a : Fin m) :
    MinkowskiSpace.minkowskiInner d
      (∑ b : Fin m, coeff b • u b) (e a) = coeff a := by
  let L : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun v => MinkowskiSpace.minkowskiInner d v (e a)
    map_add' := by
      intro v w
      unfold MinkowskiSpace.minkowskiInner
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro μ _
      simp [Pi.add_apply]
      ring
    map_smul' := by
      intro c v
      exact sourceMinkowskiInner_smul_left d c v (e a) }
  calc
    MinkowskiSpace.minkowskiInner d
        (∑ b : Fin m, coeff b • u b) (e a)
        = ∑ b : Fin m,
            MinkowskiSpace.minkowskiInner d (coeff b • u b) (e a) := by
          change L (∑ b : Fin m, coeff b • u b) =
            ∑ b : Fin m, L (coeff b • u b)
          rw [map_sum]
    _ = ∑ b : Fin m, coeff b * (if b = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          change L (coeff b • u b) = coeff b * (if b = a then 1 else 0)
          rw [L.map_smul]
          change coeff b • MinkowskiSpace.minkowskiInner d (u b) (e a) =
            coeff b * (if b = a then 1 else 0)
          rw [hdual b a]
          simp [smul_eq_mul]
    _ = coeff a := by
          simp

/-- The selected-coordinate projection of the Gram differential has exactly
the symmetric selected-coordinate subspace as its range. -/
theorem sourceSelectedGramCoord_comp_differential_range_eq
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (_hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    LinearMap.range
      ((sourceSelectedGramCoord n (min n (d + 1)) I).comp
        (sourceRealGramDifferential d n x)) =
      sourceSelectedSymCoordSubspace n (min n (d + 1)) I := by
  let m := min n (d + 1)
  apply le_antisymm
  · rintro A ⟨h, rfl⟩
    exact sourceSelectedGramCoord_differential_mem d n x h I
  · intro A hA
    rcases exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero
        d n hminor with
      ⟨u, hdual⟩
    let selectedVar : Fin m → Fin (d + 1) → ℝ := fun a =>
      (1 / 2 : ℝ) •
        ∑ b : Fin m, A (I a) b • u b
    let residualVar : Fin n → Fin (d + 1) → ℝ := fun r =>
      ∑ a : Fin m,
        (A r a - MinkowskiSpace.minkowskiInner d (x r) (selectedVar a)) • u a
    let h : Fin n → Fin (d + 1) → ℝ := fun r =>
      if hr : r ∈ Set.range I then
        selectedVar ((Equiv.ofInjective I hI).symm ⟨r, hr⟩)
      else residualVar r
    have hsym :
        ∀ a b : Fin m, A (I a) b = A (I b) a :=
      (mem_sourceSelectedSymCoordSubspace).1 hA
    have h_at_selected : ∀ a : Fin m, h (I a) = selectedVar a := by
      intro a
      change (if hr : I a ∈ Set.range I then
          selectedVar ((Equiv.ofInjective I hI).symm ⟨I a, hr⟩)
        else residualVar (I a)) = selectedVar a
      rw [dif_pos ⟨a, rfl⟩]
      rw [Equiv.ofInjective_symm_apply hI a]
    have h_at_unselected :
        ∀ r : Fin n, r ∉ Set.range I → h r = residualVar r := by
      intro r hr
      change (if hr' : r ∈ Set.range I then
          selectedVar ((Equiv.ofInjective I hI).symm ⟨r, hr'⟩)
        else residualVar r) = residualVar r
      rw [dif_neg hr]
    have hselected_pair :
        ∀ a b : Fin m,
          MinkowskiSpace.minkowskiInner d (selectedVar a) (x (I b)) =
            (1 / 2 : ℝ) * A (I a) b := by
      intro a b
      unfold selectedVar
      rw [sourceMinkowskiInner_smul_left]
      rw [minkowskiInner_sum_smul_dual_left d m hdual]
    have hresidual_pair :
        ∀ r : Fin n, ∀ a : Fin m,
          MinkowskiSpace.minkowskiInner d (residualVar r) (x (I a)) =
            A r a - MinkowskiSpace.minkowskiInner d (x r) (selectedVar a) := by
      intro r a
      unfold residualVar
      rw [minkowskiInner_sum_smul_dual_left d m hdual]
    have h_selected :
        ∀ a b : Fin m,
          sourceRealGramDifferential d n x h (I a) (I b) =
            A (I a) b := by
      intro a b
      rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
      rw [h_at_selected a, h_at_selected b]
      rw [hselected_pair a b]
      rw [sourceMinkowskiInner_comm d (x (I a)) (selectedVar b),
        hselected_pair b a]
      have hsymAB : A (I b) a = A (I a) b := hsym b a
      nlinarith
    have h_unselected :
        ∀ r : Fin n, r ∉ Set.range I →
          ∀ a : Fin m,
            sourceRealGramDifferential d n x h r (I a) = A r a := by
      intro r hr a
      rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
      rw [h_at_unselected r hr, h_at_selected a]
      rw [hresidual_pair r a]
      ring
    refine ⟨h, ?_⟩
    ext r a
    simp [sourceSelectedGramCoord_apply]
    by_cases hr : r ∈ Set.range I
    · let c : Fin m := (Equiv.ofInjective I hI).symm ⟨r, hr⟩
      have hc : I c = r := by
        exact Equiv.apply_ofInjective_symm hI ⟨r, hr⟩
      calc
        sourceRealGramDifferential d n x h r (I a)
            = sourceRealGramDifferential d n x h (I c) (I a) := by
              rw [hc]
        _ = A (I c) a := h_selected c a
        _ = A r a := by rw [hc]
    · exact h_unselected r hr a

/-- The codomain-restricted selected Gram differential is surjective onto the
selected symmetric-coordinate subspace at a nonzero-minor point. -/
theorem sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    Function.Surjective
      (sourceSelectedGramDifferentialToSym d n (min n (d + 1)) x I) := by
  let m := min n (d + 1)
  intro A
  let L := sourceRealGramDifferential d n x
  let P := sourceSelectedGramCoord n m I
  have hA :
      (A : Fin n → Fin m → ℝ) ∈ LinearMap.range (P.comp L) := by
    rw [sourceSelectedGramCoord_comp_differential_range_eq d n hI hJ hminor]
    exact A.property
  rcases hA with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  ext i a
  exact congrFun (congrFun hh i) a

/-- The selected real Gram coordinate map has the local product chart supplied
by the finite-dimensional implicit-function theorem at a nonzero-minor point. -/
theorem sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n → Fin (d + 1) → ℝ)
        (sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (sourceSelectedGramDifferentialToSym d n
              (min n (d + 1)) x0 I)),
      x0 ∈ e.source ∧
      e x0 =
        (sourceSelectedRealGramMap d n (min n (d + 1)) I x0, 0) ∧
      ∀ x ∈ e.source,
        (e x).1 = sourceSelectedRealGramMap d n (min n (d + 1)) I x := by
  let m := min n (d + 1)
  let f := sourceSelectedRealGramMap d n m I
  let f' : (Fin n → Fin (d + 1) → ℝ) →L[ℝ]
      sourceSelectedSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedGramDifferentialToSym d n m x0 I)
  have hstrict : HasStrictFDerivAt f f' x0 := by
    simpa [f, f'] using
      sourceSelectedRealGramMap_hasStrictFDerivAt d n m I x0
  have hsurj : f'.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor)
  let e := hstrict.implicitToOpenPartialHomeomorph f f' hsurj
  refine ⟨e, ?_, ?_, ?_⟩
  · exact hstrict.mem_implicitToOpenPartialHomeomorph_source hsurj
  · simpa [e, f, f'] using hstrict.implicitToOpenPartialHomeomorph_self hsurj
  · intro x hx
    simpa [e, f, f'] using
      hstrict.implicitToOpenPartialHomeomorph_fst hsurj x

/-- Linearity of the source Minkowski pairing in finite sums on the left. -/
theorem sourceMinkowskiInner_sum_smul_left
    (d m : ℕ)
    (coeff : Fin m → ℝ)
    (u : Fin m → Fin (d + 1) → ℝ)
    (v : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d
      (∑ a : Fin m, coeff a • u a) v =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d (u a) v := by
  let L : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun w => MinkowskiSpace.minkowskiInner d w v
    map_add' := by
      intro p q
      unfold MinkowskiSpace.minkowskiInner
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro μ _
      simp [Pi.add_apply]
      ring
    map_smul' := by
      intro c p
      exact sourceMinkowskiInner_smul_left d c p v }
  calc
    MinkowskiSpace.minkowskiInner d
        (∑ a : Fin m, coeff a • u a) v
        = ∑ a : Fin m, MinkowskiSpace.minkowskiInner d (coeff a • u a) v := by
          change L (∑ a : Fin m, coeff a • u a) =
            ∑ a : Fin m, L (coeff a • u a)
          rw [map_sum]
    _ = ∑ a : Fin m, coeff a *
          MinkowskiSpace.minkowskiInner d (u a) v := by
          apply Finset.sum_congr rfl
          intro a _
          change L (coeff a • u a) =
            coeff a * MinkowskiSpace.minkowskiInner d (u a) v
          rw [L.map_smul]
          change coeff a • MinkowskiSpace.minkowskiInner d (u a) v =
            coeff a * MinkowskiSpace.minkowskiInner d (u a) v
          simp [smul_eq_mul]

/-- Linearity of the source Minkowski pairing in finite sums on the right. -/
theorem sourceMinkowskiInner_sum_smul_right
    (d m : ℕ)
    (u : Fin (d + 1) → ℝ)
    (coeff : Fin m → ℝ)
    (v : Fin m → Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d u
      (∑ a : Fin m, coeff a • v a) =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d u (v a) := by
  rw [sourceMinkowskiInner_comm d u (∑ a : Fin m, coeff a • v a)]
  rw [sourceMinkowskiInner_sum_smul_left d m coeff v u]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceMinkowskiInner_comm d (v a) u]

/-- Right additivity of the source Minkowski pairing, with no dimension side
condition. -/
theorem sourceMinkowskiInner_add_right
    (d : ℕ) (x y z : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d x (y + z) =
      MinkowskiSpace.minkowskiInner d x y +
        MinkowskiSpace.minkowskiInner d x z := by
  unfold MinkowskiSpace.minkowskiInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  simp [Pi.add_apply]
  ring

/-- Right scalar linearity of the source Minkowski pairing, with no dimension
side condition. -/
theorem sourceMinkowskiInner_smul_right
    (d : ℕ) (c : ℝ) (x y : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d x (c • y) =
      c * MinkowskiSpace.minkowskiInner d x y := by
  rw [sourceMinkowskiInner_comm d x (c • y)]
  rw [sourceMinkowskiInner_smul_left d c y x]
  rw [sourceMinkowskiInner_comm d y x]

/-- The source Minkowski pairing is nondegenerate in the left argument. -/
theorem sourceMinkowskiInner_left_nonDegenerate
    (d : ℕ) {w : Fin (d + 1) → ℝ}
    (horth :
      ∀ v : Fin (d + 1) → ℝ,
        MinkowskiSpace.minkowskiInner d w v = 0) :
    w = 0 := by
  ext μ
  have hμ := horth (sourceStdBasisVector d μ)
  unfold MinkowskiSpace.minkowskiInner sourceStdBasisVector at hμ
  simp [Pi.single_apply] at hμ
  rcases hμ with hsig | hw
  · exfalso
    by_cases h0 : μ = 0
    · simp [MinkowskiSpace.metricSignature, h0] at hsig
    · simp [MinkowskiSpace.metricSignature, h0] at hsig
  · exact hw

/-- A vector orthogonal to a spanning selected family is zero. -/
theorem sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family
    (d m : ℕ)
    {e : Fin m → Fin (d + 1) → ℝ}
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    {w : Fin (d + 1) → ℝ}
    (horth :
      ∀ a : Fin m,
        MinkowskiSpace.minkowskiInner d w (e a) = 0) :
    w = 0 := by
  apply sourceMinkowskiInner_left_nonDegenerate d
  intro v
  let L : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun u => MinkowskiSpace.minkowskiInner d w u
    map_add' := by
      intro u v
      exact sourceMinkowskiInner_add_right d w u v
    map_smul' := by
      intro c u
      exact sourceMinkowskiInner_smul_right d c w u }
  change L v = 0
  have hv : v ∈ Submodule.span ℝ (Set.range e) := by
    rw [hspan]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro u ⟨a, rfl⟩
    exact horth a
  · unfold L
    unfold MinkowskiSpace.minkowskiInner
    simp
  · intro u v _ _ hu hv
    simp [map_add, hu, hv]
  · intro c u _ hu
    simp [map_smul, hu]

/-- If the number of source rows is at most the spacetime dimension, an
injective selected-row map with `min n (d + 1)` rows is surjective. -/
theorem sourceSelectedIndex_surjective_of_le
    (d n : ℕ)
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I)
    (hn : n ≤ d + 1) :
    Function.Surjective I := by
  have hcard :
      Fintype.card (Fin (min n (d + 1))) = Fintype.card (Fin n) := by
    simp [Nat.min_eq_left hn]
  let e : Fin (min n (d + 1)) ≃ Fin n := Fintype.equivOfCardEq hcard
  exact (Finite.injective_iff_surjective_of_equiv e).1 hI

/-- In the complementary case `d + 1 ≤ n`, a nonzero maximal selected minor
makes the selected rows span the whole source spacetime. -/
theorem sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0)
    (hD : d + 1 ≤ n) :
    Submodule.span ℝ
        (Set.range (fun a : Fin (min n (d + 1)) => x (I a))) = ⊤ := by
  have hli :=
    linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero d n hminor
  have hcard :
      Fintype.card (Fin (min n (d + 1))) =
        Module.finrank ℝ (Fin (d + 1) → ℝ) := by
    simp [Nat.min_eq_right hD]
  exact hli.span_eq_top_of_card_eq_finrank' hcard

/-- Left subtraction for the source Minkowski pairing. -/
theorem sourceMinkowskiInner_sub_left
    (d : ℕ) (x y z : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d (x - y) z =
      MinkowskiSpace.minkowskiInner d x z -
        MinkowskiSpace.minkowskiInner d y z := by
  unfold MinkowskiSpace.minkowskiInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  simp [Pi.sub_apply]
  ring

/-- Right subtraction for the source Minkowski pairing. -/
theorem sourceMinkowskiInner_sub_right
    (d : ℕ) (x y z : Fin (d + 1) → ℝ) :
    MinkowskiSpace.minkowskiInner d x (y - z) =
      MinkowskiSpace.minkowskiInner d x y -
        MinkowskiSpace.minkowskiInner d x z := by
  rw [sourceMinkowskiInner_comm d x (y - z)]
  rw [sourceMinkowskiInner_sub_left d y z x]
  rw [sourceMinkowskiInner_comm d y x]
  rw [sourceMinkowskiInner_comm d z x]

/-- Coefficients expressing every source row in the selected-row span supplied
by a nonzero regular minor. -/
theorem sourceRows_coefficients_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    ∃ c : Fin n → Fin (min n (d + 1)) → ℝ,
      ∀ r : Fin n,
        x r = ∑ a : Fin (min n (d + 1)), c r a • x (I a) := by
  let m := min n (d + 1)
  have hspan :=
    span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero
      d n hminor
  have hexists : ∀ r : Fin n,
      ∃ c : Fin m → ℝ,
        ∑ a : Fin m, c a • x (I a) = x r := by
    intro r
    have hxmem : x r ∈
        Submodule.span ℝ (Set.range (fun a : Fin m => x (I a))) := by
      rw [hspan]
      change x r ∈ Submodule.span ℝ (Set.range x)
      exact Submodule.subset_span ⟨r, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
      (v := fun a : Fin m => x (I a))).1 hxmem
  choose c hc using hexists
  exact ⟨c, fun r => (hc r).symm⟩

/-- On a fixed nonzero selected-minor chart, the selected Gram coordinates
determine the full source Gram matrix. -/
theorem sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hminor_y : sourceRegularMinor d n I J y ≠ 0)
    (hsel :
      sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n x) =
        sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n y)) :
    sourceRealMinkowskiGram d n x =
      sourceRealMinkowskiGram d n y := by
  ext r s
  by_cases hn : n ≤ d + 1
  · have hsurj := sourceSelectedIndex_surjective_of_le d n hI hn
    rcases hsurj s with ⟨a, rfl⟩
    have h := congrFun (congrFun hsel r) a
    simpa [sourceSelectedGramCoord_apply] using h
  · have hD : d + 1 ≤ n := by omega
    let m := min n (d + 1)
    rcases sourceRows_coefficients_of_sourceRegularMinor_ne_zero d n
        hminor_x with
      ⟨c, hc⟩
    let yApprox : Fin n → Fin (d + 1) → ℝ := fun q =>
      ∑ a : Fin m, c q a • y (I a)
    have hspan_y : Submodule.span ℝ
        (Set.range (fun a : Fin m => y (I a))) = ⊤ := by
      simpa [m] using
        sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero
          d n hminor_y hD
    have hy_eq : ∀ q : Fin n, y q = yApprox q := by
      intro q
      have hzero : y q - yApprox q = 0 := by
        apply sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family
          d m hspan_y
        intro b
        rw [sourceMinkowskiInner_sub_left]
        have hsel_qb := congrFun (congrFun hsel q) b
        change sourceRealMinkowskiGram d n x q (I b) =
          sourceRealMinkowskiGram d n y q (I b) at hsel_qb
        have hx_expand :
            MinkowskiSpace.minkowskiInner d (x q) (x (I b)) =
              ∑ a : Fin m,
                c q a *
                  MinkowskiSpace.minkowskiInner d (x (I a)) (x (I b)) := by
          rw [hc q]
          rw [sourceMinkowskiInner_sum_smul_left]
        have hyApprox_expand :
            MinkowskiSpace.minkowskiInner d (yApprox q) (y (I b)) =
              ∑ a : Fin m,
                c q a *
                  MinkowskiSpace.minkowskiInner d (y (I a)) (y (I b)) := by
          unfold yApprox
          rw [sourceMinkowskiInner_sum_smul_left]
        have hblock : ∀ a : Fin m,
            MinkowskiSpace.minkowskiInner d (y (I a)) (y (I b)) =
              MinkowskiSpace.minkowskiInner d (x (I a)) (x (I b)) := by
          intro a
          have h := congrFun (congrFun hsel (I a)) b
          change sourceRealMinkowskiGram d n x (I a) (I b) =
            sourceRealMinkowskiGram d n y (I a) (I b) at h
          simpa [sourceRealMinkowskiGram_apply_eq_minkowskiInner] using h.symm
        have hyApprox_eq_x :
            MinkowskiSpace.minkowskiInner d (yApprox q) (y (I b)) =
              MinkowskiSpace.minkowskiInner d (x q) (x (I b)) := by
          rw [hyApprox_expand, hx_expand]
          apply Finset.sum_congr rfl
          intro a _
          rw [hblock a]
        have hy_eq_x :
            MinkowskiSpace.minkowskiInner d (y q) (y (I b)) =
              MinkowskiSpace.minkowskiInner d (x q) (x (I b)) := by
          simpa [sourceRealMinkowskiGram_apply_eq_minkowskiInner] using
            hsel_qb.symm
        nlinarith
      exact sub_eq_zero.mp hzero
    have hx_expand_rs :
        sourceRealMinkowskiGram d n x r s =
          ∑ a : Fin m,
            c s a * sourceRealMinkowskiGram d n x r (I a) := by
      rw [sourceRealMinkowskiGram_apply_eq_minkowskiInner]
      rw [hc s]
      rw [sourceMinkowskiInner_sum_smul_right]
      rfl
    have hy_expand_rs :
        sourceRealMinkowskiGram d n y r s =
          ∑ a : Fin m,
            c s a * sourceRealMinkowskiGram d n y r (I a) := by
      rw [sourceRealMinkowskiGram_apply_eq_minkowskiInner]
      rw [hy_eq s]
      unfold yApprox
      rw [sourceMinkowskiInner_sum_smul_right]
      rfl
    calc
      sourceRealMinkowskiGram d n x r s
          = ∑ a : Fin m,
              c s a * sourceRealMinkowskiGram d n x r (I a) := hx_expand_rs
      _ = ∑ a : Fin m,
              c s a * sourceRealMinkowskiGram d n y r (I a) := by
            apply Finset.sum_congr rfl
            intro a _
            have h := congrFun (congrFun hsel r) a
            simpa [sourceSelectedGramCoord_apply] using
              congrArg (fun z => c s a * z) h
      _ = sourceRealMinkowskiGram d n y r s := hy_expand_rs.symm

/-- If the selected rows of the right-hand source point span spacetime, then
selected coordinates equal to those of a left regular-minor point determine the
full source Gram matrix. -/
theorem sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hspan_y :
      Submodule.span ℝ
        (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤)
    (hsel :
      sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n x) =
        sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n y)) :
    sourceRealMinkowskiGram d n x =
      sourceRealMinkowskiGram d n y := by
  ext r s
  let m := min n (d + 1)
  rcases sourceRows_coefficients_of_sourceRegularMinor_ne_zero d n
      hminor_x with
    ⟨c, hc⟩
  let yApprox : Fin n → Fin (d + 1) → ℝ := fun q =>
    ∑ a : Fin m, c q a • y (I a)
  have hy_eq : ∀ q : Fin n, y q = yApprox q := by
    intro q
    have hzero : y q - yApprox q = 0 := by
      apply sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m hspan_y
      intro b
      rw [sourceMinkowskiInner_sub_left]
      have hsel_qb := congrFun (congrFun hsel q) b
      change sourceRealMinkowskiGram d n x q (I b) =
        sourceRealMinkowskiGram d n y q (I b) at hsel_qb
      have hx_expand :
          MinkowskiSpace.minkowskiInner d (x q) (x (I b)) =
            ∑ a : Fin m,
              c q a *
                MinkowskiSpace.minkowskiInner d (x (I a)) (x (I b)) := by
        rw [hc q]
        rw [sourceMinkowskiInner_sum_smul_left]
      have hyApprox_expand :
          MinkowskiSpace.minkowskiInner d (yApprox q) (y (I b)) =
            ∑ a : Fin m,
              c q a *
                MinkowskiSpace.minkowskiInner d (y (I a)) (y (I b)) := by
        unfold yApprox
        rw [sourceMinkowskiInner_sum_smul_left]
      have hblock : ∀ a : Fin m,
          MinkowskiSpace.minkowskiInner d (y (I a)) (y (I b)) =
            MinkowskiSpace.minkowskiInner d (x (I a)) (x (I b)) := by
        intro a
        have h := congrFun (congrFun hsel (I a)) b
        change sourceRealMinkowskiGram d n x (I a) (I b) =
          sourceRealMinkowskiGram d n y (I a) (I b) at h
        simpa [sourceRealMinkowskiGram_apply_eq_minkowskiInner] using h.symm
      have hyApprox_eq_x :
          MinkowskiSpace.minkowskiInner d (yApprox q) (y (I b)) =
            MinkowskiSpace.minkowskiInner d (x q) (x (I b)) := by
        rw [hyApprox_expand, hx_expand]
        apply Finset.sum_congr rfl
        intro a _
        rw [hblock a]
      have hy_eq_x :
          MinkowskiSpace.minkowskiInner d (y q) (y (I b)) =
            MinkowskiSpace.minkowskiInner d (x q) (x (I b)) := by
        simpa [sourceRealMinkowskiGram_apply_eq_minkowskiInner] using
          hsel_qb.symm
      nlinarith
    exact sub_eq_zero.mp hzero
  have hx_expand_rs :
      sourceRealMinkowskiGram d n x r s =
        ∑ a : Fin m,
          c s a * sourceRealMinkowskiGram d n x r (I a) := by
    rw [sourceRealMinkowskiGram_apply_eq_minkowskiInner]
    rw [hc s]
    rw [sourceMinkowskiInner_sum_smul_right]
    rfl
  have hy_expand_rs :
      sourceRealMinkowskiGram d n y r s =
        ∑ a : Fin m,
          c s a * sourceRealMinkowskiGram d n y r (I a) := by
    rw [sourceRealMinkowskiGram_apply_eq_minkowskiInner]
    rw [hy_eq s]
    unfold yApprox
    rw [sourceMinkowskiInner_sum_smul_right]
    rfl
  calc
    sourceRealMinkowskiGram d n x r s
        = ∑ a : Fin m,
            c s a * sourceRealMinkowskiGram d n x r (I a) := hx_expand_rs
    _ = ∑ a : Fin m,
            c s a * sourceRealMinkowskiGram d n y r (I a) := by
          apply Finset.sum_congr rfl
          intro a _
          have h := congrFun (congrFun hsel r) a
          simpa [sourceSelectedGramCoord_apply] using
            congrArg (fun z => c s a * z) h
    _ = sourceRealMinkowskiGram d n y r s := hy_expand_rs.symm

/-- In the full-spacetime case, equality of selected Gram coordinates with a
regular selected-minor point transfers full span to the arbitrary right-hand
selected rows. -/
theorem sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hsel :
      sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n x) =
        sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n y))
    (hD : d + 1 ≤ n) :
    Submodule.span ℝ
      (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤ := by
  let m := min n (d + 1)
  have hspan_x : Submodule.span ℝ
      (Set.range (fun a : Fin m => x (I a))) = ⊤ := by
    simpa [m] using
      sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero d n hminor_x hD
  have hli_x : LinearIndependent ℝ (fun a : Fin m => x (I a)) := by
    simpa [m] using
      linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero d n hminor_x
  have hli_y : LinearIndependent ℝ (fun a : Fin m => y (I a)) := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hsum a
    have hxcombo_zero :
        (∑ c : Fin m, coeff c • x (I c)) = 0 := by
      apply sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m hspan_x
      intro b
      have hyorth :
          MinkowskiSpace.minkowskiInner d
            (∑ c : Fin m, coeff c • y (I c)) (y (I b)) = 0 := by
        rw [hsum]
        unfold MinkowskiSpace.minkowskiInner
        simp
      calc
        MinkowskiSpace.minkowskiInner d
            (∑ c : Fin m, coeff c • x (I c)) (x (I b))
            = ∑ c : Fin m,
                coeff c *
                  MinkowskiSpace.minkowskiInner d (x (I c)) (x (I b)) := by
              rw [sourceMinkowskiInner_sum_smul_left]
        _ = ∑ c : Fin m,
                coeff c *
                  MinkowskiSpace.minkowskiInner d (y (I c)) (y (I b)) := by
              apply Finset.sum_congr rfl
              intro c _
              have h := congrFun (congrFun hsel (I c)) b
              change sourceRealMinkowskiGram d n x (I c) (I b) =
                sourceRealMinkowskiGram d n y (I c) (I b) at h
              simpa [sourceRealMinkowskiGram_apply_eq_minkowskiInner] using
                congrArg (fun z => coeff c * z) h
        _ = MinkowskiSpace.minkowskiInner d
            (∑ c : Fin m, coeff c • y (I c)) (y (I b)) := by
              rw [sourceMinkowskiInner_sum_smul_left]
        _ = 0 := hyorth
    exact (Fintype.linearIndependent_iff.mp hli_x coeff hxcombo_zero) a
  have hcard :
      Fintype.card (Fin m) =
        Module.finrank ℝ (Fin (d + 1) → ℝ) := by
    simp [m, Nat.min_eq_right hD]
  exact hli_y.span_eq_top_of_card_eq_finrank' hcard

/-- Selected coordinates of one regular selected-minor source point determine
any Gram matrix in the real source Gram variety. -/
theorem sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero_of_mem_variety
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {G : Fin n → Fin n → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : sourceRegularMinor d n I J x ≠ 0)
    (hG : G ∈ sourceRealGramVariety d n)
    (hsel :
      sourceSelectedGramCoord n (min n (d + 1)) I
          (sourceRealMinkowskiGram d n x) =
        sourceSelectedGramCoord n (min n (d + 1)) I G) :
    sourceRealMinkowskiGram d n x = G := by
  rcases hG with ⟨y, rfl⟩
  by_cases hn : n ≤ d + 1
  · ext r s
    have hsurj := sourceSelectedIndex_surjective_of_le d n hI hn
    rcases hsurj s with ⟨a, rfl⟩
    have h := congrFun (congrFun hsel r) a
    simpa [sourceSelectedGramCoord_apply] using h
  · have hD : d + 1 ≤ n := by omega
    have hspan_y :
        Submodule.span ℝ
          (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤ :=
      sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular
        d n hminor_x hsel hD
    exact
      sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
        d n hminor_x hspan_y hsel

/-- In the selected-coordinate implicit chart, the full source Gram map is
constant on local vertical fibers after shrinking to the same nonzero-minor
chart. -/
theorem sourceRealGramMap_constant_on_selectedVerticalFibers
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n → Fin (d + 1) → ℝ)
        (sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (sourceSelectedGramDifferentialToSym d n
              (min n (d + 1)) x0 I)),
      x0 ∈ e.source ∧
      ∃ U : Set (Fin n → Fin (d + 1) → ℝ),
        IsOpen U ∧ x0 ∈ U ∧ U ⊆ e.source ∧
        (∀ x ∈ U, sourceRegularMinor d n I J x ≠ 0) ∧
        ∀ y ∈ U, ∀ z ∈ U,
          (e y).1 = (e z).1 ->
          sourceRealMinkowskiGram d n y =
            sourceRealMinkowskiGram d n z := by
  rcases sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hx0e, _hebase, hefst⟩
  let U : Set (Fin n → Fin (d + 1) → ℝ) :=
    e.source ∩ {x | sourceRegularMinor d n I J x ≠ 0}
  refine ⟨e, hx0e, U, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.open_source.inter
      (isOpen_ne_fun (continuous_sourceRegularMinor d n I J)
        continuous_const)
  · exact ⟨hx0e, hminor⟩
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.2
  · intro y hy z hz hyz
    have hselSubtype :
        sourceSelectedRealGramMap d n (min n (d + 1)) I y =
          sourceSelectedRealGramMap d n (min n (d + 1)) I z := by
      rw [← hefst y hy.1, ← hefst z hz.1, hyz]
    have hsel :
        sourceSelectedGramCoord n (min n (d + 1)) I
            (sourceRealMinkowskiGram d n y) =
          sourceSelectedGramCoord n (min n (d + 1)) I
            (sourceRealMinkowskiGram d n z) := by
      exact congrArg Subtype.val hselSubtype
    exact sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero
      d n hI hy.2 hz.2 hsel

/-- Inside any open source neighborhood of a regular point, the real source
Gram map sends a smaller regular source patch to a relatively open neighborhood
in the real source Gram variety. -/
theorem sourceRealGramMap_localRelOpenImage_in_open_of_regular
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x0)
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    (hV_open : IsOpen V)
    (hx0V : x0 ∈ V) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℝ),
      IsOpen U ∧ x0 ∈ U ∧ U ⊆ V ∧
      ∃ O : Set (Fin n → Fin n → ℝ),
        sourceRealMinkowskiGram d n x0 ∈ O ∧
        IsRelOpenInSourceRealGramVariety d n O ∧
        O ⊆ sourceRealMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ x ∈ U,
          SourceGramRegularAt d n x ∧
          sourceRealMinkowskiGram d n x = G := by
  rcases exists_nonzero_minor_of_sourceGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  rcases sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hx0e, _hebase, hefst⟩
  let U : Set (Fin n → Fin (d + 1) → ℝ) :=
    (e.source ∩ {x | sourceRegularMinor d n I J x ≠ 0}) ∩ V
  have hUopen : IsOpen U := by
    exact (e.open_source.inter
      (isOpen_ne_fun (continuous_sourceRegularMinor d n I J)
        continuous_const)).inter hV_open
  have hx0U : x0 ∈ U := ⟨⟨hx0e, hminor⟩, hx0V⟩
  have hUsub : U ⊆ e.source := fun _ hx => hx.1.1
  have hUV : U ⊆ V := fun _ hx => hx.2
  have hUminor :
      ∀ x ∈ U, sourceRegularMinor d n I J x ≠ 0 :=
    fun _ hx => hx.1.2
  let m := min n (d + 1)
  let S := sourceSelectedSymCoordSubspace n m I
  let K := LinearMap.ker
    (sourceSelectedGramDifferentialToSym d n m x0 I)
  let T : Set (S × K) := e '' U
  let R : Set S := Prod.fst '' T
  have hTopen : IsOpen T := by
    exact e.isOpen_image_of_subset_source hUopen hUsub
  have hRopen : IsOpen R := by
    exact isOpenMap_fst T hTopen
  rcases isOpen_induced_iff.mp hRopen with
    ⟨R0, hR0open, hR0pre⟩
  let E0 : Set (Fin n → Fin n → ℝ) :=
    {G | sourceSelectedGramCoord n m I G ∈ R0}
  let O : Set (Fin n → Fin n → ℝ) :=
    E0 ∩ sourceRealGramVariety d n
  have hPcont : Continuous (sourceSelectedGramCoord n m I) :=
    LinearMap.continuous_of_finiteDimensional
      (sourceSelectedGramCoord n m I)
  have hE0open : IsOpen E0 := by
    exact hR0open.preimage hPcont
  have hbaseR :
      sourceSelectedRealGramMap d n m I x0 ∈ R := by
    refine ⟨e x0, ?_, ?_⟩
    · exact ⟨x0, hx0U, rfl⟩
    · exact hefst x0 hx0e
  have hbaseR0 :
      (sourceSelectedRealGramMap d n m I x0 :
          Fin n → Fin m → ℝ) ∈ R0 := by
    have hpre :
        sourceSelectedRealGramMap d n m I x0 ∈
          Subtype.val ⁻¹' R0 := by
      rw [hR0pre]
      exact hbaseR
    exact hpre
  have hbaseO :
      sourceRealMinkowskiGram d n x0 ∈ O := by
    refine ⟨?_, ?_⟩
    · exact hbaseR0
    · exact ⟨x0, rfl⟩
  have hOreal :
      ∀ G ∈ O, ∃ x ∈ U,
        SourceGramRegularAt d n x ∧
          sourceRealMinkowskiGram d n x = G := by
    intro G hGO
    rcases hGO with ⟨hGE0, hGvar⟩
    have hGsym : ∀ i j : Fin n, G i j = G j i := by
      rcases hGvar with ⟨y, rfl⟩
      intro i j
      exact sourceRealMinkowskiGram_symm d n y i j
    let A : S :=
      ⟨sourceSelectedGramCoord n m I G, by
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
        sourceSelectedRealGramMap d n m I u = A := by
      exact (hefst u (hUsub huU)).symm.trans hpA
    have hsel :
        sourceSelectedGramCoord n m I
            (sourceRealMinkowskiGram d n u) =
          sourceSelectedGramCoord n m I G := by
      exact congrArg Subtype.val hselSubtype
    have hGram :
        sourceRealMinkowskiGram d n u = G :=
      sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero_of_mem_variety
        d n hI (hUminor u huU) hGvar hsel
    have hregu : SourceGramRegularAt d n u :=
      sourceGramRegularAt_of_exists_nonzero_minor d n
        ⟨I, hI, J, hJ, hUminor u huU⟩
    exact ⟨u, huU, hregu, hGram⟩
  have hOsubset :
      O ⊆ sourceRealMinkowskiGram d n '' U := by
    intro G hG
    rcases hOreal G hG with ⟨u, huU, _hregu, hGram⟩
    exact ⟨u, huU, hGram⟩
  refine ⟨U, hUopen, hx0U, hUV, O, hbaseO, ?_, hOsubset, hOreal⟩
  exact ⟨E0, hE0open, rfl⟩

/-- The real source Gram map sends a small regular source patch to a relatively
open neighborhood in the real source Gram variety. -/
theorem sourceRealGramMap_localRelOpenImage_of_regular
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x0) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℝ),
      IsOpen U ∧ x0 ∈ U ∧
      ∃ O : Set (Fin n → Fin n → ℝ),
        sourceRealMinkowskiGram d n x0 ∈ O ∧
        IsRelOpenInSourceRealGramVariety d n O ∧
        O ⊆ sourceRealMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ x ∈ U,
          SourceGramRegularAt d n x ∧
          sourceRealMinkowskiGram d n x = G := by
  rcases sourceRealGramMap_localRelOpenImage_in_open_of_regular
      d n hreg isOpen_univ (by trivial) with
    ⟨U, hUopen, hx0U, _hUuniv, O, hbaseO, hOrel, hOsubset, hOreal⟩
  exact ⟨U, hUopen, hx0U, O, hbaseO, hOrel, hOsubset, hOreal⟩

/-- If a differential image has zero selected coordinates, then the whole
differential image is zero. -/
theorem sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0)
    {h : Fin n → Fin (d + 1) → ℝ}
    (hsel :
      sourceSelectedGramCoord n (min n (d + 1)) I
        ((sourceRealGramDifferential d n x) h) = 0) :
    (sourceRealGramDifferential d n x) h = 0 := by
  let m := min n (d + 1)
  rcases sourceRows_coefficients_of_sourceRegularMinor_ne_zero d n hminor with
    ⟨c, hc⟩
  let hApprox : Fin n → Fin (d + 1) → ℝ := fun r =>
    ∑ a : Fin m, c r a • h (I a)
  have hzero_col :
      ∀ i : Fin n, ∀ a : Fin m,
        sourceRealGramDifferential d n x h i (I a) = 0 := by
    intro i a
    have happ := congrFun (congrFun hsel i) a
    simpa [sourceSelectedGramCoord_apply] using happ
  have hApprox_pair_eq :
      ∀ j : Fin n, ∀ b : Fin m,
        MinkowskiSpace.minkowskiInner d (hApprox j) (x (I b)) +
          MinkowskiSpace.minkowskiInner d (x j) (h (I b)) = 0 := by
    intro j b
    calc
      MinkowskiSpace.minkowskiInner d (hApprox j) (x (I b)) +
          MinkowskiSpace.minkowskiInner d (x j) (h (I b))
          =
        (∑ a : Fin m,
            c j a * MinkowskiSpace.minkowskiInner d (h (I a)) (x (I b))) +
          ∑ a : Fin m,
            c j a * MinkowskiSpace.minkowskiInner d (x (I a)) (h (I b)) := by
            unfold hApprox
            rw [sourceMinkowskiInner_sum_smul_left]
            rw [hc j]
            rw [sourceMinkowskiInner_sum_smul_left]
      _ = ∑ a : Fin m,
          c j a *
            (MinkowskiSpace.minkowskiInner d (h (I a)) (x (I b)) +
              MinkowskiSpace.minkowskiInner d (x (I a)) (h (I b))) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = ∑ a : Fin m,
          c j a * sourceRealGramDifferential d n x h (I a) (I b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
      _ = 0 := by
            simp [hzero_col]
  have hdiff_orth :
      ∀ j : Fin n, ∀ b : Fin m,
        MinkowskiSpace.minkowskiInner d (h j - hApprox j) (x (I b)) = 0 := by
    intro j b
    have hz := hzero_col j b
    rw [sourceRealGramDifferential_apply_eq_minkowskiInner] at hz
    have ha := hApprox_pair_eq j b
    rw [sourceMinkowskiInner_sub_left]
    nlinarith
  have hdiff_orth_full :
      ∀ i j : Fin n,
        MinkowskiSpace.minkowskiInner d (x i) (h j - hApprox j) = 0 := by
    intro i j
    calc
      MinkowskiSpace.minkowskiInner d (x i) (h j - hApprox j)
          = MinkowskiSpace.minkowskiInner d (h j - hApprox j) (x i) := by
            rw [sourceMinkowskiInner_comm]
      _ = MinkowskiSpace.minkowskiInner d (h j - hApprox j)
          (∑ a : Fin m, c i a • x (I a)) := by
            rw [← hc i]
      _ = ∑ a : Fin m,
          c i a *
            MinkowskiSpace.minkowskiInner d (h j - hApprox j) (x (I a)) := by
            rw [sourceMinkowskiInner_sum_smul_right]
      _ = 0 := by
            simp [hdiff_orth]
  ext i j
  rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
  have hreplace :
      MinkowskiSpace.minkowskiInner d (x i) (h j) =
        MinkowskiSpace.minkowskiInner d (x i) (hApprox j) := by
    have horth := hdiff_orth_full i j
    rw [sourceMinkowskiInner_sub_right] at horth
    nlinarith
  rw [hreplace]
  calc
    MinkowskiSpace.minkowskiInner d (h i) (x j) +
        MinkowskiSpace.minkowskiInner d (x i) (hApprox j)
        =
      (∑ a : Fin m,
          c j a * MinkowskiSpace.minkowskiInner d (h i) (x (I a))) +
        ∑ a : Fin m,
          c j a * MinkowskiSpace.minkowskiInner d (x i) (h (I a)) := by
          rw [hc j]
          rw [sourceMinkowskiInner_sum_smul_right]
          unfold hApprox
          rw [sourceMinkowskiInner_sum_smul_right]
    _ = ∑ a : Fin m,
        c j a *
          (MinkowskiSpace.minkowskiInner d (h i) (x (I a)) +
            MinkowskiSpace.minkowskiInner d (x i) (h (I a))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ a : Fin m,
        c j a * sourceRealGramDifferential d n x h i (I a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
    _ = 0 := by
          simp [hzero_col]

/-- The selected-coordinate projection is injective on the range of the full
Gram differential at a nonzero-minor point. -/
theorem sourceSelectedGramCoord_injective_on_differential_range
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (_hI : Function.Injective I)
    (_hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    Function.Injective
      (fun y : LinearMap.range (sourceRealGramDifferential d n x) =>
        (sourceSelectedGramCoord n (min n (d + 1)) I) y) := by
  intro y z hyz
  rcases y with ⟨δy, hy⟩
  rcases z with ⟨δz, hz⟩
  rcases hy with ⟨hyvar, rfl⟩
  rcases hz with ⟨hzvar, rfl⟩
  apply Subtype.ext
  have hselzero :
      sourceSelectedGramCoord n (min n (d + 1)) I
          ((sourceRealGramDifferential d n x) (hyvar - hzvar)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hyz
  have hker :=
    sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero
      d n hminor hselzero
  have hsub :
      (sourceRealGramDifferential d n x) hyvar -
          (sourceRealGramDifferential d n x) hzvar = 0 := by
    simpa [map_sub] using hker
  exact sub_eq_zero.mp hsub

/-- At a nonzero-minor point, the selected symmetric differential has the same
kernel as the full Gram differential. -/
theorem sourceSelectedGramDifferentialToSym_ker_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    LinearMap.ker
      (sourceSelectedGramDifferentialToSym d n (min n (d + 1)) x I) =
      LinearMap.ker (sourceRealGramDifferential d n x) := by
  ext h
  constructor
  · intro hh
    rw [LinearMap.mem_ker] at hh ⊢
    apply sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero
      d n hminor
    have hval := congrArg Subtype.val hh
    ext i a
    exact congrFun (congrFun hval i) a
  · intro hh
    rw [LinearMap.mem_ker] at hh ⊢
    ext i a
    exact congrFun (congrFun hh i) (I a)

/-- Strict upper pairs in the selected coordinate block. -/
abbrev sourceSelectedUpperPair (m : ℕ) :=
  {p : Fin m × Fin m // p.1 < p.2}

/-- The strict-upper skew coordinates measuring failure of selected-block
symmetry. -/
def sourceSelectedSkewCoord
    (n m : ℕ) (I : Fin m → Fin n) :
    (Fin n → Fin m → ℝ) →ₗ[ℝ]
      (sourceSelectedUpperPair m → ℝ) where
  toFun := fun A p => A (I p.1.1) p.1.2 - A (I p.1.2) p.1.1
  map_add' := by
    intro A B
    ext p
    simp
    ring
  map_smul' := by
    intro c A
    ext p
    simp
    ring

/-- The kernel of the strict-upper skew map is exactly the selected symmetric
coordinate subspace. -/
theorem sourceSelectedSkewCoord_ker
    (n m : ℕ) (I : Fin m → Fin n) :
    LinearMap.ker (sourceSelectedSkewCoord n m I) =
      sourceSelectedSymCoordSubspace n m I := by
  ext A
  constructor
  · intro hA
    rw [LinearMap.mem_ker] at hA
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · have hp := congrFun hA (⟨(a, b), hab⟩ : sourceSelectedUpperPair m)
      simpa [sourceSelectedSkewCoord] using sub_eq_zero.mp hp
    · subst hab
      rfl
    · have hp := congrFun hA (⟨(b, a), hab⟩ : sourceSelectedUpperPair m)
      have hzero : A (I b) a - A (I a) b = 0 := by
        simpa [sourceSelectedSkewCoord] using hp
      exact (sub_eq_zero.mp hzero).symm
  · intro hA
    rw [LinearMap.mem_ker]
    ext p
    rcases p with ⟨⟨a, b⟩, hab⟩
    change A (I a) b - A (I b) a = 0
    exact sub_eq_zero.mpr (hA a b)

/-- The strict-upper skew coordinate map is surjective when the selected row
map is injective. -/
theorem sourceSelectedSkewCoord_surjective
    (n m : ℕ) (I : Fin m → Fin n)
    (hI : Function.Injective I) :
    Function.Surjective (sourceSelectedSkewCoord n m I) := by
  intro B
  let A : Fin n → Fin m → ℝ := fun r b =>
    if hr : r ∈ Set.range I then
      let a := (Equiv.ofInjective I hI).symm ⟨r, hr⟩
      if hlt : a < b then B ⟨(a, b), hlt⟩ else 0
    else 0
  refine ⟨A, ?_⟩
  ext p
  rcases p with ⟨⟨a, b⟩, hab⟩
  change A (I a) b - A (I b) a = B ⟨(a, b), hab⟩
  simp [A, Equiv.ofInjective_symm_apply, hab, not_lt_of_gt hab]

/-- Strict upper selected pairs are equivalent to
`Sigma (fun b : Fin m => Fin b.val)`. -/
def sourceSelectedUpperPairEquivSigma
    (m : ℕ) :
    sourceSelectedUpperPair m ≃ Sigma (fun b : Fin m => Fin b.val) where
  toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun := fun q =>
    ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv := by
    intro p
    rcases p with ⟨⟨a, b⟩, hab⟩
    rfl
  right_inv := by
    intro q
    rcases q with ⟨b, k⟩
    rfl

/-- The number of strict upper selected pairs is `m * (m - 1) / 2`. -/
theorem card_sourceSelectedUpperPair
    (m : ℕ) :
    Fintype.card (sourceSelectedUpperPair m) = m * (m - 1) / 2 := by
  calc
    Fintype.card (sourceSelectedUpperPair m)
        = Fintype.card (Sigma (fun b : Fin m => Fin b.val)) := by
          exact Fintype.card_congr (sourceSelectedUpperPairEquivSigma m)
    _ = ∑ b : Fin m, b.val := by
          simp
    _ = ∑ i ∈ Finset.range m, i := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) m)
    _ = m * (m - 1) / 2 := by
          rw [Finset.sum_range_id]

/-- The selected symmetric-coordinate subspace has the expected dimension. -/
theorem finrank_sourceSelectedSymCoordSubspace
    (n m : ℕ)
    (I : Fin m → Fin n)
    (hI : Function.Injective I) :
    Module.finrank ℝ (sourceSelectedSymCoordSubspace n m I) =
      n * m - (m * (m - 1)) / 2 := by
  let skew := sourceSelectedSkewCoord n m I
  have hker : LinearMap.ker skew = sourceSelectedSymCoordSubspace n m I :=
    sourceSelectedSkewCoord_ker n m I
  have hsurj : LinearMap.range skew = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedSkewCoord_surjective n m I hI)
  have hrank := LinearMap.finrank_range_add_finrank_ker skew
  have hrange :
      Module.finrank ℝ (LinearMap.range skew) =
        m * (m - 1) / 2 := by
    rw [hsurj]
    rw [finrank_top]
    simpa [Module.finrank_fintype_fun_eq_card] using
      card_sourceSelectedUpperPair m
  have hdomain :
      Module.finrank ℝ (Fin n → Fin m → ℝ) = n * m := by
    rw [Module.finrank_pi_fintype]
    simp [Fintype.card_fin]
  rw [hrange, hker, hdomain] at hrank
  omega

/-- At a point with a nonzero maximal source minor, the real Gram
differential has the expected rank. -/
theorem sourceRealGramDifferential_rank_of_exists_nonzero_minor
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hminor :
      ∃ I : Fin (min n (d + 1)) → Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
          sourceRegularMinor d n I J x ≠ 0) :
    Module.finrank ℝ
      (LinearMap.range (sourceRealGramDifferential d n x)) =
      sourceGramExpectedDim d n := by
  let m := min n (d + 1)
  rcases hminor with ⟨I, hI, J, hJ, hdet⟩
  let L := sourceRealGramDifferential d n x
  let P := sourceSelectedGramCoord n m I
  let S := sourceSelectedSymCoordSubspace n m I
  let rangeToSelectedSym : LinearMap.range L →ₗ[ℝ] S := {
    toFun := fun y =>
      ⟨P y, by
        change P ↑y ∈ sourceSelectedSymCoordSubspace n (min n (d + 1)) I
        rw [← sourceSelectedGramCoord_comp_differential_range_eq
          d n hI hJ hdet]
        rcases y.property with ⟨h, hy⟩
        exact ⟨h, by
          change P (L h) = P ↑y
          rw [hy]⟩⟩
    map_add' := by
      intro y z
      ext i a
      rfl
    map_smul' := by
      intro c y
      ext i a
      rfl }
  have hinj : Function.Injective rangeToSelectedSym := by
    intro y z hyz
    apply sourceSelectedGramCoord_injective_on_differential_range d n hI hJ hdet
    exact congrArg Subtype.val hyz
  have hsurj : Function.Surjective rangeToSelectedSym := by
    intro A
    have hA :
        (A : Fin n → Fin m → ℝ) ∈
          LinearMap.range (P.comp L) := by
      rw [sourceSelectedGramCoord_comp_differential_range_eq d n hI hJ hdet]
      exact A.property
    rcases hA with ⟨h, hh⟩
    refine ⟨⟨L h, ⟨h, rfl⟩⟩, ?_⟩
    ext i a
    exact congrFun (congrFun hh i) a
  let e : LinearMap.range L ≃ₗ[ℝ] S :=
    LinearEquiv.ofBijective rangeToSelectedSym ⟨hinj, hsurj⟩
  calc
    Module.finrank ℝ (LinearMap.range L)
        = Module.finrank ℝ S := e.finrank_eq
    _ = n * m - (m * (m - 1)) / 2 :=
        finrank_sourceSelectedSymCoordSubspace n m I hI
    _ = sourceGramExpectedDim d n := by
        simp [sourceGramExpectedDim, m]

/-- At a regular source configuration, the real Gram differential has the
expected rank. -/
theorem sourceRealGramDifferential_rank_of_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    Module.finrank ℝ
      (LinearMap.range (sourceRealGramDifferential d n x)) =
      sourceGramExpectedDim d n :=
  sourceRealGramDifferential_rank_of_exists_nonzero_minor d n
    (exists_nonzero_minor_of_sourceGramRegularAt d n hreg)

/-- Complexifying a real regular source configuration remains regular. -/
theorem sourceComplex_regular_of_real_regular
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x) :
    SourceComplexGramRegularAt d n (realEmbed x) := by
  rcases exists_nonzero_minor_of_sourceGramRegularAt d n hreg with
    ⟨I, _hI, J, _hJ, hdet⟩
  let m := min n (d + 1)
  let restrictJ : (Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin m → ℂ) := {
    toFun := fun v b => v (J b)
    map_add' := by
      intro v w
      ext b
      simp
    map_smul' := by
      intro c v
      ext b
      simp }
  have hdet_real :
      (Matrix.of fun a b : Fin m => x (I a) (J b)).det ≠ 0 := by
    simpa [sourceRegularMinor, m] using hdet
  have hdetC :
      (Matrix.of fun a b : Fin m => (x (I a) (J b) : ℂ)).det ≠ 0 := by
    let M : Matrix (Fin m) (Fin m) ℝ :=
      Matrix.of fun a b => x (I a) (J b)
    have hmatrix : Complex.ofRealHom.mapMatrix M =
        (Matrix.of fun a b : Fin m => (x (I a) (J b) : ℂ)) := by
      ext a b
      rfl
    rw [← hmatrix]
    have hmap := RingHom.map_det Complex.ofRealHom M
    rw [← hmap]
    have hM : M.det ≠ 0 := by
      simpa [M] using hdet_real
    exact (Complex.ofReal_ne_zero).2 hM
  have hrowsC : LinearIndependent ℂ
      (fun a : Fin m => fun b : Fin m => (x (I a) (J b) : ℂ)) := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetC
  have hxIC : LinearIndependent ℂ
      (fun a : Fin m => realEmbed (d := d) (n := n) x (I a)) := by
    apply LinearIndependent.of_comp restrictJ
    simpa [Function.comp_def, restrictJ, realEmbed, m] using hrowsC
  unfold SourceComplexGramRegularAt
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n (realEmbed x)
  have hxIS : LinearIndependent ℂ
      (fun a : Fin m =>
        (⟨realEmbed (d := d) (n := n) x (I a), by
          change realEmbed (d := d) (n := n) x (I a) ∈
            Submodule.span ℂ (Set.range (realEmbed x))
          exact Submodule.subset_span ⟨I a, rfl⟩⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype
    simpa [Function.comp_def, S, m] using hxIC
  have hlower : m ≤ Module.finrank ℂ S := by
    simpa [Fintype.card_fin] using hxIS.fintype_card_le_finrank
  have hupper_n : Module.finrank ℂ S ≤ n := by
    simpa [S, sourceComplexConfigurationSpan] using
      (finrank_range_le_card (R := ℂ) (b := realEmbed x))
  have hupper_d : Module.finrank ℂ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [Module.finrank_fin_fun] using h
  have hupper : Module.finrank ℂ S ≤ m :=
    le_min hupper_n hupper_d
  exact le_antisymm hupper hlower

/-- At a real source point, the complex Gram differential range is the complex
span of the complexified real Gram differential range. -/
theorem sourceComplexGramDifferential_realEmbed_range_eq_complex_span
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    LinearMap.range
        (sourceComplexGramDifferential d n (realEmbed x)) =
      Submodule.span ℂ
        (sourceRealGramComplexify n ''
          LinearMap.range (sourceRealGramDifferential d n x)) := by
  apply le_antisymm
  · rintro δ ⟨h, rfl⟩
    let hre : Fin n → Fin (d + 1) → ℝ := fun i μ => (h i μ).re
    let him : Fin n → Fin (d + 1) → ℝ := fun i μ => (h i μ).im
    have hdecomp : h = realEmbed hre + Complex.I • realEmbed him := by
      ext i μ
      simpa [hre, him, realEmbed, smul_eq_mul, mul_comm] using
        (Complex.re_add_im (h i μ)).symm
    rw [hdecomp, map_add, map_smul]
    apply Submodule.add_mem
    · rw [sourceComplexGramDifferential_realEmbed]
      exact Submodule.subset_span
        ⟨(sourceRealGramDifferential d n x) hre, ⟨hre, rfl⟩, rfl⟩
    · apply Submodule.smul_mem
      rw [sourceComplexGramDifferential_realEmbed]
      exact Submodule.subset_span
        ⟨(sourceRealGramDifferential d n x) him, ⟨him, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro δ ⟨δR, hδR, rfl⟩
    rcases hδR with ⟨h, rfl⟩
    exact ⟨realEmbed h, by
      rw [sourceComplexGramDifferential_realEmbed]⟩

end BHW
