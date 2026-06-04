import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFrame
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Quotient preimages for Hall-Wightman maximal isotropic frames

This file keeps the next quotient/rank-nullity support for
`complexMinkowski_maximalIsotropicFrameIn_extending` outside the already large
maximal-frame file.  The declarations here start the concrete preimage packet
for the quotient `Rperp / R`: define the preimage in `Rperp`, retype it in `N`
and in original source coordinates, and prove the original-coordinate preimage
remains inside `N` and contains the original totally isotropic subspace.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option maxHeartbeats 800000

local instance complexMinkowskiRelativeOrthogonalHasQuotient
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    HasQuotient (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
      (Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)) :=
  Submodule.hasQuotient (R := ℂ)
    (M := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)

/-- A subspace is totally isotropic for a bilinear form when every two vectors
in the subspace pair to zero.  This pointwise form avoids quotient-subtype
packaging during the relative-orthogonal argument below. -/
def BilinFormTotallyIsotropicSubspace
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V)
    (Q : Submodule ℂ V) : Prop :=
  ∀ {x y : V}, x ∈ Q → y ∈ Q → B x y = 0

/-- A totally isotropic subspace maximal by finite dimension for a fixed
bilinear form. -/
structure BilinFormMaximalTotallyIsotropicSubspace
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) where
  Q : Submodule ℂ V
  Q_iso : BilinFormTotallyIsotropicSubspace B Q
  maximal :
    ∀ S : Submodule ℂ V,
      BilinFormTotallyIsotropicSubspace B S →
        Module.finrank ℂ S ≤ Module.finrank ℂ Q

/-- Every finite-dimensional vector space with a bilinear form contains a
totally isotropic subspace of maximal finite dimension. -/
theorem bilinForm_maximalTotallyIsotropicSubspace_exists
    {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) :
    ∃ Q : Submodule ℂ V,
      BilinFormTotallyIsotropicSubspace B Q ∧
        ∀ S : Submodule ℂ V,
          BilinFormTotallyIsotropicSubspace B S →
            Module.finrank ℂ S ≤ Module.finrank ℂ Q := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ Q : Submodule ℂ V,
      BilinFormTotallyIsotropicSubspace B Q ∧
        Module.finrank ℂ Q = k
  have hP0 : P 0 := by
    refine ⟨⊥, ?_, ?_⟩
    · intro x y hx _hy
      have hx0 : x = 0 := by
        simpa using (Submodule.mem_bot ℂ).1 hx
      rw [hx0]
      simp
    · simp
  let k := Nat.findGreatest P (Module.finrank ℂ V)
  have hPk : P k := Nat.findGreatest_spec (by simp) hP0
  rcases hPk with ⟨Q, hQ_iso, hQ_rank⟩
  refine ⟨Q, hQ_iso, ?_⟩
  intro S hS_iso
  have hS_bound : Module.finrank ℂ S ≤ Module.finrank ℂ V := by
    simpa using
      Submodule.finrank_mono
        (show S ≤ (⊤ : Submodule ℂ V) from le_top)
  have hP_S : P (Module.finrank ℂ S) :=
    ⟨S, hS_iso, rfl⟩
  have hle : Module.finrank ℂ S ≤ k :=
    Nat.le_findGreatest hS_bound hP_S
  simpa [k, hQ_rank] using hle

/-- Packaged maximal isotropic subspace for a finite-dimensional bilinear
form. -/
noncomputable def bilinFormMaximalTotallyIsotropicSubspace
    {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) :
    BilinFormMaximalTotallyIsotropicSubspace B :=
  let h := bilinForm_maximalTotallyIsotropicSubspace_exists B
  let Q := Classical.choose h
  { Q := Q
    Q_iso := (Classical.choose_spec h).1
    maximal := (Classical.choose_spec h).2 }

/-- The image carrier of a linear map after quotienting its codomain by a
submodule, defined by explicit quotient-class representatives. -/
def linearMapQuotientImageCarrier
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V) :
    Submodule ℂ (V ⧸ p) where
  carrier := {q | ∃ x : W, q = p.mkQ (A x)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨xw, rfl⟩
    rcases hy with ⟨yw, rfl⟩
    refine ⟨xw + yw, ?_⟩
    simp
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨xw, rfl⟩
    refine ⟨c • xw, ?_⟩
    simp

/-- The quotient-image representative map from the domain to its image carrier. -/
def linearMapToQuotientImageCarrier
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V) :
    W →ₗ[ℂ] linearMapQuotientImageCarrier p A where
  toFun x := ⟨p.mkQ (A x), ⟨x, rfl⟩⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

/-- The representative map onto the generic quotient-image carrier is
surjective by construction. -/
theorem linearMapToQuotientImageCarrier_surjective
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V) :
    Function.Surjective (linearMapToQuotientImageCarrier p A) := by
  intro q
  rcases q.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  ext
  exact hx.symm

/-- Kernel membership for the generic quotient-image representative map. -/
theorem linearMapToQuotientImageCarrier_mem_ker_iff
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V)
    (x : W) :
    x ∈ LinearMap.ker (linearMapToQuotientImageCarrier p A) ↔ A x ∈ p := by
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hxval := congrArg Subtype.val hx
    change p.mkQ (A x) = 0 at hxval
    rw [Submodule.mkQ_apply] at hxval
    exact (Submodule.Quotient.mk_eq_zero (p := p) (x := A x)).1 hxval
  · intro hx
    rw [LinearMap.mem_ker]
    ext
    change p.mkQ (A x) = 0
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (p := p) (x := A x)).2 hx

/-- The kernel of the generic representative map is the comap of the quotient
submodule along the original linear map. -/
theorem linearMapToQuotientImageCarrier_ker_eq_comap
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V) :
    LinearMap.ker (linearMapToQuotientImageCarrier p A) = p.comap A := by
  ext x
  exact linearMapToQuotientImageCarrier_mem_ker_iff p A x

/-- Rank-nullity for the generic representative map onto a quotient-image
carrier. -/
theorem linearMapQuotientImageCarrier_finrank_add_ker
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V) :
    Module.finrank ℂ (linearMapQuotientImageCarrier p A) +
      Module.finrank ℂ (LinearMap.ker (linearMapToQuotientImageCarrier p A)) =
        Module.finrank ℂ W := by
  let f := linearMapToQuotientImageCarrier p A
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.2
      (linearMapToQuotientImageCarrier_surjective p A)
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrank
  simpa [f] using hrank

/-- A quotient-image carrier is totally isotropic when the chosen quotient
representatives pair to zero. -/
theorem linearMapQuotientImageCarrier_isotropic_of_pair_zero
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V)
    (B : LinearMap.BilinForm ℂ (V ⧸ p))
    (h_pair : ∀ x y : W, B (p.mkQ (A x)) (p.mkQ (A y)) = 0) :
    BilinFormTotallyIsotropicSubspace B (linearMapQuotientImageCarrier p A) := by
  intro x y hx hy
  rcases hx with ⟨xw, rfl⟩
  rcases hy with ⟨yw, rfl⟩
  exact h_pair xw yw

/-- A maximal isotropic quotient subspace bounds any quotient-image carrier whose
representatives pair to zero. -/
theorem linearMapQuotientImageCarrier_finrank_le_of_maximal_isotropic
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (p : Submodule ℂ V)
    (A : W →ₗ[ℂ] V)
    (B : LinearMap.BilinForm ℂ (V ⧸ p))
    (Qmax : Submodule ℂ (V ⧸ p))
    (hmax :
      ∀ Q : Submodule ℂ (V ⧸ p),
        BilinFormTotallyIsotropicSubspace B Q →
          Module.finrank ℂ Q ≤ Module.finrank ℂ Qmax)
    (h_pair : ∀ x y : W, B (p.mkQ (A x)) (p.mkQ (A y)) = 0) :
    Module.finrank ℂ (linearMapQuotientImageCarrier p A) ≤
      Module.finrank ℂ Qmax :=
  hmax (linearMapQuotientImageCarrier p A)
    (linearMapQuotientImageCarrier_isotropic_of_pair_zero p A B h_pair)

/-- The explicit carrier of the preimage of a quotient submodule under the
quotient map.  This avoids unfolding `Submodule.comap` at dependent source
specializations while remaining definitionally the same carrier. -/
def quotientPreimageCarrier
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    Submodule ℂ V where
  carrier := {x | p.mkQ x ∈ Q}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    exact Q.add_mem hx hy
  smul_mem' := by
    intro c x hx
    exact Q.smul_mem c hx

/-- The explicit quotient-preimage carrier agrees with the `comap` carrier. -/
theorem quotientPreimageCarrier_eq_comap
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    quotientPreimageCarrier p Q = Q.comap p.mkQ := by
  ext x
  rfl

/-- The quotient map from the full preimage of a quotient submodule to that
quotient submodule. -/
def quotientPreimageToSubmodule
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    Q.comap p.mkQ →ₗ[ℂ] Q where
  toFun x := ⟨p.mkQ x, x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

/-- The quotient-preimage map is onto the chosen quotient submodule. -/
theorem quotientPreimageToSubmodule_surjective
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    Function.Surjective (quotientPreimageToSubmodule p Q) := by
  intro q
  obtain ⟨x, hx⟩ := p.mkQ_surjective q
  refine ⟨⟨x, ?_⟩, ?_⟩
  · simp [hx, q.2]
  · ext
    exact hx

/-- The kernel of the quotient-preimage map is exactly the original quotient
submodule, retyped inside the preimage. -/
theorem quotientPreimageToSubmodule_ker_eq_comap
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    LinearMap.ker (quotientPreimageToSubmodule p Q) =
      p.comap (Q.comap p.mkQ).subtype := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hxval := congrArg Subtype.val hx
    change p.mkQ (x : V) = 0 at hxval
    rw [Submodule.mkQ_apply] at hxval
    exact (Submodule.Quotient.mk_eq_zero (p := p) (x := (x : V))).1 hxval
  · intro hx
    rw [LinearMap.mem_ker]
    ext
    change p.mkQ (x : V) = 0
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (p := p) (x := (x : V))).2 hx

/-- The preimage of a quotient submodule has dimension equal to the dimension of
the quotient kernel plus the dimension of the quotient submodule. -/
theorem quotientPreimage_finrank_eq_add
    {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    Module.finrank ℂ (Q.comap p.mkQ) =
      Module.finrank ℂ p + Module.finrank ℂ Q := by
  let f := quotientPreimageToSubmodule p Q
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.2
      (quotientPreimageToSubmodule_surjective p Q)
  have hker_fin :
      Module.finrank ℂ (LinearMap.ker f) = Module.finrank ℂ p := by
    rw [quotientPreimageToSubmodule_ker_eq_comap]
    exact LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (Submodule.le_comap_mkQ p Q))
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, hker_fin] at hrank
  rw [add_comm] at hrank
  exact hrank.symm

/-- Finrank version for the explicit quotient-preimage carrier. -/
theorem quotientPreimageCarrier_finrank_eq_add
    {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (p : Submodule ℂ V)
    (Q : Submodule ℂ (V ⧸ p)) :
    Module.finrank ℂ (quotientPreimageCarrier p Q) =
      Module.finrank ℂ p + Module.finrank ℂ Q := by
  rw [quotientPreimageCarrier_eq_comap]
  exact quotientPreimage_finrank_eq_add p Q

/-- Arithmetic cancellation for the two rank-nullity identities used in the
compatible maximal-isotropic extension. -/
theorem quotient_rankNullity_cancel_le
    {s ker image inter range r q Q : ℕ}
    (hS : s = ker + range)
    (hker : image + inter = ker)
    (hrange : range + inter ≤ r)
    (himage : image ≤ q)
    (hQ : Q = r + q) :
    s ≤ Q := by
  omega

/-- Specialized maximal isotropic quotient subspace for the relative-orthogonal
quotient form `Rperp / R`. -/
theorem complexMinkowskiRelativeOrthogonalQuotient_maximalIsotropicSubspace_exists
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    ∃ Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN),
      BilinFormTotallyIsotropicSubspace
        (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)
        Qbar ∧
        ∀ S : Submodule ℂ
          (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
            complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN),
          BilinFormTotallyIsotropicSubspace
            (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)
            S →
            Module.finrank ℂ S ≤ Module.finrank ℂ Qbar :=
  bilinForm_maximalTotallyIsotropicSubspace_exists
    (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)

/-- Packaged maximal isotropic quotient subspace for the relative-orthogonal
quotient form `Rperp / R`. -/
noncomputable def complexMinkowskiRelativeOrthogonalQuotient_maximalIsotropicSubspace
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    BilinFormMaximalTotallyIsotropicSubspace
      (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN) :=
  bilinFormMaximalTotallyIsotropicSubspace
    (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)

/-- Specialized package for a maximal isotropic subspace of the
relative-orthogonal quotient `Rperp / R`. -/
structure ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) where
  Q : Submodule ℂ
    (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)
  Q_iso :
    BilinFormTotallyIsotropicSubspace
      (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN) Q
  maximal :
    ∀ S : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN),
      BilinFormTotallyIsotropicSubspace
        (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN) S →
        Module.finrank ℂ S ≤ Module.finrank ℂ Q

/-- Packaged specialized maximal isotropic quotient subspace. -/
noncomputable def complexMinkowskiRelativeOrthogonalQuotient_maximalPackage
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage (d := d) (N := N) RN := by
  let M :=
    complexMinkowskiRelativeOrthogonalQuotient_maximalIsotropicSubspace
      (d := d) (N := N) RN
  exact { Q := M.Q, Q_iso := M.Q_iso, maximal := M.maximal }

/-- Pair an isotropic test subspace `S` against the fixed subspace `R`, landing
in the dual of `R`.  This is the first rank-nullity map in the compatible
maximal-frame extension proof. -/
def complexMinkowskiPairingToSubmoduleDual
    (d : ℕ)
    (R S : Submodule ℂ (Fin (d + 1) → ℂ)) :
    S →ₗ[ℂ] Module.Dual ℂ R where
  toFun s :=
    { toFun := fun r =>
        sourceComplexMinkowskiInner d
          (s : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ)
      map_add' := by
        intro x y
        rw [Submodule.coe_add, sourceComplexMinkowskiInner_add_right]
      map_smul' := by
        intro c x
        rw [Submodule.coe_smul, sourceComplexMinkowskiInner_smul_right]
        simp }
  map_add' := by
    intro x y
    ext r
    change sourceComplexMinkowskiInner d
        ((x + y : S) : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ) +
        sourceComplexMinkowskiInner d
          (y : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ)
    rw [Submodule.coe_add, sourceComplexMinkowskiInner_add_left]
  map_smul' := by
    intro c x
    ext r
    change sourceComplexMinkowskiInner d
        ((c • x : S) : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ) =
      c * sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ) (r : Fin (d + 1) → ℂ)
    rw [Submodule.coe_smul, sourceComplexMinkowskiInner_smul_left]

/-- The range of the pairing map `S -> R*` annihilates the intersection
`S ∩ R` when `S` is totally isotropic. -/
theorem complexMinkowskiPairingToSubmoduleDual_range_le_dualAnnihilator
    {d : ℕ}
    {R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hS_iso : ComplexMinkowskiTotallyIsotropicSubspace d S) :
    LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S) ≤
      (complexMinkowskiSubmoduleIn (d := d) R S).dualAnnihilator := by
  intro φ hφ
  rcases hφ with ⟨s, rfl⟩
  rw [Submodule.mem_dualAnnihilator]
  intro r hr
  exact hS_iso s ⟨(r : Fin (d + 1) → ℂ), hr⟩

/-- Dimension form of the annihilator bound for the pairing map `S -> R*`.
The `finrank (S ∩ R)` term is the one that later cancels against the quotient
map kernel. -/
theorem complexMinkowskiPairingToSubmoduleDual_range_add_inter_finrank_le
    {d : ℕ}
    {R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hS_iso : ComplexMinkowskiTotallyIsotropicSubspace d S) :
    Module.finrank ℂ
        (LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S)) +
      Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) ≤
        Module.finrank ℂ R := by
  let T := complexMinkowskiSubmoduleIn (d := d) R S
  have hle :
      LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S) ≤
        T.dualAnnihilator := by
    simpa [T] using
      complexMinkowskiPairingToSubmoduleDual_range_le_dualAnnihilator
        (d := d) (R := R) (S := S) hS_iso
  calc
    Module.finrank ℂ
          (LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S)) +
        Module.finrank ℂ T
        ≤ Module.finrank ℂ T.dualAnnihilator + Module.finrank ℂ T := by
          exact Nat.add_le_add_right (Submodule.finrank_mono hle) _
    _ = Module.finrank ℂ R := by
      rw [add_comm]
      exact Subspace.finrank_add_finrank_dualAnnihilator_eq T

/-- The kernel of the pairing map `S -> R*` consists exactly of those vectors
of `S` that lie in the relative orthogonal of `R` inside `N`. -/
theorem complexMinkowskiPairingToSubmoduleDual_mem_ker_iff
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (x : S) :
    x ∈ LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) ↔
      (⟨(x : Fin (d + 1) → ℂ), hS_le x.2⟩ : N) ∈
        complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) := by
  constructor
  · intro hx r
    rw [LinearMap.mem_ker] at hx
    have hval := congrArg
      (fun φ : Module.Dual ℂ R =>
        φ ⟨((r : N) : Fin (d + 1) → ℂ), r.2⟩) hx
    simpa [complexMinkowskiPairingToSubmoduleDual] using hval
  · intro hx
    rw [LinearMap.mem_ker]
    ext r
    let rN : complexMinkowskiSubmoduleIn (d := d) N R :=
      ⟨⟨(r : Fin (d + 1) → ℂ), hR_le r.2⟩, r.2⟩
    have hval := hx rN
    simpa [complexMinkowskiPairingToSubmoduleDual, rN] using hval

/-- The kernel of `S -> R*`, retyped into the relative orthogonal `Rperp`
inside `N`. -/
def complexMinkowskiPairingKerToRelativeOrthogonal
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N) :
    LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ]
      complexMinkowskiRelativeOrthogonalIn (d := d) N
        (complexMinkowskiSubmoduleIn (d := d) N R) where
  toFun x :=
    ⟨⟨((x : LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) : S),
        hS_le (x : S).2⟩,
      (complexMinkowskiPairingToSubmoduleDual_mem_ker_iff
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le (x : S)).1 x.2⟩
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl

@[simp]
theorem complexMinkowskiPairingKerToRelativeOrthogonal_apply_coe
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (x : LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) :
    (((complexMinkowskiPairingKerToRelativeOrthogonal
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le x :
        complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R)) : N) :
      Fin (d + 1) → ℂ) =
        ((x : LinearMap.ker
          (complexMinkowskiPairingToSubmoduleDual d R S)) : S) := rfl

/-- Membership in the retyped `R` inside `Rperp` is the same as the underlying
source vector of the pairing kernel lying in `R`. -/
theorem complexMinkowskiPairingKerToRelativeOrthogonal_mem_Rin_iff
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (x : LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) :
    complexMinkowskiPairingKerToRelativeOrthogonal
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le x ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
        (complexMinkowskiSubmoduleIn (d := d) N R) ↔
    (((x : LinearMap.ker
        (complexMinkowskiPairingToSubmoduleDual d R S)) : S) :
      Fin (d + 1) → ℂ) ∈ R := by
  rfl

/-- The kernel term in the generic quotient-image rank-nullity formula is
linearly equivalent to the retyped intersection `S ∩ R`. -/
noncomputable def complexMinkowskiPairingKerToRelativeOrthogonalComapEquivInter
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    complexMinkowskiSubmoduleIn (d := d) R S ≃ₗ[ℂ]
      (let RN := complexMinkowskiSubmoduleIn (d := d) N R
       let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
       let Rin : Submodule ℂ Rperp :=
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
       let A :
          LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ] Rperp :=
        complexMinkowskiPairingKerToRelativeOrthogonal
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le
       Rin.comap A) where
  toFun t := by
    let s : S := ⟨(t : Fin (d + 1) → ℂ), t.2⟩
    have hsKer :
        s ∈ LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) := by
      rw [LinearMap.mem_ker]
      ext r
      exact hR_iso ⟨(t : Fin (d + 1) → ℂ), (t : R).2⟩ r
    let x :
        LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) :=
      ⟨s, hsKer⟩
    refine ⟨x, ?_⟩
    change complexMinkowskiPairingKerToRelativeOrthogonal
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le x ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
        (complexMinkowskiSubmoduleIn (d := d) N R)
    rw [complexMinkowskiPairingKerToRelativeOrthogonal_mem_Rin_iff
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le x]
    exact (t : R).2
  invFun x := by
    let xker : LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) := x
    have hxR :
        (((xker : LinearMap.ker
          (complexMinkowskiPairingToSubmoduleDual d R S)) : S) :
            Fin (d + 1) → ℂ) ∈ R := by
      rw [← complexMinkowskiPairingKerToRelativeOrthogonal_mem_Rin_iff
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le xker]
      exact x.2
    exact ⟨⟨(xker : S), hxR⟩, (xker : S).2⟩
  left_inv t := by
    ext i
    rfl
  right_inv x := by
    ext i
    rfl
  map_add' t u := by
    ext i
    rfl
  map_smul' c t := by
    ext i
    rfl

/-- Finrank form of the equivalence between the generic quotient-image kernel
term and the retyped intersection `S ∩ R`. -/
theorem complexMinkowskiPairingKerToRelativeOrthogonal_comap_finrank_eq_inter
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    Module.finrank ℂ
      (let RN := complexMinkowskiSubmoduleIn (d := d) N R
       let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
       let Rin : Submodule ℂ Rperp :=
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
       let A :
          LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ] Rperp :=
        complexMinkowskiPairingKerToRelativeOrthogonal
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le
       Rin.comap A) =
        Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) := by
  exact
    (LinearEquiv.finrank_eq
      (complexMinkowskiPairingKerToRelativeOrthogonalComapEquivInter
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le hR_iso)).symm

/-- Rank-nullity for `ker(S -> R*) -> Rperp / R`, in the generic quotient-image
carrier form. -/
theorem complexMinkowskiPairingKer_genericQuotientImage_finrank_add_inter
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    Module.finrank ℂ
      (let RN := complexMinkowskiSubmoduleIn (d := d) N R
       let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
       let Rin : Submodule ℂ Rperp :=
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
       let A :
          LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ] Rperp :=
        complexMinkowskiPairingKerToRelativeOrthogonal
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le
       linearMapQuotientImageCarrier
        (V := Rperp)
        (W := LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
        Rin A) +
      Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) =
        Module.finrank ℂ
          (LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
  let Rin : Submodule ℂ Rperp :=
    complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
  let A :
      LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ] Rperp :=
    complexMinkowskiPairingKerToRelativeOrthogonal
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le
  change
    Module.finrank ℂ
        (linearMapQuotientImageCarrier
          (V := Rperp)
          (W := LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
          Rin A) +
      Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) =
        Module.finrank ℂ
          (LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
  have h :=
    linearMapQuotientImageCarrier_finrank_add_ker
      (V := Rperp)
      (W := LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
      Rin A
  rw [linearMapToQuotientImageCarrier_ker_eq_comap
    (V := Rperp)
    (W := LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
    Rin A] at h
  rw [complexMinkowskiPairingKerToRelativeOrthogonal_comap_finrank_eq_inter
    (d := d) (N := N) (R := R) (S := S) hR_le hS_le hR_iso] at h
  exact h

/-- The image of `ker(S -> R*)` in the quotient `Rperp / R`, represented as a
submodule carrier rather than as a separate dependent quotient map. -/
def complexMinkowskiPairingKernelQuotientImage
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N) :
    Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R)) where
  carrier := {q |
    ∃ x : LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S),
      q =
        Submodule.mkQ
          (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
            (complexMinkowskiSubmoduleIn (d := d) N R))
          (complexMinkowskiPairingKerToRelativeOrthogonal
            (d := d) (N := N) (R := R) (S := S) hR_le hS_le x)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨xker, rfl⟩
    rcases hy with ⟨yker, rfl⟩
    refine ⟨xker + yker, ?_⟩
    simp
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨xker, rfl⟩
    refine ⟨c • xker, ?_⟩
    simp

/-- Rank-nullity for the concrete quotient image of `ker(S -> R*)`. -/
theorem complexMinkowskiPairingKernelQuotientImage_finrank_add_inter
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    Module.finrank ℂ
        (complexMinkowskiPairingKernelQuotientImage
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le) +
      Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) =
        Module.finrank ℂ
          (LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
  let Rin : Submodule ℂ Rperp :=
    complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
  let A :
      LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S) →ₗ[ℂ] Rperp :=
    complexMinkowskiPairingKerToRelativeOrthogonal
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le
  change
    Module.finrank ℂ
        (linearMapQuotientImageCarrier
          (V := Rperp)
          (W := LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
          Rin A) +
      Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) =
        Module.finrank ℂ
          (LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S))
  exact
    complexMinkowskiPairingKer_genericQuotientImage_finrank_add_inter
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le hR_iso

/-- The quotient-image carrier of `ker(S -> R*)` is isotropic for the induced
quotient form when `S` is totally isotropic. -/
theorem complexMinkowskiPairingKernelQuotientImage_isotropic
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hS_iso : ComplexMinkowskiTotallyIsotropicSubspace d S) :
    BilinFormTotallyIsotropicSubspace
      (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N)
        (complexMinkowskiSubmoduleIn (d := d) N R))
      (complexMinkowskiPairingKernelQuotientImage
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le) := by
  intro x y hx hy
  rcases hx with ⟨xker, rfl⟩
  rcases hy with ⟨yker, rfl⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  change
    complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N)
        (complexMinkowskiSubmoduleIn (d := d) N R)
      (Quotient.mk''
        (complexMinkowskiPairingKerToRelativeOrthogonal
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le xker))
      (Quotient.mk''
        (complexMinkowskiPairingKerToRelativeOrthogonal
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le yker)) = 0
  rw [complexMinkowskiRelativeOrthogonalQuotientForm_mk]
  exact hS_iso (xker : S) (yker : S)

/-- A maximal isotropic quotient subspace bounds the concrete quotient image of
`ker(S -> R*)`. -/
theorem complexMinkowskiPairingKernelQuotientImage_finrank_le_of_maximal
    {d : ℕ}
    {N R S : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hS_iso : ComplexMinkowskiTotallyIsotropicSubspace d S)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R)))
    (hQbar_max :
      ∀ T : Submodule ℂ
        (complexMinkowskiRelativeOrthogonalIn (d := d) N
            (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
            (complexMinkowskiSubmoduleIn (d := d) N R)),
        BilinFormTotallyIsotropicSubspace
          (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N)
            (complexMinkowskiSubmoduleIn (d := d) N R))
          T →
          Module.finrank ℂ T ≤ Module.finrank ℂ Qbar) :
    Module.finrank ℂ
      (complexMinkowskiPairingKernelQuotientImage
        (d := d) (N := N) (R := R) (S := S) hR_le hS_le) ≤
      Module.finrank ℂ Qbar :=
  hQbar_max
    (complexMinkowskiPairingKernelQuotientImage
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le)
    (complexMinkowskiPairingKernelQuotientImage_isotropic
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le hS_iso)

/-- The preimage in `Rperp` of a subspace of the quotient `Rperp / R`. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN) :=
  quotientPreimageCarrier
    (V := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
    (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) Qbar

/-- The same quotient preimage retyped as a subspace of the ambient subtype
`N`. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimageInN
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ N :=
  (complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
    (d := d) (N := N) RN Qbar).map
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN).subtype

/-- The quotient preimage returned to original ambient source coordinates. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimage
    {d : ℕ}
    (N : Submodule ℂ (Fin (d + 1) → ℂ))
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  (complexMinkowskiRelativeOrthogonalQuotientPreimageInN
    (d := d) (N := N) RN Qbar).map N.subtype

/-- For a totally isotropic `R ≤ N`, the source-coordinate quotient preimage has
dimension `finrank R + finrank Qbar`. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimage_finrank_eq_add
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R))) :
    Module.finrank ℂ
        (complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) Qbar) =
      Module.finrank ℂ R + Module.finrank ℂ Qbar := by
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimage]
  rw [Submodule.finrank_map_subtype_eq]
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageInN]
  rw [Submodule.finrank_map_subtype_eq]
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp]
  rw [quotientPreimageCarrier_finrank_eq_add]
  rw [complexMinkowskiSubmoduleInRelativeOrthogonal_finrank_eq_of_totallyIsotropic
    (d := d) (N := N) (R := R) hR_le hR_iso]

/-- The ambient-coordinate quotient preimage remains inside `N`. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimage_le
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    complexMinkowskiRelativeOrthogonalQuotientPreimage
      (d := d) N RN Qbar ≤ N := by
  intro x hx
  rcases hx with ⟨xN, _hxN, rfl⟩
  exact xN.2

/-- Any vector in the retyped copy of `R` maps to zero in `Rperp / R`, hence
belongs to every quotient preimage.  This pointwise form keeps elaboration
lighter than the corresponding submodule-order statement. -/
theorem complexMinkowskiSubmoduleInRelativeOrthogonal_mkQ_mem_quotientPreimage
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (x : complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
    (hx : x ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) :
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x ∈
        Qbar := by
  rw [Submodule.mkQ_apply]
  have hx0 :
      Submodule.Quotient.mk
          (p := complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x =
        Submodule.Quotient.mk
          (p := complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)
          (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) := by
    apply Quotient.sound'
    let Rin :=
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
    have hxSub :
        x - 0 ∈ Rin := by
      change x + -(0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin
      have hzero : (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin :=
        Rin.zero_mem
      have hneg : -(0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin :=
        Submodule.neg_mem
          (p := Rin)
          (x := (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN))
          hzero
      exact Rin.add_mem hx hneg
    simpa [Submodule.quotientRel_def] using hxSub
  rw [hx0]
  simp

/-- If `R ≤ N` is totally isotropic, then every point of `R` belongs to the
ambient-coordinate preimage of any quotient subspace of `Rperp / R`. -/
theorem complexMinkowskiSubmodule_mem_relativeOrthogonalQuotientPreimage
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R)))
    {x : Fin (d + 1) → ℂ}
    (hx : x ∈ R) :
    x ∈ complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
      (complexMinkowskiSubmoduleIn (d := d) N R) Qbar := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
  have hRN_le : RN ≤ Rperp :=
    complexMinkowskiSubmoduleIn_le_relativeOrthogonalIn_of_totallyIsotropic
      (N := N) (R := R) hR_iso
  let xN : N := ⟨x, hR_le hx⟩
  have hxRN : xN ∈ RN := hx
  let xRperp : Rperp := ⟨xN, hRN_le hxRN⟩
  have hxRin : xRperp ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN := hxRN
  have hxPre : xRperp ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar := by
    exact
      complexMinkowskiSubmoduleInRelativeOrthogonal_mkQ_mem_quotientPreimage
        (d := d) (N := N) RN Qbar xRperp hxRin
  have hxPreN : xN ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar := by
    refine ⟨xRperp, hxPre, ?_⟩
    rfl
  exact ⟨xN, hxPreN, rfl⟩

/-- If `R ≤ N` is totally isotropic, then `R` is contained in every ambient
quotient preimage associated to `Rperp / R`. -/
theorem complexMinkowskiSubmodule_le_relativeOrthogonalQuotientPreimage
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R))) :
    R ≤ complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
      (complexMinkowskiSubmoduleIn (d := d) N R) Qbar := by
  intro x hx
  exact
    complexMinkowskiSubmodule_mem_relativeOrthogonalQuotientPreimage
      (d := d) (N := N) (R := R) hR_le hR_iso Qbar hx

/-- The quotient preimage in `Rperp` is isotropic whenever the quotient
subspace is isotropic for the induced quotient form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp_pair_zero
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0)
    {x y : complexMinkowskiRelativeOrthogonalIn (d := d) N RN}
    (hx : x ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar)
    (hy : y ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar) :
    sourceComplexMinkowskiInner d
      (((x : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) : N) :
        Fin (d + 1) → ℂ)
      (((y : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) : N) :
        Fin (d + 1) → ℂ) = 0 := by
  change
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x ∈
        Qbar at hx
  change
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) y ∈
        Qbar at hy
  rw [Submodule.mkQ_apply] at hx hy
  have hxy := hQbar_pair_zero
    (x := Quotient.mk'' x) (y := Quotient.mk'' y) hx hy
  simpa [complexMinkowskiRelativeOrthogonalQuotientForm_mk] using hxy

/-- The quotient preimage retyped in `N` is isotropic whenever the quotient
subspace is isotropic for the induced quotient form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageInN_pair_zero
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0)
    {x y : N}
    (hx : x ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar)
    (hy : y ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar) :
    sourceComplexMinkowskiInner d
      (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) = 0 := by
  rcases hx with ⟨xperp, hxperp, hx_eq⟩
  rcases hy with ⟨yperp, hyperp, hy_eq⟩
  rw [← hx_eq, ← hy_eq]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp_pair_zero
      (d := d) (N := N) RN Qbar hQbar_pair_zero hxperp hyperp

/-- The ambient-coordinate quotient preimage is a totally isotropic source
subspace whenever the quotient subspace is isotropic for the induced quotient
form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimage_isotropic
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N RN Qbar) := by
  intro x y
  rcases x.2 with ⟨xN, hxN, hx_eq⟩
  rcases y.2 with ⟨yN, hyN, hy_eq⟩
  rw [← hx_eq, ← hy_eq]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimageInN_pair_zero
      (d := d) (N := N) RN Qbar hQbar_pair_zero hxN hyN

/-- Candidate source subspace obtained as the preimage of a packaged maximal
isotropic quotient subspace.  This name hides the long quotient-preimage
expression in later field statements. -/
@[irreducible] def complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
    (complexMinkowskiSubmoduleIn (d := d) N R) M.Q

/-- Rank comparison against a candidate `Q` whose dimension is
`finrank R + finrank M.Q`, where `M.Q` is maximal isotropic in `Rperp / R`. -/
theorem complexMinkowskiSubspace_finrank_le_of_quotient_maximal
    {d : ℕ}
    {N R S Q : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hS_le : S ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hS_iso : ComplexMinkowskiTotallyIsotropicSubspace d S)
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R))
    (hQ_fin :
      Module.finrank ℂ Q = Module.finrank ℂ R + Module.finrank ℂ M.Q) :
    Module.finrank ℂ S ≤ Module.finrank ℂ Q := by
  have hS_rank :
      Module.finrank ℂ S =
        Module.finrank ℂ
            (LinearMap.ker (complexMinkowskiPairingToSubmoduleDual d R S)) +
          Module.finrank ℂ
            (LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S)) := by
    have h :=
      LinearMap.finrank_range_add_finrank_ker
        (complexMinkowskiPairingToSubmoduleDual d R S)
    rw [add_comm] at h
    exact h.symm
  have hker_rank :=
    complexMinkowskiPairingKernelQuotientImage_finrank_add_inter
      (d := d) (N := N) (R := R) (S := S) hR_le hS_le hR_iso
  have hrange :
      Module.finrank ℂ
          (LinearMap.range (complexMinkowskiPairingToSubmoduleDual d R S)) +
        Module.finrank ℂ (complexMinkowskiSubmoduleIn (d := d) R S) ≤
          Module.finrank ℂ R :=
    complexMinkowskiPairingToSubmoduleDual_range_add_inter_finrank_le
      (d := d) (R := R) (S := S) hS_iso
  have himage :
      Module.finrank ℂ
        (complexMinkowskiPairingKernelQuotientImage
          (d := d) (N := N) (R := R) (S := S) hR_le hS_le) ≤
        Module.finrank ℂ M.Q :=
    complexMinkowskiPairingKernelQuotientImage_finrank_le_of_maximal
      (d := d) (N := N) (R := R) (S := S)
      hR_le hS_le hS_iso M.Q M.maximal
  exact quotient_rankNullity_cancel_le hS_rank hker_rank hrange himage hQ_fin

/-- Global maximality of a candidate `Q` follows from the quotient-maximal
dimension formula. -/
theorem complexMinkowskiSubspace_global_maximal_of_quotient_maximal
    {d : ℕ}
    {N R Q : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R))
    (hQ_fin :
      Module.finrank ℂ Q = Module.finrank ℂ R + Module.finrank ℂ M.Q) :
    ∀ S : Submodule ℂ (Fin (d + 1) → ℂ),
      S ≤ N →
      ComplexMinkowskiTotallyIsotropicSubspace d S →
      Module.finrank ℂ S ≤ Module.finrank ℂ Q := by
  intro S hS_le hS_iso
  exact
    complexMinkowskiSubspace_finrank_le_of_quotient_maximal
      (d := d) (N := N) (R := R) (S := S) (Q := Q)
      hR_le hS_le hR_iso hS_iso M hQ_fin

end BHW
