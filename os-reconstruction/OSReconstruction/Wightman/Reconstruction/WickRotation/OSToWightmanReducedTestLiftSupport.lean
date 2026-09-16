/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced









open scoped Classical NNReal
open BigOperators MeasureTheory

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

theorem minkowski_isSpacelike_neg_iff
    (v : MinkowskiSpace d) :
    MinkowskiSpace.IsSpacelike d (-v) ↔
      MinkowskiSpace.IsSpacelike d v := by
  unfold MinkowskiSpace.IsSpacelike MinkowskiSpace.minkowskiNormSq
  rw [MinkowskiSpace.minkowskiInner_neg_left,
    MinkowskiSpace.minkowskiInner_neg_right]
  ring_nf

/-- Basepoint fiber marginal of an absolute test in real difference
coordinates. -/
noncomputable def reducedFiberIntegral
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ) :
    NPointDomain d m → ℂ :=
  fun ξ => ∫ x₀ : SpacetimeDim d,
    f ((BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m x₀ ξ))

omit [NeZero d] in
/-- The fiber marginal can be nonzero only over reduced coordinates that occur
above a nonzero absolute test value. -/
theorem reducedFiberIntegral_support_subset_of_absolute_reduced_support
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ)
    (S : Set (NPointDomain d m))
    (hf_support :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈ S) :
    Function.support (reducedFiberIntegral (d := d) m f) ⊆ S := by
  intro ξ hξ
  by_contra hξS
  have hzero :
      ∀ x₀ : SpacetimeDim d,
        f ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) = 0 := by
    intro x₀
    by_contra hx₀
    have hred :
        BHW.reducedDiffMapReal (m + 1) d
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) = ξ :=
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) (m := m) x₀ ξ
    have hS_abs :=
      hf_support
        ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) hx₀
    have hS_ξ : ξ ∈ S := by
      rw [hred] at hS_abs
      exact hS_abs
    exact hξS hS_ξ
  have hmargin_zero : reducedFiberIntegral (d := d) m f ξ = 0 := by
    simp [reducedFiberIntegral, hzero]
  exact hξ hmargin_zero

omit [NeZero d] in
/-- Compact absolute support projects to compact support of the basepoint fiber
marginal. -/
theorem reducedFiberIntegral_hasCompactSupport
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ)
    (hf_compact : HasCompactSupport f) :
    HasCompactSupport (reducedFiberIntegral (d := d) m f) := by
  let K : Set (NPointDomain d m) :=
    BHW.reducedDiffMapRealCLM (m + 1) d ''
      tsupport (f : NPointDomain d (m + 1) → ℂ)
  have hK_compact : IsCompact K := by
    exact hf_compact.isCompact.image
      (BHW.reducedDiffMapRealCLM (m + 1) d).continuous
  have hf_support_to_K :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈ K := by
    intro x hx
    exact ⟨x, subset_tsupport _ hx, rfl⟩
  have hsupport :
      Function.support (reducedFiberIntegral (d := d) m f) ⊆ K :=
    reducedFiberIntegral_support_subset_of_absolute_reduced_support
      (d := d) m f K hf_support_to_K
  exact HasCompactSupport.of_support_subset_isCompact hK_compact hsupport

/-- Fiber marginal of an absolute Schwartz test, named for the canonical-swap
normal form of the reduced Ruelle theorem. -/
def reducedFiberMarginal
    (m : ℕ) (f : SchwartzNPoint d (m + 1)) :
    NPointDomain d m → ℂ :=
  reducedFiberIntegral (d := d) m
    (f : NPointDomain d (m + 1) → ℂ)

omit [NeZero d] in
/-- Real form of the induced reduced permutation action. -/
def realPermOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) : NPointDomain d m :=
  fun k μ =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
      (fun k μ => (ξ k μ : ℂ)) k μ).re

omit [NeZero d] in
/-- Complexifying the real induced reduced permutation recovers the complex
induced action on real reduced configurations. -/
theorem ofReal_realPermOnReducedDiff_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) :
    (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (fun k μ => (ξ k μ : ℂ)) := by
  ext k μ
  apply Complex.ext
  · simp [realPermOnReducedDiff]
  · exact (permOnReducedDiff_ofReal_im_zero (d := d) m σ ξ k μ).symm

omit [NeZero d] in
/-- Quotienting absolute coordinates to reduced differences commutes with
absolute permutation, when the absolute configuration is written in basepoint
plus reduced-difference coordinates. -/
theorem reducedDiffMapReal_permute_realDiffCoordCLE_symm_prependBasepointReal
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x₀ : SpacetimeDim d) (ξ : NPointDomain d m) :
    BHW.reducedDiffMapReal (m + 1) d
        (fun k =>
          (BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ) (σ k)) =
      realPermOnReducedDiff (d := d) m σ ξ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let y : NPointDomain d (m + 1) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m x₀ ξ)
  let z : Fin (m + 1) → Fin (d + 1) → ℂ :=
    fun k μ => (y k μ : ℂ)
  have hred_real :
      BHW.reducedDiffMapReal (m + 1) d y = ξ := by
    simpa [y] using
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) (m := m) x₀ ξ
  have hred_complex :
      BHW.reducedDiffMap (m + 1) d z =
        fun k μ => (ξ k μ : ℂ) := by
    ext k μ
    have h :
        y ⟨k.val + 1, by omega⟩ μ -
            y ⟨k.val, by omega⟩ μ =
          ξ k μ := by
      have hk := congrFun (congrFun hred_real k) μ
      rw [BHW.reducedDiffMapReal_apply] at hk
      exact hk
    rw [BHW.reducedDiffMap_eq_successive_differences]
    change ((y ⟨k.val + 1, by omega⟩ μ : ℂ) -
        (y ⟨k.val, by omega⟩ μ : ℂ)) = (ξ k μ : ℂ)
    simpa using congrArg (fun r : ℝ => (r : ℂ)) h
  have hperm_complex :
      (fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d
          (fun k => y (σ k)) k μ : ℂ)) =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ) := by
    calc
      (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d
            (fun k => y (σ k)) k μ : ℂ))
          =
        BHW.reducedDiffMap (m + 1) d (fun k μ => z (σ k) μ) := by
          ext k μ
          rw [BHW.reducedDiffMap_eq_successive_differences]
          change
            ((y (σ ⟨k.val + 1, by omega⟩) μ -
                y (σ ⟨k.val, by omega⟩) μ : ℝ) : ℂ) =
              (y (σ ⟨k.val + 1, by omega⟩) μ : ℂ) -
                (y (σ ⟨k.val, by omega⟩) μ : ℂ)
          simp
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d z) := by
          exact (BHW.permOnReducedDiff_reducedDiffMap
            (d := d) (n := m + 1) σ z).symm
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (fun k μ => (ξ k μ : ℂ)) := by
          exact congrArg
            (fun η =>
              BHW.permOnReducedDiff (d := d) (n := m + 1) σ η)
            hred_complex
      _ =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ) := by
          simpa using
            (ofReal_realPermOnReducedDiff_eq (d := d) m σ ξ).symm
  ext k μ
  exact Complex.ofReal_injective
    (congrFun (congrFun hperm_complex k) μ)

omit [NeZero d] in
/-- On the selected adjacent reduced difference, the induced real adjacent
transposition acts by negation. -/
theorem realPermOnReducedDiff_adjacentSwap_selected
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ⟨i.val, by omega⟩ =
      -ξ ⟨i.val, by omega⟩ := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        ⟨i.val, by omega⟩)
      μ
  have hselectedμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_selected
        (d := d) m i hi (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ⟨i.val, by omega⟩ μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) ⟨i.val, by omega⟩ μ := hcomplexμ
    _ = -((ξ ⟨i.val, by omega⟩ μ : ℂ)) := by
        simpa using hselectedμ
    _ = ((-ξ ⟨i.val, by omega⟩ μ : ℝ) : ℂ) := by simp

omit [NeZero d] in
/-- The real induced reduced permutation action is inverted by the inverse
absolute permutation. -/
theorem realPermOnReducedDiff_symm_apply
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m σ.symm
        (realPermOnReducedDiff (d := d) m σ ξ) = ξ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  have hinner :
      (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ ξC := by
    simpa [ξC] using ofReal_realPermOnReducedDiff_eq (d := d) m σ ξ
  ext k μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m σ.symm
        (realPermOnReducedDiff (d := d) m σ ξ) k μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm
        (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) k μ := by
          exact congrFun
            (congrFun
              (ofReal_realPermOnReducedDiff_eq
                (d := d) m σ.symm
                (realPermOnReducedDiff (d := d) m σ ξ))
              k)
            μ
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ξC) k μ := by
          exact congrFun
            (congrFun
              (congrArg
                (fun η =>
                  BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm η)
                hinner)
              k)
            μ
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1) (σ * σ.symm) ξC k μ := by
          exact congrFun
            (congrFun
              ((BHW.permOnReducedDiff_mul (d := d) (n := m + 1)
                σ σ.symm ξC).symm)
              k)
            μ
    _ = (ξ k μ : ℂ) := by
          have hone :
              BHW.permOnReducedDiff (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) ξC = ξC :=
                BHW.permOnReducedDiff_one (d := d) (n := m + 1) ξC
          rw [show σ * σ.symm = 1 by exact mul_inv_cancel σ]
          exact congrFun (congrFun hone k) μ

omit [NeZero d] in
/-- The induced real reduced permutation action is continuous. -/
theorem continuous_realPermOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    Continuous (realPermOnReducedDiff (d := d) m σ) := by
  have hcomplexify :
      Continuous (fun ξ : NPointDomain d m =>
        ((fun k μ => (ξ k μ : ℂ)) : BHW.ReducedNPointConfig d m)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply k))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  change Continuous fun ξ : NPointDomain d m =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
      (fun k μ => (ξ k μ : ℂ)) k μ).re
  exact Complex.continuous_re.comp
    ((continuous_apply μ).comp
      ((continuous_apply k).comp
        ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ).continuous.comp
          hcomplexify)))

omit [NeZero d] in
/-- The induced real reduced permutation action as a homeomorphism. -/
noncomputable def realPermOnReducedDiffHomeomorph
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃ₜ NPointDomain d m where
  toFun := realPermOnReducedDiff (d := d) m σ
  invFun := realPermOnReducedDiff (d := d) m σ.symm
  left_inv := by
    intro ξ
    exact realPermOnReducedDiff_symm_apply (d := d) m σ ξ
  right_inv := by
    intro ξ
    simpa using realPermOnReducedDiff_symm_apply (d := d) m σ.symm ξ
  continuous_toFun := continuous_realPermOnReducedDiff (d := d) m σ
  continuous_invFun := continuous_realPermOnReducedDiff (d := d) m σ.symm

omit [NeZero d] in
/-- The induced real reduced permutation action as a real linear equivalence.

This is the linear/Jacobian package behind the reduced Ruelle change of
variables.  The map is defined through the complex reduced action and then
restricted to real configurations; linearity follows by complexifying the real
test configurations. -/
noncomputable def realPermOnReducedDiffLinearEquiv
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃ₗ[ℝ] NPointDomain d m where
  toFun := realPermOnReducedDiff (d := d) m σ
  invFun := realPermOnReducedDiff (d := d) m σ.symm
  map_add' := by
    intro ξ η
    ext k μ
    simp only [realPermOnReducedDiff, Pi.add_apply]
    simp_rw [Complex.ofReal_add]
    change (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
      ((fun k μ => (ξ k μ : ℂ)) + (fun k μ => (η k μ : ℂ))) k μ).re = _
    rw [(BHW.permOnReducedDiff (d := d) (n := m + 1) σ).map_add]
    simp [Pi.add_apply]
  map_smul' := by
    intro a ξ
    ext k μ
    have h :=
      congrFun
        (congrFun
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ).map_smul
            (a : ℂ) (fun k μ => (ξ k μ : ℂ)))
          k)
        μ
    have harg :
        (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) =
          ((a : ℂ) • fun k μ => (ξ k μ : ℂ)) := by
      ext k μ
      simp [Pi.smul_apply]
    change
      ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) k μ).re =
        a *
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ)) k μ).re
    calc
      ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) k μ).re =
        ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          ((a : ℂ) • fun k μ => (ξ k μ : ℂ)) k μ).re := by
            exact congrArg
              (fun F =>
                ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ) F k μ).re)
              harg
      _ = (((a : ℂ) •
          (BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ))) k μ).re := by
            exact congrArg Complex.re h
      _ =
        a *
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ)) k μ).re := by
            change
              (((a : ℂ) *
                ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
                  (fun k μ => (ξ k μ : ℂ)) k μ)).re) =
                a *
                  ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
                    (fun k μ => (ξ k μ : ℂ)) k μ).re
            simp
  left_inv := by
    intro ξ
    exact realPermOnReducedDiff_symm_apply (d := d) m σ ξ
  right_inv := by
    intro ξ
    simpa using realPermOnReducedDiff_symm_apply (d := d) m σ.symm ξ

omit [NeZero d] in
/-- The induced real reduced permutation action as a continuous linear
equivalence. -/
noncomputable def realPermOnReducedDiffCLE
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃L[ℝ] NPointDomain d m :=
  (realPermOnReducedDiffLinearEquiv (d := d) m σ).toContinuousLinearEquiv

omit [NeZero d] in
/-- The induced real adjacent reduced transposition preserves Lebesgue
measure on reduced coordinates.

This is the Jacobian-one change-of-variables fact needed by the
fiber-marginal Ruelle comparison: the adjacent transposition is an involutive
real linear equivalence, hence its determinant has absolute value `1`. -/
theorem realPermOnReducedDiff_adjacentSwap_measurePreserving
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    MeasurePreserving
      (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩))
      (volume : Measure (NPointDomain d m))
      (volume : Measure (NPointDomain d m)) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let e : NPointDomain d m ≃ₗ[ℝ] NPointDomain d m :=
    realPermOnReducedDiffLinearEquiv (d := d) m τ
  have hcomp : (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m).comp
        (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
      LinearMap.id := by
    apply LinearMap.ext
    intro ξ
    ext k μ
    change realPermOnReducedDiff (d := d) m τ
        (realPermOnReducedDiff (d := d) m τ ξ) k μ = ξ k μ
    have h :=
      realPermOnReducedDiff_symm_apply (d := d) m τ ξ
    simpa [τ] using congrFun (congrFun h k) μ
  have hdet_sq :
      LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) *
          LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
        1 := by
    have h := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_id] at h
    exact h
  have hdet_abs :
      |LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m)| = 1 := by
    have hpow :
        LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) ^ 2 =
          1 := by
      simpa [pow_two] using hdet_sq
    rcases sq_eq_one_iff.mp hpow with hdet | hdet <;> simp [hdet]
  have hsymm_eq :
      (e.symm : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
        (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) := by
    apply LinearMap.ext
    intro ξ
    ext k μ
    change realPermOnReducedDiff (d := d) m τ.symm ξ k μ =
      realPermOnReducedDiff (d := d) m τ ξ k μ
    simp [τ]
  have hdet_abs_symm :
      |LinearMap.det (e.symm : NPointDomain d m →ₗ[ℝ] NPointDomain d m)| = 1 := by
    rw [hsymm_eq]
    exact hdet_abs
  constructor
  · exact ((realPermOnReducedDiffCLE (d := d) m τ).continuous.measurable)
  · change Measure.map (⇑e) (volume : Measure (NPointDomain d m)) =
      (volume : Measure (NPointDomain d m))
    ext s hs
    have hmeas : Measurable (⇑e : NPointDomain d m → NPointDomain d m) :=
      e.toContinuousLinearEquiv.continuous.measurable
    rw [Measure.map_apply hmeas hs]
    change volume (e ⁻¹' s) = volume s
    rw [Measure.addHaar_preimage_linearEquiv
      (volume : Measure (NPointDomain d m)) e s]
    simp [hdet_abs_symm]

end OSReconstruction
