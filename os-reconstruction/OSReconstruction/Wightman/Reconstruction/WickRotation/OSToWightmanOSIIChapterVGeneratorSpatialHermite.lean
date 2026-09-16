/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialFiniteShell
import OSReconstruction.SCV.ComplexSchwartz
import GeneralResults.SchwartzProducts
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

noncomputable def section43SpatialParticleCLE (d k : ℕ) :
    Section43SpatialSpace d k ≃L[ℝ] (Fin k → Fin d → ℝ) :=
  (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := ℝ)).trans
    ((uncurryLinearEquiv k d ℝ).symm.toContinuousLinearEquiv)

@[simp]
theorem section43SpatialParticleCLE_apply
    (d k : ℕ) (η : Section43SpatialSpace d k)
    (i : Fin k) (j : Fin d) :
    section43SpatialParticleCLE d k η i j =
      (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := ℝ) η) (i, j) := rfl

noncomputable def section43SpatialRealSchwartzCLE (d k : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℝ ≃L[ℝ]
      SchwartzMap (Fin k → Fin d → ℝ) ℝ := by
  let e := section43SpatialParticleCLE d k
  let toFwd :
      SchwartzMap (Section43SpatialSpace d k) ℝ →L[ℝ]
        SchwartzMap (Fin k → Fin d → ℝ) ℝ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e.symm
  let toInv :
      SchwartzMap (Fin k → Fin d → ℝ) ℝ →L[ℝ]
        SchwartzMap (Section43SpatialSpace d k) ℝ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext η
            simp [toFwd, toInv, e,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, e,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

noncomputable def section43SpatialRapidDecayCLE
    (d k : ℕ) [NeZero d] (hk : 0 < k) :
    SchwartzMap (Section43SpatialSpace d k) ℝ ≃L[ℝ]
      GaussianField.RapidDecaySeq :=
  (section43SpatialRealSchwartzCLE d k).trans
    (GaussianField.productRapidDecayEquiv k hk)

noncomputable def realSpatialHermite
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℝ :=
  (section43SpatialRapidDecayCLE d k hk).symm
    (GaussianField.RapidDecaySeq.basisVec m)

/-- The one-particle real Hermite factors of the `m`-th spatial basis vector. -/
noncomputable def realSpatialHermiteFactor
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) (i : Fin k) :
    SchwartzMap (Fin d → ℝ) ℝ :=
  GaussianField.DyninMityaginSpace.basis
    (E := SchwartzMap (Fin d → ℝ) ℝ)
    (GaussianField.productBasisIndices
      (D := Fin d → ℝ) k hk m i)

/-- Spatial Hermite basis vectors factor over the particle labels. -/
theorem realSpatialHermite_apply
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ)
    (η : Section43SpatialSpace d k) :
    realSpatialHermite d k hk m η =
      ∏ i, realSpatialHermiteFactor d k hk m i
        (section43SpatialParticleCLE d k η i) := by
  change
    ((GaussianField.productRapidDecayEquiv
      (D := Fin d → ℝ) k hk).symm
      (GaussianField.RapidDecaySeq.basisVec m)).toFun
        (section43SpatialParticleCLE d k η) =
      ∏ i, GaussianField.DyninMityaginSpace.basis
        (E := SchwartzMap (Fin d → ℝ) ℝ)
        (GaussianField.productBasisIndices
          (D := Fin d → ℝ) k hk m i)
        (section43SpatialParticleCLE d k η i)
  exact
    GaussianField.productRapidDecayEquiv_symm_basisVec_isProductHermite
      k hk m (section43SpatialParticleCLE d k η)

noncomputable def realSpatialHermiteCoefficientCLM
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℝ →L[ℝ] ℝ :=
  (GaussianField.RapidDecaySeq.coeffCLM m).comp
    (section43SpatialRapidDecayCLE d k hk).toContinuousLinearMap

@[simp]
theorem realSpatialHermiteCoefficientCLM_apply
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ)
    (f : SchwartzMap (Section43SpatialSpace d k) ℝ) :
    realSpatialHermiteCoefficientCLM d k hk m f =
      (section43SpatialRapidDecayCLE d k hk f).val m := rfl

noncomputable def complexSpatialHermiteCoefficientLM
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →ₗ[ℂ] ℂ where
  toFun f :=
    realSpatialHermiteCoefficientCLM d k hk m (SCV.schwartzRealPartCLM f) +
      Complex.I *
        realSpatialHermiteCoefficientCLM d k hk m
          (SCV.schwartzImagPartCLM f)
  map_add' f g := by
    let L := realSpatialHermiteCoefficientCLM d k hk m
    have hre :
        SCV.schwartzRealPartCLM (f + g) =
          SCV.schwartzRealPartCLM f + SCV.schwartzRealPartCLM g :=
      SCV.schwartzRealPartCLM.map_add f g
    have him :
        SCV.schwartzImagPartCLM (f + g) =
          SCV.schwartzImagPartCLM f + SCV.schwartzImagPartCLM g :=
      SCV.schwartzImagPartCLM.map_add f g
    change
      L (SCV.schwartzRealPartCLM (f + g)) +
          I * L (SCV.schwartzImagPartCLM (f + g)) =
        (L (SCV.schwartzRealPartCLM f) +
            I * L (SCV.schwartzImagPartCLM f)) +
          (L (SCV.schwartzRealPartCLM g) +
            I * L (SCV.schwartzImagPartCLM g))
    rw [hre, him, L.map_add, L.map_add]
    push_cast
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply]
    change
      realSpatialHermiteCoefficientCLM d k hk m
          (SCV.schwartzRealPartCLM (c • f)) +
          I * realSpatialHermiteCoefficientCLM d k hk m
            (SCV.schwartzImagPartCLM (c • f)) =
        c *
          (realSpatialHermiteCoefficientCLM d k hk m
              (SCV.schwartzRealPartCLM f) +
            I * realSpatialHermiteCoefficientCLM d k hk m
              (SCV.schwartzImagPartCLM f))
    have hre :
        SCV.schwartzRealPartCLM (c • f) =
          c.re • SCV.schwartzRealPartCLM f -
            c.im • SCV.schwartzImagPartCLM f := by
      ext x
      change (c * f x).re = c.re * (f x).re - c.im * (f x).im
      exact Complex.mul_re c (f x)
    have him :
        SCV.schwartzImagPartCLM (c • f) =
          c.re • SCV.schwartzImagPartCLM f +
            c.im • SCV.schwartzRealPartCLM f := by
      ext x
      change (c * f x).im = c.re * (f x).im + c.im * (f x).re
      exact Complex.mul_im c (f x)
    rw [hre, him]
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im]

noncomputable def complexSpatialHermiteCoefficientCLM
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.mk
    (complexSpatialHermiteCoefficientLM d k hk m)
    (by
      let L := realSpatialHermiteCoefficientCLM d k hk m
      have hRe :
          Continuous fun f : SchwartzMap (Section43SpatialSpace d k) ℂ =>
            (L (SCV.schwartzRealPartCLM f) : ℂ) :=
        Complex.ofRealCLM.continuous.comp
          (L.continuous.comp SCV.schwartzRealPartCLM.continuous)
      have hIm :
          Continuous fun f : SchwartzMap (Section43SpatialSpace d k) ℂ =>
            (L (SCV.schwartzImagPartCLM f) : ℂ) :=
        Complex.ofRealCLM.continuous.comp
          (L.continuous.comp SCV.schwartzImagPartCLM.continuous)
      exact hRe.add (continuous_const.mul hIm))

@[simp]
theorem complexSpatialHermiteCoefficientCLM_apply
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ)
    (f : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    complexSpatialHermiteCoefficientCLM d k hk m f =
      realSpatialHermiteCoefficientCLM d k hk m
          (SCV.schwartzRealPartCLM f) +
        Complex.I *
          realSpatialHermiteCoefficientCLM d k hk m
            (SCV.schwartzImagPartCLM f) := rfl

noncomputable def spatialHermite
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ :=
  SCV.schwartzOfRealCLM (realSpatialHermite d k hk m)

/-- The complexified one-particle factors of a spatial Hermite basis vector. -/
noncomputable def spatialHermiteFactor
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ) (i : Fin k) :
    SchwartzMap (Fin d → ℝ) ℂ :=
  SCV.schwartzOfRealCLM (realSpatialHermiteFactor d k hk m i)

/-- Complex spatial Hermite basis vectors remain literal particlewise
products. -/
theorem spatialHermite_apply
    (d k : ℕ) [NeZero d] (hk : 0 < k) (m : ℕ)
    (η : Section43SpatialSpace d k) :
    spatialHermite d k hk m η =
      ∏ i, spatialHermiteFactor d k hk m i
        (section43SpatialParticleCLE d k η i) := by
  simp only [spatialHermite, SCV.schwartzOfRealCLM_apply,
    realSpatialHermite_apply, spatialHermiteFactor]
  push_cast
  rfl

theorem hasSum_complexSpatialHermite
    (d k : ℕ) [NeZero d] (hk : 0 < k)
    (f : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    HasSum
      (fun m =>
        complexSpatialHermiteCoefficientCLM d k hk m f •
          spatialHermite d k hk m)
      f := by
  let e := section43SpatialRapidDecayCLE d k hk
  let fRe := SCV.schwartzRealPartCLM f
  let fIm := SCV.schwartzImagPartCLM f
  have hRe0 :=
    (GaussianField.RapidDecaySeq.hasSum_basisVec (e fRe)).mapL
      e.symm.toContinuousLinearMap
  have hIm0 :=
    (GaussianField.RapidDecaySeq.hasSum_basisVec (e fIm)).mapL
      e.symm.toContinuousLinearMap
  have hRe :
      HasSum
        (fun m =>
          (realSpatialHermiteCoefficientCLM d k hk m fRe : ℂ) •
            spatialHermite d k hk m)
        (SCV.schwartzOfRealCLM fRe) := by
    have h := hRe0.mapL SCV.schwartzOfRealCLM
    convert h using 1 <;>
      simp [e, fRe, spatialHermite, realSpatialHermite,
        realSpatialHermiteCoefficientCLM_apply]
  have hIm :
      HasSum
        (fun m =>
          (Complex.I *
              realSpatialHermiteCoefficientCLM d k hk m fIm) •
            spatialHermite d k hk m)
        (Complex.I • SCV.schwartzOfRealCLM fIm) := by
    have h := (hIm0.mapL SCV.schwartzOfRealCLM).const_smul Complex.I
    convert h using 1 <;>
      simp [e, fIm, spatialHermite, realSpatialHermite,
        realSpatialHermiteCoefficientCLM_apply, mul_smul]
  have h := hRe.add hIm
  convert h using 1
  · funext m
    rw [← add_smul]
    rfl
  · exact (SCV.complexSchwartzDecomposeCLE.symm_apply_apply f).symm

/-- The canonical finite spatial Hermite projector. -/
noncomputable def spatialHermitePartialSum
    (d k : ℕ) [NeZero d] (hk : 0 < k) (N : ℕ)
    (f : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ :=
  ∑ m ∈ Finset.range N,
    complexSpatialHermiteCoefficientCLM d k hk m f •
      spatialHermite d k hk m

/-- Canonical finite Hermite projectors converge in the spatial Schwartz
topology. -/
theorem tendsto_spatialHermitePartialSum
    (d k : ℕ) [NeZero d] (hk : 0 < k)
    (f : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto
      (fun N => spatialHermitePartialSum d k hk N f)
      atTop (𝓝 f) := by
  exact (hasSum_complexSpatialHermite d k hk f).tendsto_sum_nat

/-- Hermite coefficients of every complex spatial Schwartz test decay fast
enough to be summable against an arbitrary polynomial weight. -/
theorem summable_norm_coefficient_mul_weight
    {d n : ℕ} [NeZero d] {hn : 0 < n}
    (p : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    Summable fun m =>
      ‖complexSpatialHermiteCoefficientCLM d n hn m χ‖ *
        (1 + (m : ℝ)) ^ p := by
  let e := section43SpatialRapidDecayCLE d n hn
  let a := e (SCV.schwartzRealPartCLM χ)
  let b := e (SCV.schwartzImagPartCLM χ)
  have ha :
      Summable fun m => |a.val m| * (1 + (m : ℝ)) ^ p :=
    a.rapid_decay p
  have hb :
      Summable fun m => |b.val m| * (1 + (m : ℝ)) ^ p :=
    b.rapid_decay p
  have hab :
      Summable fun m =>
        (|a.val m| + |b.val m|) * (1 + (m : ℝ)) ^ p := by
    exact (ha.add hb).congr fun m => by ring
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _)
      (pow_nonneg (by positivity) p))
    (fun m => by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) p)
      rw [complexSpatialHermiteCoefficientCLM_apply]
      change ‖(a.val m : ℂ) + Complex.I * (b.val m : ℂ)‖ ≤
        |a.val m| + |b.val m|
      calc
        ‖(a.val m : ℂ) + Complex.I * (b.val m : ℂ)‖
            ≤ ‖(a.val m : ℂ)‖ + ‖Complex.I * (b.val m : ℂ)‖ :=
          norm_add_le _ _
        _ = |a.val m| + |b.val m| := by
          rw [norm_mul, Complex.norm_I, one_mul]
          simp)
    hab



/-- Scalar Chapter V generator modes indexed by the product Hermite basis on
the `k + 1` absolute spatial points. The continuous `lift` inserts the
basepoint variable into a reduced `k`-difference spatial test before its
Hermite coefficients are extracted.

This is the split-compatible coordinate system: every absolute Hermite basis
vector factors pointwise, and an admissible generator split partitions those
factors into its left `n` and right `m` source blocks. -/
structure GeneratorAbsoluteSpatialHermiteModeData
    (d k : ℕ) [NeZero d] where
  lift :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ
  domain : GeneratorIndex k → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  mode : GeneratorIndex k → ℕ → OSIITimeGapSpace k → ℂ
  mode_holomorphic :
    ∀ i m, DifferentiableOn ℂ (mode i m) (domain i)

namespace GeneratorAbsoluteSpatialHermiteModeData

variable {d k : ℕ} [NeZero d]

/-- Extract the `m`-th absolute-point Hermite coefficient after applying the
declared reduced-to-absolute spatial lift. -/
noncomputable def coefficient
    (B : GeneratorAbsoluteSpatialHermiteModeData d k)
    (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ] ℂ :=
  (complexSpatialHermiteCoefficientCLM
    d (k + 1) (Nat.succ_pos k) m).comp B.lift

/-- Turn split-compatible absolute-point Hermite modes into finite
reduced-spatial distribution shells. -/
noncomputable def toFiniteShellData
    (B : GeneratorAbsoluteSpatialHermiteModeData d k) :
    GeneratorSpatialFiniteShellData d k where
  domain := B.domain
  domain_open := B.domain_open
  coefficient := B.coefficient
  mode := B.mode
  mode_holomorphic := B.mode_holomorphic

/-- The exact sourcewise growth estimate needed for the absolute Hermite shell
tails: locally in each generator domain, all scalar modes obey one polynomial
bound in the basis index. -/
def LocallyPolynomiallyBounded
    (B : GeneratorAbsoluteSpatialHermiteModeData d k) : Prop :=
  ∀ i z, z ∈ B.domain i →
    ∃ V ∈ 𝓝[B.domain i] z, ∃ C ≥ 0, ∃ p : ℕ,
      ∀ w ∈ V, ∀ m,
        ‖B.mode i m w‖ ≤ C * (1 + (m : ℝ)) ^ p

/-- A local polynomial bound on the split-compatible product-Hermite modes
implies the full locally uniform Cauchy contract for arbitrary reduced
spatial Schwartz tests. -/
theorem toFiniteShellData_locallyUniformCauchy
    (B : GeneratorAbsoluteSpatialHermiteModeData d k)
    (hB : B.LocallyPolynomiallyBounded) :
    B.toFiniteShellData.LocallyUniformCauchy := by
  intro i χ z hz
  obtain ⟨V, hV, C, hC, p, hbound⟩ := hB i z hz
  refine ⟨V, hV, ?_⟩
  let coefficient : ℕ → ℂ :=
    fun m => B.coefficient m χ
  have hcoeff :
      Summable fun m =>
        ‖coefficient m‖ * (1 + (m : ℝ)) ^ p := by
    exact
      summable_norm_coefficient_mul_weight p (B.lift χ)
  have hmajor :
      Summable fun m =>
        C * (‖coefficient m‖ * (1 + (m : ℝ)) ^ p) :=
    hcoeff.mul_left C
  have huniform :=
    tendstoUniformlyOn_tsum_nat hmajor
      (s := V)
      (f := fun m w => B.mode i m w * coefficient m)
      (fun m w hw => by
        rw [norm_mul]
        calc
          ‖B.mode i m w‖ * ‖coefficient m‖
              ≤ (C * (1 + (m : ℝ)) ^ p) * ‖coefficient m‖ := by
                exact mul_le_mul_of_nonneg_right
                  (hbound w hw m) (norm_nonneg _)
          _ = C * (‖coefficient m‖ * (1 + (m : ℝ)) ^ p) := by
                ring)
  have hcauchy := huniform.uniformCauchySeqOn
  simpa [GeneratorSpatialFiniteShellData.finiteShell_apply,
    toFiniteShellData, coefficient,
    GeneratorAbsoluteSpatialHermiteModeData.coefficient] using hcauchy

end GeneratorAbsoluteSpatialHermiteModeData

end OSIIChapterV
end OSReconstruction
