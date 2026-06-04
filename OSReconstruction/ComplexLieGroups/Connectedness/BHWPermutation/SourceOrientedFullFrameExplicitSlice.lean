import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameOrbit
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Explicit full-frame gauge slice

This file packages the constructive right inverse used in the full-frame
oriented differential surjectivity proof as a named linear map.  Its range is a
concrete complement to the infinitesimal special-Lorentz orbit tangent, giving
an explicit gauge-slice packet for the real-compatible chart route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The explicit right inverse to the full-frame oriented differential on the
oriented hypersurface tangent space. -/
noncomputable def sourceFullFrameOrientedDifferentialRightInverseLinear
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (_hM0 : IsUnit M0.det) :
    sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) →ₗ[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ where
  toFun := fun Y =>
    let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
        ComplexLorentzGroup.ηℂ (d := d))
    M0 * B
  map_add' := by
    intro Y Z
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Z : SourceFullFrameOrientedCoord d).1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (M0.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      ComplexLorentzGroup.ηℂ (d := d)
    have hOf :
        Matrix.of
            ((Y : SourceFullFrameOrientedCoord d).1 +
              (Z : SourceFullFrameOrientedCoord d).1) = A + B := by
      exact
        (Matrix.of_add_of
          (Y : SourceFullFrameOrientedCoord d).1
          (Z : SourceFullFrameOrientedCoord d).1).symm
    have hlin :
        M0⁻¹ * (A + B) * C * E =
          M0⁻¹ * A * C * E + M0⁻¹ * B * C * E := by
      noncomm_ring
    change
      M0 * ((2 : ℂ)⁻¹ •
        (M0⁻¹ *
          Matrix.of
            ((Y + Z :
              sourceFullFrameOrientedTangentSpace d
                (sourceFullFrameOrientedGram d M0)) :
                SourceFullFrameOrientedCoord d).1 *
          (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) =
        M0 * ((2 : ℂ)⁻¹ •
          (M0⁻¹ * Matrix.of (Y : SourceFullFrameOrientedCoord d).1 *
            (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) +
        M0 * ((2 : ℂ)⁻¹ •
          (M0⁻¹ * Matrix.of (Z : SourceFullFrameOrientedCoord d).1 *
            (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d)))
    simp only [Submodule.coe_add, Prod.fst_add]
    dsimp [A, B, C, E] at hOf hlin
    rw [hOf, hlin, smul_add, Matrix.mul_add]
  map_smul' := by
    intro c Y
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (M0.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      ComplexLorentzGroup.ηℂ (d := d)
    have hOf :
        Matrix.of (c • (Y : SourceFullFrameOrientedCoord d).1) =
          c • A := by
      exact (Matrix.smul_of c (Y : SourceFullFrameOrientedCoord d).1).symm
    have hlin :
        M0⁻¹ * (c • A) * C * E =
          c • (M0⁻¹ * A * C * E) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    change
      M0 * ((2 : ℂ)⁻¹ •
        (M0⁻¹ *
          Matrix.of
            ((c • Y :
              sourceFullFrameOrientedTangentSpace d
                (sourceFullFrameOrientedGram d M0)) :
                SourceFullFrameOrientedCoord d).1 *
          (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) =
        c •
          (M0 * ((2 : ℂ)⁻¹ •
            (M0⁻¹ * Matrix.of (Y : SourceFullFrameOrientedCoord d).1 *
              (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))))
    simp only [Submodule.coe_smul, Prod.smul_fst]
    dsimp [A, C, E] at hOf hlin
    rw [hOf, hlin]
    rw [smul_smul, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    rw [mul_comm c]

@[simp]
theorem sourceFullFrameOrientedDifferentialRightInverseLinear_apply
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (Y : sourceFullFrameOrientedTangentSpace d
      (sourceFullFrameOrientedGram d M0)) :
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0 Y =
      let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        Matrix.of (Y : SourceFullFrameOrientedCoord d).1
      let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
          ComplexLorentzGroup.ηℂ (d := d))
      M0 * B :=
  rfl

/-- The constructed linear map is a right inverse to the full-frame oriented
differential. -/
theorem sourceFullFrameOrientedDifferential_rightInverse
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (Y : sourceFullFrameOrientedTangentSpace d
      (sourceFullFrameOrientedGram d M0)) :
    sourceFullFrameOrientedDifferential d M0
        (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0 Y) =
      (Y : SourceFullFrameOrientedCoord d) := by
  let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.of (Y : SourceFullFrameOrientedCoord d).1
  let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
      ComplexLorentzGroup.ηℂ (d := d))
  change sourceFullFrameOrientedDifferential d M0 (M0 * B) =
    (Y : SourceFullFrameOrientedCoord d)
  have hgram :
      Matrix.of
          (sourceFullFrameOrientedDifferential d M0 (M0 * B)).1 = G :=
    sourceFullFrameOrientedDifferential_constructedGram
      (d := d) hM0 (Y := (Y : SourceFullFrameOrientedCoord d)) Y.property.1
  have hdet :
      (sourceFullFrameOrientedDifferential d M0 (M0 * B)).2 =
        (Y : SourceFullFrameOrientedCoord d).2 :=
    sourceFullFrameOrientedDifferential_constructedDet
      (d := d) hM0 (Y := (Y : SourceFullFrameOrientedCoord d)) Y.property hgram
  apply Prod.ext
  · ext a b
    exact
      congrArg
        (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M a b) hgram
  · exact hdet

/-- The explicit gauge slice is the range of the constructive differential
right inverse. -/
noncomputable def sourceFullFrameOrientedDifferentialRightInverseRange
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  LinearMap.range (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0)

/-- The explicit right-inverse range is complementary to the full-frame
special-Lorentz orbit tangent. -/
theorem sourceFullFrameOrientedDifferentialRightInverseRange_isCompl
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    IsCompl
      (sourceFullFrameOrientedDifferentialRightInverseRange d hM0)
      (sourceFullFrameOrbitTangent d M0) := by
  let T := sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  let R : T →ₗ[ℂ] Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0
  let S : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    LinearMap.range R
  let K : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    sourceFullFrameOrbitTangent d M0
  have hker :
      LinearMap.ker (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap =
        K := by
    dsimp [K]
    exact sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent
      (d := d) hM0
  have hdisjoint : Disjoint S K := by
    rw [Submodule.disjoint_def]
    intro X hXS hXK
    rcases hXS with ⟨Y, rfl⟩
    have hkerX :
        R Y ∈
          LinearMap.ker
            (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap := by
      rw [hker]
      exact hXK
    have hzeroDiff : sourceFullFrameOrientedDifferential d M0 (R Y) = 0 := by
      simpa [sourceFullFrameOrientedDifferentialCLM,
        sourceFullFrameOrientedDifferentialLinear] using
        (LinearMap.mem_ker.mp hkerX)
    have hYzero : (Y : SourceFullFrameOrientedCoord d) = 0 := by
      have hright :=
        sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
      rw [hright] at hzeroDiff
      exact hzeroDiff
    have hY0 : Y = 0 := Subtype.ext hYzero
    simp [hY0, R]
  have hcodisjoint : Codisjoint S K := by
    rw [codisjoint_iff_le_sup]
    intro X _hX
    let L :=
      (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap
    let Y : T :=
      ⟨L X, by
        change sourceFullFrameOrientedDifferential d M0 X ∈
          sourceFullFrameOrientedTangentSpace d
            (sourceFullFrameOrientedGram d M0)
        exact
          (sourceFullFrameOrientedDifferential_range_subset_tangent
            (d := d) hM0) ⟨X, rfl⟩⟩
    have hSY : R Y ∈ S := ⟨Y, rfl⟩
    have hKY : X - R Y ∈ K := by
      rw [← hker, LinearMap.mem_ker]
      have hRY : L (R Y) = L X := by
        have hright :=
          sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
        change sourceFullFrameOrientedDifferential d M0 (R Y) =
          sourceFullFrameOrientedDifferential d M0 X
        rw [hright]
        rfl
      calc
        L (X - R Y) = L X - L (R Y) := by simp
        _ = 0 := by rw [hRY, sub_self]
    exact Submodule.mem_sup.mpr ⟨R Y, hSY, X - R Y, hKY, by abel⟩
  change IsCompl S K
  exact IsCompl.mk hdisjoint hcodisjoint

/-- A full-frame gauge-slice packet using the explicit right-inverse range,
instead of an arbitrary complement. -/
noncomputable def sourceFullFrameExplicitGaugeSliceData
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    SourceFullFrameGaugeSliceData d M0 := by
  let T := sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  let R : T →ₗ[ℂ] Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0
  let S : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    LinearMap.range R
  let K : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    sourceFullFrameOrbitTangent d M0
  let L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →ₗ[ℂ]
      SourceFullFrameOrientedCoord d :=
    (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap
  have hCompl : IsCompl S K := by
    exact sourceFullFrameOrientedDifferentialRightInverseRange_isCompl
      (d := d) hM0
  have hker : LinearMap.ker L = K := by
    dsimp [L, K]
    exact sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent
      (d := d) hM0
  let LS : S →ₗ[ℂ] T :=
    { toFun := fun X =>
        ⟨L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), by
          change sourceFullFrameOrientedDifferential d M0
              (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
            sourceFullFrameOrientedTangentSpace d
              (sourceFullFrameOrientedGram d M0)
          exact
            (sourceFullFrameOrientedDifferential_range_subset_tangent
              (d := d) hM0)
              ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        simp [L]
      map_smul' := by
        intro c X
        apply Subtype.ext
        simp [L] }
  have hLS_inj : Function.Injective LS := by
    intro X Y hXY
    apply Subtype.ext
    have hval :
        L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
          L (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
      exact congrArg Subtype.val hXY
    have hdiffK :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ K := by
      rw [← hker, LinearMap.mem_ker]
      rw [map_sub, hval, sub_self]
    have hdiffS :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ S :=
      S.sub_mem X.property Y.property
    have hzero :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 0 :=
      submodule_mem_isCompl_inter_eq_zero hCompl hdiffS hdiffK
    exact sub_eq_zero.mp hzero
  have hLS_surj : Function.Surjective LS := by
    intro Y
    refine ⟨⟨R Y, ⟨Y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change L (R Y) = (Y : SourceFullFrameOrientedCoord d)
    have hright := sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
    change sourceFullFrameOrientedDifferential d M0 (R Y) =
      (Y : SourceFullFrameOrientedCoord d) at hright
    exact hright
  let e : S ≃ₗ[ℂ] T := LinearEquiv.ofBijective LS ⟨hLS_inj, hLS_surj⟩
  refine
    { slice := S
      isCompl := hCompl
      differential_iso := e
      differential_iso_eq := ?_ }
  intro X
  rfl

/-- Real product-coordinate model for full-frame oriented tangent data. -/
abbrev SourceFullFrameRealOrientedCoord (d : ℕ) :=
  (Fin (d + 1) → Fin (d + 1) → ℝ) × ℝ

/-- Componentwise complexification of real full-frame oriented coordinates. -/
def sourceFullFrameRealOrientedCoordComplexify
    (d : ℕ) (Y : SourceFullFrameRealOrientedCoord d) :
    SourceFullFrameOrientedCoord d :=
  (fun a b => (Y.1 a b : ℂ), (Y.2 : ℂ))

/-- Componentwise complexification as a real-linear map. -/
def sourceFullFrameRealOrientedCoordComplexifyLinear
    (d : ℕ) :
    SourceFullFrameRealOrientedCoord d →ₗ[ℝ]
      SourceFullFrameOrientedCoord d where
  toFun := sourceFullFrameRealOrientedCoordComplexify d
  map_add' := by
    intro Y Z
    apply Prod.ext
    · funext a b
      simp [sourceFullFrameRealOrientedCoordComplexify]
    · simp [sourceFullFrameRealOrientedCoordComplexify]
  map_smul' := by
    intro c Y
    apply Prod.ext
    · funext a b
      dsimp [sourceFullFrameRealOrientedCoordComplexify]
      change ((c * Y.1 a b : ℝ) : ℂ) =
        (c : ℂ) * (Y.1 a b : ℂ)
      rw [Complex.ofReal_mul]
    · dsimp [sourceFullFrameRealOrientedCoordComplexify]
      change ((c * Y.2 : ℝ) : ℂ) = (c : ℂ) * (Y.2 : ℂ)
      rw [Complex.ofReal_mul]

@[simp]
theorem sourceFullFrameRealOrientedCoordComplexifyLinear_apply
    (d : ℕ) (Y : SourceFullFrameRealOrientedCoord d) :
    sourceFullFrameRealOrientedCoordComplexifyLinear d Y =
      sourceFullFrameRealOrientedCoordComplexify d Y :=
  rfl

/-- Componentwise complexification of real full-frame oriented coordinates is
injective. -/
theorem sourceFullFrameRealOrientedCoordComplexify_injective
    (d : ℕ) :
    Function.Injective (sourceFullFrameRealOrientedCoordComplexify d) := by
  intro Y Z hYZ
  apply Prod.ext
  · funext a b
    exact
      Complex.ofReal_injective
        (congrFun (congrFun (congrArg Prod.fst hYZ) a) b)
  · exact Complex.ofReal_injective (congrArg Prod.snd hYZ)

/-- Entrywise real part of a complex full-frame oriented coordinate. -/
def sourceFullFrameOrientedCoordRe
    (d : ℕ) (Y : SourceFullFrameOrientedCoord d) :
    SourceFullFrameRealOrientedCoord d :=
  (fun a b => (Y.1 a b).re, Y.2.re)

/-- Entrywise imaginary part of a complex full-frame oriented coordinate. -/
def sourceFullFrameOrientedCoordIm
    (d : ℕ) (Y : SourceFullFrameOrientedCoord d) :
    SourceFullFrameRealOrientedCoord d :=
  (fun a b => (Y.1 a b).im, Y.2.im)

/-- A complex full-frame oriented coordinate decomposes into its real and
imaginary real-coordinate parts. -/
theorem sourceFullFrameOrientedCoord_re_im_decomp
    (d : ℕ) (Y : SourceFullFrameOrientedCoord d) :
    Y =
      sourceFullFrameRealOrientedCoordComplexify d
        (sourceFullFrameOrientedCoordRe d Y) +
        Complex.I •
          sourceFullFrameRealOrientedCoordComplexify d
            (sourceFullFrameOrientedCoordIm d Y) := by
  apply Prod.ext
  · funext a b
    change Y.1 a b = (Y.1 a b).re + Complex.I * (Y.1 a b).im
    rw [mul_comm]
    exact (Complex.re_add_im (Y.1 a b)).symm
  · change Y.2 = Y.2.re + Complex.I * Y.2.im
    rw [mul_comm]
    exact (Complex.re_add_im Y.2).symm

@[simp]
theorem sourceFullFrameOrientedCoordRe_complexify
    (d : ℕ) (Y : SourceFullFrameRealOrientedCoord d) :
    sourceFullFrameOrientedCoordRe d
        (sourceFullFrameRealOrientedCoordComplexify d Y) = Y := by
  apply Prod.ext
  · funext a b
    simp [sourceFullFrameOrientedCoordRe,
      sourceFullFrameRealOrientedCoordComplexify]
  · simp [sourceFullFrameOrientedCoordRe,
      sourceFullFrameRealOrientedCoordComplexify]

@[simp]
theorem sourceFullFrameOrientedCoordIm_complexify
    (d : ℕ) (Y : SourceFullFrameRealOrientedCoord d) :
    sourceFullFrameOrientedCoordIm d
        (sourceFullFrameRealOrientedCoordComplexify d Y) = 0 := by
  apply Prod.ext
  · funext a b
    simp [sourceFullFrameOrientedCoordIm,
      sourceFullFrameRealOrientedCoordComplexify]
  · simp [sourceFullFrameOrientedCoordIm,
      sourceFullFrameRealOrientedCoordComplexify]

/-- Real and imaginary real oriented coordinates cannot cancel in
`Y + I Z = 0` after componentwise complexification. -/
theorem sourceFullFrameRealOrientedCoordComplexify_add_I_smul_eq_zero
    {d : ℕ}
    {Y Z : SourceFullFrameRealOrientedCoord d}
    (h :
      sourceFullFrameRealOrientedCoordComplexify d Y +
          Complex.I • sourceFullFrameRealOrientedCoordComplexify d Z =
        (0 : SourceFullFrameOrientedCoord d)) :
    Y = 0 ∧ Z = 0 := by
  constructor
  · apply Prod.ext
    · funext a b
      have hentry := congrFun (congrFun (congrArg Prod.fst h) a) b
      have hre := congrArg Complex.re hentry
      simp [sourceFullFrameRealOrientedCoordComplexify, smul_eq_mul] at hre
      exact hre
    · have hentry := congrArg Prod.snd h
      have hre := congrArg Complex.re hentry
      simp [sourceFullFrameRealOrientedCoordComplexify, smul_eq_mul] at hre
      exact hre
  · apply Prod.ext
    · funext a b
      have hentry := congrFun (congrFun (congrArg Prod.fst h) a) b
      have him := congrArg Complex.im hentry
      simp [sourceFullFrameRealOrientedCoordComplexify, smul_eq_mul] at him
      exact him
    · have hentry := congrArg Prod.snd h
      have him := congrArg Complex.im hentry
      simp [sourceFullFrameRealOrientedCoordComplexify, smul_eq_mul] at him
      exact him

/-- If `a` and `b` are real-valued complex scalars, then `a + I b = 0`
forces both to vanish. -/
theorem complex_add_I_mul_eq_zero_of_im_eq_zero
    {a b : ℂ}
    (ha : a.im = 0)
    (hb : b.im = 0)
    (h : a + Complex.I * b = 0) :
    a = 0 ∧ b = 0 := by
  constructor
  · apply Complex.ext
    · have hre := congrArg Complex.re h
      simp [hb, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
      exact hre
    · simpa using ha
  · apply Complex.ext
    · have him := congrArg Complex.im h
      simp [ha, hb, Complex.mul_im, Complex.I_re, Complex.I_im] at him
      exact him
    · simpa using hb

/-- The real tangent model for the full-frame oriented hypersurface at a real
base frame, defined as the real form whose componentwise complexification lies
in the checked complex tangent space. -/
def sourceFullFrameRealOrientedTangentSpace
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Submodule ℝ (SourceFullFrameRealOrientedCoord d) where
  carrier :=
    {Y |
      sourceFullFrameRealOrientedCoordComplexify d Y ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))}
  zero_mem' := by
    change
      sourceFullFrameRealOrientedCoordComplexify d 0 ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    change
      (0 : SourceFullFrameOrientedCoord d) ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    exact
      Submodule.zero_mem
        (sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)))
  add_mem' := by
    intro Y Z hY hZ
    have hadd :
        sourceFullFrameRealOrientedCoordComplexify d (Y + Z) =
          sourceFullFrameRealOrientedCoordComplexify d Y +
            sourceFullFrameRealOrientedCoordComplexify d Z := by
      apply Prod.ext
      · funext a b
        simp [sourceFullFrameRealOrientedCoordComplexify]
      · simp [sourceFullFrameRealOrientedCoordComplexify]
    change
      sourceFullFrameRealOrientedCoordComplexify d (Y + Z) ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    rw [hadd]
    exact
      (sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))).add_mem hY hZ
  smul_mem' := by
    intro c Y hY
    have hsmul :
        sourceFullFrameRealOrientedCoordComplexify d (c • Y) =
          (c : ℂ) • sourceFullFrameRealOrientedCoordComplexify d Y := by
      apply Prod.ext
      · funext a b
        dsimp [sourceFullFrameRealOrientedCoordComplexify]
        change ((c * Y.1 a b : ℝ) : ℂ) =
          (c : ℂ) * (Y.1 a b : ℂ)
        rw [Complex.ofReal_mul]
      · dsimp [sourceFullFrameRealOrientedCoordComplexify]
        change ((c * Y.2 : ℝ) : ℂ) = (c : ℂ) * (Y.2 : ℂ)
        rw [Complex.ofReal_mul]
    change
      sourceFullFrameRealOrientedCoordComplexify d (c • Y) ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    rw [hsmul]
    exact
      (sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))).smul_mem
          (c : ℂ) hY

theorem mem_sourceFullFrameRealOrientedTangentSpace
    {d : ℕ}
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {Y : SourceFullFrameRealOrientedCoord d} :
    Y ∈ sourceFullFrameRealOrientedTangentSpace d M0R ↔
      sourceFullFrameRealOrientedCoordComplexify d Y ∈
      sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) :=
  Iff.rfl

/-- Componentwise complexification sends the real tangent model into the
complex full-frame tangent space. -/
def sourceFullFrameRealOrientedTangentComplexifyLinear
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameRealOrientedTangentSpace d M0R →ₗ[ℝ]
      sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) where
  toFun := fun Y =>
    ⟨sourceFullFrameRealOrientedCoordComplexify d
      (Y : SourceFullFrameRealOrientedCoord d), Y.property⟩
  map_add' := by
    intro Y Z
    apply Subtype.ext
    change
      sourceFullFrameRealOrientedCoordComplexify d
          ((Y : SourceFullFrameRealOrientedCoord d) +
            (Z : SourceFullFrameRealOrientedCoord d)) =
        sourceFullFrameRealOrientedCoordComplexify d
            (Y : SourceFullFrameRealOrientedCoord d) +
          sourceFullFrameRealOrientedCoordComplexify d
            (Z : SourceFullFrameRealOrientedCoord d)
    simpa using
      (sourceFullFrameRealOrientedCoordComplexifyLinear d).map_add
        (Y : SourceFullFrameRealOrientedCoord d)
        (Z : SourceFullFrameRealOrientedCoord d)
  map_smul' := by
    intro c Y
    apply Subtype.ext
    change
      sourceFullFrameRealOrientedCoordComplexify d
          (c • (Y : SourceFullFrameRealOrientedCoord d)) =
        (c : ℂ) •
          sourceFullFrameRealOrientedCoordComplexify d
            (Y : SourceFullFrameRealOrientedCoord d)
    exact
      (sourceFullFrameRealOrientedCoordComplexifyLinear d).map_smul
        c (Y : SourceFullFrameRealOrientedCoord d)

@[simp]
theorem sourceFullFrameRealOrientedTangentComplexifyLinear_apply
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Y : sourceFullFrameRealOrientedTangentSpace d M0R) :
    sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Y =
      ⟨sourceFullFrameRealOrientedCoordComplexify d
        (Y : SourceFullFrameRealOrientedCoord d), Y.property⟩ :=
  rfl

/-- The real tangent complexification map is injective. -/
theorem sourceFullFrameRealOrientedTangentComplexifyLinear_injective
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Function.Injective
      (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R) := by
  intro Y Z hYZ
  apply Subtype.ext
  exact
    sourceFullFrameRealOrientedCoordComplexify_injective d
      (congrArg Subtype.val hYZ)

/-- The real version of the constructive full-frame differential right-inverse
formula. -/
noncomputable def sourceFullFrameRealDifferentialRightInverseFormula
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Y : SourceFullFrameRealOrientedCoord d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of Y.1
  let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    (2 : ℝ)⁻¹ • (M0R⁻¹ * G * (M0R.transpose)⁻¹ *
      LorentzLieGroup.minkowskiMatrix d)
  M0R * B

/-- The real right-inverse formula is linear in the real tangent coordinate. -/
noncomputable def sourceFullFrameRealDifferentialRightInverseFormulaLinear
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    SourceFullFrameRealOrientedCoord d →ₗ[ℝ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ where
  toFun := sourceFullFrameRealDifferentialRightInverseFormula d M0R
  map_add' := by
    intro Y Z
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of Y.1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of Z.1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      (M0R.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      LorentzLieGroup.minkowskiMatrix d
    have hOf : Matrix.of ((Y.1 + Z.1)) = A + B := by
      exact (Matrix.of_add_of Y.1 Z.1).symm
    have hlin :
        M0R⁻¹ * (A + B) * C * E =
          M0R⁻¹ * A * C * E + M0R⁻¹ * B * C * E := by
      noncomm_ring
    change
      M0R * ((2 : ℝ)⁻¹ •
          (M0R⁻¹ * Matrix.of (Y + Z).1 * (M0R.transpose)⁻¹ *
            LorentzLieGroup.minkowskiMatrix d)) =
        M0R * ((2 : ℝ)⁻¹ •
          (M0R⁻¹ * Matrix.of Y.1 * (M0R.transpose)⁻¹ *
            LorentzLieGroup.minkowskiMatrix d)) +
        M0R * ((2 : ℝ)⁻¹ •
          (M0R⁻¹ * Matrix.of Z.1 * (M0R.transpose)⁻¹ *
            LorentzLieGroup.minkowskiMatrix d))
    simp only [Prod.fst_add]
    dsimp [A, B, C, E] at hOf hlin
    rw [hOf, hlin, smul_add, Matrix.mul_add]
  map_smul' := by
    intro c Y
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of Y.1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      (M0R.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      LorentzLieGroup.minkowskiMatrix d
    have hOf : Matrix.of (c • Y.1) = c • A := by
      exact (Matrix.smul_of c Y.1).symm
    have hlin :
        M0R⁻¹ * (c • A) * C * E =
          c • (M0R⁻¹ * A * C * E) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    change
      M0R * ((2 : ℝ)⁻¹ •
          (M0R⁻¹ * Matrix.of (c • Y).1 * (M0R.transpose)⁻¹ *
            LorentzLieGroup.minkowskiMatrix d)) =
        c •
          (M0R * ((2 : ℝ)⁻¹ •
            (M0R⁻¹ * Matrix.of Y.1 * (M0R.transpose)⁻¹ *
              LorentzLieGroup.minkowskiMatrix d)))
    simp only [Prod.smul_fst]
    dsimp [A, C, E] at hOf hlin
    rw [hOf, hlin]
    rw [smul_smul, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    rw [mul_comm c]

@[simp]
theorem sourceFullFrameRealDifferentialRightInverseFormulaLinear_apply
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Y : SourceFullFrameRealOrientedCoord d) :
    sourceFullFrameRealDifferentialRightInverseFormulaLinear d M0R Y =
      sourceFullFrameRealDifferentialRightInverseFormula d M0R Y :=
  rfl

/-- The real right inverse restricted to the real full-frame tangent model. -/
noncomputable def sourceFullFrameRealDifferentialRightInverseLinear
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (_hM0R : IsUnit M0R.det) :
    sourceFullFrameRealOrientedTangentSpace d M0R →ₗ[ℝ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  (sourceFullFrameRealDifferentialRightInverseFormulaLinear d M0R).comp
    (sourceFullFrameRealOrientedTangentSpace d M0R).subtype

@[simp]
theorem sourceFullFrameRealDifferentialRightInverseLinear_apply
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : sourceFullFrameRealOrientedTangentSpace d M0R) :
    sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y =
      sourceFullFrameRealDifferentialRightInverseFormula d M0R
        (Y : SourceFullFrameRealOrientedCoord d) :=
  rfl

/-- Complexifying a real full-frame matrix complexifies its determinant. -/
theorem sourceFullFrame_matrix_map_ofReal_det
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det Complex.ofRealHom M0R).symm

/-- A real determinant unit remains a unit after complexifying the matrix. -/
theorem sourceFullFrame_matrix_map_ofReal_det_isUnit
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    IsUnit (M0R.map Complex.ofReal).det := by
  rw [sourceFullFrame_matrix_map_ofReal_det]
  exact hM0R.map Complex.ofRealHom

/-- The real explicit slice is the range of the real constructive differential
right inverse. -/
noncomputable def sourceFullFrameRealDifferentialRightInverseRange
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Submodule ℝ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  LinearMap.range (sourceFullFrameRealDifferentialRightInverseLinear d hM0R)

/-- Componentwise complexification commutes with the nonsingular inverse for
real matrices. -/
theorem matrix_map_ofReal_nonsing_inv
    (d : ℕ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hA : IsUnit A.det) :
    (A⁻¹).map Complex.ofReal = (A.map Complex.ofReal)⁻¹ := by
  symm
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  have h :=
    congrArg
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M i j)
      (Matrix.nonsing_inv_mul A hA)
  simp [Matrix.mul_apply] at h ⊢
  simp only [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]
  rw [h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The real Minkowski metric matrix complexifies to the complex Lorentz metric
matrix. -/
theorem sourceFullFrame_minkowskiMatrix_map_ofReal
    (d : ℕ) :
    (LorentzLieGroup.minkowskiMatrix d).map Complex.ofReal =
      ComplexLorentzGroup.ηℂ (d := d) := by
  ext i j
  by_cases hij : i = j <;>
    simp [LorentzLieGroup.minkowskiMatrix, ComplexLorentzGroup.ηℂ, hij]

/-- The complex Minkowski metric determinant is the complexification of the
real Minkowski metric determinant. -/
theorem minkowskiMetricDet_eq_ofReal_minkowskiMatrix_det
    (d : ℕ) :
    minkowskiMetricDet d =
      ((LorentzLieGroup.minkowskiMatrix d).det : ℂ) := by
  rw [minkowskiMetricDet]
  rw [← sourceFullFrame_minkowskiMatrix_map_ofReal d]
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det Complex.ofRealHom
      (LorentzLieGroup.minkowskiMatrix d)).symm

/-- The real full-frame Gram matrix `M η Mᵀ`. -/
def sourceFullFrameRealGramMatrix
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  M0R * LorentzLieGroup.minkowskiMatrix d * M0R.transpose

/-- The real Minkowski metric determinant is a unit. -/
theorem sourceFullFrame_minkowskiMatrix_det_isUnit
    (d : ℕ) :
    IsUnit (LorentzLieGroup.minkowskiMatrix d).det := by
  have hsquare :
      (LorentzLieGroup.minkowskiMatrix d).det *
          (LorentzLieGroup.minkowskiMatrix d).det = 1 := by
    have h := congrArg Matrix.det (LorentzLieGroup.minkowskiMatrix_sq d)
    simpa [Matrix.det_mul] using h
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hsquare)

/-- A nonsingular real full frame has nonsingular real Gram matrix. -/
theorem sourceFullFrameRealGramMatrix_det_isUnit
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    IsUnit (sourceFullFrameRealGramMatrix d M0R).det := by
  rw [sourceFullFrameRealGramMatrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  rw [mul_assoc]
  exact hM0R.mul ((sourceFullFrame_minkowskiMatrix_det_isUnit d).mul hM0R)

/-- At a real full-frame base, the complex Gram matrix is the complexification
of the real Gram matrix. -/
theorem sourceFullFrameGram_map_ofReal_matrix
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix.of (sourceFullFrameGram d (M0R.map Complex.ofReal)) =
      (sourceFullFrameRealGramMatrix d M0R).map Complex.ofReal := by
  rw [sourceFullFrameGram_eq_mul_eta_transpose]
  ext i j
  simp [sourceFullFrameRealGramMatrix, Matrix.mul_apply,
    ComplexLorentzGroup.ηℂ, LorentzLieGroup.minkowskiMatrix,
    Matrix.diagonal_apply]

/-- The inverse of the complex Gram matrix at a real full-frame base is the
complexification of the inverse real Gram matrix. -/
theorem sourceFullFrameGram_map_ofReal_matrix_inv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    ((Matrix.of (sourceFullFrameGram d (M0R.map Complex.ofReal)))⁻¹) =
      ((sourceFullFrameRealGramMatrix d M0R)⁻¹).map Complex.ofReal := by
  rw [sourceFullFrameGram_map_ofReal_matrix]
  exact
    (matrix_map_ofReal_nonsing_inv d
      (sourceFullFrameRealGramMatrix d M0R)
      (sourceFullFrameRealGramMatrix_det_isUnit d hM0R)).symm

/-- The inverse of the complexification of the real Gram matrix is the
complexification of its real inverse. -/
theorem sourceFullFrameRealGramMatrix_map_ofReal_inv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    ((sourceFullFrameRealGramMatrix d M0R).map Complex.ofReal)⁻¹ =
      ((sourceFullFrameRealGramMatrix d M0R)⁻¹).map Complex.ofReal :=
  (matrix_map_ofReal_nonsing_inv d
    (sourceFullFrameRealGramMatrix d M0R)
    (sourceFullFrameRealGramMatrix_det_isUnit d hM0R)).symm

/-- Matrix form of complexifying the Gram component of a real full-frame
oriented coordinate. -/
theorem sourceFullFrameRealOrientedCoordComplexify_matrix_of
    (d : ℕ) (Y : SourceFullFrameRealOrientedCoord d) :
    Matrix.of (sourceFullFrameRealOrientedCoordComplexify d Y).1 =
      (Matrix.of Y.1).map Complex.ofReal := by
  ext i j
  rfl

/-- The linearized oriented equation has real value on complexified real
coordinates at a complexified real full-frame base. -/
theorem sourceFullFrameOrientedEquationDerivLinear_realComplexify_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : SourceFullFrameRealOrientedCoord d) :
    Complex.im
      (sourceFullFrameOrientedEquationDerivLinear d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
        (sourceFullFrameRealOrientedCoordComplexify d Y)) = 0 := by
  simp only [sourceFullFrameOrientedEquationDerivLinear,
    sourceFullFrameOrientedGram, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sourceFullFrameGram_map_ofReal_matrix,
    sourceFullFrameRealGramMatrix_map_ofReal_inv d hM0R,
    sourceFullFrameRealOrientedCoordComplexify_matrix_of,
    minkowskiMetricDet_eq_ofReal_minkowskiMatrix_det,
    sourceFullFrame_matrix_map_ofReal_det d M0R,
    sourceFullFrame_matrix_map_ofReal_det d
      (sourceFullFrameRealGramMatrix d M0R)]
  simp [sourceFullFrameRealOrientedCoordComplexify, Matrix.mul_apply,
    Matrix.trace]

/-- The real part of a complex tangent coordinate at a complexified real
full-frame base is a real tangent coordinate. -/
theorem sourceFullFrameOrientedTangent_re_mem
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    {Y : SourceFullFrameOrientedCoord d}
    (hY :
      Y ∈ sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))) :
    sourceFullFrameOrientedCoordRe d Y ∈
      sourceFullFrameRealOrientedTangentSpace d M0R := by
  rw [mem_sourceFullFrameRealOrientedTangentSpace]
  rw [mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero]
  have hY' :
      Y ∈ sourceFullFrameSymmetricCoordSubmodule d ∧
        sourceFullFrameOrientedEquationDerivLinear d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) Y = 0 := by
    exact
      (mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero).1
        hY
  constructor
  · intro a b
    change ((Y.1 a b).re : ℂ) = ((Y.1 b a).re : ℂ)
    exact_mod_cast congrArg Complex.re (hY'.1 a b)
  · let L :=
      sourceFullFrameOrientedEquationDerivLinear d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    have hsplit :
        L Y =
          L (sourceFullFrameRealOrientedCoordComplexify d
              (sourceFullFrameOrientedCoordRe d Y)) +
            Complex.I *
              L (sourceFullFrameRealOrientedCoordComplexify d
                (sourceFullFrameOrientedCoordIm d Y)) := by
      have h :=
        congrArg L (sourceFullFrameOrientedCoord_re_im_decomp d Y)
      simpa [L] using h
    have hzero :
        L (sourceFullFrameRealOrientedCoordComplexify d
              (sourceFullFrameOrientedCoordRe d Y)) +
            Complex.I *
              L (sourceFullFrameRealOrientedCoordComplexify d
                (sourceFullFrameOrientedCoordIm d Y)) = 0 := by
      rw [← hsplit, hY'.2]
    exact
      (complex_add_I_mul_eq_zero_of_im_eq_zero
        (sourceFullFrameOrientedEquationDerivLinear_realComplexify_im
          d hM0R (sourceFullFrameOrientedCoordRe d Y))
        (sourceFullFrameOrientedEquationDerivLinear_realComplexify_im
          d hM0R (sourceFullFrameOrientedCoordIm d Y))
        hzero).1

/-- The imaginary part of a complex tangent coordinate at a complexified real
full-frame base is a real tangent coordinate. -/
theorem sourceFullFrameOrientedTangent_im_mem
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    {Y : SourceFullFrameOrientedCoord d}
    (hY :
      Y ∈ sourceFullFrameOrientedTangentSpace d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))) :
    sourceFullFrameOrientedCoordIm d Y ∈
      sourceFullFrameRealOrientedTangentSpace d M0R := by
  rw [mem_sourceFullFrameRealOrientedTangentSpace]
  rw [mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero]
  have hY' :
      Y ∈ sourceFullFrameSymmetricCoordSubmodule d ∧
        sourceFullFrameOrientedEquationDerivLinear d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) Y = 0 := by
    exact
      (mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero).1
        hY
  constructor
  · intro a b
    change ((Y.1 a b).im : ℂ) = ((Y.1 b a).im : ℂ)
    exact_mod_cast congrArg Complex.im (hY'.1 a b)
  · let L :=
      sourceFullFrameOrientedEquationDerivLinear d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
    have hsplit :
        L Y =
          L (sourceFullFrameRealOrientedCoordComplexify d
              (sourceFullFrameOrientedCoordRe d Y)) +
            Complex.I *
              L (sourceFullFrameRealOrientedCoordComplexify d
                (sourceFullFrameOrientedCoordIm d Y)) := by
      have h :=
        congrArg L (sourceFullFrameOrientedCoord_re_im_decomp d Y)
      simpa [L] using h
    have hzero :
        L (sourceFullFrameRealOrientedCoordComplexify d
              (sourceFullFrameOrientedCoordRe d Y)) +
            Complex.I *
              L (sourceFullFrameRealOrientedCoordComplexify d
                (sourceFullFrameOrientedCoordIm d Y)) = 0 := by
      rw [← hsplit, hY'.2]
    exact
      (complex_add_I_mul_eq_zero_of_im_eq_zero
        (sourceFullFrameOrientedEquationDerivLinear_realComplexify_im
          d hM0R (sourceFullFrameOrientedCoordRe d Y))
        (sourceFullFrameOrientedEquationDerivLinear_realComplexify_im
          d hM0R (sourceFullFrameOrientedCoordIm d Y))
        hzero).2

/-- Entrywise real part of a complex full-frame matrix. -/
def sourceFullFrameMatrixRe
    {d : ℕ}
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).re

/-- Entrywise imaginary part of a complex full-frame matrix. -/
def sourceFullFrameMatrixIm
    {d : ℕ}
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).im

/-- A complex full-frame matrix decomposes into real and imaginary parts. -/
theorem sourceFullFrameMatrix_re_im_decomp
    {d : ℕ}
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    X =
      (sourceFullFrameMatrixRe X).map Complex.ofReal +
        Complex.I • (sourceFullFrameMatrixIm X).map Complex.ofReal := by
  ext i j
  simp only [sourceFullFrameMatrixRe, sourceFullFrameMatrixIm,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (X i j)).symm

/-- Real and imaginary real matrices cannot cancel in
`A + I B = 0` after componentwise complexification. -/
theorem sourceFullFrameMatrix_map_ofReal_add_I_smul_eq_zero
    {d : ℕ}
    {A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h :
      A.map Complex.ofReal + Complex.I • B.map Complex.ofReal =
        (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :
    A = 0 ∧ B = 0 := by
  constructor
  · ext i j
    have hij := congr_fun (congr_fun h i) j
    have hre := congrArg Complex.re hij
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hre
    exact hre
  · ext i j
    have hij := congr_fun (congr_fun h i) j
    have him := congrArg Complex.im hij
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at him
    exact him

/-- The explicit complex right inverse is the componentwise complexification of
the real right-inverse formula whenever the complexified real coordinate lies in
the complex tangent space. -/
theorem sourceFullFrameOrientedDifferentialRightInverseLinear_realComplexify
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : SourceFullFrameRealOrientedCoord d)
    (hY :
      sourceFullFrameRealOrientedCoordComplexify d Y ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))) :
    sourceFullFrameOrientedDifferentialRightInverseLinear d
        (M0 := M0R.map Complex.ofReal)
        (by
          have hdetMap :
              (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
            simpa [RingHom.mapMatrix_apply] using
              (RingHom.map_det Complex.ofRealHom M0R).symm
          rw [hdetMap]
          exact hM0R.map Complex.ofRealHom)
        ⟨sourceFullFrameRealOrientedCoordComplexify d Y, hY⟩ =
      (sourceFullFrameRealDifferentialRightInverseFormula d M0R Y).map
        Complex.ofReal := by
  let hM0C : IsUnit (M0R.map Complex.ofReal).det := by
    have hdetMap : (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
      simpa [RingHom.mapMatrix_apply] using
        (RingHom.map_det Complex.ofRealHom M0R).symm
    rw [hdetMap]
    exact hM0R.map Complex.ofRealHom
  change
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C
        ⟨sourceFullFrameRealOrientedCoordComplexify d Y, hY⟩ =
      (sourceFullFrameRealDifferentialRightInverseFormula d M0R Y).map
        Complex.ofReal
  rw [sourceFullFrameOrientedDifferentialRightInverseLinear_apply]
  simp only [sourceFullFrameRealDifferentialRightInverseFormula]
  let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of Y.1
  have hG :
      Matrix.of (sourceFullFrameRealOrientedCoordComplexify d Y).1 =
        G.map Complex.ofReal := by
    dsimp [G]
    exact sourceFullFrameRealOrientedCoordComplexify_matrix_of d Y
  have hInvM := matrix_map_ofReal_nonsing_inv d M0R hM0R
  have hMtUnit : IsUnit M0R.transpose.det := by
    simpa [Matrix.det_transpose] using hM0R
  have hInvMt := matrix_map_ofReal_nonsing_inv d M0R.transpose hMtUnit
  have hMtMap :
      M0R.transpose.map Complex.ofReal =
        (M0R.map Complex.ofReal).transpose := by
    ext i j
    rfl
  have hEta := sourceFullFrame_minkowskiMatrix_map_ofReal d
  rw [hG, ← hInvM, ← hMtMap, ← hInvMt, ← hEta]
  ext i j
  simp [G, Matrix.mul_apply, smul_eq_mul]
  simp only [← Complex.ofReal_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The real right inverse on the real tangent model complexifies to the
explicit complex right inverse. -/
theorem sourceFullFrameRealDifferentialRightInverseLinear_complexify
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : sourceFullFrameRealOrientedTangentSpace d M0R) :
    (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y).map
        Complex.ofReal =
      sourceFullFrameOrientedDifferentialRightInverseLinear d
        (M0 := M0R.map Complex.ofReal)
        (by
          have hdetMap :
              (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
            simpa [RingHom.mapMatrix_apply] using
              (RingHom.map_det Complex.ofRealHom M0R).symm
          rw [hdetMap]
          exact hM0R.map Complex.ofRealHom)
        ⟨sourceFullFrameRealOrientedCoordComplexify d
            (Y : SourceFullFrameRealOrientedCoord d), Y.property⟩ := by
  change
    (sourceFullFrameRealDifferentialRightInverseFormula d M0R
        (Y : SourceFullFrameRealOrientedCoord d)).map Complex.ofReal =
      sourceFullFrameOrientedDifferentialRightInverseLinear d
        (M0 := M0R.map Complex.ofReal)
        (by
          have hdetMap :
              (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
            simpa [RingHom.mapMatrix_apply] using
              (RingHom.map_det Complex.ofRealHom M0R).symm
          rw [hdetMap]
          exact hM0R.map Complex.ofRealHom)
        ⟨sourceFullFrameRealOrientedCoordComplexify d
            (Y : SourceFullFrameRealOrientedCoord d), Y.property⟩
  symm
  exact
    sourceFullFrameOrientedDifferentialRightInverseLinear_realComplexify
      d hM0R (Y : SourceFullFrameRealOrientedCoord d) Y.property

/-- The real right inverse lands, after complexification, in the explicit
complex gauge slice. -/
theorem sourceFullFrameRealDifferentialRightInverseLinear_mem_complexSlice
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : sourceFullFrameRealOrientedTangentSpace d M0R) :
    (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y).map
        Complex.ofReal ∈
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice := by
  let hM0C : IsUnit (M0R.map Complex.ofReal).det :=
    sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let YC := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Y
  have hcomplex :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y).map
          Complex.ofReal =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC := by
    simpa [hM0C, YC, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Y
  rw [hcomplex]
  change
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC ∈
      sourceFullFrameOrientedDifferentialRightInverseRange d hM0C
  exact ⟨YC, rfl⟩

/-- Every element of the real explicit slice complexifies into the explicit
complex gauge slice. -/
theorem sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hX : X ∈ sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    X.map Complex.ofReal ∈
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice := by
  rcases hX with ⟨Y, rfl⟩
  exact sourceFullFrameRealDifferentialRightInverseLinear_mem_complexSlice
    d hM0R Y

/-- Every element of the explicit complex slice at a complexified real base
splits as the componentwise complexification of two real-slice elements. -/
theorem sourceFullFrameExplicitComplexSlice_re_im_mem_realRange
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X :
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice) :
    ∃ XR XI : sourceFullFrameRealDifferentialRightInverseRange d hM0R,
      (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
        (XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal +
          Complex.I •
            (XI : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal := by
  let hM0C : IsUnit (M0R.map Complex.ofReal).det :=
    sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  change
    ∃ XR XI : sourceFullFrameRealDifferentialRightInverseRange d hM0R,
      (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
        (XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal +
          Complex.I •
            (XI : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal
  rcases X.property with ⟨Y, hXY⟩
  let Yr : sourceFullFrameRealOrientedTangentSpace d M0R :=
    ⟨sourceFullFrameOrientedCoordRe d (Y : SourceFullFrameOrientedCoord d),
      sourceFullFrameOrientedTangent_re_mem d hM0R Y.property⟩
  let Yi : sourceFullFrameRealOrientedTangentSpace d M0R :=
    ⟨sourceFullFrameOrientedCoordIm d (Y : SourceFullFrameOrientedCoord d),
      sourceFullFrameOrientedTangent_im_mem d hM0R Y.property⟩
  let XR : sourceFullFrameRealDifferentialRightInverseRange d hM0R :=
    ⟨sourceFullFrameRealDifferentialRightInverseLinear d hM0R Yr, ⟨Yr, rfl⟩⟩
  let XI : sourceFullFrameRealDifferentialRightInverseRange d hM0R :=
    ⟨sourceFullFrameRealDifferentialRightInverseLinear d hM0R Yi, ⟨Yi, rfl⟩⟩
  refine ⟨XR, XI, ?_⟩
  let R :=
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C
  have hYsplit :
      Y =
        sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yr +
          Complex.I •
            sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yi := by
    apply Subtype.ext
    change
      (Y : SourceFullFrameOrientedCoord d) =
        sourceFullFrameRealOrientedCoordComplexify d
            (Yr : SourceFullFrameRealOrientedCoord d) +
          Complex.I •
            sourceFullFrameRealOrientedCoordComplexify d
              (Yi : SourceFullFrameRealOrientedCoord d)
    simpa [Yr, Yi] using
      sourceFullFrameOrientedCoord_re_im_decomp d
        (Y : SourceFullFrameOrientedCoord d)
  have hRsplit :
      R Y =
        R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yr) +
          Complex.I •
            R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yi) := by
    let A := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yr
    let B := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yi
    calc
      R Y = R (A + Complex.I • B) := by
        rw [hYsplit]
      _ = R A + R (Complex.I • B) := by
        exact (R.map_add A (Complex.I • B))
      _ = R A + Complex.I • R B := by
        rw [R.map_smul]
  have hYr :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Yr).map
          Complex.ofReal =
        R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yr) := by
    simpa [R, hM0C, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Yr
  have hYi :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Yi).map
          Complex.ofReal =
        R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yi) := by
    simpa [R, hM0C, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Yi
  calc
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = R Y := hXY.symm
    _ =
        R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yr) +
          Complex.I •
            R (sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Yi) := hRsplit
    _ =
        (XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal +
          Complex.I •
            (XI : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal := by
      rw [← hYr, ← hYi]

/-- The canonical finite basis of the real explicit slice. -/
noncomputable def sourceFullFrameRealDifferentialRightInverseRangeBasis
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Module.Basis
      (Fin (Module.finrank ℝ
        (sourceFullFrameRealDifferentialRightInverseRange d hM0R)))
      ℝ (sourceFullFrameRealDifferentialRightInverseRange d hM0R) :=
  Module.finBasis ℝ (sourceFullFrameRealDifferentialRightInverseRange d hM0R)

/-- A real basis vector of the real explicit slice, complexified as an element
of the explicit complex slice. -/
noncomputable def sourceFullFrameRealSliceComplexBasisVector
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (i : Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R))) :
    (sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice :=
  let b := sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R
  ⟨((b i : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
    sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
      d hM0R (b i).property⟩

/-- Complex coordinates on the explicit complex slice obtained by
complexifying the canonical real basis of the real explicit slice. -/
noncomputable def sourceFullFrameRealSliceComplexCoordLinearMap
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    (Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R)) → ℂ) →ₗ[ℂ]
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice where
  toFun := fun q =>
    ∑ i, q i • sourceFullFrameRealSliceComplexBasisVector d hM0R i
  map_add' := by
    intro q r
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c q
    simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

/-- On real coordinates, the complex coordinate map is exactly componentwise
complexification of the corresponding real basis expansion. -/
theorem sourceFullFrameRealSliceComplexCoordLinearMap_real_eq
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (q : Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R)) → ℝ) :
    sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
        (fun i => (q i : ℂ)) =
      ⟨(((sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R).equivFun.symm q :
          sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
        sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
          d hM0R
          (((sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R).equivFun.symm q :
            sourceFullFrameRealDifferentialRightInverseRange d hM0R).property)⟩ := by
  apply Subtype.ext
  ext a b
  rw [Module.Basis.equivFun_symm_apply]
  simp only [sourceFullFrameRealSliceComplexCoordLinearMap,
    sourceFullFrameRealSliceComplexBasisVector, LinearMap.coe_mk,
    AddHom.coe_mk]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [Complex.ofReal_sum]
  simp

/-- The complex coordinate map splits a coordinate vector into the images of
its real and imaginary coordinate parts. -/
theorem sourceFullFrameRealSliceComplexCoordLinearMap_re_im_decomp
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (q : Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R)) → ℂ) :
    sourceFullFrameRealSliceComplexCoordLinearMap d hM0R q =
      sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
          (fun i => ((q i).re : ℂ)) +
        Complex.I •
          sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
            (fun i => ((q i).im : ℂ)) := by
  let C := sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
  let qR : Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R)) → ℂ :=
    fun i => ((q i).re : ℂ)
  let qI : Fin (Module.finrank ℝ
      (sourceFullFrameRealDifferentialRightInverseRange d hM0R)) → ℂ :=
    fun i => ((q i).im : ℂ)
  have hq : q = qR + Complex.I • qI := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, qR, qI, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (q i)).symm
  calc
    C q = C (qR + Complex.I • qI) := by rw [hq]
    _ = C qR + C (Complex.I • qI) := C.map_add qR (Complex.I • qI)
    _ = C qR + Complex.I • C qI := by rw [C.map_smul]

/-- The real-basis complex coordinate map is injective. -/
theorem sourceFullFrameRealSliceComplexCoordLinearMap_injective
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Function.Injective
      (sourceFullFrameRealSliceComplexCoordLinearMap d hM0R) := by
  let Rr := sourceFullFrameRealDifferentialRightInverseRange d hM0R
  let C := sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
  let b := sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R
  intro q r hqr
  have hdiff : C (q - r) = 0 := by
    rw [map_sub, hqr, sub_self]
  let qR : Fin (Module.finrank ℝ Rr) → ℝ := fun i => ((q - r) i).re
  let qI : Fin (Module.finrank ℝ Rr) → ℝ := fun i => ((q - r) i).im
  have hsplit :
      C (q - r) =
        C (fun i => (qR i : ℂ)) +
          Complex.I • C (fun i => (qI i : ℂ)) := by
    simpa [C, qR, qI] using
      sourceFullFrameRealSliceComplexCoordLinearMap_re_im_decomp
        d hM0R (q - r)
  have hsub :
      C (fun i => (qR i : ℂ)) +
          Complex.I • C (fun i => (qI i : ℂ)) = 0 := by
    rwa [← hsplit]
  have hrealR :
      C (fun i => (qR i : ℂ)) =
        ⟨(((b.equivFun.symm qR : Rr) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R ((b.equivFun.symm qR : Rr).property)⟩ := by
    simpa [C, b, Rr] using
      sourceFullFrameRealSliceComplexCoordLinearMap_real_eq d hM0R qR
  have hrealI :
      C (fun i => (qI i : ℂ)) =
        ⟨(((b.equivFun.symm qI : Rr) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R ((b.equivFun.symm qI : Rr).property)⟩ := by
    simpa [C, b, Rr] using
      sourceFullFrameRealSliceComplexCoordLinearMap_real_eq d hM0R qI
  rw [hrealR, hrealI] at hsub
  have hmat :
      (((b.equivFun.symm qR : Rr) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) +
        Complex.I •
          (((b.equivFun.symm qI : Rr) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) = 0 := by
    simpa [Submodule.coe_add, Submodule.coe_smul_of_tower] using
      congrArg Subtype.val hsub
  have hparts :=
    sourceFullFrameMatrix_map_ofReal_add_I_smul_eq_zero hmat
  have hqR_zero : qR = 0 := by
    have hXR : (b.equivFun.symm qR : Rr) = 0 := by
      apply Subtype.ext
      exact hparts.1
    calc
      qR = b.equivFun (b.equivFun.symm qR) :=
        (b.equivFun.apply_symm_apply qR).symm
      _ = b.equivFun (0 : Rr) := congrArg b.equivFun hXR
      _ = 0 := b.equivFun.map_zero
  have hqI_zero : qI = 0 := by
    have hXI : (b.equivFun.symm qI : Rr) = 0 := by
      apply Subtype.ext
      exact hparts.2
    calc
      qI = b.equivFun (b.equivFun.symm qI) :=
        (b.equivFun.apply_symm_apply qI).symm
      _ = b.equivFun (0 : Rr) := congrArg b.equivFun hXI
      _ = 0 := b.equivFun.map_zero
  ext i
  have hre : (q i - r i).re = 0 := by
    simpa [qR, Pi.sub_apply] using congrFun hqR_zero i
  have him : (q i - r i).im = 0 := by
    simpa [qI, Pi.sub_apply] using congrFun hqI_zero i
  have hzero : q i - r i = 0 := Complex.ext hre him
  exact sub_eq_zero.mp hzero

/-- The real-basis complex coordinate map is surjective onto the explicit
complex slice. -/
theorem sourceFullFrameRealSliceComplexCoordLinearMap_surjective
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Function.Surjective
      (sourceFullFrameRealSliceComplexCoordLinearMap d hM0R) := by
  let Rr := sourceFullFrameRealDifferentialRightInverseRange d hM0R
  let C := sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
  let b := sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R
  intro X
  rcases sourceFullFrameExplicitComplexSlice_re_im_mem_realRange d hM0R X with
    ⟨XR, XI, hX⟩
  let qR : Fin (Module.finrank ℝ Rr) → ℝ := b.equivFun XR
  let qI : Fin (Module.finrank ℝ Rr) → ℝ := b.equivFun XI
  let q : Fin (Module.finrank ℝ Rr) → ℂ :=
    fun i => (qR i : ℂ) + Complex.I * (qI i : ℂ)
  refine ⟨q, ?_⟩
  have hqsplit :
      q = (fun i => (qR i : ℂ)) +
          Complex.I • (fun i => (qI i : ℂ)) := by
    ext i
    simp [q, smul_eq_mul]
  have hCsplit :
      C q =
        C (fun i => (qR i : ℂ)) +
          Complex.I • C (fun i => (qI i : ℂ)) := by
    calc
      C q =
          C ((fun i => (qR i : ℂ)) +
            Complex.I • (fun i => (qI i : ℂ))) := by rw [hqsplit]
      _ = C (fun i => (qR i : ℂ)) +
            C (Complex.I • (fun i => (qI i : ℂ))) := by
        exact C.map_add (fun i => (qR i : ℂ))
          (Complex.I • (fun i => (qI i : ℂ)))
      _ = C (fun i => (qR i : ℂ)) +
            Complex.I • C (fun i => (qI i : ℂ)) := by
        rw [C.map_smul]
  have hrealR :
      C (fun i => (qR i : ℂ)) =
        ⟨((XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R XR.property⟩ := by
    simpa [C, b, Rr, qR] using
      sourceFullFrameRealSliceComplexCoordLinearMap_real_eq d hM0R qR
  have hrealI :
      C (fun i => (qI i : ℂ)) =
        ⟨((XI : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R XI.property⟩ := by
    simpa [C, b, Rr, qI] using
      sourceFullFrameRealSliceComplexCoordLinearMap_real_eq d hM0R qI
  calc
    C q =
        C (fun i => (qR i : ℂ)) +
          Complex.I • C (fun i => (qI i : ℂ)) := hCsplit
    _ =
        ⟨((XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R XR.property⟩ +
          Complex.I •
            ⟨((XI : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
              sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
                d hM0R XI.property⟩ := by
      rw [hrealR, hrealI]
    _ = X := by
      apply Subtype.ext
      simpa [Submodule.coe_add, Submodule.coe_smul_of_tower] using hX.symm

/-- Finite-coordinate real-form data for the explicit full-frame slice.

The producer for this packet is the remaining finite-dimensional linear
algebra step before the real implicit-function theorem: it must choose real
coordinates on the real right-inverse range and compatible complex coordinates
on the explicit complex slice. -/
structure SourceFullFrameRealSliceFiniteCoordData
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hM0R : IsUnit M0R.det) where
  realModelDim : ℕ
  realCoordEquiv :
    (Fin realModelDim → ℝ) ≃ₗ[ℝ]
      sourceFullFrameRealDifferentialRightInverseRange d hM0R
  complexCoordEquiv :
    (Fin realModelDim → ℂ) ≃L[ℂ]
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice
  complexCoordEquiv_real_eq :
    ∀ q : Fin realModelDim → ℝ,
      complexCoordEquiv (fun i => (q i : ℂ)) =
        ⟨((realCoordEquiv q :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal),
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R (realCoordEquiv q).property⟩

/-- Finite-coordinate real-form data for the explicit full-frame slice,
constructed from a real basis of the real right-inverse range and its
componentwise complexification. -/
theorem sourceFullFrameRealSliceFiniteCoordData
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Nonempty (SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) := by
  let Rr := sourceFullFrameRealDifferentialRightInverseRange d hM0R
  let b := sourceFullFrameRealDifferentialRightInverseRangeBasis d hM0R
  let C := sourceFullFrameRealSliceComplexCoordLinearMap d hM0R
  let eC : (Fin (Module.finrank ℝ Rr) → ℂ) ≃L[ℂ]
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice :=
    (LinearEquiv.ofBijective C
      ⟨sourceFullFrameRealSliceComplexCoordLinearMap_injective d hM0R,
        sourceFullFrameRealSliceComplexCoordLinearMap_surjective d hM0R⟩).toContinuousLinearEquiv
  exact ⟨{
    realModelDim := Module.finrank ℝ Rr
    realCoordEquiv := b.equivFun.symm
    complexCoordEquiv := eC
    complexCoordEquiv_real_eq := by
      intro q
      change C (fun i => (q i : ℂ)) = _
      simpa [C, b, Rr] using
        sourceFullFrameRealSliceComplexCoordLinearMap_real_eq d hM0R q }⟩

/-- The real right inverse is injective on the real tangent model. -/
theorem sourceFullFrameRealDifferentialRightInverseLinear_injective
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Function.Injective
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R) := by
  intro Y Z hYZ
  apply sourceFullFrameRealOrientedTangentComplexifyLinear_injective d M0R
  apply Subtype.ext
  have hmap :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y).map
          Complex.ofReal =
        (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Z).map
          Complex.ofReal := by
    rw [hYZ]
  let hM0C : IsUnit (M0R.map Complex.ofReal).det := by
    have hdetMap :
        (M0R.map Complex.ofReal).det = (M0R.det : ℂ) := by
      simpa [RingHom.mapMatrix_apply] using
        (RingHom.map_det Complex.ofRealHom M0R).symm
    rw [hdetMap]
    exact hM0R.map Complex.ofRealHom
  let YC := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Y
  let ZC := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Z
  have hYc :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Y).map
          Complex.ofReal =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC := by
    simpa [hM0C, YC, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Y
  have hZc :
      (sourceFullFrameRealDifferentialRightInverseLinear d hM0R Z).map
          Complex.ofReal =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C ZC := by
    simpa [hM0C, ZC, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Z
  have hright :
      sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C ZC := by
    rw [← hYc, ← hZc]
    exact hmap
  have hdiff :=
    congrArg (sourceFullFrameOrientedDifferential d
      (M0R.map Complex.ofReal)) hright
  have hdiff' : (YC : SourceFullFrameOrientedCoord d) =
      (ZC : SourceFullFrameOrientedCoord d) := by
    change
      sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC) =
        sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C ZC)
        at hdiff
    rw [sourceFullFrameOrientedDifferential_rightInverse d hM0C YC,
      sourceFullFrameOrientedDifferential_rightInverse d hM0C ZC] at hdiff
    exact hdiff
  simpa [YC, ZC, sourceFullFrameRealOrientedTangentComplexifyLinear] using hdiff'

end BHW
