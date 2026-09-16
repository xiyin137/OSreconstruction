import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalLocalTestPartition
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIEuclideanRotationSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISchwartzLinearAction
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Original-OS Euclidean covariance of the positive-chamber current

The common basepoint and every gap must rotate together. Independence of the
normalized basepoint cutoff then gives the genuine reduced E1 identity, on
sources whose original and rotated supports both lie in the positive chamber.
-/

noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace Topology
open scoped Classical Distributions Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

omit [NeZero d] in
theorem osiiEuclideanRotationInvCLE_measurePreserving
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1) (hdet : R.det = 1) :
    MeasurePreserving (osiiEuclideanRotationInvCLE R hR)
      (volume : Measure (SpacetimeDim d)) volume := by
  refine ⟨(osiiEuclideanRotationInvCLE R hR).continuous.measurable, ?_⟩
  change Measure.map (Matrix.toLin' R.transpose) volume = volume
  simpa [Matrix.det_transpose, hdet] using
    (Real.map_matrix_volume_pi_eq_smul_volume_pi
      (M := R.transpose) (by simp [Matrix.det_transpose, hdet]))

/-- A proper Euclidean rotation preserves the normalized basepoint integral. -/
def osiiEuclideanRotateBasepointCutoff
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (chi : BHW.NormalizedBasepointCutoff d) :
    BHW.NormalizedBasepointCutoff d where
  toSchwartz := SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (osiiEuclideanRotationInvCLE R hR) chi.toSchwartz
  integral_eq_one := by
    have h := (osiiEuclideanRotationInvCLE_measurePreserving R hR hdet).integral_comp'
      (f := (osiiEuclideanRotationInvCLE R hR).toHomeomorph.toMeasurableEquiv)
      (fun x => chi.toSchwartz x)
    exact h.trans chi.integral_eq_one

@[simp] theorem osiiEuclideanRotateBasepointCutoff_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (chi : BHW.NormalizedBasepointCutoff d) (x : SpacetimeDim d) :
    (osiiEuclideanRotateBasepointCutoff R hR hdet chi).toSchwartz x =
      chi.toSchwartz (R.transpose.mulVec x) := rfl

omit [NeZero d] in
/-- Difference coordinates intertwine every diagonal linear action. -/
theorem osiiEuclideanRotation_reducedDiffMapReal
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (x : NPointDomain d (k + 1)) :
    BHW.reducedDiffMapReal (k + 1) d (fun i => R.mulVec (x i)) =
      fun j => R.mulVec (BHW.reducedDiffMapReal (k + 1) d x j) := by
  ext j mu
  change R.mulVec (x ⟨j.val + 1, by omega⟩) mu -
      R.mulVec (x ⟨j.val, by omega⟩) mu =
    R.mulVec (x ⟨j.val + 1, by omega⟩ - x ⟨j.val, by omega⟩) mu
  rw [Matrix.mulVec_sub]
  rfl

/-- The full-point rotation rotates both factors of the reduced source lift. -/
theorem osiiEuclideanRotateSchwartz_reducedTestLift
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (chi : BHW.NormalizedBasepointCutoff d) (phi : SchwartzNPoint d k) :
    osiiEuclideanRotateSchwartz R hR
        (BHW.reducedTestLift k d chi.toSchwartz phi) =
      BHW.reducedTestLift k d
        (osiiEuclideanRotateBasepointCutoff R hR hdet chi).toSchwartz
        (osiiEuclideanRotateSchwartz R hR phi) := by
  ext x
  simp only [osiiEuclideanRotateSchwartz_apply, BHW.reducedTestLift_apply,
    osiiEuclideanRotateBasepointCutoff_apply,
    osiiEuclideanRotation_reducedDiffMapReal]
  rfl

namespace OSIIChapterV

/-- Rotate a compact positive-chamber test when its rotated support remains
inside the same chamber. -/
def initialPhysicalRotatePositiveTest
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤)
    (hsupport : tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.mulVec (x i))) ⊆
      initialReducedStrictPositiveGapRegion d k) :
    TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤ where
  toFun := fun x => phi (fun i => R.transpose.mulVec (x i))
  contDiff' := phi.contDiff.comp
    (osiiEuclideanRotateNPointCLE (n := k) R hR).contDiff
  hasCompactSupport' := phi.hasCompactSupport.comp_homeomorph
    (osiiEuclideanRotateNPointCLE (n := k) R hR).toHomeomorph
  tsupport_subset' := hsupport

@[simp] theorem initialPhysicalRotatePositiveTest_apply
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤)
    (hsupport : tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.mulVec (x i))) ⊆
      initialReducedStrictPositiveGapRegion d k)
    (x : NPointDomain d k) :
    initialPhysicalRotatePositiveTest R hR phi hsupport x =
      phi (fun i => R.transpose.mulVec (x i)) := rfl

theorem initialPhysicalTestToSchwartzCLM_rotatePositiveTest
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤)
    (hsupport : tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.mulVec (x i))) ⊆
      initialReducedStrictPositiveGapRegion d k) :
    initialPhysicalTestToSchwartzCLM
        (initialReducedStrictPositiveGapOpen d k)
        (initialPhysicalRotatePositiveTest R hR phi hsupport) =
      osiiEuclideanRotateSchwartz R hR
        (initialPhysicalTestToSchwartzCLM
          (initialReducedStrictPositiveGapOpen d k) phi) := by
  ext x
  simp [initialPhysicalRotatePositiveTest]

variable [NeZero k]

/-- Original E1, descended to the actual positive-chamber LF current. No
analytic continuation, corrected growth, or reconstructed spectrum is used. -/
theorem initialPhysicalPositiveChamberCurrent_rotate_eq
    (OS : OsterwalderSchraderAxioms d)
    (chi : BHW.NormalizedBasepointCutoff d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1) (hdet : R.det = 1)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤)
    (hsupport : tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.mulVec (x i))) ⊆
      initialReducedStrictPositiveGapRegion d k) :
    initialPhysicalPositiveChamberCurrent (k := k) OS chi
        (initialPhysicalRotatePositiveTest R hR phi hsupport) =
      initialPhysicalPositiveChamberCurrent (k := k) OS chi phi := by
  let chiR := osiiEuclideanRotateBasepointCutoff R hR hdet chi
  let phiR := initialPhysicalRotatePositiveTest R hR phi hsupport
  have hlift : initialPhysicalPositiveSourceLiftCLM chiR phiR =
      osiiEuclideanRotateZeroDiagonal R hR
        (initialPhysicalPositiveSourceLiftCLM chi phi) := by
    apply Subtype.ext
    rw [initialPhysicalPositiveSourceLiftCLM_coe]
    change BHW.reducedTestLift k d chiR.toSchwartz
        (initialPhysicalTestToSchwartzCLM
          (initialReducedStrictPositiveGapOpen d k) phiR) =
      osiiEuclideanRotateSchwartz R hR
        (BHW.reducedTestLift k d chi.toSchwartz
          (initialPhysicalTestToSchwartzCLM
            (initialReducedStrictPositiveGapOpen d k) phi))
    rw [initialPhysicalTestToSchwartzCLM_rotatePositiveTest]
    exact (osiiEuclideanRotateSchwartz_reducedTestLift R hR hdet chi _).symm
  calc
    initialPhysicalPositiveChamberCurrent (k := k) OS chi phiR =
        initialPhysicalPositiveChamberCurrent (k := k) OS chiR phiR :=
      congrArg (fun T => T phiR)
        (initialPhysicalPositiveChamberCurrent_basepoint_independent OS chi chiR)
    _ = OS.S (k + 1) (osiiEuclideanRotateZeroDiagonal R hR
        (initialPhysicalPositiveSourceLiftCLM chi phi)) := by
      rw [initialPhysicalPositiveChamberCurrent_apply, hlift]
    _ = initialPhysicalPositiveChamberCurrent (k := k) OS chi phi :=
      osiiEuclideanRotateZeroDiagonal_schwinger_eq OS R hR hdet _

end OSIIChapterV

/-- The same real linear generator in every particle block. -/
def osiiDiagonalRealMatrixCLM
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real) :
    NPointDomain d k →L[Real] NPointDomain d k :=
  ContinuousLinearMap.pi fun j =>
    (Matrix.toLin' Y).toContinuousLinearMap.comp (ContinuousLinearMap.proj j)

omit [NeZero d] in
@[simp] theorem osiiDiagonalRealMatrixCLM_apply
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (x : NPointDomain d k) (j : Fin k) :
    osiiDiagonalRealMatrixCLM Y x j = Y.mulVec (x j) := rfl

private def realMatrixEntryCLM (mu nu : Fin (d + 1)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) Real →L[Real] Real :=
  ((LinearMap.proj nu : (Fin (d + 1) -> Real) →ₗ[Real] Real).comp
    (LinearMap.proj mu : Matrix (Fin (d + 1)) (Fin (d + 1)) Real →ₗ[Real]
      (Fin (d + 1) -> Real))).toContinuousLinearMap

omit [NeZero d] in
theorem osiiEuclidean_exp_skew_orthogonal
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (t : Real) :
    (NormedSpace.exp (t • Y)).transpose * NormedSpace.exp (t • Y) = 1 := by
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY, smul_neg]
  rw [← Matrix.exp_add_of_commute (-(t • Y)) (t • Y)
    (Commute.neg_left (Commute.refl (t • Y)))]
  simp

omit [NeZero d] in
theorem osiiEuclidean_exp_skew_det_one
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (t : Real) :
    (NormedSpace.exp (t • Y)).det = 1 := by
  have hsq (u : Real) : (NormedSpace.exp (u • Y)).det ^ 2 = 1 := by
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using
      congrArg Matrix.det (osiiEuclidean_exp_skew_orthogonal Y hY u)
  have hc : Continuous (fun u : Real => (NormedSpace.exp (u • Y)).det) :=
    (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).matrix_det
  have hvalues (u : Real) : (NormedSpace.exp (u • Y)).det = 1 ∨
      (NormedSpace.exp (u • Y)).det = -1 := by
    rcases (sq_eq_one_iff).mp (hsq u) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hclosed : IsClosed {u : Real | (NormedSpace.exp (u • Y)).det = 1} :=
    isClosed_eq hc continuous_const
  have hopen : IsOpen {u : Real | (NormedSpace.exp (u • Y)).det = 1} := by
    have heq : {u : Real | (NormedSpace.exp (u • Y)).det = 1} =
        {u : Real | (NormedSpace.exp (u • Y)).det = -1}ᶜ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h hneg => by rw [h] at hneg; norm_num at hneg,
        fun h => (hvalues u).resolve_right h⟩
    rw [heq]
    exact (isClosed_eq hc continuous_const).isOpen_compl
  have hall := (show IsClopen {u : Real | (NormedSpace.exp (u • Y)).det = 1} from
    ⟨hclosed, hopen⟩).eq_univ ⟨0, by simp⟩
  change t ∈ {u : Real | (NormedSpace.exp (u • Y)).det = 1}
  rw [hall]
  exact Set.mem_univ t

/-- The forward diagonal action of the genuine Euclidean one-parameter group. -/
def osiiEuclideanSkewFlow
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (t : Real) :
    NPointDomain d k ≃L[Real] NPointDomain d k :=
  (osiiEuclideanRotateNPointCLE (NormedSpace.exp (t • Y))
    (osiiEuclidean_exp_skew_orthogonal Y hY t)).symm

omit [NeZero d] in
@[simp] theorem osiiEuclideanSkewFlow_apply
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (t : Real) (x : NPointDomain d k) (j : Fin k) :
    osiiEuclideanSkewFlow Y hY t x j = (NormedSpace.exp (t • Y)).mulVec (x j) := rfl

omit [NeZero d] in
@[simp] theorem osiiEuclideanSkewFlow_symm_apply
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (t : Real) (x : NPointDomain d k) (j : Fin k) :
    (osiiEuclideanSkewFlow Y hY t).symm x j =
      (NormedSpace.exp (t • Y)).transpose.mulVec (x j) := rfl

omit [NeZero d] in
@[simp] theorem osiiEuclideanSkewFlow_zero
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) :
    osiiEuclideanSkewFlow (k := k) Y hY 0 = ContinuousLinearEquiv.refl Real _ := by
  ext x j mu
  simp

omit [NeZero d] in
private theorem contDiff_osiiRealMatrixExp
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real) :
    ContDiff Real (⊤ : ℕ∞) (fun t : Real => NormedSpace.exp (t • Y)) := by
  have h : AnalyticOnNhd Real
      (NormedSpace.exp : Matrix (Fin (d + 1)) (Fin (d + 1)) Real ->
        Matrix (Fin (d + 1)) (Fin (d + 1)) Real) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact h.contDiff.comp (contDiff_id.smul contDiff_const)

omit [NeZero d] in
theorem contDiff_osiiEuclideanSkewFlow
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) :
    ContDiff Real (⊤ : ℕ∞)
      (fun p : Real × NPointDomain d k => osiiEuclideanSkewFlow Y hY p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  apply contDiff_pi.mpr
  intro mu
  simp only [osiiEuclideanSkewFlow_apply, Matrix.mulVec, dotProduct]
  apply ContDiff.sum
  intro nu _
  let ev := realMatrixEntryCLM mu nu
  exact ((ev.contDiff.comp (contDiff_osiiRealMatrixExp Y)).comp contDiff_fst).mul
    (by fun_prop)

omit [NeZero d] in
theorem continuous_osiiEuclideanSkewFlow_symm
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) :
    Continuous
      (fun p : Real × NPointDomain d k => (osiiEuclideanSkewFlow Y hY p.1).symm p.2) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro mu
  simp only [osiiEuclideanSkewFlow_symm_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  apply continuous_finset_sum
  intro nu _
  let ev := realMatrixEntryCLM nu mu
  exact ((ev.continuous.comp (contDiff_osiiRealMatrixExp Y).continuous).comp
    continuous_fst).mul (by fun_prop)

omit [NeZero d] in
theorem hasDerivAt_osiiEuclideanSkewFlow_zero
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (x : NPointDomain d k) :
    HasDerivAt (fun t : Real => osiiEuclideanSkewFlow Y hY t x)
      (osiiDiagonalRealMatrixCLM Y x) 0 := by
  have hmat : HasDerivAt (fun t : Real => NormedSpace.exp (t • Y)) Y 0 := by
    simpa using hasDerivAt_exp_smul_const Y (0 : Real)
  apply hasDerivAt_pi.mpr
  intro j
  apply hasDerivAt_pi.mpr
  intro mu
  simp only [osiiEuclideanSkewFlow_apply, osiiDiagonalRealMatrixCLM_apply,
    Matrix.mulVec, dotProduct]
  apply HasDerivAt.fun_sum
  intro nu _
  let ev := realMatrixEntryCLM mu nu
  exact (ev.hasFDerivAt.comp_hasDerivAt 0 hmat).mul_const (x j nu)

omit [NeZero d] in
theorem hasDerivAt_schwartz_osiiEuclideanSkewFlow_zero
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y) (phi : SchwartzNPoint d k) (x : NPointDomain d k) :
    HasDerivAt (fun t : Real => phi (osiiEuclideanSkewFlow Y hY t x))
      (OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y) phi x) 0 := by
  have h := (phi.hasFDerivAt (osiiEuclideanSkewFlow Y hY 0 x)).comp_hasDerivAt 0
    (hasDerivAt_osiiEuclideanSkewFlow_zero Y hY x)
  convert h using 1 <;> first | rfl | simp

namespace OSIIChapterV

/-- The Euclidean generator applied to an actual compact chamber source. -/
def initialPhysicalEuclideanWardTest
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤) :
    TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤ :=
  let F := initialPhysicalTestToSchwartzCLM
    (initialReducedStrictPositiveGapOpen d k) phi
  let G := OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y) F
  initialPhysicalSchwartzToTestFunction (initialReducedStrictPositiveGapOpen d k)
    G
    (OSIIChapterVI.linearVectorFieldCLM_hasCompactSupport _ F
      (by
        dsimp only [F]
        rw [initialPhysicalTestToSchwartzCLM_apply]
        change HasCompactSupport (phi : NPointDomain d k → Complex)
        exact phi.hasCompactSupport))
    ((OSIIChapterVI.tsupport_linearVectorFieldCLM_subset _ F).trans
      (initialPhysicalTestToSchwartzCLM_tsupport_subset
        (initialReducedStrictPositiveGapOpen d k) phi))

@[simp] theorem initialPhysicalTestToSchwartzCLM_euclideanWardTest
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤) :
    initialPhysicalTestToSchwartzCLM (initialReducedStrictPositiveGapOpen d k)
        (initialPhysicalEuclideanWardTest Y phi) =
      OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y)
        (initialPhysicalTestToSchwartzCLM (initialReducedStrictPositiveGapOpen d k) phi) := by
  exact initialPhysicalTestToSchwartzCLM_schwartzToTestFunction _ _ _ _

variable [NeZero k]

/-- The genuine infinitesimal Euclidean Ward identity on the original
positive-chamber current. The nearby finite rotations are all computed by
one fixed reduced Schwinger functional before differentiation. -/
theorem initialPhysicalPositiveChamberCurrent_euclideanWard_eq_zero
    (OS : OsterwalderSchraderAxioms d)
    (chi : BHW.NormalizedBasepointCutoff d)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y)
    (phi : TestFunction (initialReducedStrictPositiveGapOpen d k) Complex ⊤) :
    initialPhysicalPositiveChamberCurrent (k := k) OS chi
      (initialPhysicalEuclideanWardTest Y phi) = 0 := by
  let U := initialReducedStrictPositiveGapOpen d k
  let F := initialPhysicalTestToSchwartzCLM U phi
  let e := osiiEuclideanSkewFlow (k := k) Y hY
  let G := OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y) F
  have hF : HasCompactSupport (F : NPointDomain d k -> Complex) := by
    dsimp only [F]
    rw [initialPhysicalTestToSchwartzCLM_apply]
    change HasCompactSupport (phi : NPointDomain d k → Complex)
    exact phi.hasCompactSupport
  have he := contDiff_osiiEuclideanSkewFlow (k := k) Y hY
  have hinv := continuous_osiiEuclideanSkewFlow_symm (k := k) Y hY
  obtain ⟨K, hK, hKU, hnear⟩ :=
    OSIIChapterVI.exists_compact_tsupport_linearAction_subset e hinv F hF
      (initialReducedStrictPositiveGapRegion d k)
      isOpen_initialReducedStrictPositiveGapRegion (by
        intro x hx
        have hxU := initialPhysicalTestToSchwartzCLM_tsupport_subset U phi hx
        change x ∈ initialReducedStrictPositiveGapRegion d k at hxU
        simpa [e] using hxU)
  have hzero : SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e 0) F = F := by
    ext x
    simp [e]
  have hFK : tsupport (F : NPointDomain d k -> Complex) ⊆ K := by
    simpa only [hzero] using hnear.self_of_nhds
  obtain ⟨C⟩ := CanonicalReducedCompactCutoffData.nonempty
    (section43QTimeCLM d k '' K) (hK.image (section43QTimeCLM d k).continuous)
    (by rintro tau ⟨x, hx, rfl⟩; exact hKU hx)
  let T := canonicalReducedTimeCutoffSchwingerCLM OS C.cutoff C.cutoff_support
  have hcurrent (psi : TestFunction U Complex ⊤)
      (hpsi : tsupport (initialPhysicalTestToSchwartzCLM U psi :
        NPointDomain d k -> Complex) ⊆ K) :
      initialPhysicalPositiveChamberCurrent (k := k) OS chi psi =
        T (initialPhysicalTestToSchwartzCLM U psi) := by
    apply initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff OS chi C psi
    intro x hx
    exact ⟨x, hpsi hx, rfl⟩
  have hconst : (fun t : Real => T
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) F)) =ᶠ[nhds 0]
      (fun _ => T F) := by
    filter_upwards [hnear] with t ht
    let R := NormedSpace.exp (t • Y)
    have hRt : R.transpose.transpose * R.transpose = 1 := by
      simpa only [Matrix.transpose_transpose] using
        mul_eq_one_comm.mpr (osiiEuclidean_exp_skew_orthogonal Y hY t)
    have hdet : R.transpose.det = 1 := by
      simpa [Matrix.det_transpose, R] using osiiEuclidean_exp_skew_det_one Y hY t
    have hsupport : tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.transpose.mulVec (x i))) ⊆
        initialReducedStrictPositiveGapRegion d k := by
      intro x hx
      apply hKU
      apply ht
      change x ∈ tsupport (fun x : NPointDomain d k =>
        phi (fun i => R.transpose.transpose.mulVec (x i)))
      exact hx
    let phit := initialPhysicalRotatePositiveTest R.transpose hRt phi hsupport
    have hFt : initialPhysicalTestToSchwartzCLM U phit =
        SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) F := by
      ext x
      simp [phit, F, U, e, R, initialPhysicalTestToSchwartzCLM_apply]
      rfl
    calc
      T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) F) =
          initialPhysicalPositiveChamberCurrent (k := k) OS chi phit := by
        rw [← hFt]
        exact (hcurrent phit (by rw [hFt]; exact ht)).symm
      _ = initialPhysicalPositiveChamberCurrent (k := k) OS chi phi :=
        initialPhysicalPositiveChamberCurrent_rotate_eq OS chi R.transpose hRt hdet phi hsupport
      _ = T F := hcurrent phi hFK
  have hderiv : HasDerivAt
      (fun t : Real => T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) F))
      (T G) 0 :=
    OSIIChapterVI.hasDerivAt_compactLinearAction_pairing T e he hinv F hF 0 G
      (hasDerivAt_schwartz_osiiEuclideanSkewFlow_zero Y hY F)
  have hTG : T G = 0 :=
    hderiv.unique ((hasDerivAt_const (0 : Real) (T F)).congr_of_eventuallyEq hconst)
  calc
    initialPhysicalPositiveChamberCurrent (k := k) OS chi
        (initialPhysicalEuclideanWardTest Y phi) =
        T (initialPhysicalTestToSchwartzCLM U (initialPhysicalEuclideanWardTest Y phi)) := by
      apply hcurrent
      rw [initialPhysicalTestToSchwartzCLM_euclideanWardTest]
      exact (OSIIChapterVI.tsupport_linearVectorFieldCLM_subset _ F).trans hFK
    _ = 0 := by rw [initialPhysicalTestToSchwartzCLM_euclideanWardTest]; exact hTG

/-- The same original-E1 Ward identity, in the canonical reduced-cutoff
interface used by the real edges of the time continuation. -/
theorem canonicalReducedTimeCutoffSchwingerCLM_euclideanWard_eq_zero
    (OS : OsterwalderSchraderAxioms d)
    {compactCarrier : Set (Fin k -> Real)}
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y)
    (phi : SchwartzNPoint d k)
    (hphi : HasCompactSupport (phi : NPointDomain d k -> Complex))
    (hcarrier : ∀ x ∈ tsupport (phi : NPointDomain d k -> Complex),
      section43QTimeCLM d k x ∈ compactCarrier) :
    canonicalReducedTimeCutoffSchwingerCLM OS C.cutoff C.cutoff_support
      (OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y) phi) = 0 := by
  let U := initialReducedStrictPositiveGapOpen d k
  have hpositive : tsupport (phi : NPointDomain d k -> Complex) ⊆
      initialReducedStrictPositiveGapRegion d k := by
    intro x hx
    exact C.cutoff_support (subset_tsupport _ (by
      change C.cutoff (section43QTimeCLM d k x) ≠ 0
      rw [C.cutoff_one_on _ (C.compactCarrier_subset (hcarrier x hx))]
      exact one_ne_zero))
  let psi := initialPhysicalSchwartzToTestFunction U phi hphi hpositive
  let chi := BHW.normalizedCutoffOfBump d
  have hsource : initialPhysicalTestToSchwartzCLM U psi = phi :=
    initialPhysicalTestToSchwartzCLM_schwartzToTestFunction U phi hphi hpositive
  have hcut := initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff
    OS chi C (initialPhysicalEuclideanWardTest Y psi) (by
      intro x hx
      rw [initialPhysicalTestToSchwartzCLM_euclideanWardTest, hsource] at hx
      exact hcarrier x (OSIIChapterVI.tsupport_linearVectorFieldCLM_subset _ phi hx))
  calc
    canonicalReducedTimeCutoffSchwingerCLM OS C.cutoff C.cutoff_support
        (OSIIChapterVI.linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y) phi) =
        initialPhysicalPositiveChamberCurrent (k := k) OS chi
          (initialPhysicalEuclideanWardTest Y psi) := by
      have hsource' : initialPhysicalTestToSchwartzCLM
          (initialReducedStrictPositiveGapOpen d k) psi = phi := by
        simpa [U] using hsource
      rw [initialPhysicalTestToSchwartzCLM_euclideanWardTest, hsource'] at hcut
      exact hcut.symm
    _ = 0 := initialPhysicalPositiveChamberCurrent_euclideanWard_eq_zero OS chi Y hY psi

end OSIIChapterV
end OSReconstruction
