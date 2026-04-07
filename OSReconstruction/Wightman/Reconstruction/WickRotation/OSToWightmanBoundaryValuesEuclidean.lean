/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanEuclideanLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

/-!
# Euclidean Support For Boundary Values

OS-side Euclidean rotation pairings for the boundary-value witness `bvt_F`.
This packages the exact distributional Euclidean hypothesis needed by the
strict OS-II Lorentz-covariance route in `OSToWightmanBoundaryValues.lean`.
-/

noncomputable section

open scoped Classical NNReal
open BigOperators Finset

variable {d : ℕ} [NeZero d]

private noncomputable def euclideanRotationInvCLEquiv
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' R.transpose
          invFun := Matrix.toLin' R
          left_inv := fun v => by
            show (Matrix.toLin' R) ((Matrix.toLin' R.transpose) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hR', Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' R.transpose) ((Matrix.toLin' R) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

private noncomputable def euclideanRotateSchwartz {n : ℕ}
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrRight
      (fun (_ : Fin n) => euclideanRotationInvCLEquiv R hR)) φ

private theorem euclideanRotateSchwartz_apply {n : ℕ}
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) (φ : SchwartzNPoint d n) (x : NPointDomain d n) :
    (euclideanRotateSchwartz R hR φ).toFun x =
      φ.toFun (fun i => R.transpose.mulVec (x i)) := by
  simp only [euclideanRotateSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, euclideanRotationInvCLEquiv]
  rfl

/-- Euclidean rotation pairing for the reconstructed Wick-section witness `bvt_F`.

This is the exact OS-side distributional input required by the production
Euclidean-to-Lorentz bridge: the Schwinger rotation axiom is transported to the
Wick-section integral formula for `bvt_F`, but only on compactly supported
tests whose support already lies in the honest forward-tube Wick section before
and after the Euclidean rotation. -/
theorem bvt_F_ofEuclidean_wick_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ)
      (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (hdet : R.det = 1) (hR : R.transpose * R = 1)
      (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hdet hR)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hdet hR)
                (fun k => wickRotatePoint (x k))) * φ x
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := by
  intro n R hdet hR φ hφ_compact hφ_tsupport
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  let eR : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    ContinuousLinearEquiv.piCongrRight
      (fun (_ : Fin n) => euclideanRotationInvCLEquiv R hR)
  let φR : SchwartzNPoint d n := euclideanRotateSchwartz R hR φ
  have hφ_wick :
      tsupport (φ : NPointDomain d n → ℂ) ⊆
        {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} := by
    intro x hx
    exact (hφ_tsupport hx).1
  have hφ_coeff :
      (ZeroDiagonalSchwartz.ofClassical φ).1 = φ :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
      (d := d) (n := n) φ hφ_wick
  have hφR_tsupport :
      tsupport (φR : NPointDomain d n → ℂ) =
        eR.toHomeomorph ⁻¹' tsupport (φ : NPointDomain d n → ℂ) := by
    simpa [φR, eR, euclideanRotateSchwartz,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage (g := (φ : NPointDomain d n → ℂ)) eR.toHomeomorph)
  have hφR_wick :
      tsupport (φR : NPointDomain d n → ℂ) ⊆
        {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} := by
    intro x hx
    have hy : (fun i => R.transpose.mulVec (x i)) ∈ tsupport (φ : NPointDomain d n → ℂ) := by
      simpa [hφR_tsupport, eR, euclideanRotationInvCLEquiv] using hx
    have hy_pair := hφ_tsupport hy
    have hwick :
        (fun k => wickRotatePoint (x k)) =
          BHW.complexLorentzAction
            (ComplexLorentzGroup.ofEuclidean R hdet hR)
            (fun k => wickRotatePoint (R.transpose.mulVec (x k))) := by
      ext k μ
      calc
        wickRotatePoint (x k) μ
            = wickRotatePoint (R.mulVec (R.transpose.mulVec (x k))) μ := by
                congr 1
                simpa [Matrix.mulVec_mulVec, hR']
        _ =
          ∑ ν,
            (ComplexLorentzGroup.ofEuclidean R hdet hR).val μ ν *
              wickRotatePoint (R.transpose.mulVec (x k)) ν := by
                exact wickRotatePoint_ofEuclidean R hdet hR (R.transpose.mulVec (x k)) μ
    simpa [hwick] using hy_pair.2
  have hφR_coeff :
      (ZeroDiagonalSchwartz.ofClassical φR).1 = φR :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
      (d := d) (n := n) φR hφR_wick
  let φ0 : ZeroDiagonalSchwartz d n := ZeroDiagonalSchwartz.ofClassical φ
  let φR0 : ZeroDiagonalSchwartz d n := ZeroDiagonalSchwartz.ofClassical φR
  have hRtrans_orth : R.transpose.transpose * R.transpose = 1 := by
    simpa using hR'
  have hRtrans_det : R.transpose.det = 1 := by
    simpa [Matrix.det_transpose] using hdet
  have hrot :
      OS.S n φ0 = OS.S n φR0 := by
    refine OS.E1_rotation_invariant n R.transpose hRtrans_orth hRtrans_det φ0 φR0 ?_
    intro x
    rw [hφR_coeff, hφ_coeff]
    exact euclideanRotateSchwartz_apply R hR φ x
  have hchange :
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hdet hR)
              (fun k => wickRotatePoint (x k))) * φ x
        =
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φR x := by
    let h : NPointDomain d n → ℂ :=
      fun x => bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φR x
    calc
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hdet hR)
              (fun k => wickRotatePoint (x k))) * φ x
          =
        ∫ x : NPointDomain d n, h (fun i => R.mulVec (x i)) := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x => by
            have hwick :
                (fun k => wickRotatePoint (R.mulVec (x k))) =
                  BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R hdet hR)
                    (fun k => wickRotatePoint (x k)) := by
              ext k μ
              exact wickRotatePoint_ofEuclidean R hdet hR (x k) μ
            have hφeval :
                φR (fun i => R.mulVec (x i)) = φ x := by
              change (euclideanRotateSchwartz R hR φ).toFun (fun i => R.mulVec (x i)) = φ x
              rw [euclideanRotateSchwartz_apply]
              congr 1
              ext i j
              simp [Matrix.mulVec_mulVec, hR]
            simp [h, hwick, hφeval]
      _ = ∫ x : NPointDomain d n, h x :=
        integral_orthogonal_eq_self R hR h
      _ =
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φR x := rfl
  calc
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.complexLorentzAction
            (ComplexLorentzGroup.ofEuclidean R hdet hR)
            (fun k => wickRotatePoint (x k))) * φ x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φR x := hchange
    _ = ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (φR0.1 x) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by rw [hφR_coeff]
    _ = OS.S n φR0 := by
          exact (bvt_euclidean_restriction OS lgc n φR0).symm
    _ = OS.S n φ0 := hrot.symm
    _ = ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (φ0.1 x) := by
            exact (bvt_euclidean_restriction OS lgc n φ0)
    _ =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x => by rw [hφ_coeff]
