import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- Continuous-linear time projection used by the derivative formula for the
Section 4.3 Fourier-Laplace integral. -/
noncomputable def section43QTimeCLM (d n : ℕ) [NeZero d] :
    NPointDomain d n →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d))).comp
    (nPointTimeSpatialCLE (d := d) n).toContinuousLinearMap

@[simp] theorem section43QTimeCLM_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) :
    section43QTimeCLM d n q = section43QTime (d := d) (n := n) q := by
  rfl

/-- Continuous-linear spatial projection used by the derivative formula for the
Section 4.3 Fourier-Laplace integral. -/
noncomputable def section43QSpatialCLM (d n : ℕ) [NeZero d] :
    NPointDomain d n →L[ℝ] EuclideanSpace ℝ (Fin n × Fin d) :=
  (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d))).comp
    (nPointTimeSpatialCLE (d := d) n).toContinuousLinearMap

@[simp] theorem section43QSpatialCLM_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) :
    section43QSpatialCLM d n q = section43QSpatial (d := d) (n := n) q := by
  rfl

/-- Coordinate bound for the time selector, stated using the coordinate
projection CLM that appears in the derivative formula. -/
theorem abs_section43QTime_coord_le_opNorm
    (d n : ℕ) [NeZero d]
    (m : NPointDomain d n) (k : Fin n) :
    |section43QTime (d := d) (n := n) m k| ≤
      ‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖ := by
  let L : NPointDomain d n →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj
      (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
      (section43QTimeCLM d n))
  simpa [L, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm L m

/-- Coordinate bound for the spatial selector, stated using the Euclidean
coordinate projection CLM. -/
theorem abs_section43QSpatial_coord_le_opNorm
    (d n : ℕ) [NeZero d]
    (m : NPointDomain d n) (i : Fin n × Fin d) :
    |section43QSpatial (d := d) (n := n) m i| ≤
      ‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
          (section43QSpatialCLM d n))‖ * ‖m‖ := by
  let L : NPointDomain d n →L[ℝ] ℝ :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (section43QSpatialCLM d n))
  simpa [L, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm L m

/-- Coordinate multiplier Schwartz input produced by differentiating the
spatial Fourier variable in the Section 4.3 Fourier-Laplace integrand. -/
noncomputable def section43SpatialMultiplierTransport
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (i : Fin n × Fin d) : SchwartzNPoint d n :=
  (nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
    (-(2 * Real.pi * Complex.I) •
      SchwartzMap.smulLeftCLM ℂ
        (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
          ((p.1 i : ℝ) : ℂ))
        (nPointSpatialTimeSchwartzCLE (d := d) (n := n) F))

theorem partialFourierSpatial_fun_finset_sum
    (d n : ℕ)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) (∑ i ∈ s, F i) p =
      ∑ i ∈ s, partialFourierSpatial_fun (d := d) (n := n) (F i) p := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · have hzero :
        partialFourierSpatial_fun (d := d) (n := n) (0 : SchwartzNPoint d n) p = 0 := by
      simpa using
        (partialFourierSpatial_fun_smul (d := d) (n := n) (a := 0)
          (f := (0 : SchwartzNPoint d n)) p)
    simpa using hzero
  · intro a s ha ih
    simp [Finset.sum_insert, ha, ih, partialFourierSpatial_fun_add]

theorem partialFourierSpatial_fun_fintype_sum
    (d n : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) (∑ i, F i) p =
      ∑ i, partialFourierSpatial_fun (d := d) (n := n) (F i) p := by
  classical
  simpa using
    (partialFourierSpatial_fun_finset_sum (d := d) (n := n)
      (s := Finset.univ) F p)

/-- Coordinate expansion of the spatial derivative of the partial spatial
Fourier transform.  This removes the direction-dependent multiplier
`inner η v` and replaces it with a finite sum of fixed coordinate multiplier
Schwartz inputs. -/
theorem fderiv_partialFourierSpatial_fun_spatial_apply_eq_sum_multiplierTransport
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (τ : Fin n → ℝ)
    (ξ v : EuclideanSpace ℝ (Fin n × Fin d)) :
    fderiv ℝ
      (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
      ξ v =
      ∑ i : Fin n × Fin d,
        ((v i : ℝ) : ℂ) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ) := by
  calc
    fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ v =
        partialFourierSpatial_fun (d := d) (n := n)
          ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
            (-(2 * Real.pi * Complex.I) •
              SchwartzMap.smulLeftCLM ℂ
                (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                  ((inner ℝ p.1 v : ℝ) : ℂ))
                (nPointSpatialTimeSchwartzCLE (d := d) (n := n) F)))
          (τ, ξ) := by
            exact fderiv_partialFourierSpatial_fun_spatial_apply_eq_transportSchwartz
              (d := d) (n := n) (f := F) (t := τ) (ξ := ξ) (m := v)
    _ = ∑ i : Fin n × Fin d,
        ((v i : ℝ) : ℂ) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ) := by
            let E := nPointSpatialTimeSchwartzCLE (d := d) (n := n)
            have hinput :
                (E.symm
                  (-(2 * Real.pi * Complex.I) •
                    SchwartzMap.smulLeftCLM ℂ
                      (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                        ((inner ℝ p.1 v : ℝ) : ℂ))
                      (E F))) =
                ∑ i : Fin n × Fin d,
                  ((v i : ℝ) : ℂ) • section43SpatialMultiplierTransport d n F i := by
              have hinput_fwd :
                  E
                    (E.symm
                      (-(2 * Real.pi * Complex.I) •
                        SchwartzMap.smulLeftCLM ℂ
                          (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                            ((inner ℝ p.1 v : ℝ) : ℂ))
                          (E F))) =
                  E
                    (∑ i : Fin n × Fin d,
                      ((v i : ℝ) : ℂ) • section43SpatialMultiplierTransport d n F i) := by
                ext p
                have hinner :
                    (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                      ((inner ℝ p.1 v : ℝ) : ℂ)).HasTemperateGrowth := by
                  let Lfst :
                      (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) →L[ℝ]
                        EuclideanSpace ℝ (Fin n × Fin d) :=
                    ContinuousLinearMap.fst ℝ
                      (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ)
                  let Linner : EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] ℝ :=
                    (innerSL ℝ) v
                  have hreal : Function.HasTemperateGrowth (Linner.comp Lfst) :=
                    (Linner.comp Lfst).hasTemperateGrowth
                  simpa [Lfst, Linner, real_inner_comm] using
                    Complex.ofRealCLM.toContinuousLinearMap.hasTemperateGrowth.comp hreal
                have hcoord :
                    ∀ i : Fin n × Fin d,
                      (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                        ((p.1 i : ℝ) : ℂ)).HasTemperateGrowth := by
                  intro i
                  let Lfst :
                      (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) →L[ℝ]
                        EuclideanSpace ℝ (Fin n × Fin d) :=
                    ContinuousLinearMap.fst ℝ
                      (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ)
                  let Lcoord :
                      (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) →L[ℝ] ℝ :=
                    (EuclideanSpace.proj (𝕜 := ℝ) i).comp Lfst
                  have hreal : Function.HasTemperateGrowth Lcoord :=
                    Lcoord.hasTemperateGrowth
                  simpa [Lfst, Lcoord] using
                    Complex.ofRealCLM.toContinuousLinearMap.hasTemperateGrowth.comp hreal
                simp only [E, section43SpatialMultiplierTransport, map_sum, map_smul,
                  ContinuousLinearEquiv.apply_symm_apply, SchwartzMap.smul_apply]
                simp_rw [SchwartzMap.smulLeftCLM_apply_apply hinner]
                let G : (Fin n × Fin d) →
                    SchwartzMap
                      (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ :=
                  fun x =>
                    ((v x : ℝ) : ℂ) •
                      -(2 * (Real.pi : ℂ) * Complex.I) •
                        SchwartzMap.smulLeftCLM ℂ
                          (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                            ((p.1 x : ℝ) : ℂ))
                          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) F)
                have hsum_apply : (∑ x : Fin n × Fin d, G x) p = ∑ x, G x p := by
                  classical
                  let P : Finset (Fin n × Fin d) → Prop := fun s =>
                    (∑ x ∈ s, G x) p = ∑ x ∈ s, G x p
                  change P Finset.univ
                  refine Finset.induction_on (Finset.univ : Finset (Fin n × Fin d)) ?empty ?insert
                  · simp [P]
                  · intro a s ha ih
                    simp [P]
                rw [show
                    (∑ x : Fin n × Fin d,
                      ((v x : ℝ) : ℂ) •
                        -(2 * (Real.pi : ℂ) * Complex.I) •
                          SchwartzMap.smulLeftCLM ℂ
                            (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                              ((p.1 x : ℝ) : ℂ))
                            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) F)) p =
                      (∑ x : Fin n × Fin d, G x) p by
                    rfl]
                rw [hsum_apply]
                have hG_eval :
                    ∀ x : Fin n × Fin d,
                      G x p =
                        ((v x : ℝ) : ℂ) *
                          (-(2 * (Real.pi : ℂ) * Complex.I)) *
                            (((p.1 x : ℝ) : ℂ) *
                              ((nPointSpatialTimeSchwartzCLE (d := d) (n := n) F) p)) := by
                  intro x
                  dsimp [G]
                  change
                    ((v x : ℝ) : ℂ) *
                        ((-(2 * (Real.pi : ℂ) * Complex.I)) *
                          ((SchwartzMap.smulLeftCLM ℂ
                            (fun p : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) =>
                              ((p.1 x : ℝ) : ℂ))
                            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) F)) p)) =
                      ((v x : ℝ) : ℂ) *
                        (-(2 * (Real.pi : ℂ) * Complex.I)) *
                          (((p.1 x : ℝ) : ℂ) *
                            ((nPointSpatialTimeSchwartzCLE (d := d) (n := n) F) p))
                  rw [SchwartzMap.smulLeftCLM_apply_apply (hcoord x)]
                  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
                rw [show
                    (∑ x : Fin n × Fin d, G x p) =
                      ∑ x : Fin n × Fin d,
                        ((v x : ℝ) : ℂ) *
                          (-(2 * (Real.pi : ℂ) * Complex.I)) *
                            (((p.1 x : ℝ) : ℂ) *
                              ((nPointSpatialTimeSchwartzCLE (d := d) (n := n) F) p)) by
                    refine Finset.sum_congr rfl ?_
                    intro x _hx
                    exact hG_eval x]
                simp [PiLp.inner_apply, real_inner_eq_re_inner ℝ, RCLike.inner_apply,
                  Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, smul_eq_mul,
                  mul_assoc, mul_comm]
              exact E.injective hinput_fwd
            rw [hinput]
            rw [partialFourierSpatial_fun_fintype_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa using
              (partialFourierSpatial_fun_smul (d := d) (n := n)
                (a := ((v i : ℝ) : ℂ))
                (f := section43SpatialMultiplierTransport d n F i)
                (p := (τ, ξ)))

/-- Norm bound following from the coordinate expansion of the spatial
derivative of the partial spatial Fourier transform. -/
theorem norm_fderiv_partialFourierSpatial_fun_spatial_apply_le_sum_multiplierTransport
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (τ : Fin n → ℝ)
    (ξ v : EuclideanSpace ℝ (Fin n × Fin d)) :
    ‖fderiv ℝ
      (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
      ξ v‖ ≤
      ∑ i : Fin n × Fin d,
        |v i| *
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
  rw [fderiv_partialFourierSpatial_fun_spatial_apply_eq_sum_multiplierTransport]
  calc
    ‖∑ i : Fin n × Fin d,
        ((v i : ℝ) : ℂ) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖
        ≤ ∑ i : Fin n × Fin d,
            ‖((v i : ℝ) : ℂ) *
              partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          exact norm_sum_le _ _
    _ = ∑ i : Fin n × Fin d,
        |v i| *
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [Complex.norm_real, Real.norm_eq_abs]

/-- Continuous-linear argument of the Laplace exponential in the Section 4.3
Fourier-Laplace integrand, with the time variable `τ` fixed. -/
noncomputable def section43FourierLaplace_expArgCLM
    (d n : ℕ) [NeZero d] (τ : Fin n → ℝ) :
    NPointDomain d n →L[ℝ] ℂ :=
  ∑ k : Fin n,
    (((ContinuousLinearMap.proj
        (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n)).smulRight
        (-(τ k : ℂ)))

@[simp] theorem section43FourierLaplace_expArgCLM_apply
    (d n : ℕ) [NeZero d] (τ : Fin n → ℝ) (q : NPointDomain d n) :
    section43FourierLaplace_expArgCLM d n τ q =
      -(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) := by
  simp [section43FourierLaplace_expArgCLM, mul_comm]

/-- CLM-valued first derivative candidate for the Section 4.3 Fourier-Laplace
time integrand.  Applied to a direction `m`, it is the derivative of the
Laplace exponential in the time variables plus the spatial derivative of the
partial spatial Fourier transform. -/
noncomputable def section43FourierLaplace_timeIntegrandFDerivCLM
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (τ : Fin n → ℝ) :
    NPointDomain d n →L[ℝ] ℂ :=
  let E : ℂ :=
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let P : ℂ :=
    partialFourierSpatial_fun (d := d) (n := n) F
      (τ, section43QSpatial (d := d) (n := n) q)
  (∑ k : Fin n,
    (((ContinuousLinearMap.proj
        (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n)).smulRight
        (-(τ k : ℂ) * E * P))) +
  E •
    ((fderiv ℝ
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
      (section43QSpatial (d := d) (n := n) q)).comp
        (section43QSpatialCLM d n))

@[simp] theorem section43FourierLaplace_timeIntegrandFDerivCLM_apply
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q m : NPointDomain d n)
    (τ : Fin n → ℝ) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
      let E : ℂ :=
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
      let P : ℂ :=
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q)
      (∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * E * P)) +
      E •
        (fderiv ℝ
          (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
            partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
          (section43QSpatial (d := d) (n := n) q))
          (section43QSpatial (d := d) (n := n) m) := by
  simp [section43FourierLaplace_timeIntegrandFDerivCLM]

/-- The explicit pointwise first-derivative CLM depends continuously on the
real time variable `τ`. -/
theorem continuous_section43FourierLaplace_timeIntegrandFDerivCLM
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n) :
    Continuous fun τ : Fin n → ℝ =>
      section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ := by
  refine (continuous_clm_apply (𝕜 := ℝ) (E := NPointDomain d n) (F := ℂ)).2 ?_
  intro m
  let Efun : (Fin n → ℝ) → ℂ := fun τ =>
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let Pfun : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) F
      (τ, section43QSpatial (d := d) (n := n) q)
  let Dfun : (Fin n → ℝ) → ℂ := fun τ =>
    (fderiv ℝ
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
      (section43QSpatial (d := d) (n := n) q))
      (section43QSpatial (d := d) (n := n) m)
  have hE : Continuous Efun := by
    dsimp [Efun]
    fun_prop
  have hP : Continuous Pfun := by
    let hbase : Continuous
        (partialFourierSpatial_fun (d := d) (n := n) F) :=
      continuous_partialFourierSpatial_fun (d := d) (n := n) F
    let hpath : Continuous fun τ : Fin n → ℝ =>
        (τ, section43QSpatial (d := d) (n := n) q) :=
      continuous_id.prodMk continuous_const
    simpa [Pfun] using hbase.comp hpath
  have hD : Continuous Dfun := by
    let hbase : Continuous
        (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) =>
          fderiv ℝ
            (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
              partialFourierSpatial_fun (d := d) (n := n) F (p.1, ξ))
            p.2 (section43QSpatial (d := d) (n := n) m)) :=
      continuous_partialFourierSpatial_fun_spatialDerivative_apply
        (d := d) (n := n) F (section43QSpatial (d := d) (n := n) m)
    let hpath : Continuous fun τ : Fin n → ℝ =>
        (τ, section43QSpatial (d := d) (n := n) q) :=
      continuous_id.prodMk continuous_const
    simpa [Dfun, Function.comp_apply] using hbase.comp hpath
  have htime : Continuous fun τ : Fin n → ℝ =>
      ∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * Efun τ * Pfun τ) := by
    refine continuous_finset_sum Finset.univ fun k _ => ?_
    have hτk : Continuous fun τ : Fin n → ℝ => (τ k : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_apply k)
    have hscalar : Continuous fun τ : Fin n → ℝ =>
        -(τ k : ℂ) * Efun τ * Pfun τ :=
      ((hτk.neg).mul hE).mul hP
    exact continuous_const.smul hscalar
  have hspace : Continuous fun τ : Fin n → ℝ => Efun τ • Dfun τ :=
    hE.smul hD
  have htarget : Continuous fun τ : Fin n → ℝ =>
      let E : ℂ :=
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
      let P : ℂ :=
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q)
      (∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * E * P)) +
      E •
        (fderiv ℝ
          (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
            partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
          (section43QSpatial (d := d) (n := n) q))
          (section43QSpatial (d := d) (n := n) m) := by
    simpa [Efun, Pfun, Dfun] using htime.add hspace
  convert htarget using 1
  ext τ
  exact section43FourierLaplace_timeIntegrandFDerivCLM_apply d n F q m τ

/-- The explicit pointwise first-derivative CLM depends continuously on both
the ambient variable `q` and the real time variable `τ`. -/
theorem continuous_section43FourierLaplace_timeIntegrandFDerivCLM_joint
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n) :
    Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
      section43FourierLaplace_timeIntegrandFDerivCLM d n F p.1 p.2 := by
  refine (continuous_clm_apply (𝕜 := ℝ) (E := NPointDomain d n) (F := ℂ)).2 ?_
  intro m
  let Efun : NPointDomain d n × (Fin n → ℝ) → ℂ := fun p =>
    Complex.exp
      (-(∑ k : Fin n,
        (p.2 k : ℂ) *
          (section43QTime (d := d) (n := n) p.1 k : ℂ)))
  let Pfun : NPointDomain d n × (Fin n → ℝ) → ℂ := fun p =>
    partialFourierSpatial_fun (d := d) (n := n) F
      (p.2, section43QSpatial (d := d) (n := n) p.1)
  let Dfun : NPointDomain d n × (Fin n → ℝ) → ℂ := fun p =>
    (fderiv ℝ
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (p.2, ξ))
      (section43QSpatial (d := d) (n := n) p.1))
      (section43QSpatial (d := d) (n := n) m)
  have hE : Continuous Efun := by
    have hsum : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
        ∑ k : Fin n,
          (p.2 k : ℂ) *
            (section43QTime (d := d) (n := n) p.1 k : ℂ) := by
      refine continuous_finset_sum Finset.univ fun k _ => ?_
      have hτk : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
          (p.2 k : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_apply k).comp continuous_snd)
      have hqtime : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
          section43QTime (d := d) (n := n) p.1 := by
        simpa using ((section43QTimeCLM d n).continuous.comp continuous_fst)
      have hqk : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
          (section43QTime (d := d) (n := n) p.1 k : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_apply k).comp hqtime)
      exact hτk.mul hqk
    simpa [Efun] using Complex.continuous_exp.comp hsum.neg
  have hP : Continuous Pfun := by
    let hbase : Continuous
        (partialFourierSpatial_fun (d := d) (n := n) F) :=
      continuous_partialFourierSpatial_fun (d := d) (n := n) F
    let hpath : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
        (p.2, section43QSpatial (d := d) (n := n) p.1) :=
      continuous_snd.prodMk ((section43QSpatialCLM d n).continuous.comp continuous_fst)
    simpa [Pfun] using hbase.comp hpath
  have hD : Continuous Dfun := by
    let hbase : Continuous
        (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) =>
          fderiv ℝ
            (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
              partialFourierSpatial_fun (d := d) (n := n) F (p.1, ξ))
            p.2 (section43QSpatial (d := d) (n := n) m)) :=
      continuous_partialFourierSpatial_fun_spatialDerivative_apply
        (d := d) (n := n) F (section43QSpatial (d := d) (n := n) m)
    let hpath : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
        (p.2, section43QSpatial (d := d) (n := n) p.1) :=
      continuous_snd.prodMk ((section43QSpatialCLM d n).continuous.comp continuous_fst)
    simpa [Dfun, Function.comp_apply] using hbase.comp hpath
  have htime : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
      ∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(p.2 k : ℂ) * Efun p * Pfun p) := by
    refine continuous_finset_sum Finset.univ fun k _ => ?_
    have hτk : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
        (p.2 k : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_apply k).comp continuous_snd)
    have hscalar : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
        -(p.2 k : ℂ) * Efun p * Pfun p :=
      ((hτk.neg).mul hE).mul hP
    exact continuous_const.smul hscalar
  have hspace : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
      Efun p • Dfun p :=
    hE.smul hD
  have htarget : Continuous fun p : NPointDomain d n × (Fin n → ℝ) =>
      let E : ℂ :=
        Complex.exp
          (-(∑ k : Fin n,
            (p.2 k : ℂ) *
              (section43QTime (d := d) (n := n) p.1 k : ℂ)))
      let P : ℂ :=
        partialFourierSpatial_fun (d := d) (n := n) F
          (p.2, section43QSpatial (d := d) (n := n) p.1)
      (∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(p.2 k : ℂ) * E * P)) +
      E •
        (fderiv ℝ
          (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
            partialFourierSpatial_fun (d := d) (n := n) F (p.2, ξ))
          (section43QSpatial (d := d) (n := n) p.1))
          (section43QSpatial (d := d) (n := n) m) := by
    simpa [Efun, Pfun, Dfun] using htime.add hspace
  convert htarget using 1
  ext p
  exact section43FourierLaplace_timeIntegrandFDerivCLM_apply d n F p.1 m p.2

/-- The undifferentiated Section 4.3 Fourier-Laplace time integrand is
continuous as a function of the real time variable `τ`. -/
theorem continuous_section43FourierLaplace_timeIntegrand
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n) :
    Continuous fun τ : Fin n → ℝ =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q) := by
  have hE : Continuous fun τ : Fin n → ℝ =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) := by
    fun_prop
  have hP : Continuous fun τ : Fin n → ℝ =>
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q) := by
    let hbase : Continuous (partialFourierSpatial_fun (d := d) (n := n) F) :=
      continuous_partialFourierSpatial_fun (d := d) (n := n) F
    let hpath : Continuous fun τ : Fin n → ℝ =>
        (τ, section43QSpatial (d := d) (n := n) q) :=
      continuous_id.prodMk continuous_const
    simpa using hbase.comp hpath
  exact hE.mul hP

set_option backward.isDefEq.respectTransparency false in
/-- First derivative candidate for the Section 4.3 Fourier-Laplace integral,
as the Bochner integral of the CLM-valued pointwise derivative. -/
noncomputable def section43FourierLaplaceIntegral_fderivCandidate
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (q : NPointDomain d n) :
    NPointDomain d n →L[ℝ] ℂ :=
  ∫ τ : Fin n → ℝ,
    section43FourierLaplace_timeIntegrandFDerivCLM d n
      (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ

/-- Pointwise first derivative of the Section 4.3 Fourier-Laplace time
integrand.  This is the product rule for the Laplace exponential and the
spatial partial Fourier transform, expressed in the explicit CLM form that will
later be integrated in `τ`. -/
theorem hasFDerivAt_section43FourierLaplace_timeIntegrand
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (τ : Fin n → ℝ) :
    HasFDerivAt
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q' k : ℂ))) *
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q'))
      (section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ)
      q := by
  let L : NPointDomain d n →L[ℝ] ℂ :=
    section43FourierLaplace_expArgCLM d n τ
  have hL_apply : ∀ q' : NPointDomain d n,
      L q' =
        -(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q' k : ℂ)) := by
    intro q'
    simp [L]
  have hE : HasFDerivAt
      (fun q' : NPointDomain d n => Complex.exp (L q'))
      (Complex.exp (L q) • L) q := by
    exact L.hasFDerivAt.cexp
  have hP0 : HasFDerivAt
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
      (fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q))
      (section43QSpatial (d := d) (n := n) q) := by
    exact (differentiableAt_partialFourierSpatial_fun_spatial
      (d := d) (n := n) F τ
      (section43QSpatial (d := d) (n := n) q)).hasFDerivAt
  have hP : HasFDerivAt
      (fun q' : NPointDomain d n =>
        partialFourierSpatial_fun (d := d) (n := n) F
          (τ, section43QSpatial (d := d) (n := n) q'))
      ((fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q)).comp
          (section43QSpatialCLM d n)) q := by
    simpa using hP0.comp q (section43QSpatialCLM d n).hasFDerivAt
  have hprod := hE.mul hP
  convert hprod using 1
  · ext q'
    simp [hL_apply]
  · ext m
    simp [section43FourierLaplace_timeIntegrandFDerivCLM, L,
      section43FourierLaplace_expArgCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      mul_assoc, mul_left_comm, mul_comm, add_comm]
    ring_nf
    rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    ring_nf

private theorem exists_pos_le_on_compact_of_forall_pos
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {g : E → ℝ} (hg : Continuous g)
    (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ g x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hx₀_min⟩ := hK.exists_isMinOn hne hg.continuousOn
    have hx₀_pos : 0 < g x₀ := hpos x₀ hx₀
    refine ⟨g x₀ / 2, by linarith, ?_⟩
    intro x hx
    have hle : g x₀ ≤ g x := isMinOn_iff.mp hx₀_min x hx
    linarith
  · refine ⟨1, by positivity, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

/-- Compact support inside the OS ordered positive-time region is uniformly
separated from every time-wall and every ordered-pair collision wall. -/
theorem exists_orderedPositiveTimeRegion_margin_of_compact_tsupport_subset
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ δ > 0,
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)} := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hf_compact
  let I : Type := ULift Unit ⊕ (Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2})
  have hI_nonempty : (Finset.univ : Finset I).Nonempty := by
    exact ⟨Sum.inl (ULift.up ()), Finset.mem_univ _⟩
  let lowerFun : I → (NPointDomain d n → ℝ) := fun a =>
    match a with
    | Sum.inl _ => fun _ => 1
    | Sum.inr (Sum.inl i) => fun x => x i 0
    | Sum.inr (Sum.inr p) => fun x => x p.1.2 0 - x p.1.1 0
  have hbounds : ∀ a : I, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ lowerFun a x := by
    intro a
    cases a with
    | inl _ =>
        refine ⟨1, by positivity, ?_⟩
        intro x hx
        simp [lowerFun]
    | inr b =>
        cases b with
        | inl i =>
            refine exists_pos_le_on_compact_of_forall_pos hK_compact ?_ ?_
            · exact (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply i)
            · intro x hx
              exact (hf_ord hx i).1
        | inr p =>
            refine exists_pos_le_on_compact_of_forall_pos hK_compact ?_ ?_
            · exact (((continuous_apply (0 : Fin (d + 1))).comp
                (continuous_apply p.1.2)).sub
                ((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply p.1.1)))
            · intro x hx
              exact sub_pos.mpr ((hf_ord hx p.1.1).2 p.1.2 p.2)
  let ε : I → ℝ := fun a => Classical.choose (hbounds a)
  have hε_pos : ∀ a : I, 0 < ε a := fun a => (Classical.choose_spec (hbounds a)).1
  have hε_le : ∀ a : I, ∀ x ∈ K, ε a ≤ lowerFun a x :=
    fun a => (Classical.choose_spec (hbounds a)).2
  let δ : ℝ := (Finset.univ : Finset I).inf' hI_nonempty ε
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact (Finset.lt_inf'_iff hI_nonempty).2 (fun a _ha => hε_pos a)
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx
  constructor
  · intro i
    have hδ_le_ε : δ ≤ ε (Sum.inr (Sum.inl i) : I) := by
      dsimp [δ]
      exact Finset.inf'_le (s := (Finset.univ : Finset I)) (f := ε)
        (b := (Sum.inr (Sum.inl i) : I)) (Finset.mem_univ _)
    have hε_le_x : ε (Sum.inr (Sum.inl i) : I) ≤ x i 0 := by
      simpa [lowerFun] using hε_le (Sum.inr (Sum.inl i) : I) x hx
    exact le_trans hδ_le_ε hε_le_x
  · intro i j hij
    let a : I := Sum.inr (Sum.inr ⟨(i, j), hij⟩)
    have hδ_le_ε : δ ≤ ε a := by
      dsimp [δ]
      exact Finset.inf'_le (s := (Finset.univ : Finset I)) (f := ε)
        (b := a) (Finset.mem_univ _)
    have hε_le_x : ε a ≤ x j 0 - x i 0 := by
      simpa [a, lowerFun] using hε_le a x hx
    exact le_trans hδ_le_ε hε_le_x

/-- The ordered-region margin becomes a coordinatewise positive margin after
the OS-I difference-coordinate pullback. -/
theorem tsupport_section43DiffPullback_subset_margin_positiveOrthant
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    tsupport
      (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆
        {ξ | ∀ k : Fin n, δ ≤ ξ k 0} := by
  intro ξ hξ k
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm ξ
  have hpre : y ∈ tsupport (f : NPointDomain d n → ℂ) := by
    exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
      (section43DiffCoordRealCLE d n).symm.continuous hξ
  have hy := hδ_supp hpre
  have hcoord :
      ξ k 0 =
        (if hk : k.val = 0 then y k 0 else y k 0 - y ⟨k.val - 1, by omega⟩ 0) := by
    have happly :=
      congr_fun (congr_fun ((section43DiffCoordRealCLE d n).apply_symm_apply ξ) k) 0
    rw [section43DiffCoordRealCLE_apply] at happly
    exact happly.symm
  rw [hcoord]
  by_cases hk : k.val = 0
  · simp [hk, hy.1 k]
  · simp [hk]
    have hprev_lt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
      exact Fin.mk_lt_mk.mpr (by omega)
    exact hy.2 ⟨k.val - 1, by omega⟩ k hprev_lt

/-- Spatial Fourier transform does not enlarge the time support: with a strict
ordered-support margin, every time slice below that margin vanishes. -/
theorem partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hτ : ∃ i : Fin n, τ i < δ) :
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) (τ, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards with η
  rcases hτ with ⟨i, hi⟩
  let x : NPointDomain d n := (nPointTimeSpatialCLE (d := d) n).symm (τ, η)
  have hx_not_tsupport :
      x ∉ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro hx
    have hx_margin :=
      tsupport_section43DiffPullback_subset_margin_positiveOrthant
        d n f hf_ord hδ_supp hx i
    have hτ_le : δ ≤ τ i := by
      simpa [x, nPointTimeSpatialCLE] using hx_margin
    exact not_le_of_gt hi hτ_le
  have hx_zero :
      ((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_not_tsupport
  simp [x, nPointTimeSpatialSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hx_zero]

/-- Compact support of the original ordered-time test gives an upper bound on
the time block of the OS-I difference-coordinate pullback.  This is the upper
time-slab input needed for ambient differentiability of the Fourier-Laplace
integral near the positive-energy boundary. -/
theorem exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R := by
  classical
  let K : Set (NPointDomain d n) := tsupport (f : NPointDomain d n → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hf_compact
  let g : NPointDomain d n → (Fin n → ℝ) := fun y =>
    section43QTime (d := d) (n := n) ((section43DiffCoordRealCLE d n) y)
  have hg_cont : Continuous g := by
    dsimp [g, section43QTime, nPointTimeSpatialCLE]
    fun_prop
  rcases hK_compact.exists_bound_of_continuousOn (f := g) hg_cont.continuousOn with
    ⟨R₀, hR₀⟩
  let R : ℝ := max R₀ 0
  refine ⟨R, le_max_right R₀ 0, ?_⟩
  intro ξ hξ
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm ξ
  have hy : y ∈ K := by
    exact tsupport_comp_subset_preimage (f : NPointDomain d n → ℂ)
      (section43DiffCoordRealCLE d n).symm.continuous hξ
  have hbound : ‖g y‖ ≤ R₀ := hR₀ y hy
  have hgy : g y = section43QTime (d := d) (n := n) ξ := by
    simp [g, y]
  have hboundξ : ‖section43QTime (d := d) (n := n) ξ‖ ≤ R₀ := by
    simpa [hgy] using hbound
  exact hboundξ.trans (le_max_left R₀ 0)

/-- Spatial Fourier transform does not enlarge the compact time slab: if a time
slice lies above the compact-support time-norm bound, the partial spatial
Fourier transform vanishes. -/
theorem partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {R : ℝ}
    (hR_supp :
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R)
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hτ : R < ‖τ‖) :
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) (τ, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards with η
  let x : NPointDomain d n := (nPointTimeSpatialCLE (d := d) n).symm (τ, η)
  have hx_not_tsupport :
      x ∉ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro hx
    have hx_bound := hR_supp x hx
    have htime : section43QTime (d := d) (n := n) x = τ := by
      ext i
      simp [x, section43QTime, nPointTimeSpatialCLE]
    have hle : ‖τ‖ ≤ R := by
      simpa [htime] using hx_bound
    exact not_le_of_gt hτ hle
  have hx_zero :
      ((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_not_tsupport
  simp [x, nPointTimeSpatialSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hx_zero]

/-- The pointwise first-derivative CLM of the Section 4.3 Fourier-Laplace
integrand vanishes on time slices outside the compact-support time slab. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_timeNorm_gt_bound
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {R : ℝ}
    (hR_supp :
      ∀ ξ ∈ tsupport
        (((section43DiffPullbackCLM d n ⟨f, hf_ord⟩ : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)),
        ‖section43QTime (d := d) (n := n) ξ‖ ≤ R)
    (q : NPointDomain d n) (τ : Fin n → ℝ)
    (hτ : R < ‖τ‖) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n
      (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ = 0 := by
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  have hP_zero :
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q) = 0 := by
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
        d n f hf_ord hR_supp τ
        (section43QSpatial (d := d) (n := n) q) hτ
  have hfun_zero :
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)) = fun _ => 0 := by
    funext ξ
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
        d n f hf_ord hR_supp τ ξ hτ
  have hfderiv_zero :
      fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q) = 0 := by
    rw [hfun_zero]
    simp
  ext m
  simp [section43FourierLaplace_timeIntegrandFDerivCLM, F, hP_zero, hfderiv_zero]

/-- The pointwise first-derivative CLM of the Section 4.3 Fourier-Laplace
integrand vanishes on time slices below a strict ordered-support margin. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_exists_time_lt_margin
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n) (τ : Fin n → ℝ)
    (hτ : ∃ i : Fin n, τ i < δ) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n
      (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ = 0 := by
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  have hP_zero :
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q) = 0 := by
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
        d n f hf_ord hδ_supp τ
        (section43QSpatial (d := d) (n := n) q) hτ
  have hfun_zero :
      (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)) = fun _ => 0 := by
    funext ξ
    simpa [F] using
      partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
        d n f hf_ord hδ_supp τ ξ hτ
  have hfderiv_zero :
      fderiv ℝ
        (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ))
        (section43QSpatial (d := d) (n := n) q) = 0 := by
    rw [hfun_zero]
    simp
  ext m
  simp [section43FourierLaplace_timeIntegrandFDerivCLM, F, hP_zero, hfderiv_zero]

/-- For compact ordered support, the pointwise first-derivative CLM is compactly
supported as a function of the time variable `τ`. -/
theorem hasCompactSupport_section43FourierLaplace_timeIntegrandFDerivCLM_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    HasCompactSupport fun τ : Fin n → ℝ =>
      section43FourierLaplace_timeIntegrandFDerivCLM d n
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ := by
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    d n f hf_ord hf_compact with ⟨R, _hR_nonneg, hR_supp⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro τ hτ_support
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra hnot
  have hlt : R < ‖τ‖ := lt_of_not_ge hnot
  have hzero :=
    section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_timeNorm_gt_bound
      d n f hf_ord hR_supp q τ hlt
  exact hτ_support hzero

set_option backward.isDefEq.respectTransparency false in
/-- For compact ordered support, the pointwise first-derivative CLM is
integrable as a function of the time variable `τ`. -/
theorem integrable_section43FourierLaplace_timeIntegrandFDerivCLM_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    Integrable
      (fun τ : Fin n → ℝ =>
        section43FourierLaplace_timeIntegrandFDerivCLM d n
          (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q τ) := by
  exact (continuous_section43FourierLaplace_timeIntegrandFDerivCLM
    (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q).integrable_of_hasCompactSupport
      (hasCompactSupport_section43FourierLaplace_timeIntegrandFDerivCLM_of_compact
        d n f hf_ord hf_compact q)

/-- A constant restricted to a compact time ball is integrable.  This is the
scalar bound used by the local dominated-derivative theorem. -/
theorem integrable_indicator_time_closedBall_const
    (n : ℕ) (R C : ℝ) :
    Integrable
      (Set.indicator (Metric.closedBall (0 : Fin n → ℝ) R)
        (fun _ : Fin n → ℝ => C)) := by
  have hK : IsCompact (Metric.closedBall (0 : Fin n → ℝ) R) :=
    isCompact_closedBall (0 : Fin n → ℝ) R
  have hIntOn :
      IntegrableOn (fun _ : Fin n → ℝ => C)
        (Metric.closedBall (0 : Fin n → ℝ) R) := by
    exact continuousOn_const.integrableOn_compact hK
  exact hIntOn.integrable_indicator hK.measurableSet

set_option backward.isDefEq.respectTransparency false in
/-- Joint continuity gives a scalar norm bound for the pointwise derivative
CLM on any compact product of an ambient `q`-ball and a time ball. -/
theorem exists_section43FourierLaplace_timeIntegrandFDerivCLM_norm_bound_on_compact
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n) (R : ℝ) :
    ∃ C : ℝ,
      ∀ q' ∈ Metric.closedBall q (1 : ℝ),
      ∀ τ ∈ Metric.closedBall (0 : Fin n → ℝ) R,
        ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q' τ‖ ≤ C := by
  classical
  let Kq : Set (NPointDomain d n) := Metric.closedBall q (1 : ℝ)
  let Kτ : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  let K : Set (NPointDomain d n × (Fin n → ℝ)) := Kq ×ˢ Kτ
  have hKq : IsCompact Kq := isCompact_closedBall q (1 : ℝ)
  have hKτ : IsCompact Kτ := isCompact_closedBall (0 : Fin n → ℝ) R
  have hK : IsCompact K := hKq.prod hKτ
  let g : NPointDomain d n × (Fin n → ℝ) → ℝ := fun p =>
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F p.1 p.2‖
  have hg_cont : Continuous g := by
    exact continuous_norm.comp
      (continuous_section43FourierLaplace_timeIntegrandFDerivCLM_joint
        (d := d) (n := n) F)
  rcases hK.bddAbove_image hg_cont.continuousOn with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro q' hq' τ hτ
  exact hC ⟨(q', τ), ⟨hq', hτ⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Local domination for the pointwise derivative CLM: under compact ordered
support, one integrable scalar function dominates the derivative CLM uniformly
for `q'` in a fixed compact neighborhood of `q`. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_local_bound_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    ∃ bound : (Fin n → ℝ) → ℝ,
      Integrable bound ∧
      ∀ᵐ τ, ∀ q' ∈ Metric.closedBall q (1 : ℝ),
        ‖section43FourierLaplace_timeIntegrandFDerivCLM d n
          (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q' τ‖ ≤ bound τ := by
  classical
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    d n f hf_ord hf_compact with ⟨R, _hR_nonneg, hR_supp⟩
  let Kτ : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases exists_section43FourierLaplace_timeIntegrandFDerivCLM_norm_bound_on_compact
    (d := d) (n := n) F q R with ⟨C, hC⟩
  refine ⟨Set.indicator Kτ (fun _ => C), ?_, ?_⟩
  · simpa [Kτ] using integrable_indicator_time_closedBall_const n R C
  · filter_upwards with τ q' hq'
    by_cases hτ : τ ∈ Kτ
    · rw [Set.indicator_of_mem hτ]
      simpa [F, Kτ] using hC q' hq' τ hτ
    · have hdist_not : ¬ dist τ (0 : Fin n → ℝ) ≤ R := by
        simpa [Kτ, Metric.mem_closedBall] using hτ
      have hlt_dist : R < dist τ (0 : Fin n → ℝ) := lt_of_not_ge hdist_not
      have hlt : R < ‖τ‖ := by
        simpa [dist_eq_norm, sub_zero] using hlt_dist
      have hzero :=
        section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_timeNorm_gt_bound
          d n f hf_ord hR_supp q' τ hlt
      rw [Set.indicator_of_notMem hτ, hzero, norm_zero]

/-- For compact ordered support, the undifferentiated Section 4.3
Fourier-Laplace time integrand is compactly supported in `τ`. -/
theorem hasCompactSupport_section43FourierLaplace_timeIntegrand_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    HasCompactSupport fun τ : Fin n → ℝ =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q) := by
  rcases exists_section43DiffPullback_timeNorm_bound_of_compact_tsupport
    d n f hf_ord hf_compact with ⟨R, _hR_nonneg, hR_supp⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro τ hτ_support
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra hnot
  have hlt : R < ‖τ‖ := lt_of_not_ge hnot
  have hzero :=
    partialFourierSpatial_section43DiffPullback_eq_zero_of_timeNorm_gt_bound
      d n f hf_ord hR_supp τ (section43QSpatial (d := d) (n := n) q) hlt
  exact hτ_support (by simp [hzero])

/-- For compact ordered support, the undifferentiated Section 4.3
Fourier-Laplace time integrand is integrable for every ambient `q`. -/
theorem integrable_section43FourierLaplace_timeIntegrand_of_compact
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    Integrable fun τ : Fin n → ℝ =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q) := by
  exact (continuous_section43FourierLaplace_timeIntegrand
    d n (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) q).integrable_of_hasCompactSupport
      (hasCompactSupport_section43FourierLaplace_timeIntegrand_of_compact
        d n f hf_ord hf_compact q)

set_option backward.isDefEq.respectTransparency false in
/-- Ambient first derivative of the Section 4.3 Fourier-Laplace integral under
compact ordered support.  This is the differentiated-under-the-integral
formula supplied by the compact-slab domination packet above. -/
theorem section43FourierLaplaceIntegral_hasFDerivAt_of_compact_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (q : NPointDomain d n) :
    HasFDerivAt
      (fun q' : NPointDomain d n =>
        section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q')
      (section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q)
      q := by
  let Fpull : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  let Fint : NPointDomain d n → (Fin n → ℝ) → ℂ := fun q' τ =>
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q' k : ℂ))) *
    partialFourierSpatial_fun (d := d) (n := n) Fpull
      (τ, section43QSpatial (d := d) (n := n) q')
  let Fderiv : NPointDomain d n → (Fin n → ℝ) → NPointDomain d n →L[ℝ] ℂ :=
    fun q' τ => section43FourierLaplace_timeIntegrandFDerivCLM d n Fpull q' τ
  rcases section43FourierLaplace_timeIntegrandFDerivCLM_local_bound_of_compact
    d n f hf_ord hf_compact q with ⟨bound, hbound_int, hbound⟩
  have hs : Metric.closedBall q (1 : ℝ) ∈ 𝓝 q :=
    Metric.closedBall_mem_nhds q zero_lt_one
  have hF_meas : ∀ᶠ q' in 𝓝 q, AEStronglyMeasurable (Fint q') := by
    exact Filter.Eventually.of_forall fun q' =>
      (continuous_section43FourierLaplace_timeIntegrand
        d n Fpull q').aestronglyMeasurable
  have hF_int : Integrable (Fint q) := by
    simpa [Fint, Fpull] using
      integrable_section43FourierLaplace_timeIntegrand_of_compact
        d n f hf_ord hf_compact q
  have hFderiv_meas : AEStronglyMeasurable (Fderiv q) := by
    exact (continuous_section43FourierLaplace_timeIntegrandFDerivCLM
      (d := d) (n := n) Fpull q).aestronglyMeasurable
  have hdiff : ∀ᵐ τ : Fin n → ℝ, ∀ q' ∈ Metric.closedBall q (1 : ℝ),
      HasFDerivAt (Fint · τ) (Fderiv q' τ) q' := by
    filter_upwards with τ q' _hq'
    simpa [Fint, Fderiv, Fpull] using
      hasFDerivAt_section43FourierLaplace_timeIntegrand
        d n Fpull q' τ
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume)
      (F := Fint) (F' := Fderiv) (x₀ := q)
      (s := Metric.closedBall q (1 : ℝ)) (bound := bound)
      hs hF_meas hF_int hFderiv_meas hbound hbound_int hdiff
  simpa [section43FourierLaplaceIntegral,
    section43FourierLaplaceIntegral_fderivCandidate, Fint, Fderiv, Fpull] using hmain

/-- On time slices above a strict support margin, the Laplace exponential gains
uniform damping by the total positive-energy time. -/
theorem norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (τ : Fin n → ℝ) {δ : ℝ}
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (hτ : ∀ i : Fin n, δ ≤ τ i) :
    ‖Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))‖ ≤
      Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hsum_ge :
      δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k ≤
        ∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hτ k) (by
        simpa [section43QTime, nPointTimeSpatialCLE] using hq k)
  have hre :
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))).re =
        -(∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k) := by
    simp
  rw [hre]
  exact neg_le_neg hsum_ge

/-- The strict ordered-support margin gives the Section 4.3 time integrand an
exponential positive-energy damping factor. -/
theorem norm_section43FourierLaplace_timeIntegrand_le_exp_neg_margin_sum
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) :
    ‖Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q)‖ ≤
      Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k)) *
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
  by_cases hlt : ∃ i : Fin n, τ i < δ
  · have hF_zero :
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q) = 0 := by
      exact partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
        d n f hf_ord hδ_supp τ (section43QSpatial (d := d) (n := n) q) hlt
    simp [hF_zero]
  · have hτ : ∀ i : Fin n, δ ≤ τ i := by
      intro i
      exact le_of_not_gt fun hi => hlt ⟨i, hi⟩
    have hE_le :=
      norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
        d n q τ hq hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hE_le (norm_nonneg _)

/-- Positive-energy bound for the time-derivative part of the pointwise
first-derivative CLM. -/
theorem norm_section43FourierLaplace_timeDerivativeSum_le_exp_margin_sum
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    {δ : ℝ}
    (q m : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) (hτ : ∀ i : Fin n, δ ≤ τ i) :
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let E : ℂ :=
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
    let P : ℂ :=
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q)
    ‖∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * E * P)‖ ≤
      ∑ k : Fin n,
        (‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖) *
          (‖τ‖ * A * ‖P‖) := by
  intro A E P
  have hE :
      ‖E‖ ≤ A := by
    simpa [A, E] using
      norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
        d n q τ hq hτ
  calc
    ‖∑ k : Fin n,
        (section43QTime (d := d) (n := n) m k : ℝ) •
          (-(τ k : ℂ) * E * P)‖
        ≤ ∑ k : Fin n,
            ‖(section43QTime (d := d) (n := n) m k : ℝ) •
              (-(τ k : ℂ) * E * P)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ k : Fin n,
        (‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖) *
          (‖τ‖ * A * ‖P‖) := by
          refine Finset.sum_le_sum fun k _hk => ?_
          have hm := abs_section43QTime_coord_le_opNorm d n m k
          have hτk : |τ k| ≤ ‖τ‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm τ k
          calc
            ‖(section43QTime (d := d) (n := n) m k : ℝ) •
                (-(τ k : ℂ) * E * P)‖ =
                |section43QTime (d := d) (n := n) m k| *
                  (|τ k| * ‖E‖ * ‖P‖) := by
                  simp [Complex.norm_real, Real.norm_eq_abs,
                    mul_assoc, mul_left_comm]
            _ ≤ (‖((ContinuousLinearMap.proj
                  (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
                  (section43QTimeCLM d n))‖ * ‖m‖) *
                (‖τ‖ * A * ‖P‖) := by
                  gcongr

/-- Positive-energy bound for the spatial-derivative part of the pointwise
first-derivative CLM. -/
theorem norm_section43FourierLaplace_spatialDerivativeTerm_le_exp_margin_sum
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    {δ : ℝ}
    (q m : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) (hτ : ∀ i : Fin n, δ ≤ τ i) :
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let E : ℂ :=
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    ‖E •
      (fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ)
        (section43QSpatial (d := d) (n := n) m)‖ ≤
      A *
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
  intro A E ξ
  have hE :
      ‖E‖ ≤ A := by
    simpa [A, E] using
      norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
        d n q τ hq hτ
  let D : ℂ :=
    (fderiv ℝ
      (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
      ξ)
      (section43QSpatial (d := d) (n := n) m)
  have hD :
      ‖D‖ ≤
        ∑ i : Fin n × Fin d,
          |section43QSpatial (d := d) (n := n) m i| *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
    simpa [D] using
      norm_fderiv_partialFourierSpatial_fun_spatial_apply_le_sum_multiplierTransport
        d n F τ ξ (section43QSpatial (d := d) (n := n) m)
  have hD_coord :
      ∑ i : Fin n × Fin d,
          |section43QSpatial (d := d) (n := n) m i| *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ ≤
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
    refine Finset.sum_le_sum fun i _hi => ?_
    have hi := abs_section43QSpatial_coord_le_opNorm d n m i
    exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
  calc
    ‖E •
      (fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ)
        (section43QSpatial (d := d) (n := n) m)‖ =
        ‖E‖ * ‖D‖ := by
          simp [D]
    _ ≤ A * ‖D‖ := by
          exact mul_le_mul_of_nonneg_right hE (norm_nonneg D)
    _ ≤ A *
        ∑ i : Fin n × Fin d,
          |section43QSpatial (d := d) (n := n) m i| *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          exact mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le
    _ ≤ A *
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          exact mul_le_mul_of_nonneg_left hD_coord (Real.exp_pos _).le

/-- Pointwise positive-energy bound for the explicit first-derivative CLM
applied to one ambient direction. -/
theorem norm_section43FourierLaplace_timeIntegrandFDerivCLM_apply_le_exp_margin_sum
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    {δ : ℝ}
    (q m : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) (hτ : ∀ i : Fin n, δ ≤ τ i) :
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    let P : ℂ :=
      partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m‖ ≤
      (∑ k : Fin n,
        (‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖) *
          (‖τ‖ * A * ‖P‖)) +
      A *
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
  intro A ξ P
  let E : ℂ :=
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let T : ℂ :=
    ∑ k : Fin n,
      (section43QTime (d := d) (n := n) m k : ℝ) •
        (-(τ k : ℂ) * E * P)
  let S : ℂ :=
    E •
      (fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ)
        (section43QSpatial (d := d) (n := n) m)
  have happly :
      section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m = T + S := by
    simp [T, S, E, P, ξ, section43FourierLaplace_timeIntegrandFDerivCLM_apply]
  have hT :
      ‖T‖ ≤
      ∑ k : Fin n,
        (‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖) *
          (‖τ‖ * A * ‖P‖) := by
    simpa [T, E, P, A] using
      norm_section43FourierLaplace_timeDerivativeSum_le_exp_margin_sum
        d n F q m hq τ hτ
  have hS :
      ‖S‖ ≤
      A *
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
    simpa [S, E, A, ξ] using
      norm_section43FourierLaplace_spatialDerivativeTerm_le_exp_margin_sum
        d n F q m hq τ hτ
  calc
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m‖ =
        ‖T + S‖ := by rw [happly]
    _ ≤ ‖T‖ + ‖S‖ := norm_add_le T S
    _ ≤
      (∑ k : Fin n,
        (‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ * ‖m‖) *
          (‖τ‖ * A * ‖P‖)) +
      A *
        ∑ i : Fin n × Fin d,
          (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ * ‖m‖) *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          exact add_le_add hT hS

set_option backward.isDefEq.respectTransparency false in
/-- Operator-norm version of the pointwise positive-energy bound for the
explicit first-derivative CLM. -/
theorem norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_exp_margin_sum
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    {δ : ℝ}
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) (hτ : ∀ i : Fin n, δ ≤ τ i) :
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    let P : ℂ :=
      partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ‖ ≤
      (∑ k : Fin n,
        ‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ *
          (‖τ‖ * A * ‖P‖)) +
      A *
        ∑ i : Fin n × Fin d,
          ‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
  intro A ξ P
  let Tcoef : Fin n → ℝ := fun k =>
    ‖((ContinuousLinearMap.proj
      (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
      (section43QTimeCLM d n))‖
  let Scoef : Fin n × Fin d → ℝ := fun i =>
    ‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (section43QSpatialCLM d n))‖
  let M : ℝ :=
    (∑ k : Fin n, Tcoef k * (‖τ‖ * A * ‖P‖)) +
    A *
      ∑ i : Fin n × Fin d, Scoef i *
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ContinuousLinearMap.opNorm_le_bound
    (section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ) hM_nonneg ?_
  intro m
  have happly :=
    norm_section43FourierLaplace_timeIntegrandFDerivCLM_apply_le_exp_margin_sum
      d n F q m hq τ hτ
  calc
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m‖
        ≤ (∑ k : Fin n,
            (‖((ContinuousLinearMap.proj
              (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
              (section43QTimeCLM d n))‖ * ‖m‖) *
              (‖τ‖ * A * ‖P‖)) +
          A *
            ∑ i : Fin n × Fin d,
              (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
                (section43QSpatialCLM d n))‖ * ‖m‖) *
                ‖partialFourierSpatial_fun (d := d) (n := n)
                  (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          simpa [A, ξ, P] using happly
    _ = M * ‖m‖ := by
          have htime :
              (∑ k : Fin n, (Tcoef k * ‖m‖) * (‖τ‖ * A * ‖P‖)) =
                (∑ k : Fin n, Tcoef k * (‖τ‖ * A * ‖P‖)) * ‖m‖ := by
            calc
              (∑ k : Fin n, (Tcoef k * ‖m‖) * (‖τ‖ * A * ‖P‖)) =
                  ∑ k : Fin n, (Tcoef k * (‖τ‖ * A * ‖P‖)) * ‖m‖ := by
                    refine Finset.sum_congr rfl ?_
                    intro k _hk
                    ring
              _ = (∑ k : Fin n, Tcoef k * (‖τ‖ * A * ‖P‖)) * ‖m‖ := by
                    rw [Finset.sum_mul]
          have hspace :
              A *
                (∑ i : Fin n × Fin d,
                  (Scoef i * ‖m‖) *
                    ‖partialFourierSpatial_fun (d := d) (n := n)
                      (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) =
                (A *
                  ∑ i : Fin n × Fin d,
                    Scoef i *
                      ‖partialFourierSpatial_fun (d := d) (n := n)
                        (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) * ‖m‖ := by
            have hsum :
                (∑ i : Fin n × Fin d,
                  (Scoef i * ‖m‖) *
                    ‖partialFourierSpatial_fun (d := d) (n := n)
                      (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) =
                    (∑ i : Fin n × Fin d,
                      Scoef i *
                        ‖partialFourierSpatial_fun (d := d) (n := n)
                          (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) * ‖m‖ := by
              calc
                (∑ i : Fin n × Fin d,
                  (Scoef i * ‖m‖) *
                    ‖partialFourierSpatial_fun (d := d) (n := n)
                      (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) =
                    ∑ i : Fin n × Fin d,
                      (Scoef i *
                        ‖partialFourierSpatial_fun (d := d) (n := n)
                          (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) * ‖m‖ := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      ring
                _ = (∑ i : Fin n × Fin d,
                      Scoef i *
                        ‖partialFourierSpatial_fun (d := d) (n := n)
                          (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) * ‖m‖ := by
                      rw [Finset.sum_mul]
            rw [hsum]
            ring
          rw [show
              (∑ k : Fin n,
                (‖((ContinuousLinearMap.proj
                  (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
                  (section43QTimeCLM d n))‖ * ‖m‖) *
                  (‖τ‖ * A * ‖P‖)) =
                (∑ k : Fin n, (Tcoef k * ‖m‖) * (‖τ‖ * A * ‖P‖)) by
                simp [Tcoef]]
          rw [show
              (∑ i : Fin n × Fin d,
                (‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
                  (section43QSpatialCLM d n))‖ * ‖m‖) *
                  ‖partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) =
                (∑ i : Fin n × Fin d,
                  (Scoef i * ‖m‖) *
                    ‖partialFourierSpatial_fun (d := d) (n := n)
                      (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) by
                simp [Scoef]]
          rw [htime, hspace]
          ring

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise operator-norm derivative bound for the OS-I pullback input, with
the lower-margin branch closed by support vanishing. -/
theorem norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_exp_margin_sum_of_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) :
    let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    let P : ℂ :=
      partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ‖ ≤
      (∑ k : Fin n,
        ‖((ContinuousLinearMap.proj
          (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n))‖ *
          (‖τ‖ * A * ‖P‖)) +
      A *
        ∑ i : Fin n × Fin d,
          ‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
            (section43QSpatialCLM d n))‖ *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
  intro F A ξ P
  by_cases hlow : ∃ i : Fin n, τ i < δ
  · have hzero :=
      section43FourierLaplace_timeIntegrandFDerivCLM_eq_zero_of_exists_time_lt_margin
        d n f hf_ord hδ_supp q τ hlow
    rw [hzero, norm_zero]
    positivity
  · have hτ : ∀ i : Fin n, δ ≤ τ i := by
      intro i
      exact le_of_not_gt fun hi => hlow ⟨i, hi⟩
    simpa [F, A, ξ, P] using
      norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_exp_margin_sum
        d n F q hq τ hτ

/-- Base norm estimate for the Section 4.3 Fourier-Laplace integral: the strict
ordered-support margin factors out as exponential positive-energy damping. -/
theorem section43FourierLaplaceIntegral_norm_le_exp_margin_integral
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
      ∫ τ : Fin n → ℝ,
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
  let E : (Fin n → ℝ) → ℂ := fun τ =>
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
      (τ, section43QSpatial (d := d) (n := n) q)
  let A : ℝ := Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k))
  have hF_int : Integrable F (volume : Measure (Fin n → ℝ)) := by
    simpa [F] using
      integrable_partialFourierSpatial_timeSlice
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (section43QSpatial (d := d) (n := n) q)
  have hAF_int : Integrable (fun τ : Fin n → ℝ => A * ‖F τ‖)
      (volume : Measure (Fin n → ℝ)) := by
    exact hF_int.norm.const_mul A
  have hpoint : ∀ τ : Fin n → ℝ, ‖E τ * F τ‖ ≤ A * ‖F τ‖ := by
    intro τ
    simpa [E, F, A] using
      norm_section43FourierLaplace_timeIntegrand_le_exp_neg_margin_sum
        d n f hf_ord hδ_supp q hq τ
  calc
    ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ = ‖∫ τ : Fin n → ℝ, E τ * F τ‖ := by
      simp [section43FourierLaplaceIntegral, E, F]
    _ ≤ ∫ τ : Fin n → ℝ, ‖E τ * F τ‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ τ : Fin n → ℝ, A * ‖F τ‖ := by
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun τ => norm_nonneg (E τ * F τ))
        hAF_int
        (Filter.Eventually.of_forall hpoint)
    _ = A * ∫ τ : Fin n → ℝ, ‖F τ‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
      ∫ τ : Fin n → ℝ,
        ‖partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)‖ := by
      rfl

/-- The Euclidean norm is bounded by the sum of absolute coordinate values. -/
theorem euclidean_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (ξ : EuclideanSpace ℝ ι) :
    ‖ξ‖ ≤ ∑ i : ι, ‖ξ i‖ := by
  have hsum_nonneg : 0 ≤ ∑ i : ι, ‖ξ i‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg ξ) hsum_nonneg).mp
  calc
    ‖ξ‖ ^ 2 = ∑ i : ι, ‖ξ i‖ ^ 2 := EuclideanSpace.norm_sq_eq ξ
    _ ≤ (∑ i : ι, ‖ξ i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i : ι => ‖ξ i‖)
        (fun i _hi => norm_nonneg _)

/-- The finite sup norm on real-valued functions is bounded by the sum of
absolute coordinate values. -/
theorem pi_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    ‖x‖ ≤ ∑ i : ι, ‖x i‖ := by
  classical
  by_cases hne : (Finset.univ : Finset ι).Nonempty
  · obtain ⟨i, hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset ι)) hne
        (fun j : ι => ‖x j‖₊)
    have hnorm_eq : ‖x‖ = ‖x i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun y : NNReal => (y : ℝ)) hi_sup
    rw [hnorm_eq]
    exact Finset.single_le_sum (fun j _hj => norm_nonneg (x j)) hi
  · have hempty : (Finset.univ : Finset ι) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [Pi.norm_def]
    simp [hempty]

/-- On the nonnegative orthant, the finite sup norm is bounded by the sum of
coordinates. -/
theorem pi_norm_le_sum_of_nonneg {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∀ i : ι, 0 ≤ x i) :
    ‖x‖ ≤ ∑ i : ι, x i := by
  calc
    ‖x‖ ≤ ∑ i : ι, ‖x i‖ := pi_norm_le_sum_norm x
    _ = ∑ i : ι, x i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Real.norm_of_nonneg (hx i)

/-- Version of `euclidean_norm_le_sum_norm` with a dummy constant coordinate,
suited to later finite-power comparisons for `(1 + ‖ξ‖)^r`. -/
theorem one_add_euclidean_norm_le_sum_option_norm {ι : Type*} [Fintype ι]
    (ξ : EuclideanSpace ℝ ι) :
    1 + ‖ξ‖ ≤
      ∑ a : Option ι, match a with | none => (1 : ℝ) | some i => ‖ξ i‖ := by
  calc
    1 + ‖ξ‖ ≤ 1 + ∑ i : ι, ‖ξ i‖ := by
      nlinarith [euclidean_norm_le_sum_norm ξ]
    _ = ∑ a : Option ι, match a with | none => (1 : ℝ) | some i => ‖ξ i‖ := by
      simp

/-- Finite-coordinate power comparison for the Euclidean rapid-decay weight.

This turns the single weight `(1 + ‖ξ‖)^r` into a finite sum of coordinate
powers, with a dimension-only constant. -/
theorem one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
    {ι : Type*} [Fintype ι] (r : ℕ)
    (ξ : EuclideanSpace ℝ ι) :
    (1 + ‖ξ‖) ^ r ≤
      (Fintype.card (Option ι) : ℝ) ^ r *
        ∑ a : Option ι,
          (match a with | none => (1 : ℝ) | some i => ‖ξ i‖) ^ r := by
  classical
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  have hw_nonneg : ∀ a : Option ι, 0 ≤ w a := by
    intro a
    cases a <;> simp [w]
  have hbase : 1 + ‖ξ‖ ≤ ∑ a : Option ι, w a := by
    simpa [w] using one_add_euclidean_norm_le_sum_option_norm (ι := ι) ξ
  have hcard_ge_one : 1 ≤ (Fintype.card (Option ι) : ℝ) := by
    exact_mod_cast
      (Nat.succ_le_of_lt
        (Fintype.card_pos_iff.mpr ⟨(none : Option ι)⟩))
  cases r with
  | zero =>
      simp
  | succ m =>
      have hpow_base :
          (1 + ‖ξ‖) ^ (m + 1) ≤ (∑ a : Option ι, w a) ^ (m + 1) := by
        exact pow_le_pow_left₀ (by positivity) hbase (m + 1)
      have hjensen :
          (∑ a : Option ι, w a) ^ (m + 1) ≤
            (Fintype.card (Option ι) : ℝ) ^ m *
              ∑ a : Option ι, w a ^ (m + 1) := by
        simpa using
          (pow_sum_le_card_mul_sum_pow
            (s := (Finset.univ : Finset (Option ι))) (f := w)
            (fun a _ha => hw_nonneg a) m)
      have hcard_pow_le :
          (Fintype.card (Option ι) : ℝ) ^ m ≤
            (Fintype.card (Option ι) : ℝ) ^ (m + 1) := by
        calc
          (Fintype.card (Option ι) : ℝ) ^ m =
              (Fintype.card (Option ι) : ℝ) ^ m * 1 := by
                rw [mul_one]
          _ ≤ (Fintype.card (Option ι) : ℝ) ^ m *
              (Fintype.card (Option ι) : ℝ) := by
                exact mul_le_mul_of_nonneg_left hcard_ge_one (by positivity)
          _ = (Fintype.card (Option ι) : ℝ) ^ (m + 1) := by
                rw [pow_succ]
      have hsum_nonneg : 0 ≤ ∑ a : Option ι, w a ^ (m + 1) := by
        exact Finset.sum_nonneg fun a _ha => pow_nonneg (hw_nonneg a) (m + 1)
      calc
        (1 + ‖ξ‖) ^ (m + 1) ≤ (∑ a : Option ι, w a) ^ (m + 1) := hpow_base
        _ ≤ (Fintype.card (Option ι) : ℝ) ^ m *
            ∑ a : Option ι, w a ^ (m + 1) := hjensen
        _ ≤ (Fintype.card (Option ι) : ℝ) ^ (m + 1) *
            ∑ a : Option ι, w a ^ (m + 1) := by
              exact mul_le_mul_of_nonneg_right hcard_pow_le hsum_nonneg

/-- Uniform polynomial time decay of the partial spatial Fourier transform.

The older `exists_normPow_bound_partialFourierSpatial_timeSlice` exposes the
same estimate after fixing the spatial frequency.  This version keeps the
constant independent of that frequency, which is the form needed for
dominated-convergence estimates in the Fourier-Laplace witness construction. -/
theorem exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d)),
        ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  by_cases hK : K = 0
  · subst K
    refine ⟨C0, hC0_nonneg, ?_⟩
    intro τ ξ
    simpa using hC0 (τ, ξ)
  classical
  choose Ccoord hCcoord_nonneg hCcoord using
    fun i : Fin n =>
      exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
        (d := d) (n := n) f i K
  let Csum : ℝ := C0 + ∑ i : Fin n, Ccoord i
  refine ⟨Csum, add_nonneg hC0_nonneg (Finset.sum_nonneg fun i _ => hCcoord_nonneg i), ?_⟩
  intro τ ξ
  by_cases hτnorm : ‖τ‖ = 0
  · have hpow : ‖τ‖ ^ K = 0 := by
      rw [hτnorm]
      exact zero_pow hK
    exact le_trans (by simp [hpow]) (add_nonneg hC0_nonneg
      (Finset.sum_nonneg fun i _ => hCcoord_nonneg i))
  · have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      by_contra hne
      have hempty : (Finset.univ : Finset (Fin n)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hnorm_zero : ‖τ‖ = 0 := by
        rw [Pi.norm_def]
        simp [hempty]
      exact hτnorm hnorm_zero
    obtain ⟨i, _hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n))) huniv_nonempty
        (fun j : Fin n => ‖τ j‖₊)
    have hnorm_eq : ‖τ‖ = ‖τ i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun x : NNReal => (x : ℝ)) hi_sup
    have hcoord := hCcoord i (τ, ξ)
    have hrewrite :
        ‖τ‖ ^ K *
            ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, hnorm_eq]
    calc
      ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := hrewrite
      _ ≤ Ccoord i := hcoord
      _ ≤ Csum := by
        have hi_le_sum : Ccoord i ≤ ∑ j : Fin n, Ccoord j :=
          Finset.single_le_sum (fun j _ => hCcoord_nonneg j) (Finset.mem_univ i)
        exact hi_le_sum.trans (by simp [Csum, hC0_nonneg])

/-- Uniform integrable domination for time slices of the partial spatial
Fourier transform. -/
theorem exists_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  let μ : Measure (Fin n → ℝ) := volume
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) f μ.integrablePower with
    ⟨C1, hC1_nonneg, hC1⟩
  let I : ℝ := ∫ τ : Fin n → ℝ, (1 + ‖τ‖) ^ (-(μ.integrablePower : ℝ))
  let C : ℝ := 2 ^ μ.integrablePower * I * (C0 + C1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => by positivity
  refine ⟨C, by positivity, ?_⟩
  intro ξ
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hbound0 : ∀ τ : Fin n → ℝ, ‖F τ‖ ≤ C0 := by
    intro τ
    simpa [F] using hC0 (τ, ξ)
  have hboundPow : ∀ τ : Fin n → ℝ,
      ‖τ‖ ^ (0 + μ.integrablePower) * ‖F τ‖ ≤ C1 := by
    intro τ
    simpa [F, Nat.zero_add] using hC1 τ ξ
  have hmain := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := μ) (f := F) (C₁ := C0) (C₂ := C1) (k := 0) hbound0 hboundPow
  simpa [F, μ, C, I, Nat.zero_add] using hmain

/-- Uniform time-moment integral control for time slices of the partial
spatial Fourier transform.  This is the derivative-ready version of
`exists_integral_norm_partialFourierSpatial_timeSlice_uniform`: time
derivatives of the Laplace exponential introduce powers of `τ`. -/
theorem exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  let μ : Measure (Fin n → ℝ) := volume
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) f (K + μ.integrablePower) with
    ⟨C1, hC1_nonneg, hC1⟩
  let I : ℝ := ∫ τ : Fin n → ℝ, (1 + ‖τ‖) ^ (-(μ.integrablePower : ℝ))
  let C : ℝ := 2 ^ μ.integrablePower * I * (C0 + C1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => by positivity
  refine ⟨C, by positivity, ?_⟩
  intro ξ
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hbound0 : ∀ τ : Fin n → ℝ, ‖F τ‖ ≤ C0 := by
    intro τ
    simpa [F] using hC0 (τ, ξ)
  have hboundPow : ∀ τ : Fin n → ℝ,
      ‖τ‖ ^ (K + μ.integrablePower) * ‖F τ‖ ≤ C1 := by
    intro τ
    simpa [F] using hC1 τ ξ
  have hmain := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := μ) (f := F) (C₁ := C0) (C₂ := C1) (k := K) hbound0 hboundPow
  simpa [F, μ, C, I] using hmain

/-- Fixed-spatial-frequency integrability of every polynomial time moment of
the partial spatial Fourier transform. -/
theorem integrable_timeMoment_norm_partialFourierSpatial_timeSlice
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (K : ℕ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖)
      (volume : Measure (Fin n → ℝ)) := by
  let μ : Measure (Fin n → ℝ) := volume
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hF_meas : AEStronglyMeasurable F μ := by
    simpa [F, μ] using
      (contDiff_partialFourierSpatial_fun_time
        (d := d) (n := n) f ξ).continuous.aestronglyMeasurable
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, _hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) f (K + μ.integrablePower) with
    ⟨C1, _hC1_nonneg, hC1⟩
  have hbase : ∀ τ : Fin n → ℝ, ‖F τ‖ ≤ C0 := by
    intro τ
    simpa [F] using hC0 (τ, ξ)
  have hpow : ∀ τ : Fin n → ℝ,
      ‖τ‖ ^ (K + μ.integrablePower) * ‖F τ‖ ≤ C1 := by
    intro τ
    simpa [F] using hC1 τ ξ
  simpa [F, μ] using
    (integrable_of_le_of_pow_mul_le
      (μ := μ) (f := F) (C₁ := C0) (C₂ := C1) (k := K)
      hbase hpow hF_meas)

/-- Uniform time-integral control after multiplying by a spatial coordinate
power.  This is the coordinatewise integration-by-parts estimate used for the
spatial rapid-decay half of the Fourier-Laplace witness construction. -/
theorem exists_spatialCoordPow_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (i : Fin n × Fin d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖((((ξ i : ℝ) : ℂ)) ^ k) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  induction k generalizing f with
  | zero =>
      rcases exists_integral_norm_partialFourierSpatial_timeSlice_uniform
          (d := d) (n := n) f with
        ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro ξ
      simpa using hbound ξ
  | succ k ih =>
      let c : ℂ := 2 * Real.pi * Complex.I
      let g : SchwartzNPoint d n :=
        ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
          (LineDeriv.lineDerivOp ((EuclideanSpace.single i (1 : ℝ), (0 : Fin n → ℝ)))
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      rcases ih g with ⟨C, hC_nonneg, hbound⟩
      have hc0 : c ≠ 0 := by
        have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
          exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
        exact mul_ne_zero htwoPi Complex.I_ne_zero
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      refine ⟨C / ‖c‖, by positivity, ?_⟩
      intro ξ
      let z : ℂ := ((ξ i : ℝ) : ℂ)
      have hpoint : ∀ τ : Fin n → ℝ,
          ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ‖c‖⁻¹ *
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
        intro τ
        have htransport :
            (c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ) =
              partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
          simpa [c, g, z] using
            partialFourierSpatial_fun_spatialCoord_eq_transport
              (d := d) (n := n) f i (τ, ξ)
        have hscaled_eq :
            ‖c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                (τ, ξ))‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          congr 1
          calc
            c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ))
                = (z ^ k) *
                    ((c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)) := by
                    simp [pow_succ', mul_assoc, mul_left_comm]
            _ = (z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
                    rw [htransport]
        have hscaled :
            ‖c‖ *
                ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                  (τ, ξ)‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          rw [← hscaled_eq]
          simp
        calc
          ‖(z ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
              ‖c‖⁻¹ * (‖c‖ *
                ‖(z ^ (k + 1)) *
                  partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖) := by
                field_simp [hcnorm.ne']
          _ = ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
                rw [hscaled]
      calc
        ∫ τ : Fin n → ℝ,
          ‖((((ξ i : ℝ) : ℂ)) ^ (k + 1)) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ∫ τ : Fin n → ℝ,
              ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              simpa [z] using hpoint τ
        _ = ‖c‖⁻¹ * ∫ τ : Fin n → ℝ,
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              rw [MeasureTheory.integral_const_mul]
        _ ≤ ‖c‖⁻¹ * C := by
              exact mul_le_mul_of_nonneg_left (hbound ξ) (inv_nonneg.mpr hcnorm.le)
        _ = C / ‖c‖ := by
              rw [div_eq_mul_inv, mul_comm]

/-- Uniform time-moment integral control after multiplying by a spatial
coordinate power.  This combines the derivative-ready time moments with the
coordinatewise spatial integration-by-parts estimate. -/
theorem exists_spatialCoordPow_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (i : Fin n × Fin d) (k K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖((((ξ i : ℝ) : ℂ)) ^ k) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  induction k generalizing f with
  | zero =>
      rcases exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
          (d := d) (n := n) f K with
        ⟨C, hC, hbound⟩
      refine ⟨C, hC, ?_⟩
      intro ξ
      simpa using hbound ξ
  | succ k ih =>
      let c : ℂ := 2 * Real.pi * Complex.I
      let g : SchwartzNPoint d n :=
        ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
          (LineDeriv.lineDerivOp ((EuclideanSpace.single i (1 : ℝ), (0 : Fin n → ℝ)))
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      rcases ih g with ⟨C, hC_nonneg, hbound⟩
      have hc0 : c ≠ 0 := by
        have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
          exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
        exact mul_ne_zero htwoPi Complex.I_ne_zero
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      refine ⟨C / ‖c‖, by positivity, ?_⟩
      intro ξ
      let z : ℂ := ((ξ i : ℝ) : ℂ)
      have hpoint : ∀ τ : Fin n → ℝ,
          ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ‖c‖⁻¹ *
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
        intro τ
        have htransport :
            (c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ) =
              partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
          simpa [c, g, z] using
            partialFourierSpatial_fun_spatialCoord_eq_transport
              (d := d) (n := n) f i (τ, ξ)
        have hscaled_eq :
            ‖c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                (τ, ξ))‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          congr 1
          calc
            c * ((z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ))
                = (z ^ k) *
                    ((c * z) * partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)) := by
                    simp [pow_succ', mul_assoc, mul_left_comm]
            _ = (z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ) := by
                    rw [htransport]
        have hscaled :
            ‖c‖ *
                ‖(z ^ (k + 1)) * partialFourierSpatial_fun (d := d) (n := n) f
                  (τ, ξ)‖ =
              ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
          rw [← hscaled_eq]
          simp
        calc
          ‖(z ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
              ‖c‖⁻¹ * (‖c‖ *
                ‖(z ^ (k + 1)) *
                  partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖) := by
                field_simp [hcnorm.ne']
          _ = ‖c‖⁻¹ *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
                rw [hscaled]
      calc
        ∫ τ : Fin n → ℝ,
          ‖τ‖ ^ K *
            ‖((((ξ i : ℝ) : ℂ)) ^ (k + 1)) *
              partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
            ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                (‖c‖⁻¹ *
                  ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              simpa [z] using congrArg (fun y : ℝ => ‖τ‖ ^ K * y) (hpoint τ)
        _ = ∫ τ : Fin n → ℝ,
              ‖c‖⁻¹ *
                (‖τ‖ ^ K *
                  ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with τ
              ring
        _ = ‖c‖⁻¹ * ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                ‖(z ^ k) * partialFourierSpatial_fun (d := d) (n := n) g (τ, ξ)‖ := by
              rw [MeasureTheory.integral_const_mul]
        _ ≤ ‖c‖⁻¹ * C := by
              exact mul_le_mul_of_nonneg_left (hbound ξ) (inv_nonneg.mpr hcnorm.le)
        _ = C / ‖c‖ := by
              rw [div_eq_mul_inv, mul_comm]

/-- Spatial rapid decay of every finite time-moment integral of the partial
spatial Fourier transform.  This is the main domination estimate needed when
time derivatives of the Fourier-Laplace integrand introduce powers of `τ`. -/
theorem section43PartialFourier_timeMomentIntegral_spatialRapid
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (K r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        (1 + ‖ξ‖) ^ r *
          ∫ τ : Fin n → ℝ,
            ‖τ‖ ^ K *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ ≤ C := by
  classical
  let ι : Type := Fin n × Fin d
  rcases exists_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) F K with
    ⟨C0, hC0_nonneg, hC0_bound⟩
  choose Ccoord hCcoord_nonneg hCcoord_bound using
    fun i : ι =>
      exists_spatialCoordPow_timeMoment_integral_norm_partialFourierSpatial_timeSlice_uniform
        (d := d) (n := n) F i r K
  let C : ℝ :=
    (Fintype.card (Option ι) : ℝ) ^ r *
      ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i
  have hsumC_nonneg :
      0 ≤ ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i := by
    exact Finset.sum_nonneg fun a _ha => by
      cases a <;> simp [hC0_nonneg, hCcoord_nonneg]
  refine ⟨C, mul_nonneg (by positivity) hsumC_nonneg, ?_⟩
  intro ξ
  let A : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖τ‖ ^ K *
        ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  let B : Option ι → ℝ := fun a =>
    match a with | none => A | some i => ‖ξ i‖ ^ r * A
  let D : Option ι → ℝ := fun a =>
    match a with | none => C0 | some i => Ccoord i
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun τ =>
      mul_nonneg (pow_nonneg (norm_nonneg τ) K) (norm_nonneg _)
  have hpow :
      (1 + ‖ξ‖) ^ r ≤
        (Fintype.card (Option ι) : ℝ) ^ r *
          ∑ a : Option ι, w a ^ r := by
    simpa [ι, w] using
      one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
        (ι := ι) r ξ
  have hsum_mul :
      (∑ a : Option ι, w a ^ r) * A = ∑ a : Option ι, B a := by
    rw [Finset.sum_mul]
    simp [B, w]
  have hB_le_D : ∀ a : Option ι, B a ≤ D a := by
    intro a
    cases a with
    | none =>
        simpa [B, D, A] using hC0_bound ξ
    | some i =>
        have hprod_eq :
            ‖ξ i‖ ^ r * A =
              ∫ τ : Fin n → ℝ,
                ‖τ‖ ^ K *
                  ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
          calc
            ‖ξ i‖ ^ r * A =
                ∫ τ : Fin n → ℝ,
                  ‖ξ i‖ ^ r *
                    (‖τ‖ ^ K *
                      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) := by
                  dsimp [A]
                  rw [MeasureTheory.integral_const_mul]
            _ = ∫ τ : Fin n → ℝ,
                ‖τ‖ ^ K *
                  ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with τ
                  rw [norm_mul, norm_pow, Complex.norm_real]
                  ring
        calc
          B (some i) = ‖ξ i‖ ^ r * A := by
            simp [B]
          _ = ∫ τ : Fin n → ℝ,
              ‖τ‖ ^ K *
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := hprod_eq
          _ ≤ Ccoord i := hCcoord_bound i ξ
          _ = D (some i) := by
            simp [D]
  have hsum_le : ∑ a : Option ι, B a ≤ ∑ a : Option ι, D a :=
    Finset.sum_le_sum fun a _ha => hB_le_D a
  calc
    (1 + ‖ξ‖) ^ r * A
        ≤ ((Fintype.card (Option ι) : ℝ) ^ r *
            ∑ a : Option ι, w a ^ r) * A := by
              exact mul_le_mul_of_nonneg_right hpow hA_nonneg
    _ = (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, B a := by
              rw [mul_assoc, hsum_mul]
    _ ≤ (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, D a := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = C := by
              simp [C, D]

/-- Time-coordinate operator norm coefficient in the first derivative bound. -/
noncomputable def section43QTimeCoordOpNorm
    (d n : ℕ) [NeZero d] (k : Fin n) : ℝ :=
  ‖((ContinuousLinearMap.proj
    (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
    (section43QTimeCLM d n))‖

/-- Spatial-coordinate operator norm coefficient in the first derivative
bound. -/
noncomputable def section43QSpatialCoordOpNorm
    (d n : ℕ) [NeZero d] (i : Fin n × Fin d) : ℝ :=
  ‖((EuclideanSpace.proj (𝕜 := ℝ) i).comp
    (section43QSpatialCLM d n))‖

/-- Time part of the pointwise first-derivative norm majorant. -/
noncomputable def section43FourierLaplace_timeDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (τ : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n,
    section43QTimeCoordOpNorm d n k *
      (A * (‖τ‖ *
        ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖))

/-- Spatial part of the pointwise first-derivative norm majorant. -/
noncomputable def section43FourierLaplace_spatialDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (τ : Fin n → ℝ) : ℝ :=
  A * ∑ i : Fin n × Fin d,
    section43QSpatialCoordOpNorm d n i *
      ‖partialFourierSpatial_fun (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖

/-- Full pointwise first-derivative norm majorant. -/
noncomputable def section43FourierLaplace_fderivNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (τ : Fin n → ℝ) : ℝ :=
  section43FourierLaplace_timeDerivativeNormMajorant d n F A ξ τ +
    section43FourierLaplace_spatialDerivativeNormMajorant d n F A ξ τ

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise derivative-CLM norm estimate, packaged with the finite-sum
majorant used for integration. -/
theorem norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_fderivNormMajorant_of_orderedSupport
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) :
    let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ‖ ≤
      section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
  intro F A ξ
  have h :=
    norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_exp_margin_sum_of_orderedSupport
      d n f hf_ord hδ_supp q hq τ
  have hraw :
      ‖section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ‖ ≤
        (∑ k : Fin n,
          section43QTimeCoordOpNorm d n k *
            (‖τ‖ * A *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖)) +
        A * ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
    simpa [F, A, ξ, section43QTimeCoordOpNorm, section43QSpatialCoordOpNorm]
      using h
  have hrhs :
      (∑ k : Fin n,
          section43QTimeCoordOpNorm d n k *
            (‖τ‖ * A *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖)) +
        A * ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ =
      section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
    simp only [section43FourierLaplace_fderivNormMajorant,
      section43FourierLaplace_timeDerivativeNormMajorant,
      section43FourierLaplace_spatialDerivativeNormMajorant]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _hk
    ring
  exact hraw.trans_eq hrhs

/-- Integrability of the time part of the derivative norm majorant. -/
theorem integrable_section43FourierLaplace_timeDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        section43FourierLaplace_timeDerivativeNormMajorant d n F A ξ τ)
      (volume : Measure (Fin n → ℝ)) := by
  let baseNorm : (Fin n → ℝ) → ℝ := fun τ =>
    ‖τ‖ *
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  have hbase_int : Integrable baseNorm (volume : Measure (Fin n → ℝ)) := by
    simpa [baseNorm, pow_one] using
      integrable_timeMoment_norm_partialFourierSpatial_timeSlice
        (d := d) (n := n) F 1 ξ
  dsimp [section43FourierLaplace_timeDerivativeNormMajorant]
  refine integrable_finset_sum _ ?_
  intro k _hk
  simpa [baseNorm, mul_assoc, mul_left_comm, mul_comm] using
    hbase_int.const_mul (section43QTimeCoordOpNorm d n k * A)

/-- Integrability of the spatial part of the derivative norm majorant. -/
theorem integrable_section43FourierLaplace_spatialDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        section43FourierLaplace_spatialDerivativeNormMajorant d n F A ξ τ)
      (volume : Measure (Fin n → ℝ)) := by
  have hspace_int : ∀ i : Fin n × Fin d,
      Integrable
        (fun τ : Fin n → ℝ =>
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)
        (volume : Measure (Fin n → ℝ)) := by
    intro i
    simpa using
      (integrable_partialFourierSpatial_timeSlice
        (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) ξ).norm
  dsimp [section43FourierLaplace_spatialDerivativeNormMajorant]
  refine (integrable_finset_sum _ ?_).const_mul A
  intro i _hi
  simpa using (hspace_int i).const_mul (section43QSpatialCoordOpNorm d n i)

/-- Integrability of the full derivative norm majorant. -/
theorem integrable_section43FourierLaplace_fderivNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        section43FourierLaplace_fderivNormMajorant d n F A ξ τ)
      (volume : Measure (Fin n → ℝ)) := by
  simpa [section43FourierLaplace_fderivNormMajorant] using
    (integrable_section43FourierLaplace_timeDerivativeNormMajorant
      (d := d) (n := n) F A ξ).add
      (integrable_section43FourierLaplace_spatialDerivativeNormMajorant
        (d := d) (n := n) F A ξ)

/-- Integral evaluation for the time part of the derivative norm majorant. -/
theorem integral_section43FourierLaplace_timeDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_timeDerivativeNormMajorant d n F A ξ τ) =
      A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖)) := by
  let baseNorm : (Fin n → ℝ) → ℝ := fun τ =>
    ‖τ‖ *
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  have hbase_int : Integrable baseNorm (volume : Measure (Fin n → ℝ)) := by
    simpa [baseNorm, pow_one] using
      integrable_timeMoment_norm_partialFourierSpatial_timeSlice
        (d := d) (n := n) F 1 ξ
  calc
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_timeDerivativeNormMajorant d n F A ξ τ) =
        ∑ k : Fin n,
          ∫ τ : Fin n → ℝ,
            section43QTimeCoordOpNorm d n k * (A * baseNorm τ) := by
          dsimp [section43FourierLaplace_timeDerivativeNormMajorant, baseNorm]
          rw [MeasureTheory.integral_finset_sum]
          intro k _hk
          simpa [baseNorm, mul_assoc, mul_left_comm, mul_comm] using
            hbase_int.const_mul (section43QTimeCoordOpNorm d n k * A)
    _ = ∑ k : Fin n,
          section43QTimeCoordOpNorm d n k *
            (A * ∫ τ : Fin n → ℝ, baseNorm τ) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          calc
            (∫ τ : Fin n → ℝ,
                section43QTimeCoordOpNorm d n k * (A * baseNorm τ)) =
                ∫ τ : Fin n → ℝ,
                  (section43QTimeCoordOpNorm d n k * A) * baseNorm τ := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with τ
                  ring
            _ = (section43QTimeCoordOpNorm d n k * A) *
                  ∫ τ : Fin n → ℝ, baseNorm τ := by
                  rw [MeasureTheory.integral_const_mul]
            _ = section43QTimeCoordOpNorm d n k *
                  (A * ∫ τ : Fin n → ℝ, baseNorm τ) := by
                  ring
    _ = (∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (A * ∫ τ : Fin n → ℝ, baseNorm τ) := by
          rw [Finset.sum_mul]
    _ = A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ, baseNorm τ)) := by
          ring

/-- Integral evaluation for the spatial part of the derivative norm majorant. -/
theorem integral_section43FourierLaplace_spatialDerivativeNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_spatialDerivativeNormMajorant d n F A ξ τ) =
      A * ∑ i : Fin n × Fin d,
        section43QSpatialCoordOpNorm d n i *
          (∫ τ : Fin n → ℝ,
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) := by
  have hspace_int : ∀ i : Fin n × Fin d,
      Integrable
        (fun τ : Fin n → ℝ =>
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)
        (volume : Measure (Fin n → ℝ)) := by
    intro i
    simpa using
      (integrable_partialFourierSpatial_timeSlice
        (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) ξ).norm
  calc
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_spatialDerivativeNormMajorant d n F A ξ τ) =
        ∫ τ : Fin n → ℝ,
          A * ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i *
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          rfl
    _ =
        A * ∫ τ : Fin n → ℝ,
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i *
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = A *
        (∑ i : Fin n × Fin d,
          ∫ τ : Fin n → ℝ,
            section43QSpatialCoordOpNorm d n i *
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) := by
          congr 1
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          simpa using
            (hspace_int i).const_mul (section43QSpatialCoordOpNorm d n i)
    _ = A * ∑ i : Fin n × Fin d,
        section43QSpatialCoordOpNorm d n i *
          (∫ τ : Fin n → ℝ,
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [MeasureTheory.integral_const_mul]

/-- Integral evaluation for the full derivative norm majorant. -/
theorem integral_section43FourierLaplace_fderivNormMajorant
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (A : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_fderivNormMajorant d n F A ξ τ) =
      A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
        ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            (∫ τ : Fin n → ℝ,
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)) := by
  have htime_int :=
    integrable_section43FourierLaplace_timeDerivativeNormMajorant
      (d := d) (n := n) F A ξ
  have hspace_int :=
    integrable_section43FourierLaplace_spatialDerivativeNormMajorant
      (d := d) (n := n) F A ξ
  calc
    (∫ τ : Fin n → ℝ,
      section43FourierLaplace_fderivNormMajorant d n F A ξ τ) =
        (∫ τ : Fin n → ℝ,
          section43FourierLaplace_timeDerivativeNormMajorant d n F A ξ τ) +
        ∫ τ : Fin n → ℝ,
          section43FourierLaplace_spatialDerivativeNormMajorant d n F A ξ τ := by
          dsimp [section43FourierLaplace_fderivNormMajorant]
          rw [MeasureTheory.integral_add htime_int hspace_int]
    _ = A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
        ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            (∫ τ : Fin n → ℝ,
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)) := by
          rw [integral_section43FourierLaplace_timeDerivativeNormMajorant,
            integral_section43FourierLaplace_spatialDerivativeNormMajorant]
          ring

set_option backward.isDefEq.respectTransparency false in
/-- The first-derivative candidate is bounded by the integral of the derivative
norm majorant. -/
theorem section43FourierLaplaceIntegral_fderivCandidate_norm_le_fderivNormMajorant_integral
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ ≤
      ∫ τ : Fin n → ℝ,
        section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
  intro F A ξ
  let G : (Fin n → ℝ) → NPointDomain d n →L[ℝ] ℂ := fun τ =>
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ
  have hmajorant_int :
      Integrable
        (fun τ : Fin n → ℝ =>
          section43FourierLaplace_fderivNormMajorant d n F A ξ τ)
        (volume : Measure (Fin n → ℝ)) :=
    integrable_section43FourierLaplace_fderivNormMajorant
      (d := d) (n := n) F A ξ
  have hpoint : ∀ τ : Fin n → ℝ,
      ‖G τ‖ ≤ section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
    intro τ
    simpa [G, F, A, ξ] using
      norm_section43FourierLaplace_timeIntegrandFDerivCLM_le_fderivNormMajorant_of_orderedSupport
        d n f hf_ord hδ_supp q hq τ
  calc
    ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ =
        ‖∫ τ : Fin n → ℝ, G τ‖ := by
          simp [section43FourierLaplaceIntegral_fderivCandidate, G, F]
    _ ≤ ∫ τ : Fin n → ℝ, ‖G τ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ τ : Fin n → ℝ,
        section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
        exact MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun τ => norm_nonneg (G τ))
          hmajorant_int
          (Filter.Eventually.of_forall hpoint)

set_option backward.isDefEq.respectTransparency false in
/-- Norm estimate for the first-derivative candidate of the Section 4.3
Fourier-Laplace integral.  The pointwise derivative bound is integrated in
`τ`, with the finite time- and spatial-coordinate sums pulled outside the
integral. -/
theorem section43FourierLaplaceIntegral_fderivCandidate_norm_le_exp_margin_integrals
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
    let A : ℝ :=
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k))
    let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
      section43QSpatial (d := d) (n := n) q
    ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ ≤
      A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
        ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            (∫ τ : Fin n → ℝ,
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)) := by
  intro F A ξ
  calc
    ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ ≤
        ∫ τ : Fin n → ℝ,
          section43FourierLaplace_fderivNormMajorant d n F A ξ τ := by
          simpa [F, A, ξ] using
            section43FourierLaplaceIntegral_fderivCandidate_norm_le_fderivNormMajorant_integral
              d n f hf_ord hδ_supp q hq
    _ = A *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
        ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            (∫ τ : Fin n → ℝ,
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)) := by
          simpa using
            integral_section43FourierLaplace_fderivNormMajorant
              (d := d) (n := n) F A ξ

/-- Spatial rapid decay of the time-integrated partial spatial Fourier
transform. -/
theorem section43PartialFourier_timeIntegral_spatialRapid
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        (1 + ‖ξ‖) ^ r *
          ∫ τ : Fin n → ℝ,
            ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ ≤ C := by
  classical
  let ι : Type := Fin n × Fin d
  rcases exists_integral_norm_partialFourierSpatial_timeSlice_uniform
      (d := d) (n := n) F with
    ⟨C0, hC0_nonneg, hC0_bound⟩
  choose Ccoord hCcoord_nonneg hCcoord_bound using
    fun i : ι =>
      exists_spatialCoordPow_integral_norm_partialFourierSpatial_timeSlice_uniform
        (d := d) (n := n) F i r
  let C : ℝ :=
    (Fintype.card (Option ι) : ℝ) ^ r *
      ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i
  have hsumC_nonneg :
      0 ≤ ∑ a : Option ι, match a with | none => C0 | some i => Ccoord i := by
    exact Finset.sum_nonneg fun a _ha => by
      cases a <;> simp [hC0_nonneg, hCcoord_nonneg]
  refine ⟨C, mul_nonneg (by positivity) hsumC_nonneg, ?_⟩
  intro ξ
  let A : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let w : Option ι → ℝ := fun a =>
    match a with | none => (1 : ℝ) | some i => ‖ξ i‖
  let B : Option ι → ℝ := fun a =>
    match a with | none => A | some i => ‖ξ i‖ ^ r * A
  let D : Option ι → ℝ := fun a =>
    match a with | none => C0 | some i => Ccoord i
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun τ => norm_nonneg _
  have hpow :
      (1 + ‖ξ‖) ^ r ≤
        (Fintype.card (Option ι) : ℝ) ^ r *
          ∑ a : Option ι, w a ^ r := by
    simpa [ι, w] using
      one_add_euclidean_norm_pow_le_card_pow_sum_option_norm_pow
        (ι := ι) r ξ
  have hsum_mul :
      (∑ a : Option ι, w a ^ r) * A = ∑ a : Option ι, B a := by
    rw [Finset.sum_mul]
    simp [B, w]
  have hB_le_D : ∀ a : Option ι, B a ≤ D a := by
    intro a
    cases a with
    | none =>
        simpa [B, D, A] using hC0_bound ξ
    | some i =>
        have hprod_eq :
            ‖ξ i‖ ^ r * A =
              ∫ τ : Fin n → ℝ,
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
          calc
            ‖ξ i‖ ^ r * A =
                ∫ τ : Fin n → ℝ,
                  ‖ξ i‖ ^ r *
                    ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  dsimp [A]
                  rw [MeasureTheory.integral_const_mul]
            _ = ∫ τ : Fin n → ℝ,
                ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                  partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with τ
                  simp [norm_pow, Complex.norm_real]
        calc
          B (some i) = ‖ξ i‖ ^ r * A := by
            simp [B]
          _ = ∫ τ : Fin n → ℝ,
              ‖((((ξ i : ℝ) : ℂ)) ^ r) *
                partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := hprod_eq
          _ ≤ Ccoord i := hCcoord_bound i ξ
          _ = D (some i) := by
            simp [D]
  have hsum_le : ∑ a : Option ι, B a ≤ ∑ a : Option ι, D a :=
    Finset.sum_le_sum fun a _ha => hB_le_D a
  calc
    (1 + ‖ξ‖) ^ r * A
        ≤ ((Fintype.card (Option ι) : ℝ) ^ r *
            ∑ a : Option ι, w a ^ r) * A := by
              exact mul_le_mul_of_nonneg_right hpow hA_nonneg
    _ = (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, B a := by
              rw [mul_assoc, hsum_mul]
    _ ≤ (Fintype.card (Option ι) : ℝ) ^ r * ∑ a : Option ι, D a := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = C := by
              simp [C, D]

/-- Spatial rapid decay of the integrated first-derivative majorant components.

The time part uses the `K = 1` time-moment estimate, while each transported
spatial term uses the `K = 0` estimate. -/
theorem section43FourierLaplace_fderivIntegralComponents_spatialRapid
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n × Fin d),
        (1 + ‖ξ‖) ^ r *
          ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
            (∫ τ : Fin n → ℝ,
              ‖τ‖ *
                ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i *
              (∫ τ : Fin n → ℝ,
                ‖partialFourierSpatial_fun (d := d) (n := n)
                  (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)) ≤ C := by
  classical
  rcases section43PartialFourier_timeMomentIntegral_spatialRapid
      (d := d) (n := n) F 1 r with
    ⟨Ctime, hCtime_nonneg, hCtime_bound⟩
  choose Cspace hCspace_nonneg hCspace_bound using
    fun i : Fin n × Fin d =>
      section43PartialFourier_timeMomentIntegral_spatialRapid
        (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) 0 r
  let T : ℝ := ∑ k : Fin n, section43QTimeCoordOpNorm d n k
  let C : ℝ :=
    T * Ctime +
      ∑ i : Fin n × Fin d, section43QSpatialCoordOpNorm d n i * Cspace i
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun k _hk => by
      dsimp [section43QTimeCoordOpNorm]
      exact norm_nonneg _
  have hScoef_nonneg : ∀ i : Fin n × Fin d,
      0 ≤ section43QSpatialCoordOpNorm d n i := by
    intro i
    dsimp [section43QSpatialCoordOpNorm]
    exact norm_nonneg _
  refine ⟨C, ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg hT_nonneg hCtime_nonneg)
      (Finset.sum_nonneg fun i _hi =>
        mul_nonneg (hScoef_nonneg i) (hCspace_nonneg i))
  intro ξ
  let W : ℝ := (1 + ‖ξ‖) ^ r
  let Itime : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖τ‖ *
        ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let Ispace : (Fin n × Fin d) → ℝ := fun i =>
    ∫ τ : Fin n → ℝ,
      ‖partialFourierSpatial_fun (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖
  have htime :
      W * Itime ≤ Ctime := by
    simpa [W, Itime, pow_one] using hCtime_bound ξ
  have hspace : ∀ i : Fin n × Fin d,
      W * Ispace i ≤ Cspace i := by
    intro i
    simpa [W, Ispace, pow_zero] using hCspace_bound i ξ
  have hdist :
      W *
        (T * Itime +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i * Ispace i) =
        T * (W * Itime) +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i * (W * Ispace i) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
  calc
    (1 + ‖ξ‖) ^ r *
        ((∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
          (∫ τ : Fin n → ℝ,
            ‖τ‖ *
              ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
        ∑ i : Fin n × Fin d,
          section43QSpatialCoordOpNorm d n i *
            (∫ τ : Fin n → ℝ,
              ‖partialFourierSpatial_fun (d := d) (n := n)
                (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖))
        = W *
        (T * Itime +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i * Ispace i) := by
          rfl
    _ = T * (W * Itime) +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i * (W * Ispace i) := hdist
    _ ≤ T * Ctime +
          ∑ i : Fin n × Fin d,
            section43QSpatialCoordOpNorm d n i * Cspace i := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left htime hT_nonneg)
            (Finset.sum_le_sum fun i _hi =>
              mul_le_mul_of_nonneg_left (hspace i) (hScoef_nonneg i))
    _ = C := by
          rfl

/-- Exponential damping in the positive-energy time variables dominates every
polynomial weight in the time norm. -/
theorem exp_margin_sum_controls_positiveEnergy_time_polynomial
    (d n : ℕ) [NeZero d]
    {δ : ℝ} (hδ_pos : 0 < δ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖section43QTime (d := d) (n := n) q‖) ^ r *
          Real.exp (-(δ * ∑ k : Fin n,
            section43QTime (d := d) (n := n) q k)) ≤ C := by
  rcases SCV.pow_mul_exp_neg_le_const hδ_pos r with
    ⟨C0, hC0_pos, hC0_bound⟩
  let C : ℝ := Real.exp δ * C0
  refine ⟨C, mul_nonneg (Real.exp_pos δ).le hC0_pos.le, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let s : ℝ := ∑ k : Fin n, t k
  have ht_nonneg : ∀ k : Fin n, 0 ≤ t k := by
    intro k
    simpa [t, section43QTime, nPointTimeSpatialCLE] using hq k
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun k _hk => ht_nonneg k
  have hnorm_le_sum : ‖t‖ ≤ s := by
    simpa [s] using pi_norm_le_sum_of_nonneg (x := t) ht_nonneg
  have hone_norm_le : 1 + ‖t‖ ≤ 1 + s := by
    linarith
  have hpow_le : (1 + ‖t‖) ^ r ≤ (1 + s) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hone_norm_le r
  have hx_nonneg : 0 ≤ 1 + s := by
    linarith
  have htail := hC0_bound (1 + s) hx_nonneg
  have hexp_eq :
      Real.exp (-(δ * s)) =
        Real.exp δ * Real.exp (-(δ * (1 + s))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (1 + ‖section43QTime (d := d) (n := n) q‖) ^ r *
        Real.exp (-(δ * ∑ k : Fin n,
          section43QTime (d := d) (n := n) q k))
        = (1 + ‖t‖) ^ r * Real.exp (-(δ * s)) := by
          simp [t, s]
    _ ≤ (1 + s) ^ r * Real.exp (-(δ * s)) := by
          exact mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le
    _ = Real.exp δ * ((1 + s) ^ r * Real.exp (-(δ * (1 + s)))) := by
          rw [hexp_eq]
          ring
    _ ≤ C := by
          exact mul_le_mul_of_nonneg_left htail (Real.exp_pos δ).le

/-- The full spacetime norm is controlled by the separated time and spatial
weights coming from `nPointTimeSpatialCLE`. -/
theorem one_add_norm_le_section43_time_spatial_product
    (d n : ℕ) [NeZero d] (q : NPointDomain d n) :
    1 + ‖q‖ ≤
      (1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖) *
        (1 + ‖section43QTime (d := d) (n := n) q‖) *
          (1 + ‖section43QSpatial (d := d) (n := n) q‖) := by
  let e := nPointTimeSpatialCLE (d := d) n
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let M : ℝ := ‖e.symm.toContinuousLinearMap‖
  let a : ℝ := ‖t‖
  let b : ℝ := ‖ξ‖
  let P : ℝ := (1 + a) * (1 + b)
  have hM_nonneg : 0 ≤ M := by
    exact norm_nonneg _
  have ha_nonneg : 0 ≤ a := by
    exact norm_nonneg _
  have hb_nonneg : 0 ≤ b := by
    exact norm_nonneg _
  have hpair_eq : (t, ξ) = e q := by
    ext i <;> simp [t, ξ, e, section43QTime, section43QSpatial]
  have hq_eq : q = e.symm (t, ξ) := by
    rw [hpair_eq]
    simp [e]
  have hpair_norm : ‖(t, ξ)‖ ≤ a + b := by
    dsimp [a, b]
    exact max_le_add_of_nonneg (norm_nonneg t) (norm_nonneg ξ)
  have hq_norm : ‖q‖ ≤ M * (a + b) := by
    calc
      ‖q‖ = ‖e.symm (t, ξ)‖ := by
        rw [hq_eq]
      _ ≤ M * ‖(t, ξ)‖ := by
        simpa [M] using
          (ContinuousLinearMap.le_opNorm e.symm.toContinuousLinearMap (t, ξ))
      _ ≤ M * (a + b) := by
        exact mul_le_mul_of_nonneg_left hpair_norm hM_nonneg
  have hP_ge_one : 1 ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  have hP_ge_a : a ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  have hP_ge_b : b ≤ P := by
    dsimp [P]
    nlinarith [ha_nonneg, hb_nonneg, mul_nonneg ha_nonneg hb_nonneg]
  calc
    1 + ‖q‖ ≤ 1 + M * (a + b) := by
      linarith
    _ ≤ (1 + 2 * M) * P := by
      nlinarith [hM_nonneg, hP_ge_one, hP_ge_a, hP_ge_b]
    _ = (1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖) *
        (1 + ‖section43QTime (d := d) (n := n) q‖) *
          (1 + ‖section43QSpatial (d := d) (n := n) q‖) := by
      simp [M, P, a, b, t, ξ, e, mul_assoc]

/-- Zero-derivative rapid decay of the Section 4.3 Fourier-Laplace integral on
the positive-energy half-space. -/
theorem section43FourierLaplaceIntegral_rapid_on_positiveEnergy_zeroDeriv
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖q‖) ^ r *
          ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤ C := by
  intro r
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases section43PartialFourier_timeIntegral_spatialRapid
      (d := d) (n := n) F r with
    ⟨Csp, hCsp_nonneg, hCsp_bound⟩
  rcases exp_margin_sum_controls_positiveEnergy_time_polynomial
      (d := d) (n := n) hδ_pos r with
    ⟨Ct, hCt_nonneg, hCt_bound⟩
  let A : ℝ :=
    1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖
  let C : ℝ := A ^ r * Ct * Csp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨C, mul_nonneg (mul_nonneg (pow_nonneg hA_nonneg r) hCt_nonneg) hCsp_nonneg, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let I : ℝ :=
    ∫ τ : Fin n → ℝ,
      ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖
  let E : ℝ := Real.exp (-(δ * ∑ k : Fin n, t k))
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun τ => norm_nonneg _
  have hspatial :
      (1 + ‖ξ‖) ^ r * I ≤ Csp := by
    simpa [I, F, ξ] using hCsp_bound ξ
  have htime :
      (1 + ‖t‖) ^ r * E ≤ Ct := by
    simpa [t, E] using hCt_bound q hq
  have hscalar :
      ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ ≤ E * I := by
    simpa [E, I, F, t, ξ] using
      section43FourierLaplaceIntegral_norm_le_exp_margin_integral
        d n f hf_ord hδ_supp q hq
  have hnorm :
      1 + ‖q‖ ≤ A * (1 + ‖t‖) * (1 + ‖ξ‖) := by
    simpa [A, t, ξ] using
      one_add_norm_le_section43_time_spatial_product d n q
  have hpow_norm :
      (1 + ‖q‖) ^ r ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hnorm r
  have htime_nonneg : 0 ≤ (1 + ‖t‖) ^ r * E := by
    exact mul_nonneg (pow_nonneg (by positivity) r) (Real.exp_pos _).le
  have hspatial_nonneg : 0 ≤ (1 + ‖ξ‖) ^ r * I := by
    exact mul_nonneg (pow_nonneg (by positivity) r) hI_nonneg
  have hterm_prod :
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I) ≤ Ct * Csp := by
    calc
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I)
          ≤ Ct * ((1 + ‖ξ‖) ^ r * I) := by
            exact mul_le_mul_of_nonneg_right htime hspatial_nonneg
      _ ≤ Ct * Csp := by
            exact mul_le_mul_of_nonneg_left hspatial hCt_nonneg
  calc
    (1 + ‖q‖) ^ r *
        ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖
        ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r *
            ‖section43FourierLaplaceIntegral d n ⟨f, hf_ord⟩ q‖ := by
          exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
    _ ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r * (E * I) := by
          exact mul_le_mul_of_nonneg_left hscalar (pow_nonneg (by positivity) r)
    _ = A ^ r * (((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * I)) := by
          rw [mul_pow, mul_pow]
          ring
    _ ≤ A ^ r * (Ct * Csp) := by
          exact mul_le_mul_of_nonneg_left hterm_prod (pow_nonneg hA_nonneg r)
    _ = C := by
          simp [C, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- First-derivative rapid decay of the Section 4.3 Fourier-Laplace integral
candidate on the positive-energy half-space. -/
theorem section43FourierLaplaceIntegral_fderivCandidate_rapid_on_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)}) :
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ section43PositiveEnergyRegion d n,
        (1 + ‖q‖) ^ r *
          ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ ≤ C := by
  intro r
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  rcases section43FourierLaplace_fderivIntegralComponents_spatialRapid
      (d := d) (n := n) F r with
    ⟨Csp, hCsp_nonneg, hCsp_bound⟩
  rcases exp_margin_sum_controls_positiveEnergy_time_polynomial
      (d := d) (n := n) hδ_pos r with
    ⟨Ct, hCt_nonneg, hCt_bound⟩
  let A : ℝ :=
    1 + 2 * ‖(nPointTimeSpatialCLE (d := d) n).symm.toContinuousLinearMap‖
  let C : ℝ := A ^ r * Ct * Csp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨C, mul_nonneg (mul_nonneg (pow_nonneg hA_nonneg r) hCt_nonneg) hCsp_nonneg, ?_⟩
  intro q hq
  let t : Fin n → ℝ := section43QTime (d := d) (n := n) q
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let E : ℝ := Real.exp (-(δ * ∑ k : Fin n, t k))
  let J : ℝ :=
    (∑ k : Fin n, section43QTimeCoordOpNorm d n k) *
      (∫ τ : Fin n → ℝ,
        ‖τ‖ *
          ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖) +
    ∑ i : Fin n × Fin d,
      section43QSpatialCoordOpNorm d n i *
        (∫ τ : Fin n → ℝ,
          ‖partialFourierSpatial_fun (d := d) (n := n)
            (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖)
  have hT_nonneg :
      0 ≤ ∑ k : Fin n, section43QTimeCoordOpNorm d n k := by
    exact Finset.sum_nonneg fun k _hk => by
      dsimp [section43QTimeCoordOpNorm]
      exact norm_nonneg _
  have hItime_nonneg :
      0 ≤ ∫ τ : Fin n → ℝ,
        ‖τ‖ *
          ‖partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)‖ := by
    exact integral_nonneg fun τ =>
      mul_nonneg (norm_nonneg τ) (norm_nonneg _)
  have hIspace_nonneg : ∀ i : Fin n × Fin d,
      0 ≤ ∫ τ : Fin n → ℝ,
        ‖partialFourierSpatial_fun (d := d) (n := n)
          (section43SpatialMultiplierTransport d n F i) (τ, ξ)‖ := by
    intro i
    exact integral_nonneg fun τ => norm_nonneg _
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J]
    exact add_nonneg
      (mul_nonneg hT_nonneg hItime_nonneg)
      (Finset.sum_nonneg fun i _hi =>
        mul_nonneg
          (by
            dsimp [section43QSpatialCoordOpNorm]
            exact norm_nonneg _)
          (hIspace_nonneg i))
  have hspatial :
      (1 + ‖ξ‖) ^ r * J ≤ Csp := by
    simpa [J, F, ξ] using hCsp_bound ξ
  have htime :
      (1 + ‖t‖) ^ r * E ≤ Ct := by
    simpa [t, E] using hCt_bound q hq
  have hscalar :
      ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ ≤ E * J := by
    simpa [E, J, F, t, ξ] using
      section43FourierLaplaceIntegral_fderivCandidate_norm_le_exp_margin_integrals
        d n f hf_ord hδ_supp q hq
  have hnorm :
      1 + ‖q‖ ≤ A * (1 + ‖t‖) * (1 + ‖ξ‖) := by
    simpa [A, t, ξ] using
      one_add_norm_le_section43_time_spatial_product d n q
  have hpow_norm :
      (1 + ‖q‖) ^ r ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hnorm r
  have htime_nonneg : 0 ≤ (1 + ‖t‖) ^ r * E := by
    exact mul_nonneg (pow_nonneg (by positivity) r) (Real.exp_pos _).le
  have hspatial_nonneg : 0 ≤ (1 + ‖ξ‖) ^ r * J := by
    exact mul_nonneg (pow_nonneg (by positivity) r) hJ_nonneg
  have hterm_prod :
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * J) ≤ Ct * Csp := by
    calc
      ((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * J)
          ≤ Ct * ((1 + ‖ξ‖) ^ r * J) := by
            exact mul_le_mul_of_nonneg_right htime hspatial_nonneg
      _ ≤ Ct * Csp := by
            exact mul_le_mul_of_nonneg_left hspatial hCt_nonneg
  calc
    (1 + ‖q‖) ^ r *
        ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖
        ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r *
            ‖section43FourierLaplaceIntegral_fderivCandidate d n f hf_ord q‖ := by
          exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
    _ ≤ (A * (1 + ‖t‖) * (1 + ‖ξ‖)) ^ r * (E * J) := by
          exact mul_le_mul_of_nonneg_left hscalar (pow_nonneg (by positivity) r)
    _ = A ^ r * (((1 + ‖t‖) ^ r * E) * ((1 + ‖ξ‖) ^ r * J)) := by
          rw [mul_pow, mul_pow]
          ring
    _ ≤ A ^ r * (Ct * Csp) := by
          exact mul_le_mul_of_nonneg_left hterm_prod (pow_nonneg hA_nonneg r)
    _ = C := by
          simp [C, mul_assoc]

end OSReconstruction
