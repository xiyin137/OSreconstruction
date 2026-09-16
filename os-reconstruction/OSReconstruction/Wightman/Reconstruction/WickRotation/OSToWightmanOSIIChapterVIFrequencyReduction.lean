import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge
import OSReconstruction.Wightman.Reconstruction.SchwartzNPointFlatten
import OSReconstruction.Wightman.SpectralEquivalence

/-!
# Fourier transform of the basepoint reduction

These coordinate identities do not use a selected reconstruction witness.
They identify the full frequency representative at zero total momentum with
Fourier transformation after integrating out the absolute basepoint.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The full real difference-coordinate inverse with a prepended basepoint is
the same absolute configuration as the standard zero-basepoint difference
section translated by that basepoint. -/
theorem realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
    (m : ℕ) (x₀ : SpacetimeDim d) (ξ : NPointDomain d m) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ) =
      fun k μ => x₀ μ + diffVarSection d m ξ k μ := by
  ext k μ
  induction k using Fin.induction with
  | zero =>
      rw [diffVarSection_zero, add_zero]
      have h := congrFun
        (congrFun
          ((BHW.realDiffCoordCLE (m + 1) d).apply_symm_apply
            (BHW.prependBasepointReal d m x₀ ξ)) 0) μ
      simpa [BHW.realDiffCoordCLE_apply] using h
  | succ k ih =>
      have hred :=
        congrFun
          (congrFun
            (BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
              (d := d) (m := m) x₀ ξ) k) μ
      rw [BHW.reducedDiffMapReal_apply] at hred
      have hstep :
          (BHW.realDiffCoordCLE (m + 1) d).symm
              (BHW.prependBasepointReal d m x₀ ξ) k.succ μ =
            (BHW.realDiffCoordCLE (m + 1) d).symm
              (BHW.prependBasepointReal d m x₀ ξ) k.castSucc μ +
              ξ k μ := by
        simpa [add_comm] using (eq_add_of_sub_eq hred)
      rw [hstep, ih]
      rw [diffVarSection_succ]
      ring

/-- Embed a reduced physics-convention momentum as a full Section 4.3
frequency tuple with zero total-momentum head.  The spatial rescaling is the
conversion from the physics Fourier convention to Mathlib's convention used
by the Section 4.3 spatial representative. -/
noncomputable def section43ReducedPhysicsFrequencyZeroHead
    (d k : ℕ) [NeZero d]
    (xi : Fin (k * (d + 1)) → ℝ) :
    NPointDomain d (k + 1) :=
  Fin.cons 0
    (section43SpatialFourierScaleCLE d k
      ((flattenCLEquivReal k (d + 1)).symm xi))

theorem section43ReducedPhysicsFrequencyZeroHead_rawCumulative
    (d k : ℕ) [NeZero d]
    (xi : Fin (k * (d + 1)) → ℝ) :
    section43RawCumulativeTailMomentumCLE d (k + 1)
        ((section43CumulativeTailMomentumCLE d (k + 1)).symm
          (section43ReducedPhysicsFrequencyZeroHead d k xi)) =
      Fin.cons 0 ((flattenCLEquivReal k (d + 1)).symm xi) := by
  rw [section43RawCumulativeTail_of_cumulativeTailMomentum_symm]
  ext i mu
  refine Fin.cases ?_ ?_ i
  · simp [section43ReducedPhysicsFrequencyZeroHead,
      section43SpatialFourierScaleCLE_symm_apply]
  · intro j
    by_cases hmu : mu = 0
    · subst mu
      simp [section43ReducedPhysicsFrequencyZeroHead]
    · simp [section43ReducedPhysicsFrequencyZeroHead,
        section43SpatialFourierScaleCLE_apply,
        section43SpatialFourierScaleCLE_symm_apply, hmu]
      field_simp [Real.pi_ne_zero]

theorem section43ReducedPhysicsFrequencyZeroHead_pairing
    (d k : ℕ) [NeZero d]
    (a : SpacetimeDim d)
    (eta : NPointDomain d k)
    (xi : Fin (k * (d + 1)) → ℝ) :
    (∑ i : Fin ((k + 1) * (d + 1)),
        flattenCLEquivReal (k + 1) (d + 1)
            ((section43DiffCoordRealCLE d (k + 1)).symm
              (Fin.cons a eta)) i *
          ((section43CumulativeTailMomentumCLE d (k + 1)).symm
            (section43ReducedPhysicsFrequencyZeroHead d k xi)) i) =
      ∑ i : Fin (k * (d + 1)),
        flattenCLEquivReal k (d + 1) eta i * xi i := by
  rw [section43DiffCoord_pairing_eq_rawCumulativeTail]
  rw [section43ReducedPhysicsFrequencyZeroHead_rawCumulative]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add]
  calc
    (∑ j : Fin k, ∑ mu : Fin (d + 1),
        eta j mu * ((flattenCLEquivReal k (d + 1)).symm xi) j mu) =
        ∑ p : Fin k × Fin (d + 1),
          eta p.1 p.2 * xi (finProdFinEquiv p) := by
      simpa [flattenCLEquivReal_symm_apply] using
        (Finset.sum_product
          (s := (Finset.univ : Finset (Fin k)))
          (t := (Finset.univ : Finset (Fin (d + 1))))
          (f := fun p : Fin k × Fin (d + 1) =>
            eta p.1 p.2 * xi (finProdFinEquiv p))).symm
    _ = ∑ i : Fin (k * (d + 1)),
        flattenCLEquivReal k (d + 1) eta i * xi i := by
      simpa [flattenCLEquivReal_apply] using
        (finProdFinEquiv.sum_comp
          (fun i : Fin (k * (d + 1)) =>
            flattenCLEquivReal k (d + 1) eta i * xi i))

/-- Fourier transform of the basepoint fiber reduction is restriction of the
full Section 4.3 frequency representative to zero total momentum. -/
theorem physicsFourierFlatCLM_diffVarReduction_eq_zeroHead
    (d k : ℕ) [NeZero d]
    (f : SchwartzNPoint d (k + 1))
    (xi : Fin (k * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (_root_.flattenSchwartzNPoint (d := d) (diffVarReduction d k f)) xi =
      section43FrequencyRepresentative d (k + 1) f
        (section43ReducedPhysicsFrequencyZeroHead d k xi) := by
  let q : NPointDomain d (k + 1) :=
    section43ReducedPhysicsFrequencyZeroHead d k xi
  let p : Fin ((k + 1) * (d + 1)) → ℝ :=
    (section43CumulativeTailMomentumCLE d (k + 1)).symm q
  let G : NPointDomain d (k + 1) → ℂ := fun x =>
    Complex.exp (Complex.I * ∑ i : Fin ((k + 1) * (d + 1)),
      (flattenCLEquivReal (k + 1) (d + 1) x i : ℂ) * (p i : ℂ)) * f x
  have hf : Integrable f (volume : Measure (NPointDomain d (k + 1))) := by
    let fflat : SchwartzMap (Fin ((k + 1) * (d + 1)) → ℝ) ℂ :=
      _root_.flattenSchwartzNPoint (d := d) f
    have hflat : Integrable fflat := fflat.integrable
    have hcomp : Integrable
        (fflat ∘ flattenMeasurableEquiv (k + 1) (d + 1)) :=
      (flattenMeasurableEquiv_measurePreserving (k + 1) (d + 1)).integrable_comp_of_integrable
        hflat
    have heq : fflat ∘ flattenMeasurableEquiv (k + 1) (d + 1) = f := by
      funext x
      have harg :
          (flattenCLEquivReal (k + 1) (d + 1)).symm
              (flattenMeasurableEquiv (k + 1) (d + 1) x) = x := by
        ext j mu
        rw [flattenCLEquivReal_symm_apply]
        simp [flattenMeasurableEquiv_apply]
      simp [fflat, harg]
    simpa [heq] using hcomp
  have hG : Integrable G := by
    have hcont : Continuous G := by fun_prop
    refine hf.mono hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [show ‖G x‖ = ‖Complex.exp (Complex.I *
        ∑ i : Fin ((k + 1) * (d + 1)),
          (flattenCLEquivReal (k + 1) (d + 1) x i : ℂ) * (p i : ℂ))‖ * ‖f x‖ by
      simp [G]]
    rw [Complex.norm_exp]
    simp
  have hchange := BHW.integral_realDiffCoord_change_variables
    (d := d) k G hG
  rw [← physicsFourierFlatCLM_integral]
  rw [integral_flatten_change_of_variables]
  simp only [_root_.flattenSchwartzNPoint_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  change
    (∫ eta : NPointDomain d k,
        Complex.exp (Complex.I * ∑ i : Fin (k * (d + 1)),
          (flattenCLEquivReal k (d + 1) eta i : ℂ) * (xi i : ℂ)) *
          ∫ a : SpacetimeDim d,
            f (fun j mu => a mu + diffVarSection d k eta j mu)) = _
  change _ = physicsFourierFlatCLM (_root_.flattenSchwartzNPoint (d := d) f) p
  rw [← physicsFourierFlatCLM_integral]
  rw [integral_flatten_change_of_variables]
  simp only [_root_.flattenSchwartzNPoint_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  change _ = ∫ x : NPointDomain d (k + 1), G x
  rw [hchange]
  apply integral_congr_ae
  filter_upwards with eta
  have hphase (a : SpacetimeDim d) :
      Complex.I * ∑ i : Fin ((k + 1) * (d + 1)),
          (flattenCLEquivReal (k + 1) (d + 1)
              ((BHW.realDiffCoordCLE (k + 1) d).symm
                (BHW.prependBasepointReal d k a eta)) i : ℂ) * (p i : ℂ) =
        Complex.I * ∑ i : Fin (k * (d + 1)),
          (flattenCLEquivReal k (d + 1) eta i : ℂ) * (xi i : ℂ) := by
    have hreal := section43ReducedPhysicsFrequencyZeroHead_pairing
      d k a eta xi
    have habs :
        (BHW.realDiffCoordCLE (k + 1) d).symm
            (BHW.prependBasepointReal d k a eta) =
          (section43DiffCoordRealCLE d (k + 1)).symm (Fin.cons a eta) := by
      rw [BHW.prependBasepointReal_eq_finCons]
    rw [habs]
    dsimp only [p, q]
    exact congrArg (fun z : ℂ => Complex.I * z) (by exact_mod_cast hreal)
  simp_rw [G, hphase]
  simp_rw [realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection]
  symm
  exact MeasureTheory.integral_const_mul
    (Complex.exp (Complex.I * ∑ i : Fin (k * (d + 1)),
      (flattenCLEquivReal k (d + 1) eta i : ℂ) * (xi i : ℂ)))
    (fun a : SpacetimeDim d =>
      f (fun j mu => a mu + diffVarSection d k eta j mu))

end OSReconstruction
