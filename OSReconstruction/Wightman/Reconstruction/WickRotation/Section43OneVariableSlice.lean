import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-! ### Section 4.3 one-variable time slices -/

/-- If one chosen time coordinate is negative, the time/spatial reindexing of
an ordered-positive-time Euclidean test vanishes at that point. -/
theorem section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n) f.1
      (Function.update t r s, η) = 0 := by
  have hnot_ord :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        OrderedPositiveTimeRegion d n := by
    intro hmem
    have htime : 0 <
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) := (hmem r).1
    have hEq :
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        tsupport (f.1 : NPointDomain d n → ℂ) := by
    intro hx
    exact hnot_ord (f.2 hx)
  change f.1 ((nPointTimeSpatialCLE (d := d) n).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

/-- Negative time in one chosen coordinate forces the partial spatial Fourier
transform to vanish at that point. -/
theorem section43PartialFourierSpatial_fun_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    partialFourierSpatial_fun (d := d) (n := n) f.1
      (Function.update t r s, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with η
  simp [section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time
    (f := f) (r := r) (t := t) (η := η) hs]

/-- Fixing the spatial momentum block and all but one time coordinate, the
partial spatial Fourier transform of an ordered-positive-time Euclidean test
is supported in `s >= 0` in the remaining time variable. -/
theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  intro s hs
  by_contra hs_neg
  have hs_lt : s < 0 := by
    simpa [Set.mem_Ici, not_le] using hs_neg
  have hs_not :
      s ∉ tsupport (fun s' : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f.1
          (Function.update t r s', ξ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball s (-s / 2) ∈ 𝓝 s := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s' hs'
    have hsabs : |s' - s| < -s / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs'
    have hs'_lt : s' < 0 := by
      linarith [(abs_lt.mp hsabs).2, hs_lt]
    exact section43PartialFourierSpatial_fun_eq_zero_of_neg_time
      (f := f) r t ξ hs'_lt
  exact hs_not hs

omit [NeZero d] in
/-- A Schwartz function supported on the Section-4.3 positive-energy region
vanishes when one time coordinate is negative. -/
theorem section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n) F
      (Function.update t r s, η) = 0 := by
  have hnot_region :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        section43PositiveEnergyRegion d n := by
    intro hmem
    have htime : 0 ≤
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) := hmem r
    have hEq :
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        tsupport (F : NPointDomain d n → ℂ) := by
    intro hx
    exact hnot_region (hF_supp hx)
  change F ((nPointTimeSpatialCLE (d := d) n).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

omit [NeZero d] in
/-- Negative time in one chosen coordinate forces the partial spatial Fourier
transform to vanish for any input supported in the Section-4.3 positive-energy
region. -/
theorem section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    partialFourierSpatial_fun (d := d) (n := n) F
      (Function.update t r s, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with η
  simp [section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
    (F := F) hF_supp (r := r) (t := t) (η := η) hs]

omit [NeZero d] in
/-- A one-variable time slice of any positive-energy-supported input has
support in the nonnegative half-line. -/
theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n) F
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  intro s hs
  by_contra hs_neg
  have hs_lt : s < 0 := by
    simpa [Set.mem_Ici, not_le] using hs_neg
  have hs_not :
      s ∉ tsupport (fun s' : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) F
          (Function.update t r s', ξ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball s (-s / 2) ∈ 𝓝 s := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s' hs'
    have hsabs : |s' - s| < -s / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs'
    have hs'_lt : s' < 0 := by
      linarith [(abs_lt.mp hsabs).2, hs_lt]
    exact section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy
      (F := F) hF_supp r t ξ hs'_lt
  exact hs_not hs

/-- The one-variable time slice of a Section-4.3 difference-coordinate
pullback is supported in the nonnegative half-line. -/
theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
    {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n f)
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  exact
    section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_support_positiveEnergy
      (d := d) (n := n)
      (F := section43DiffPullbackCLM d n f)
      (tsupport_section43DiffPullback_subset_positiveOrthant d n f)
      r t ξ

/-- Every fixed time-coordinate polynomial weight is uniformly bounded on a
one-variable time slice. -/
theorem section43Exists_timePow_norm_bound_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)‖ ≤ C := by
  rcases exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
      (d := d) (n := n) f r k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  simpa using hbound (Function.update t r s, ξ)

/-- The Schwartz input obtained by differentiating a one-variable time slice
in the chosen coordinate. -/
noncomputable def section43TimeDerivTransportInput
    {n : ℕ} (r : Fin n) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
    (LineDeriv.lineDerivOp
      ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
        Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
      (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))

/-- The ordinary derivative of a one-variable time slice is the same slice,
with the input replaced by `section43TimeDerivTransportInput`. -/
theorem section43Deriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (s : ℝ) :
    deriv
      (fun u : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r u, ξ))
      s =
    partialFourierSpatial_fun (d := d) (n := n)
      (section43TimeDerivTransportInput (d := d) (n := n) r f)
      (Function.update t r s, ξ) := by
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
    simpa using
      (((differentiableAt_partialFourierSpatial_fun_time
          (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
        (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
  calc
    deriv
        (fun u : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s
      =
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))) := hcomp.deriv
    _ = partialFourierSpatial_fun (d := d) (n := n)
          (section43TimeDerivTransportInput (d := d) (n := n) r f)
          (Function.update t r s, ξ) := by
            simpa [section43TimeDerivTransportInput] using
              fderiv_partialFourierSpatial_fun_time_apply_eq_transport
                (d := d) (n := n) f ξ (Function.update t r s)
                (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))

/-- Repeated time differentiation of the one-variable slice corresponds to
repeated application of `section43TimeDerivTransportInput`. -/
noncomputable def section43IteratedTimeDerivTransport
    {n : ℕ} (r : Fin n) (m : ℕ) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n :=
  (section43TimeDerivTransportInput (d := d) (n := n) r)^[m] f

/-- The `m`-th ordinary derivative of a one-variable time slice is again the
same slice, with the input replaced by the recursively transported datum. -/
theorem section43IteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∀ (m : ℕ) (f : SchwartzNPoint d n) (s : ℝ),
      iteratedDeriv m
        (fun u : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s =
      partialFourierSpatial_fun (d := d) (n := n)
        (section43IteratedTimeDerivTransport (d := d) (n := n) r m f)
        (Function.update t r s, ξ) := by
  intro m
  induction m with
  | zero =>
      intro f s
      simp [section43IteratedTimeDerivTransport]
  | succ m ih =>
      intro f s
      rw [iteratedDeriv_succ']
      have hArg :
          iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s =
          iteratedDeriv m
            (fun u : ℝ =>
              partialFourierSpatial_fun (d := d) (n := n)
                (section43TimeDerivTransportInput (d := d) (n := n) r f)
                (Function.update t r u, ξ))
            s := by
        congr 1
        ext u
        simpa using
          section43Deriv_partialFourierSpatial_timeSlice_eq_transport
            (d := d) (n := n) (f := f) r t ξ u
      calc
        iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s
          =
            iteratedDeriv m
              (fun u : ℝ =>
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43TimeDerivTransportInput (d := d) (n := n) r f)
                  (Function.update t r u, ξ))
              s := hArg
        _ = partialFourierSpatial_fun (d := d) (n := n)
              (section43IteratedTimeDerivTransport (d := d) (n := n) r (m + 1) f)
              (Function.update t r s, ξ) := by
              simpa [section43IteratedTimeDerivTransport,
                section43TimeDerivTransportInput, Function.iterate_succ_apply] using
                ih (section43TimeDerivTransportInput (d := d) (n := n) r f) s

/-- Every iterated ordinary derivative of the time slice satisfies every fixed
polynomial time-weight bound. -/
theorem section43Exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          iteratedDeriv m
            (fun u : ℝ =>
              partialFourierSpatial_fun (d := d) (n := n) f
                (Function.update t r u, ξ))
            s‖ ≤ C := by
  rcases section43Exists_timePow_norm_bound_partialFourierSpatial_timeSlice
      (d := d) (n := n)
      (f := section43IteratedTimeDerivTransport (d := d) (n := n) r m f)
      r t ξ k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  rw [section43IteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
      (d := d) (n := n) r t ξ m f s]
  simpa using hbound s

/-- Every one-variable time slice is differentiable, with derivative given by
the transported Schwartz input. -/
theorem section43Differentiable_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Differentiable ℝ
      (fun s : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  intro s
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        (partialFourierSpatial_fun (d := d) (n := n)
          (section43TimeDerivTransportInput (d := d) (n := n) r f)
          (Function.update t r s, ξ))
        s := by
    have hbase :
        HasDerivAt
          (fun u : ℝ =>
            partialFourierSpatial_fun (d := d) (n := n) f
              (Function.update t r u, ξ))
          ((fderiv ℝ
              (fun u : Fin n → ℝ =>
              partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
              (Function.update t r s))
            (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
      simpa using
        (((differentiableAt_partialFourierSpatial_fun_time
            (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
          (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
    convert hbase using 1
    simpa [section43TimeDerivTransportInput] using
      (fderiv_partialFourierSpatial_fun_time_apply_eq_transport
        (d := d) (n := n) f ξ (Function.update t r s)
        (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))).symm
  exact hcomp.differentiableAt

/-- The one-variable time slice is smooth. -/
theorem section43ContDiff_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m hm
  have hEq :
      iteratedDeriv m
        (fun s : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)) =
      fun s : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n)
          (section43IteratedTimeDerivTransport (d := d) (n := n) r m f)
          (Function.update t r s, ξ) := by
    ext s
    simpa using
      section43IteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
        (d := d) (n := n) r t ξ m f s
  rw [hEq]
  exact section43Differentiable_partialFourierSpatial_timeSlice
    (d := d) (n := n)
    (f := section43IteratedTimeDerivTransport (d := d) (n := n) r m f) r t ξ

/-- The one-variable time slice, packaged as a Schwartz function of the chosen
time coordinate. -/
noncomputable def section43PartialFourierSpatialTimeSliceSchwartz
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SchwartzMap ℝ ℂ where
  toFun := fun s : ℝ =>
    partialFourierSpatial_fun (d := d) (n := n) f
      (Function.update t r s, ξ)
  smooth' := section43ContDiff_partialFourierSpatial_timeSlice
    (d := d) (n := n) f r t ξ
  decay' := by
    intro k m
    rcases section43Exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
        (d := d) (n := n) f r t ξ k m with ⟨C, _, hC⟩
    refine ⟨C, ?_⟩
    intro s
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC s

/-- The raw one-variable complex Laplace transform used by the Section 4.3
Fourier-Laplace transport. -/
noncomputable def section43ComplexLaplaceTransform
    (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t

theorem section43ComplexLaplaceTransform_integrable_of_nonneg_re
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (s : ℂ) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * f t) := by
  apply MeasureTheory.Integrable.mono f.integrable
  · exact ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, Complex.norm_exp]
    by_cases ht : (f : ℝ → ℂ) t = 0
    · simp [ht]
    · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
      have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
        simp [Complex.mul_re]
      rw [hre]
      have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_left (norm_nonneg _) hexp

/-- The tempered functional pairing against `𝓕⁻¹ f`. -/
noncomputable def section43FourierInvPairingCLM
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
    (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => FourierTransform.fourierInv f t))

@[simp] theorem section43FourierInvPairingCLM_apply
    (f φ : SchwartzMap ℝ ℂ) :
    section43FourierInvPairingCLM f φ =
      ∫ t : ℝ, FourierTransform.fourierInv f t * φ t := by
  rw [section43FourierInvPairingCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.integralCLM_apply]
  rw [SchwartzMap.smulLeftCLM_apply]
  · simp [smul_eq_mul]
  · fun_prop

/-- Positive-support Schwartz input gives one-sided Fourier support for the
inverse-Fourier pairing functional. -/
theorem section43FourierInvPairing_hasOneSidedFourierSupport
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    SCV.HasOneSidedFourierSupport (section43FourierInvPairingCLM f) := by
  intro φ hφ_supp
  rw [section43FourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
  have hzero : ∀ x : ℝ, f x * φ x = 0 := by
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · have hx_mem : x ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hx
      have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp (hf_supp hx_mem)
      by_cases hφx : φ x = 0
      · simp [hφx]
      · have hx_neg : x < 0 := hφ_supp x (Function.mem_support.mpr hφx)
        exact (not_lt_of_ge hx_nonneg hx_neg).elim
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with x
  simp [hzero x]

/-- The one-variable support-disjoint Parseval step used after a time-slice
factorization rewrite. -/
theorem section43FourierInvPairing_annihilates_FT_of_negSupport_product
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (g φ : SchwartzMap ℝ ℂ)
    (hφ_supp : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    section43FourierInvPairingCLM f
      ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) = 0 := by
  have hprod_supp :
      ∀ x ∈ Function.support
        (((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => g y)) φ : SchwartzMap ℝ ℂ) : ℝ → ℂ),
        x < 0 := by
    intro x hx
    apply hφ_supp x
    apply Function.mem_support.mpr
    intro hφx
    apply hx
    rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) g.hasTemperateGrowth, hφx]
    simp
  exact
    (section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)
      (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) hprod_supp

/-- The support-disjoint Parseval step specialized to Section-4.3
positive-time one-variable slices. -/
theorem section43FourierInvPairingCLM_partialFourierSpatial_timeSlice_annihilates_FT_of_negSupport_product
    {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (g χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0) :
    section43FourierInvPairingCLM
        (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) χ)) = 0 := by
  refine section43FourierInvPairing_annihilates_FT_of_negSupport_product
    (f := section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
    (g := g) (φ := χ) ?_ hχ_supp
  exact section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
    (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ

/-- From positive-support Schwartz input, obtain the Paley-Wiener upper-half
plane extension with the correct distributional boundary value. -/
theorem section43ComplexLaplaceTransform_hasPaleyWienerExtension
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ t : ℝ, FourierTransform.fourierInv f t * φ t))) := by
  simpa [section43FourierInvPairingCLM_apply] using
    SCV.paley_wiener_half_line
      (section43FourierInvPairingCLM f)
      (section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)

/-- On the positive imaginary axis, the canonical Fourier-Laplace extension of
the inverse-Fourier functional induced by `f` reproduces the raw one-sided
Laplace transform, with the built-in `2π` scaling from
`SCV.paley_wiener_half_line`. -/
theorem section43FourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt
        (section43FourierInvPairingCLM f)
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
      = section43ComplexLaplaceTransform f ((2 * Real.pi * η : ℂ)) := by
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
      (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
  have hψ_inv :
      FourierTransform.fourierInv ((SchwartzMap.fourierTransformCLM ℂ) ψ) = ψ := by
    simp [SchwartzMap.fourierTransformCLM_apply]
  rw [SCV.fourierLaplaceExt_eq, section43FourierInvPairingCLM_apply,
    SchwartzMap.integral_fourierInv_mul_eq]
  rw [hψ_inv]
  change ∫ ξ : ℝ, f ξ * ψ ξ =
    ∫ t : ℝ, Complex.exp (-((2 * Real.pi * η : ℂ)) * (t : ℂ)) * f t
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : f ξ = 0
  · simp [hξ]
  · have hξ_mem : ξ ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hξ
    have hξ_nonneg : 0 ≤ ξ := Set.mem_Ici.mp (hf_supp hξ_mem)
    rw [show ψ ξ =
        SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
          (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη) ξ by rfl]
    rw [SCV.schwartzPsiZ_apply, SCV.psiZ_eq_exp_of_nonneg hξ_nonneg]
    have hexp :
        Complex.exp (Complex.I * ((((2 * Real.pi * η : ℂ) * Complex.I)) * ξ)) =
          Complex.exp (-((2 * Real.pi * η : ℂ) * ξ)) := by
      congr 1
      ring_nf
      simp
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z => f ξ * z) hexp

/-- The one-variable Paley-Wiener theorem specialized to an actual
Section-4.3 positive-time slice. -/
theorem section43PartialFourierSpatial_timeSlice_hasPaleyWienerExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (section43FourierInvPairingCLM
              (section43PartialFourierSpatialTimeSliceSchwartz
                (d := d) (n := n) f.1 r t ξ)
              φ))) := by
  simpa [section43FourierInvPairingCLM_apply] using
    section43ComplexLaplaceTransform_hasPaleyWienerExtension
      (f := section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
        (d := d) (n := n) f r t ξ)

/-- The canonical one-variable Section-4.3 upper-half-plane extension attached
to a positive-time slice. -/
noncomputable def section43PartialFourierSpatialTimeSliceCanonicalExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    SCV.fourierLaplaceExt
      (section43FourierInvPairingCLM
        (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (((2 * Real.pi : ℂ) * w))
      (by
        have hmul : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
        simpa [Complex.mul_im] using hmul)
  else
    0

/-- On the positive imaginary axis, the canonical slice extension reproduces
the raw one-sided Laplace transform of the Section-4.3 time slice. -/
theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I)
      =
    section43ComplexLaplaceTransform
      (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ)) := by
  have him : 0 < (η * Complex.I).im := by simpa using hη
  simp only [section43PartialFourierSpatialTimeSliceCanonicalExtension, dif_pos him]
  have harg :
      ((2 * Real.pi : ℂ) * (η * Complex.I)) = ((2 * Real.pi * η : ℂ) * Complex.I) := by
    ring
  simpa [harg] using
    (section43FourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
      (f := section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
        (d := d) (n := n) f r t ξ)
      hη)

/-- The one-variable Paley-Wiener Fourier-Laplace value at `2π i η` is the
same scalar as the descended Section-4.3 pairing against the corresponding
`ψ_Z` kernel. -/
theorem section43OneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt T
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  rw [SCV.fourierLaplaceExt_eq]
  symm
  exact
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := T) (hT_supp := hT_supp)
      (f := SCV.schwartzPsiZ
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη))

/-- On the positive imaginary axis, the canonical one-variable slice extension
is exactly the descended Section-4.3 Fourier pairing evaluated on the quotient
class of the same Paley-Wiener kernel `ψ_{2πiη}`. -/
theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_imagAxis_eq_descendedPsiZ
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM
          (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (section43FourierInvPairing_hasOneSidedFourierSupport
          (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
            (d := d) (n := n) f r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  have him : 0 < (η * Complex.I).im := by
    simpa using hη
  have harg : ((2 * Real.pi : ℂ) * (η * Complex.I)) =
      (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  rw [section43PartialFourierSpatialTimeSliceCanonicalExtension, dif_pos him]
  simpa [harg] using
    (section43OneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
      (T := section43FourierInvPairingCLM
        (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (hT_supp := section43FourierInvPairing_hasOneSidedFourierSupport
        (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
            (d := d) (n := n) f r t ξ))
      hη)

/-- The canonical Section-4.3 one-variable slice extension is holomorphic on
the upper half-plane. -/
theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_differentiableOn
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    DifferentiableOn ℂ
      (section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ)
      SCV.upperHalfPlane := by
  let T :=
    section43FourierInvPairingCLM
      (section43PartialFourierSpatialTimeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
  let Fcore : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  let F : ℂ → ℂ := Fcore ∘ fun w => (((2 * Real.pi : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    have hmap : Set.MapsTo (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
        SCV.upperHalfPlane SCV.upperHalfPlane := by
      intro z hz
      dsimp [SCV.upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane := by
      intro z hz
      simpa using
        ((((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (((2 * Real.pi : ℝ) : ℂ))).differentiableWithinAt))
    simpa [F, Fcore] using (SCV.fourierLaplaceExt_differentiableOn T).comp hmul hmap
  have hEq :
      section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ = F := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      show section43PartialFourierSpatialTimeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change section43PartialFourierSpatialTimeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [section43PartialFourierSpatialTimeSliceCanonicalExtension,
        dif_pos hw, dif_pos hscaled]
      simp [T]
    · have hnotscaled : ¬ 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        intro hscaled
        have hscaled' : 0 < (2 * Real.pi) * w.im := by
          simpa [Complex.mul_im, mul_assoc] using hscaled
        nlinarith [Real.two_pi_pos, hscaled']
      show section43PartialFourierSpatialTimeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change section43PartialFourierSpatialTimeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [section43PartialFourierSpatialTimeSliceCanonicalExtension,
        dif_neg hw, dif_neg hnotscaled]
  rw [hEq]
  exact hF_diff

/-- The canonical one-variable Paley-Wiener extension attached to an arbitrary
Schwartz input through the inverse-Fourier pairing. -/
noncomputable def section43FourierInvPairingCanonicalExtension
    (f : SchwartzMap ℝ ℂ) (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    SCV.fourierLaplaceExt
      (section43FourierInvPairingCLM f)
      (((2 * Real.pi : ℂ) * w))
      (by
        have hmul : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
        simpa [Complex.mul_im] using hmul)
  else
    0

/-- On the positive imaginary axis, the general canonical extension reproduces
the raw one-sided Laplace transform. -/
theorem section43FourierInvPairingCanonicalExtension_eq_complexLaplaceTransform
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    section43FourierInvPairingCanonicalExtension f (η * Complex.I) =
      section43ComplexLaplaceTransform f ((2 * Real.pi * η : ℂ)) := by
  have him : 0 < (η * Complex.I).im := by simpa using hη
  simp only [section43FourierInvPairingCanonicalExtension, dif_pos him]
  have harg :
      ((2 * Real.pi : ℂ) * (η * Complex.I)) = ((2 * Real.pi * η : ℂ) * Complex.I) := by
    ring
  simpa [harg] using
    (section43FourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
      (f := f) hf_supp hη)

/-- On the positive imaginary axis, the general canonical extension is the
descended half-line quotient pairing against the Paley-Wiener kernel. -/
theorem section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    section43FourierInvPairingCanonicalExtension f (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM f)
        (section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  have him : 0 < (η * Complex.I).im := by
    simpa using hη
  have harg : ((2 * Real.pi : ℂ) * (η * Complex.I)) =
      (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  rw [section43FourierInvPairingCanonicalExtension, dif_pos him]
  simpa [harg] using
    (section43OneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
      (T := section43FourierInvPairingCLM f)
      (hT_supp := section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)
      hη)

/-- Rescaled version of the descended-`ψ_Z` formula, written with the real
Laplace parameter `σ` rather than the imaginary height `σ / (2π)`. -/
theorem section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ_of_pos
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {σ : ℝ} (hσ : 0 < σ) :
    section43FourierInvPairingCanonicalExtension f
        ((σ / (2 * Real.pi)) * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM f)
        (section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((σ : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hσ.ne'] using hσ))) := by
  have hη : 0 < σ / (2 * Real.pi) := div_pos hσ Real.two_pi_pos
  have h :=
    section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ
      (f := f) hf_supp hη
  have hscale : 2 * Real.pi * (σ / (2 * Real.pi)) = σ := by
    field_simp [Real.two_pi_pos.ne']
  have hscaleC :
      (((2 * Real.pi * (σ / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
        ((σ : ℂ) * Complex.I) := by
    rw [hscale]
  have hscaleC' :
      2 * (Real.pi : ℂ) * ((σ : ℂ) / (2 * (Real.pi : ℂ))) * Complex.I =
        (σ : ℂ) * Complex.I := by
    have hcancel :
        2 * (Real.pi : ℂ) * ((σ : ℂ) / (2 * (Real.pi : ℂ))) = (σ : ℂ) := by
      field_simp [show (2 * (Real.pi : ℂ)) ≠ 0 by
        exact_mod_cast Real.two_pi_pos.ne']
    rw [hcancel]
  simpa [hscaleC, hscaleC'] using h

/-- The general canonical one-variable extension is holomorphic on the upper
half-plane. -/
theorem section43FourierInvPairingCanonicalExtension_differentiableOn
    (f : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ
      (section43FourierInvPairingCanonicalExtension f)
      SCV.upperHalfPlane := by
  let T := section43FourierInvPairingCLM f
  let Fcore : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  let F : ℂ → ℂ := Fcore ∘ fun w => (((2 * Real.pi : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    have hmap : Set.MapsTo (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
        SCV.upperHalfPlane SCV.upperHalfPlane := by
      intro z hz
      dsimp [SCV.upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane := by
      intro z hz
      simpa using
        ((((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (((2 * Real.pi : ℝ) : ℂ))).differentiableWithinAt))
    simpa [F, Fcore] using (SCV.fourierLaplaceExt_differentiableOn T).comp hmul hmap
  have hEq : section43FourierInvPairingCanonicalExtension f = F := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      show section43FourierInvPairingCanonicalExtension f w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change section43FourierInvPairingCanonicalExtension f w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [section43FourierInvPairingCanonicalExtension, dif_pos hw, dif_pos hscaled]
      simp [T]
    · have hnotscaled : ¬ 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        intro hscaled
        have hscaled' : 0 < (2 * Real.pi) * w.im := by
          simpa [Complex.mul_im, mul_assoc] using hscaled
        nlinarith [Real.two_pi_pos, hscaled']
      show section43FourierInvPairingCanonicalExtension f w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change section43FourierInvPairingCanonicalExtension f w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [section43FourierInvPairingCanonicalExtension, dif_neg hw, dif_neg hnotscaled]
  rw [hEq]
  exact hF_diff

/-- A positive real Laplace parameter is the canonical extension value at the
corresponding positive imaginary height after the built-in `2π` scaling. -/
theorem section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {σ : ℝ} (hσ : 0 < σ) :
    section43ComplexLaplaceTransform f (σ : ℂ) =
      section43FourierInvPairingCanonicalExtension f
        ((σ / (2 * Real.pi)) * Complex.I) := by
  have hη : 0 < σ / (2 * Real.pi) := div_pos hσ Real.two_pi_pos
  have h :=
    section43FourierInvPairingCanonicalExtension_eq_complexLaplaceTransform
      (f := f) hf_supp hη
  have hscaleC :
      2 * (Real.pi : ℂ) * ((σ : ℂ) / (2 * (Real.pi : ℂ))) = (σ : ℂ) := by
    field_simp [show (2 * (Real.pi : ℂ)) ≠ 0 by
      exact_mod_cast Real.two_pi_pos.ne']
  simpa [hscaleC] using h.symm

/-- The one-coordinate Laplace scalar from the multivariate `(4.20)` normal
form is the raw complex Laplace transform of the extracted time-slice
Schwartz function. -/
theorem section43OneCoordinateLaplaceIntegral_eq_complexLaplaceTransform
    {n : ℕ}
    (F : SchwartzNPoint d (n + 1))
    (r : Fin (n + 1))
    (t : Fin (n + 1) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin (n + 1) × Fin d))
    (σ : ℝ) :
    section43OneCoordinateLaplaceIntegral (d := d) (n := n) F r t ξ σ =
      section43ComplexLaplaceTransform
        (section43PartialFourierSpatialTimeSliceSchwartz
          (d := d) (n := n + 1) F r t ξ)
        (σ : ℂ) := by
  rw [section43OneCoordinateLaplaceIntegral, section43ComplexLaplaceTransform]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  have hslice :
      (section43PartialFourierSpatialTimeSliceSchwartz
        (d := d) (n := n + 1) F r t ξ : ℝ → ℂ) s =
        partialFourierSpatial_fun (d := d) (n := n + 1) F
          (Function.update t r s, ξ) := rfl
  rw [hslice]
  have hexp : -(s : ℂ) * (σ : ℂ) = -(σ : ℂ) * (s : ℂ) := by
    ring
  rw [hexp]

/-- Positive-energy OS I `(4.20)` normal form, with the distinguished
coordinate expressed as the raw complex Laplace transform of the extracted
one-variable time slice. -/
theorem section43FourierLaplaceIntegral_eq_iterated_complexLaplaceTransform_of_mem_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1)) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        section43ComplexLaplaceTransform
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n + 1)
            (section43DiffPullbackCLM d (n + 1) f)
            r
            ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
            (section43QSpatial (d := d) (n := n + 1) q))
          (section43QTime (d := d) (n := n + 1) q r : ℂ) := by
  rw [section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplaceIntegral_of_mem_positiveEnergy
    (d := d) (n := n) f q r hq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with τbg
  rw [section43OneCoordinateLaplaceIntegral_eq_complexLaplaceTransform]

/-- Positive-energy OS I `(4.20)` normal form with the distinguished
one-variable factor rewritten as the canonical Paley-Wiener slice extension.

The extra strict positivity hypothesis is exactly what is needed to evaluate
the canonical extension at the positive imaginary height
`q_r^0 / (2π)`. -/
theorem
    section43FourierLaplaceIntegral_eq_iterated_canonicalSliceExtension_of_mem_positiveEnergy_of_posCoord
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        section43FourierInvPairingCanonicalExtension
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n + 1)
            (section43DiffPullbackCLM d (n + 1) f)
            r
            ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
            (section43QSpatial (d := d) (n := n + 1) q))
          (((section43QTime (d := d) (n := n + 1) q r) /
              (2 * Real.pi)) * Complex.I) := by
  rw [section43FourierLaplaceIntegral_eq_iterated_complexLaplaceTransform_of_mem_positiveEnergy
    (d := d) (n := n) f q r hq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with τbg
  congr 1
  exact
    section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
      (f := section43PartialFourierSpatialTimeSliceSchwartz
        (d := d) (n := n + 1)
        (section43DiffPullbackCLM d (n + 1) f)
        r
        ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
        (section43QSpatial (d := d) (n := n + 1) q))
      (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
        (d := d) (n := n + 1) f r
        ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
        (section43QSpatial (d := d) (n := n + 1) q))
      hqr

/-- Positive-energy OS I `(4.20)` normal form with the distinguished
one-variable factor rewritten into the descended half-line quotient pairing
against the Paley-Wiener kernel `ψ_{i q_r^0}`. -/
theorem
    section43FourierLaplaceIntegral_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43FourierInvPairing_hasOneSidedFourierSupport
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q))
            (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
              (d := d) (n := n + 1) f r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime (d := d) (n := n + 1) q r : ℂ) * Complex.I))
              (by
                simpa [Complex.mul_im, hqr.ne'] using hqr))) := by
  rw [section43FourierLaplaceIntegral_eq_iterated_canonicalSliceExtension_of_mem_positiveEnergy_of_posCoord
    (d := d) (n := n) f q r hq hqr]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with τbg
  congr 1
  exact
    section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ_of_pos
      (f := section43PartialFourierSpatialTimeSliceSchwartz
        (d := d) (n := n + 1)
        (section43DiffPullbackCLM d (n + 1) f)
        r
        ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
        (section43QSpatial (d := d) (n := n + 1) q))
      (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
        (d := d) (n := n + 1) f r
        ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
        (section43QSpatial (d := d) (n := n + 1) q))
      hqr

/-- If an ambient Schwartz representative is explicitly known to be the OS I
Section 4.3 Fourier-Laplace transform on the positive-energy half-space, then
its value at a positive-energy point with one strictly positive time coordinate
has the descended one-variable `ψ_Z` normal form.

This is the first consumer-facing theorem after the OS I correction: the
hypothesis is the explicit `(4.19)-(4.20)` transform formula, not the old
`os1TransportComponent` quotient-inclusion surface. -/
theorem
    section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (Φ : SchwartzNPoint d (n + 1))
    (hΦ : section43FourierLaplaceRepresentative d (n + 1) f Φ)
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    Φ q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43FourierInvPairing_hasOneSidedFourierSupport
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q))
            (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
              (d := d) (n := n + 1) f r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime (d := d) (n := n + 1) q r : ℂ) * Complex.I))
              (by
                simpa [Complex.mul_im, hqr.ne'] using hqr))) := by
  calc
    Φ q = section43FourierLaplaceIntegral d (n + 1) f q :=
      section43FourierLaplaceRepresentative_apply
        (d := d) (n := n + 1) hΦ hq
    _ = _ :=
      section43FourierLaplaceIntegral_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
        (d := d) (n := n) f q r hq hqr

/-- Height-specialized version of
`section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord`.
If the distinguished positive-energy time coordinate is `2π η`, then the
strict positivity hypothesis required by the descended one-variable normal form
is discharged from the positive Wightman height `η`. -/
theorem
    section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (Φ : SchwartzNPoint d (n + 1))
    (hΦ : section43FourierLaplaceRepresentative d (n + 1) f Φ)
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (η : ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hη : 0 < η)
    (hqr : section43QTime (d := d) (n := n + 1) q r = 2 * Real.pi * η) :
    Φ q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43FourierInvPairing_hasOneSidedFourierSupport
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := n + 1)
              (section43DiffPullbackCLM d (n + 1) f)
              r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q))
            (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
              (d := d) (n := n + 1) f r
              ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial (d := d) (n := n + 1) q)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime (d := d) (n := n + 1) q r : ℂ) * Complex.I))
              (by
                have hpos : 0 < section43QTime (d := d) (n := n + 1) q r := by
                  rw [hqr]
                  exact mul_pos Real.two_pi_pos hη
                simpa [Complex.mul_im, hpos.ne'] using hpos))) := by
  have hqr_pos : 0 < section43QTime (d := d) (n := n + 1) q r := by
    rw [hqr]
    exact mul_pos Real.two_pi_pos hη
  exact
    section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
      (d := d) (n := n) f Φ hΦ q r hq hqr_pos

/-- Right-tail specialization of the transformed-representative normal form.

For a full pair point `q`, the first coordinate of
`section43RightTailBlock d n m q` is the central tail gap.  This theorem
packages the exact Packet-H specialization with that coordinate as the
one-variable `ψ_Z` height. -/
theorem
    section43FourierLaplaceRepresentative_rightTailBlock_eq_iterated_descendedPsiZ_of_height
    (d n m : ℕ) [NeZero d]
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (ψ : SchwartzNPoint d (m + 1))
    (hψ : section43FourierLaplaceRepresentative d (m + 1) g ψ)
    (q : NPointDomain d (n + (m + 1)))
    (η : ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hη : 0 < η)
    (hgap :
      section43QTime (d := d) (n := n + (m + 1)) q
        (section43TailGapIndex (n := n) (m := m + 1) (Nat.succ_pos m)) =
          2 * Real.pi * η) :
    let qR : NPointDomain d (m + 1) := section43RightTailBlock d n (m + 1) q
    ψ qR =
      ∫ τbg : Fin m → ℝ,
        Complex.exp
          (-(∑ i : Fin m,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := m + 1) qR
                    ((0 : Fin (m + 1)).succAbove i) : ℂ))) *
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := m + 1)
              (section43DiffPullbackCLM d (m + 1) g)
              0
              ((section43TimeSplitMeasurableEquiv (0 : Fin (m + 1))).symm (0, τbg))
              (section43QSpatial (d := d) (n := m + 1) qR)))
          (section43FourierInvPairing_hasOneSidedFourierSupport
            (section43PartialFourierSpatialTimeSliceSchwartz
              (d := d) (n := m + 1)
              (section43DiffPullbackCLM d (m + 1) g)
              0
              ((section43TimeSplitMeasurableEquiv (0 : Fin (m + 1))).symm (0, τbg))
              (section43QSpatial (d := d) (n := m + 1) qR))
            (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
              (d := d) (n := m + 1) g 0
              ((section43TimeSplitMeasurableEquiv (0 : Fin (m + 1))).symm (0, τbg))
              (section43QSpatial (d := d) (n := m + 1) qR)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime
                    (d := d) (n := m + 1)
                    qR 0 : ℂ) * Complex.I))
              (by
                have hpos :
                    0 < section43QTime (d := d) (n := m + 1)
                      qR 0 := by
                  dsimp [qR]
                  have hzero :
                      section43QTime (d := d) (n := m + 1)
                          (section43RightTailBlock d n (m + 1) q) 0 =
                        section43QTime (d := d) (n := n + (m + 1)) q
                          (section43TailGapIndex (n := n) (m := m + 1)
                            (Nat.succ_pos m)) := by
                    simpa using
                      (section43QTime_rightTailBlock_zero
                        (d := d) (n := n) (m := m + 1) q (Nat.succ_pos m))
                  rw [hzero, hgap]
                  exact mul_pos Real.two_pi_pos hη
                simpa [Complex.mul_im, hpos.ne'] using hpos))) := by
  dsimp only
  let qR : NPointDomain d (m + 1) := section43RightTailBlock d n (m + 1) q
  have hqR :
      qR ∈ section43PositiveEnergyRegion d (m + 1) := by
    dsimp [qR]
    exact section43RightTailBlock_mem_positiveEnergy (d := d) (n := n) (m := m + 1) hq
  have hgapR :
      section43QTime (d := d) (n := m + 1)
        qR 0 = 2 * Real.pi * η := by
    dsimp [qR]
    have hzero :
        section43QTime (d := d) (n := m + 1)
            (section43RightTailBlock d n (m + 1) q) 0 =
          section43QTime (d := d) (n := n + (m + 1)) q
            (section43TailGapIndex (n := n) (m := m + 1) (Nat.succ_pos m)) := by
      simpa using
        (section43QTime_rightTailBlock_zero
          (d := d) (n := n) (m := m + 1) q (Nat.succ_pos m))
    rw [hzero]
    exact hgap
  change ψ qR = _
  exact
    section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height
      (d := d) (n := m) g ψ hψ qR 0 η hqR hη hgapR

end OSReconstruction
