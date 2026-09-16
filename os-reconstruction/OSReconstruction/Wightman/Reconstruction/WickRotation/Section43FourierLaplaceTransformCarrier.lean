/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceComponentKernel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory

namespace OSReconstruction

/-- The deterministic Section 4.3 frequency projection is onto the quotient
positive-energy component. -/
theorem section43FrequencyProjection_surjective
    (d n : ℕ) [NeZero d] :
    Function.Surjective
      (section43FrequencyProjection (d := d) n :
        SchwartzNPoint d n → Section43PositiveEnergyComponent (d := d) n) := by
  intro q
  obtain ⟨Φ, hΦ⟩ := surjective_section43PositiveEnergyQuotientMap (d := d) n q
  obtain ⟨φ, hφ⟩ := section43FrequencyRepresentative_surjective d n Φ
  refine ⟨φ, ?_⟩
  simpa [section43FrequencyProjection, hφ] using hΦ

/-- The partial spatial Fourier transform of the zero Schwartz function is zero. -/
theorem partialFourierSpatial_fun_zero
    (d n : ℕ) [NeZero d]
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n)
      (0 : SchwartzNPoint d n) p = 0 := by
  rw [partialFourierSpatial_fun]
  have hslice :
      SchwartzMap.partialEval₂
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n)
            (0 : SchwartzNPoint d n)) p.1 = 0 := by
    ext η
    rfl
  rw [hslice]
  simp

/-- Pulling back the zero positive-time test to difference coordinates gives zero. -/
theorem section43DiffPullback_zero
    (d n : ℕ) [NeZero d]
    (hzero_ord :
      tsupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) :
    section43DiffPullbackCLM d n
      ⟨(0 : SchwartzNPoint d n), hzero_ord⟩ = 0 := by
  ext x
  simp [section43DiffPullbackCLM_apply]

/-- The Section 4.3 Fourier-Laplace scalar integral of the zero source is zero. -/
theorem section43FourierLaplaceIntegral_zero
    (d n : ℕ) [NeZero d]
    (hzero_ord :
      tsupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (q : NPointDomain d n) :
    section43FourierLaplaceIntegral d n
      ⟨(0 : SchwartzNPoint d n), hzero_ord⟩ q = 0 := by
  rw [section43FourierLaplaceIntegral]
  simp [section43DiffPullback_zero d n hzero_ord, partialFourierSpatial_fun_zero]

/-- The Fourier-Laplace transform component of the zero source is the zero
positive-energy quotient class. -/
theorem section43FourierLaplaceTransformComponent_zero
    (d n : ℕ) [NeZero d]
    (hzero_ord :
      tsupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (hzero_compact :
      HasCompactSupport ((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) :
    section43FourierLaplaceTransformComponent d n
      (0 : SchwartzNPoint d n) hzero_ord hzero_compact = 0 := by
  obtain ⟨Φ, hΦ_rep, hΦ_q⟩ :=
    section43FourierLaplaceTransformComponent_has_representative
      d n (0 : SchwartzNPoint d n) hzero_ord hzero_compact
  have hΦ_zero_q : section43PositiveEnergyQuotientMap (d := d) n Φ = 0 := by
    have hEqOn :
        Set.EqOn (Φ : NPointDomain d n → ℂ) (0 : NPointDomain d n → ℂ)
          (section43PositiveEnergyRegion d n) := by
      intro q hq
      rw [hΦ_rep q hq]
      exact section43FourierLaplaceIntegral_zero d n hzero_ord q
    calc
      section43PositiveEnergyQuotientMap (d := d) n Φ =
          section43PositiveEnergyQuotientMap (d := d) n 0 :=
        section43PositiveEnergyQuotientMap_eq_of_eqOn_region
          (d := d) (n := n) hEqOn
      _ = 0 := map_zero (section43PositiveEnergyQuotientMap (d := d) n)
  exact hΦ_q ▸ hΦ_zero_q

/-- A canonical ambient Schwartz representative of a compact ordered
Fourier-Laplace transform component.  The zero-source branch is explicit so
finite-support bounds for Borchers sequences remain definitional. -/
noncomputable def section43TransformComponentTarget
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    SchwartzNPoint d n := by
  classical
  exact
    if _hzero : f = 0 then
      0
    else
      Classical.choose
        (section43FrequencyProjection_surjective d n
          (section43FourierLaplaceTransformComponent d n f hf_ord hf_compact))

/-- The canonical target representative realizes the requested
Fourier-Laplace transform component in the positive-energy quotient. -/
theorem section43TransformComponentTarget_freq_eq
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    section43FrequencyProjection (d := d) n
      (section43TransformComponentTarget d n f hf_ord hf_compact) =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact := by
  classical
  by_cases hzero : f = 0
  · subst f
    simp [section43TransformComponentTarget,
      section43FourierLaplaceTransformComponent_zero]
  · simp [section43TransformComponentTarget, hzero,
      Classical.choose_spec
        (section43FrequencyProjection_surjective d n
          (section43FourierLaplaceTransformComponent d n f hf_ord hf_compact))]

/-- A source-decorated transform-component carrier: the Wightman-side Borchers
sequence is remembered together with the compact ordered Euclidean source whose
Section 4.3 Fourier-Laplace transform gives each positive-energy component. -/
structure BvtTransformComponentSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  source : PositiveTimeBorchersSequence d
  source_compact : ∀ n,
    HasCompactSupport
      ((((source : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
  freq_eq : ∀ n,
    section43FrequencyProjection (d := d) n (toBorchers.funcs n) =
      section43FourierLaplaceTransformComponent d n
        (((source : BorchersSequence d).funcs n : SchwartzNPoint d n))
        (source.ordered_tsupport n)
        (source_compact n)

/-- Build a transform-component carrier from compact positive-time Borchers
data by choosing canonical ambient representatives degreewise. -/
noncomputable def compactPositiveTime_to_BvtTransformComponentSequence
    {d : ℕ} [NeZero d]
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n :
        SchwartzNPoint d n) : NPointDomain d n → ℂ))) :
    BvtTransformComponentSequence d where
  toBorchers :=
    { funcs := fun n =>
        section43TransformComponentTarget d n
          (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))
          (F.ordered_tsupport n)
          (hF_compact n)
      bound := (F : BorchersSequence d).bound
      bound_spec := by
        intro n hn
        have hsrc0 :
            (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)) = 0 :=
          (F : BorchersSequence d).bound_spec n hn
        simp [section43TransformComponentTarget, hsrc0] }
  source := F
  source_compact := hF_compact
  freq_eq := fun n =>
    section43TransformComponentTarget_freq_eq d n
      (((F : BorchersSequence d).funcs n : SchwartzNPoint d n))
      (F.ordered_tsupport n)
      (hF_compact n)

/-- In degree zero, the deterministic frequency representative is evaluation. -/
theorem section43FrequencyRepresentative_zero_apply
    (d : ℕ) [NeZero d] (φ : SchwartzNPoint d 0) (q : NPointDomain d 0) :
    section43FrequencyRepresentative d 0 φ q = φ 0 := by
  change physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ)
      ((section43CumulativeTailMomentumCLE d 0).symm q) = φ 0
  rw [← physicsFourierFlatCLM_integral]
  have hdim : 0 * (d + 1) = 0 := by omega
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (0 * (d + 1)) → ℝ)) =
        MeasureTheory.Measure.dirac default := by
    rw [hdim]
    simpa using
      (MeasureTheory.Measure.volume_pi_eq_dirac
        (ι := Fin 0) (α := fun _ => ℝ) (x := default))
  rw [hvol, MeasureTheory.integral_dirac]
  have hsum :
      (∑ x : Fin (0 * (d + 1)),
        ((default : Fin (0 * (d + 1)) → ℝ) x : ℂ) *
          (((section43CumulativeTailMomentumCLE d 0).symm q x : ℝ) : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    have : False := by
      rw [hdim] at i
      exact Fin.elim0 i
    exact False.elim this
  rw [hsum]
  simp only [mul_zero, Complex.exp_zero, one_mul]
  exact congrArg φ (Subsingleton.elim _ _)

/-- In degree zero, the spatial Fourier transform part of the Section 4.3
Fourier-Laplace integral is evaluation. -/
theorem partialFourierSpatial_fun_zero_degree
    (d : ℕ) [NeZero d]
    (f : SchwartzNPoint d 0)
    (hf_ord :
      tsupport (f : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (p : (Fin 0 → ℝ) × EuclideanSpace ℝ (Fin 0 × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := 0)
      (section43DiffPullbackCLM d 0 ⟨f, hf_ord⟩) p = f 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 0 × Fin d))) =
        MeasureTheory.Measure.dirac 0 := by
    simpa using (volume_euclideanSpace_eq_dirac (ι := Fin 0 × Fin d))
  rw [hvol, MeasureTheory.integral_dirac]
  simp [section43DiffPullbackCLM_apply, nPointTimeSpatialSchwartzCLE]
  exact congrArg f (Subsingleton.elim _ _)

/-- In degree zero, the Section 4.3 Fourier-Laplace integral is evaluation. -/
theorem section43FourierLaplaceIntegral_zero_degree
    (d : ℕ) [NeZero d]
    (f : SchwartzNPoint d 0)
    (hf_ord :
      tsupport (f : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (q : NPointDomain d 0) :
    section43FourierLaplaceIntegral d 0 ⟨f, hf_ord⟩ q = f 0 := by
  rw [section43FourierLaplaceIntegral]
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
        MeasureTheory.Measure.dirac default := by
    simpa using
      (MeasureTheory.Measure.volume_pi_eq_dirac
        (ι := Fin 0) (α := fun _ => ℝ) (x := default))
  rw [hvol, MeasureTheory.integral_dirac]
  rw [partialFourierSpatial_fun_zero_degree]
  simp

/-- In degree zero, any Section 4.3 Fourier-Laplace representative evaluates
to the source value. -/
theorem section43FourierLaplaceRepresentative_zero_apply
    (d : ℕ) [NeZero d]
    (f Φ : SchwartzNPoint d 0)
    (hf_ord :
      tsupport (f : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hΦ : section43FourierLaplaceRepresentative d 0 ⟨f, hf_ord⟩ Φ) :
    Φ 0 = f 0 := by
  have hq : (0 : NPointDomain d 0) ∈ section43PositiveEnergyRegion d 0 := by
    simp [section43PositiveEnergyRegion]
  rw [hΦ 0 hq]
  exact section43FourierLaplaceIntegral_zero_degree d f hf_ord 0

/-- In degree zero, equality of transform components identifies the actual
scalar values. -/
theorem section43TransformComponent_zero_eval_eq
    (d : ℕ) [NeZero d]
    (φ f : SchwartzNPoint d 0)
    (hf_ord :
      tsupport (f : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hf_compact : HasCompactSupport (f : NPointDomain d 0 → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) 0 φ =
        section43FourierLaplaceTransformComponent d 0 f hf_ord hf_compact) :
    φ 0 = f 0 := by
  obtain ⟨Φ, hΦ_rep, hΦ_q⟩ :=
    section43FourierLaplaceTransformComponent_has_representative d 0 f hf_ord hf_compact
  have hquot :
      section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative d 0 φ) =
        section43PositiveEnergyQuotientMap (d := d) 0 Φ := by
    calc
      section43PositiveEnergyQuotientMap (d := d) 0
          (section43FrequencyRepresentative d 0 φ)
          = section43FourierLaplaceTransformComponent d 0 f hf_ord hf_compact := by
            simpa [section43FrequencyProjection] using hφ_freq
      _ = section43PositiveEnergyQuotientMap (d := d) 0 Φ := hΦ_q.symm
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hquot
  have hq : (0 : NPointDomain d 0) ∈ section43PositiveEnergyRegion d 0 := by
    simp [section43PositiveEnergyRegion]
  have hpoint := hEqOn hq
  rw [section43FrequencyRepresentative_zero_apply d φ 0] at hpoint
  rw [section43FourierLaplaceRepresentative_zero_apply d f Φ hf_ord hΦ_rep] at hpoint
  exact hpoint

/-- Degree-zero tests vanish to infinite order on the coincidence locus
vacuously. -/
theorem VanishesToInfiniteOrderOnCoincidence_zero_degree
    {d : ℕ} (f : SchwartzNPoint d 0) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro _k _x hx
  rcases hx with ⟨i, j, hij, _hij_eq⟩
  exact False.elim (hij (Subsingleton.elim i j))

/-- The OS Hilbert vector carried by a source-decorated transform-component
sequence. -/
noncomputable def bvt_transform_to_osHilbert
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransformComponentSequence d) :
    OSHilbertSpace OS :=
  positiveTimeBorchersVectorCore (d := d) OS F.source

/-- Compact positive-time data transported into the Section 4.3 transform
carrier has the expected OS Hilbert vector. -/
@[simp] theorem bvt_transform_to_osHilbert_compactPositiveTime
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact : ∀ n,
      HasCompactSupport ((((F : BorchersSequence d).funcs n :
        SchwartzNPoint d n) : NPointDomain d n → ℂ))) :
    bvt_transform_to_osHilbert (d := d) OS
        (compactPositiveTime_to_BvtTransformComponentSequence
          (d := d) F hF_compact) =
      positiveTimeBorchersVectorCore (d := d) OS F := rfl

end OSReconstruction
