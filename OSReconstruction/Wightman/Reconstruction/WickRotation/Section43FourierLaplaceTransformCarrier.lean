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
    simpa using
      section43PositiveEnergyQuotientMap_eq_of_eqOn_region
        (d := d) (n := n) hEqOn
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

/-- The degree-zero kernel equality is just normalization after the scalar
values of the two transform components have been identified. -/
theorem zero_degree_kernel_from_evals
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ ψ f g : SchwartzNPoint d 0)
    (hφ : φ 0 = f 0)
    (hψ : ψ 0 = g 0) :
    bvt_W OS lgc 0 (φ.conjTensorProduct ψ) =
      OS.S 0 (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  rw [bvt_normalized_from_boundaryValue (d := d) OS lgc]
  rw [lgc.normalized_zero]
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes]
  · rw [SchwartzMap.conjTensorProduct_apply]
    change starRingEnd ℂ (φ _) * ψ _ = (SchwartzMap.tensorProduct f.osConj g) _
    rw [SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply]
    have hfirst :
        (fun i : Fin 0 =>
          splitFirst 0 0 (0 : NPointDomain d (0 + 0)) (Fin.rev i)) =
            (0 : NPointDomain d 0) := Subsingleton.elim _ _
    have hlast :
        splitLast 0 0 (0 : NPointDomain d (0 + 0)) =
          (0 : NPointDomain d 0) := Subsingleton.elim _ _
    have hreflect :
        timeReflectionN d (splitFirst 0 0 (0 : NPointDomain d (0 + 0))) =
          (0 : NPointDomain d 0) := Subsingleton.elim _ _
    rw [hfirst, hlast, hreflect, hφ, hψ]
  · exact VanishesToInfiniteOrderOnCoincidence_zero_degree (f.osConjTensorProduct g)

/-- The right-degree-zero branch follows from the compiled successor-right
theorem by Hermiticity. -/
theorem kernel_zero_right_of_transformComponent_succRight
    (d m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d (m + 1)) (ψ : SchwartzNPoint d 0)
    (f : SchwartzNPoint d (m + 1))
    (hf_ord :
      tsupport (f : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hf_compact : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ))
    (g : SchwartzNPoint d 0)
    (hg_ord : tsupport (g : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hg_compact : HasCompactSupport (g : NPointDomain d 0 → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) (m + 1) φ =
        section43FourierLaplaceTransformComponent d (m + 1) f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) 0 ψ =
        section43FourierLaplaceTransformComponent d 0 g hg_ord hg_compact) :
    bvt_W OS lgc ((m + 1) + 0) (φ.conjTensorProduct ψ) =
      OS.S ((m + 1) + 0)
        (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  let Fφ : BorchersSequence d := BorchersSequence.single (m + 1) φ
  let Gψ : BorchersSequence d := BorchersSequence.single 0 ψ
  let Ff : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single (m + 1) f hf_ord
  let Gg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 0 g hg_ord
  have hflip_kernel :
      bvt_W OS lgc (0 + (m + 1)) (ψ.conjTensorProduct φ) =
        OS.S (0 + (m + 1))
          (ZeroDiagonalSchwartz.ofClassical (g.osConjTensorProduct f)) := by
    exact bvt_W_kernel_eq_osScalar_of_transformComponent_succRight
      (d := d) (n := 0) (m := m) (OS := OS) (lgc := lgc)
      (φ := ψ) (ψ := φ) (f := g) (hf_ord := hg_ord)
      (hf_compact := hg_compact) (g := f) (hg_ord := hf_ord)
      (hg_compact := hf_compact) hψ_freq hφ_freq
  have hflip_inner :
      WightmanInnerProduct d (bvt_W OS lgc) Gψ Fφ =
        PositiveTimeBorchersSequence.osInner OS Gg Ff := by
    have hOSflip :
        PositiveTimeBorchersSequence.osInner OS Gg Ff =
          OS.S (0 + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical (g.osConjTensorProduct f)) := by
      unfold PositiveTimeBorchersSequence.osInner
      simpa [Gg, Ff] using
        OSInnerProduct_single_single (d := d) OS.S OS.E0_linear
          (n := 0) (m := m + 1) (f := g) (g := f)
    rw [WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (n := 0) (m := m + 1)
      (f := ψ) (g := φ)]
    rw [hOSflip]
    simpa [Fφ, Gψ] using hflip_kernel
  have hinner :
      WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ =
        PositiveTimeBorchersSequence.osInner OS Ff Gg := by
    calc
      WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ
          = starRingEnd ℂ (WightmanInnerProduct d (bvt_W OS lgc) Gψ Fφ) := by
              exact WightmanInnerProduct_hermitian_of (d := d) (W := bvt_W OS lgc)
                (bvt_hermitian_from_boundaryValue (d := d) OS lgc) Fφ Gψ
      _ = starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS Gg Ff) := by
              exact congrArg (starRingEnd ℂ) hflip_inner
      _ = PositiveTimeBorchersSequence.osInner OS Ff Gg := by
              simpa using (PositiveTimeBorchersSequence.osInner_hermitian OS Ff Gg).symm
  calc
    bvt_W OS lgc ((m + 1) + 0) (φ.conjTensorProduct ψ)
        = WightmanInnerProduct d (bvt_W OS lgc) Fφ Gψ := by
            symm
            simpa [Fφ, Gψ] using
              WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
                (hlin := bvt_W_linear (d := d) OS lgc) (n := m + 1) (m := 0)
                (f := φ) (g := ψ)
    _ = PositiveTimeBorchersSequence.osInner OS Ff Gg := hinner
    _ = OS.S ((m + 1) + 0)
        (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
            have hOSorig :
                PositiveTimeBorchersSequence.osInner OS Ff Gg =
                  OS.S ((m + 1) + 0)
                    (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
              unfold PositiveTimeBorchersSequence.osInner
              simpa [Ff, Gg] using
                OSInnerProduct_single_single (d := d) OS.S OS.E0_linear
                  (n := m + 1) (m := 0) (f := f) (g := g)
            exact hOSorig

/-- All-degree transform-component kernel equality.  The successor-right case
is the compiled Abel theorem; the right-degree-zero cases are degree-zero
normalization and Hermiticity. -/
theorem bvt_W_kernel_eq_osScalar_of_transformComponent_allDegrees
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d k)
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d k)
    (hg_ord :
      tsupport (g : NPointDomain d k → ℂ) ⊆ OrderedPositiveTimeRegion d k)
    (hg_compact : HasCompactSupport (g : NPointDomain d k → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) k ψ =
        section43FourierLaplaceTransformComponent d k g hg_ord hg_compact) :
    bvt_W OS lgc (n + k) (φ.conjTensorProduct ψ) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  by_cases hk : k = 0
  · subst k
    by_cases hn : n = 0
    · subst n
      have hφ0 :=
        section43TransformComponent_zero_eval_eq d φ f hf_ord hf_compact hφ_freq
      have hψ0 :=
        section43TransformComponent_zero_eval_eq d ψ g hg_ord hg_compact hψ_freq
      exact zero_degree_kernel_from_evals d OS lgc φ ψ f g hφ0 hψ0
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact kernel_zero_right_of_transformComponent_succRight
        d m OS lgc φ ψ f hf_ord hf_compact g hg_ord hg_compact hφ_freq hψ_freq
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact bvt_W_kernel_eq_osScalar_of_transformComponent_succRight
      (d := d) (n := n) (m := m) (OS := OS) (lgc := lgc)
      (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
      (hf_compact := hf_compact) (g := g) (hg_ord := hg_ord)
      (hg_compact := hg_compact) hφ_freq hψ_freq

/-- On the source-decorated transform-component carrier, the Wightman
sesquilinear form is exactly the OS positive-time sesquilinear form of the
remembered sources. -/
theorem bvt_wightmanInner_eq_transform_osInner
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransformComponentSequence d) :
    WightmanInnerProduct d (bvt_W OS lgc)
        F.toBorchers G.toBorchers =
      PositiveTimeBorchersSequence.osInner OS F.source G.source := by
  let M :=
    max F.toBorchers.bound
      (max G.toBorchers.bound
        (max ((F.source : BorchersSequence d).bound)
          ((G.source : BorchersSequence d).bound)))
  have hFto_le : F.toBorchers.bound ≤ M := by
    exact le_max_left _ _
  have hGto_le : G.toBorchers.bound ≤ M := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hFsrc_le : (F.source : BorchersSequence d).bound ≤ M := by
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hGsrc_le : (G.source : BorchersSequence d).bound ≤ M := by
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hW :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers G.toBorchers
          (M + 1) (M + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFto_le
    · exact Nat.succ_le_succ hGto_le
  have hOS :
      PositiveTimeBorchersSequence.osInner OS F.source G.source =
        OSInnerProductN d OS.S
          (F.source : BorchersSequence d) (G.source : BorchersSequence d)
          (M + 1) (M + 1) := by
    unfold PositiveTimeBorchersSequence.osInner
    apply OSInnerProduct_eq_extended (d := d) OS.S OS.E0_linear
    · exact Nat.succ_le_succ hFsrc_le
    · exact Nat.succ_le_succ hGsrc_le
  rw [hW, hOS]
  unfold WightmanInnerProductN OSInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n _hn
  refine Finset.sum_congr rfl ?_
  intro k _hk
  exact bvt_W_kernel_eq_osScalar_of_transformComponent_allDegrees
    d n k OS lgc
    (F.toBorchers.funcs n) (G.toBorchers.funcs k)
    (((F.source : BorchersSequence d).funcs n : SchwartzNPoint d n))
    (F.source.ordered_tsupport n)
    (F.source_compact n)
    (((G.source : BorchersSequence d).funcs k : SchwartzNPoint d k))
    (G.source.ordered_tsupport k)
    (G.source_compact k)
    (F.freq_eq n)
    (G.freq_eq k)

/-- Positivity on the source-decorated transform-component carrier. -/
theorem bvt_wightmanInner_self_nonneg_onTransformImage
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransformComponentSequence d) :
    0 ≤
      (WightmanInnerProduct d (bvt_W OS lgc)
        F.toBorchers F.toBorchers).re := by
  rw [bvt_wightmanInner_eq_transform_osInner (d := d) OS lgc F F]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F.source

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

/-- The OS Hilbert vectors coming from compact transform-component carriers
are dense. -/
theorem bvt_transform_to_osHilbert_dense
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (bvt_transform_to_osHilbert (d := d) OS)) := by
  let R : Set (OSHilbertSpace OS) :=
    Set.range (bvt_transform_to_osHilbert (d := d) OS)
  have hpos_subset_closure :
      Set.range (positiveTimeBorchersVectorCore (d := d) OS) ⊆ closure R := by
    rintro _ ⟨F, rfl⟩
    let A : ℕ → BvtTransformComponentSequence d := fun N =>
      compactPositiveTime_to_BvtTransformComponentSequence
        (d := d)
        (compactApproxPositiveTimeBorchers (d := d) F N)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N)
    have hA_mem :
        ∀ᶠ N : ℕ in Filter.atTop,
          bvt_transform_to_osHilbert (d := d) OS (A N) ∈ R :=
      Filter.Eventually.of_forall fun N =>
        ⟨A N, rfl⟩
    have hA_tendsto :
        Filter.Tendsto
          (fun N : ℕ => bvt_transform_to_osHilbert (d := d) OS (A N))
          Filter.atTop
          (nhds (positiveTimeBorchersVectorCore (d := d) OS F)) := by
      simpa [A, bvt_transform_to_osHilbert] using
        positiveTimeBorchersVectorCore_compactApprox_tendsto (d := d) OS F
    exact mem_closure_of_tendsto hA_tendsto hA_mem
  rw [dense_iff_closure_eq]
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x _hx
    have hx_pos :
        x ∈ closure (Set.range (positiveTimeBorchersVectorCore (d := d) OS)) := by
      rw [(positiveTimeBorchersVectorCore_dense (d := d) OS).closure_eq]
      exact Set.mem_univ x
    have hx_closure_closure : x ∈ closure (closure R) :=
      closure_mono hpos_subset_closure hx_pos
    have hclosed : IsClosed (closure R) := isClosed_closure
    simpa [R, hclosed.closure_eq] using hx_closure_closure

end OSReconstruction
