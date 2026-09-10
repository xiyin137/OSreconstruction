/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertVectorField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchyKernel
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.SCV.ConnectedNeighborhood























noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A fixed family of Hilbert-space Taylor coefficients. -/
structure HilbertCauchyTaylorFamily
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : ℕ) where
  coefficient : (Fin k → ℕ) → H

namespace HilbertCauchyTaylorFamily

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {k : ℕ}

/-- The scalar monomial attached to a multi-index. -/
def monomial
    (_T : HilbertCauchyTaylorFamily H k)
    (increment : Fin k → ℂ)
    (α : Fin k → ℕ) : ℂ :=
  ∏ i, increment i ^ α i

/-- The Hilbert Taylor polynomial homogeneous of total degree `p`. -/
def homogeneousTerm
    (T : HilbertCauchyTaylorFamily H k)
    (increment : Fin k → ℂ)
    (p : ℕ) : H :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
    T.monomial increment α • T.coefficient α

/-- The finite Hilbert Taylor polynomial. -/
def partialSum
    (T : HilbertCauchyTaylorFamily H k)
    (N : ℕ)
    (increment : Fin k → ℂ) : H :=
  ∑ p ∈ Finset.range N, T.homogeneousTerm increment p

/-- The Taylor polynomial as concrete Hilbert Gram data. -/
def gramData
    (T : HilbertCauchyTaylorFamily H k)
    (increment : Fin k → ℂ) :
    HilbertTaylorGramData H where
  homogeneousTerm := T.homogeneousTerm increment
  scalarGram p q :=
    @inner ℂ H _ (T.homogeneousTerm increment p)
      (T.homogeneousTerm increment q)
  inner_homogeneousTerm_eq_scalarGram := fun _ _ => rfl

@[simp] theorem gramData_partialSum
    (T : HilbertCauchyTaylorFamily H k)
    (increment : Fin k → ℂ)
    (N : ℕ) :
    (T.gramData increment).partialSum N =
      T.partialSum N increment :=
  rfl

/-- Every finite Hilbert Taylor polynomial is entire in the increment. -/
theorem differentiable_partialSum
    (T : HilbertCauchyTaylorFamily H k)
    (N : ℕ) :
    Differentiable ℂ (T.partialSum N) := by
  apply Differentiable.fun_sum
  intro p hp
  apply Differentiable.fun_sum
  intro α hα
  exact
    (by
      unfold monomial
      fun_prop : Differentiable ℂ (fun z => T.monomial z α)).smul_const _

/-- The reflected scalar Cauchy coefficients are the Gram coefficients of the
Hilbert Taylor coefficient vectors. -/
structure ReflectedCauchyCompatibility
    (T : HilbertCauchyTaylorFamily H k)
    (D : ReflectedCauchyPolydiscData k) : Prop where
  cauchyCoeff_eq_inner :
    ∀ α β,
      SCV.cauchyCoeffPolydisc D.scalar D.center
          (fun _ => D.radius) (Fin.append α β) =
        @inner ℂ H _ (T.coefficient α) (T.coefficient β)

namespace ReflectedCauchyCompatibility

variable
  {T : HilbertCauchyTaylorFamily H k}
  {D : ReflectedCauchyPolydiscData k}

/-- One weighted reflected Cauchy term is the corresponding weighted Hilbert
coefficient pairing. -/
theorem multiIndexTerm_append_eq
    (C : T.ReflectedCauchyCompatibility D)
    (increment : Fin k → ℂ)
    (hincrement :
      ∀ i, ‖reflectedCauchyIncrement increment i‖ < D.radius)
    (α β : Fin k → ℕ) :
    (D.atIncrement
        (reflectedCauchyIncrement increment) hincrement).multiIndexTerm
        (Fin.append α β) =
      starRingEnd ℂ (T.monomial increment α) *
        T.monomial increment β *
          @inner ℂ H _ (T.coefficient α) (T.coefficient β) := by
  rw [ReflectedCauchyCoefficientData.multiIndexTerm]
  simp only [ReflectedCauchyPolydiscData.atIncrement]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right,
    reflectedCauchyIncrement_left, reflectedCauchyIncrement_right]
  rw [C.cauchyCoeff_eq_inner]
  simp only [monomial, map_prod, map_pow]

/-- The Gram coefficient of two homogeneous Hilbert Taylor polynomials is the
matching reflected bidegree of the scalar Cauchy expansion. -/
theorem inner_homogeneousTerm_eq_scalarGram
    (C : T.ReflectedCauchyCompatibility D)
    (increment : Fin k → ℂ)
    (hincrement :
      ∀ i, ‖reflectedCauchyIncrement increment i‖ < D.radius)
    (p q : ℕ) :
    @inner ℂ H _
        (T.homogeneousTerm increment p)
        (T.homogeneousTerm increment q) =
      (D.atIncrement
        (reflectedCauchyIncrement increment) hincrement).scalarGram p q := by
  rw [ReflectedCauchyCoefficientData.scalarGram_eq_sum_antidiagonalTuple]
  simp only [homogeneousTerm, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  rw [C.multiIndexTerm_append_eq increment hincrement α β]
  ring

end ReflectedCauchyCompatibility

private theorem norm_reflectedCauchyIncrement_le
    {r : ℝ} {increment : Fin k → ℂ}
    (hincrement : ∀ i, ‖increment i‖ ≤ r) :
    ∀ j, ‖reflectedCauchyIncrement increment j‖ ≤ r := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedCauchyIncrement_left]
    simpa using hincrement i
  · intro i
    rw [reflectedCauchyIncrement_right]
    exact hincrement i

private theorem norm_reflectedCauchyIncrement_lt
    {R : ℝ} {increment : Fin k → ℂ}
    (hincrement : ∀ i, ‖increment i‖ < R) :
    ∀ j, ‖reflectedCauchyIncrement increment j‖ < R := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [reflectedCauchyIncrement_left]
    simpa using hincrement i
  · intro i
    rw [reflectedCauchyIncrement_right]
    exact hincrement i

/-- Reflected scalar Cauchy control makes the Hilbert Taylor polynomials
uniformly Cauchy on every strictly smaller closed polydisc. -/
theorem uniformCauchySeqOn_partialSum_of_reflectedPolydisc
    (T : HilbertCauchyTaylorFamily H k)
    (D : ReflectedCauchyPolydiscData k)
    (C : T.ReflectedCauchyCompatibility D)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.radius) :
    UniformCauchySeqOn
      T.partialSum atTop
      (SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r)) := by
  apply
    HilbertTaylorGramData.uniformCauchySeqOn_partialSum_of_norm_scalarGram_le
      T.gramData
      (SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r))
      (D.gradedMajorant r)
      (D.gradedMajorant_nonneg hr)
      (D.summable_gradedMajorant hr hrR)
  intro z hz p q
  have hz_le : ∀ i, ‖z i‖ ≤ r := by
    intro i
    simpa [dist_zero_right] using hz i
  have hz_lt : ∀ i, ‖z i‖ < D.radius :=
    fun i => (hz_le i).trans_lt hrR
  let hincrement :
      ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius :=
    norm_reflectedCauchyIncrement_lt hz_lt
  change
    ‖@inner ℂ H _
        (T.homogeneousTerm z p)
        (T.homogeneousTerm z q)‖ ≤
      D.gradedMajorant r (p, q)
  rw [C.inner_homogeneousTerm_eq_scalarGram z hincrement p q]
  exact
    D.norm_scalarGram_atIncrement_le_gradedMajorant
      hr hrR (reflectedCauchyIncrement z) hincrement
      (norm_reflectedCauchyIncrement_le hz_le) p q

/-- One reflected scalar Cauchy polydisc constructs a holomorphic
Hilbert-valued field from coefficient vectors already living in the target
Hilbert space. -/
theorem exists_holomorphicField_of_reflectedPolydisc
    [CompleteSpace H]
    (T : HilbertCauchyTaylorFamily H k)
    (D : ReflectedCauchyPolydiscData k)
    (C : T.ReflectedCauchyCompatibility D) :
    ∃ Ψ : (Fin k → ℂ) → H,
      TendstoLocallyUniformlyOn
          T.partialSum Ψ atTop
          (SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)) ∧
        DifferentiableOn ℂ Ψ
          (SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)) := by
  apply
    SCV.exists_tendstoLocallyUniformlyOn_differentiableOn_fin_of_locally_uniformCauchy
  · intro z hz
    let r := (‖z‖ + D.radius) / 2
    have hz_norm : ‖z‖ < D.radius := by
      rw [pi_norm_lt_iff D.radius_pos]
      intro i
      simpa [dist_zero_right] using hz i
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      linarith [norm_nonneg z, D.radius_pos]
    have hzr : ‖z‖ < r := by
      dsimp [r]
      linarith
    have hrR : r < D.radius := by
      dsimp [r]
      linarith
    let V :=
      SCV.closedPolydisc (0 : Fin k → ℂ) (fun _ => r)
    have hz_open :
        z ∈ SCV.Polydisc (0 : Fin k → ℂ) (fun _ => r) := by
      intro i
      change dist (z i) 0 < r
      rw [dist_zero_right]
      exact (norm_le_pi_norm z i).trans_lt hzr
    have hV_nhds :
        V ∈ 𝓝[
          SCV.Polydisc
            (0 : Fin k → ℂ) (fun _ => D.radius)] z := by
      apply mem_nhdsWithin_of_mem_nhds
      exact Filter.mem_of_superset
        (SCV.polydisc_isOpen.mem_nhds hz_open)
        SCV.polydisc_subset_closedPolydisc
    refine ⟨V, hV_nhds, ?_⟩
    exact
      T.uniformCauchySeqOn_partialSum_of_reflectedPolydisc
        D C hr_nonneg hrR
  · intro N
    exact (T.differentiable_partialSum N).differentiableOn
  · exact SCV.polydisc_isOpen

end HilbertCauchyTaylorFamily

/-- Local equality of a scalar continuation with the reflected Hilbert kernel
forces the scalar Cauchy coefficients to be the Gram coefficients of the old
Hilbert field.

The scalar and Hilbert Cauchy radii may differ. Radius independence is obtained
by comparing both coefficient integrals with the common derivative germ at the
reflected center; the reflected-kernel coefficient factorization is then the
local theorem from `OSToWightmanOSIIChapterVHilbertCauchyKernel`. -/
theorem reflectedCauchyCompatibility_of_eventuallyEq_kernel
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {k : ℕ}
    (oldField : (Fin (k + 1) → ℂ) → H)
    (oldDomain : Set (Fin (k + 1) → ℂ))
    (oldDomain_open : IsOpen oldDomain)
    (oldField_holomorphic : DifferentiableOn ℂ oldField oldDomain)
    (center : Fin (k + 1) → ℂ)
    (oldRadius : ℝ)
    (oldRadius_pos : 0 < oldRadius)
    (oldClosedPolydisc :
      SCV.closedPolydisc center (fun _ => oldRadius) ⊆ oldDomain)
    (scalarData : ReflectedCauchyPolydiscData (k + 1))
    (scalar_center :
      scalarData.center = reflectedCauchyCenter center)
    (scalarDomain :
      Set (Fin ((k + 1) + (k + 1)) → ℂ))
    (scalarDomain_open : IsOpen scalarDomain)
    (scalarClosedPolydisc :
      SCV.closedPolydisc scalarData.center
          (fun _ => scalarData.radius) ⊆ scalarDomain)
    (scalar_holomorphic :
      DifferentiableOn ℂ scalarData.scalar scalarDomain)
    (scalar_eq_kernel :
      scalarData.scalar =ᶠ[𝓝 (reflectedCauchyCenter center)]
        reflectedHilbertKernel oldField) :
    let T : HilbertCauchyTaylorFamily H (k + 1) :=
      { coefficient := fun α =>
          SCV.cauchyCoeffPolydisc oldField center
            (fun _ => oldRadius) α }
    T.ReflectedCauchyCompatibility scalarData := by
  dsimp
  refine { cauchyCoeff_eq_inner := ?_ }
  intro α β
  have hscalarClosed :
      SCV.closedPolydisc
          (reflectedCauchyCenter center)
          (fun _ => scalarData.radius) ⊆ scalarDomain := by
    simpa only [← scalar_center] using scalarClosedPolydisc
  rw [scalar_center]
  exact
    cauchyCoeffPolydisc_eq_inner_of_eventuallyEq_reflectedHilbertKernel
      scalarData.radius_pos oldRadius_pos
      scalarDomain_open oldDomain_open
      hscalarClosed oldClosedPolydisc
      scalar_holomorphic oldField_holomorphic
      scalar_eq_kernel α β

/-- Every point of an open finite-dimensional complex domain admits a
positive-radius closed uniform polydisc contained in that domain. -/
theorem exists_closedPolydisc_subset_open
    {m : ℕ}
    {U : Set (Fin m → ℂ)}
    (hU : IsOpen U)
    {center : Fin m → ℂ}
    (hcenter : center ∈ U) :
    ∃ R > 0,
      SCV.closedPolydisc center (fun _ => R) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU center hcenter
  refine ⟨ε / 2, by linarith, fun w hw => hεU ?_⟩
  exact
    lt_of_le_of_lt
      ((dist_pi_le_iff (by linarith)).mpr hw)
      (by linarith)

/-- Package a holomorphic scalar function as reflected Cauchy data on any
positive closed uniform polydisc contained in its domain.  The boundary bound
is obtained from compactness, so no separate estimate is required when
recentering an already-constructed continuation. -/
theorem exists_reflectedCauchyPolydiscData_of_holomorphic
    {k : ℕ}
    (scalar : (Fin (k + k) → ℂ) → ℂ)
    (center : Fin (k + k) → ℂ)
    (R : ℝ)
    (hR : 0 < R)
    (U : Set (Fin (k + k) → ℂ))
    (hclosed :
      SCV.closedPolydisc center (fun _ => R) ⊆ U)
    (hscalar : DifferentiableOn ℂ scalar U) :
    ∃ D : ReflectedCauchyPolydiscData k,
      D.scalar = scalar ∧
        D.center = center ∧
          D.radius = R := by
  obtain ⟨C, hC⟩ :=
    (SCV.isCompact_closedPolydisc :
      IsCompact (SCV.closedPolydisc center (fun _ => R)))
      |>.exists_bound_of_continuousOn
        (hscalar.continuousOn.mono hclosed)
  let D : ReflectedCauchyPolydiscData k :=
    { scalar := scalar
      center := center
      radius := R
      bound := max C 0
      radius_pos := hR
      bound_nonneg := le_max_right C 0
      norm_scalar_le := by
        intro w hw
        exact
          (hC w (SCV.distinguishedBoundary_subset_closedPolydisc hw)).trans
            (le_max_left C 0) }
  exact ⟨D, rfl, rfl, rfl⟩

/-- Data for analytically continuing an existing Hilbert-valued field from an
arbitrary complex center using a larger reflected scalar Cauchy polydisc. -/
structure ComplexCenteredHilbertCauchyContinuationData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : ℕ) where
  oldField : (Fin (k + 1) → ℂ) → H
  oldDomain : Set (Fin (k + 1) → ℂ)
  oldDomain_open : IsOpen oldDomain
  oldField_holomorphic : DifferentiableOn ℂ oldField oldDomain
  center : Fin (k + 1) → ℂ
  oldRadius : ℝ
  oldRadius_pos : 0 < oldRadius
  oldClosedPolydisc :
    SCV.closedPolydisc center (fun _ => oldRadius) ⊆ oldDomain
  scalarData : ReflectedCauchyPolydiscData (k + 1)
  scalar_center :
    scalarData.center = reflectedCauchyCenter center
  scalarDomain : Set (Fin ((k + 1) + (k + 1)) → ℂ)
  scalarDomain_open : IsOpen scalarDomain
  scalarClosedPolydisc :
    SCV.closedPolydisc scalarData.center
        (fun _ => scalarData.radius) ⊆ scalarDomain
  scalar_holomorphic :
    DifferentiableOn ℂ scalarData.scalar scalarDomain
  scalar_eq_reflectedKernel :
    scalarData.scalar =ᶠ[𝓝 (reflectedCauchyCenter center)]
      reflectedHilbertKernel oldField

namespace ComplexCenteredHilbertCauchyContinuationData

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {k : ℕ}

/-- The retained local reflected-kernel germ gives the Cauchy Gram
compatibility consumed by the Hilbert Taylor construction. -/
theorem coefficientCompatibility
    (D : ComplexCenteredHilbertCauchyContinuationData H k) :
    let T : HilbertCauchyTaylorFamily H (k + 1) :=
      { coefficient := fun α =>
          SCV.cauchyCoeffPolydisc D.oldField D.center
            (fun _ => D.oldRadius) α }
    T.ReflectedCauchyCompatibility D.scalarData :=
  reflectedCauchyCompatibility_of_eventuallyEq_kernel
    D.oldField D.oldDomain D.oldDomain_open D.oldField_holomorphic
    D.center D.oldRadius D.oldRadius_pos D.oldClosedPolydisc
    D.scalarData D.scalar_center
    D.scalarDomain D.scalarDomain_open D.scalarClosedPolydisc
    D.scalar_holomorphic D.scalar_eq_reflectedKernel

/-- The old field's Cauchy coefficients, now regarded as vectors from which a
larger continuation chart will be constructed. -/
def coefficientFamily
    (D : ComplexCenteredHilbertCauchyContinuationData H k) :
    HilbertCauchyTaylorFamily H (k + 1) where
  coefficient α :=
    SCV.cauchyCoeffPolydisc D.oldField D.center
      (fun _ => D.oldRadius) α

/-- Each homogeneous vector polynomial is the matching Cauchy power-series
term of the old Hilbert field. -/
theorem homogeneousTerm_eq_cauchyPowerSeries
    (D : ComplexCenteredHilbertCauchyContinuationData H k)
    (increment : Fin (k + 1) → ℂ)
    (p : ℕ) :
    D.coefficientFamily.homogeneousTerm increment p =
      SCV.cauchyPowerSeriesPolydisc
        D.oldField D.center (fun _ => D.oldRadius) p
        (fun _ => increment) := by
  rw [SCV.cauchyPowerSeriesPolydisc_apply_diag]
  rfl

/-- The old Hilbert field is locally the sum of the same finite polynomials
used by the continuation chart. -/
theorem eventually_tendsto_partialSum_oldField
    (D : ComplexCenteredHilbertCauchyContinuationData H k) :
    ∀ᶠ increment : Fin (k + 1) → ℂ in 𝓝 0,
      Tendsto
        (fun N => D.coefficientFamily.partialSum N increment)
        atTop
        (𝓝 (D.oldField (D.center + increment))) := by
  have hp :=
    SCV.hasFPowerSeriesAt_cauchyPowerSeriesPolydisc_of_differentiableOn
      D.oldRadius_pos D.oldDomain_open D.oldClosedPolydisc
      D.oldField_holomorphic
  filter_upwards [hp.eventually_hasSum] with increment hincrement
  have hterms :
      (fun p =>
        D.coefficientFamily.homogeneousTerm increment p) =
      (fun p =>
        SCV.cauchyPowerSeriesPolydisc
          D.oldField D.center (fun _ => D.oldRadius) p
          (fun _ => increment)) := by
    funext p
    exact D.homogeneousTerm_eq_cauchyPowerSeries increment p
  have hsum :
      HasSum
        (fun p => D.coefficientFamily.homogeneousTerm increment p)
        (D.oldField (D.center + increment)) := by
    rw [hterms]
    exact hincrement
  simpa [HilbertCauchyTaylorFamily.partialSum] using hsum.tendsto_sum_nat

/-- The complex-centered scalar Gram data constructs a larger holomorphic
Hilbert chart, and that chart agrees with the old field on a neighborhood of
the chosen center. -/
theorem exists_continuationField
    (D : ComplexCenteredHilbertCauchyContinuationData H k) :
    ∃ Ψ : (Fin (k + 1) → ℂ) → H,
      TendstoLocallyUniformlyOn
          D.coefficientFamily.partialSum Ψ atTop
          (SCV.Polydisc
            (0 : Fin (k + 1) → ℂ)
            (fun _ => D.scalarData.radius)) ∧
        DifferentiableOn ℂ Ψ
          (SCV.Polydisc
            (0 : Fin (k + 1) → ℂ)
            (fun _ => D.scalarData.radius)) ∧
        ∀ᶠ increment : Fin (k + 1) → ℂ in 𝓝 0,
          Ψ increment = D.oldField (D.center + increment) := by
  obtain ⟨Ψ, hΨ, hΨ_hol⟩ :=
    D.coefficientFamily.exists_holomorphicField_of_reflectedPolydisc
      D.scalarData D.coefficientCompatibility
  refine ⟨Ψ, hΨ, hΨ_hol, ?_⟩
  have hzero :
      (0 : Fin (k + 1) → ℂ) ∈
        SCV.Polydisc 0 (fun _ => D.scalarData.radius) :=
    SCV.center_mem_polydisc (fun _ => D.scalarData.radius_pos)
  have hdomain :
      SCV.Polydisc
          (0 : Fin (k + 1) → ℂ)
          (fun _ => D.scalarData.radius) ∈
        𝓝 (0 : Fin (k + 1) → ℂ) :=
    SCV.polydisc_isOpen.mem_nhds hzero
  filter_upwards [hdomain, D.eventually_tendsto_partialSum_oldField]
    with increment hincrementDomain hincrementOld
  exact tendsto_nhds_unique
    (hΨ.tendsto_at hincrementDomain)
    hincrementOld

/-- Translate an increment-coordinate continuation field back to absolute
complex coordinates. -/
def absoluteField
    (D : ComplexCenteredHilbertCauchyContinuationData H k)
    (Ψ : (Fin (k + 1) → ℂ) → H)
    (z : Fin (k + 1) → ℂ) : H :=
  Ψ (z - D.center)

/-- In absolute coordinates, the continuation field agrees with the old field
on a neighborhood of the complex center. -/
theorem eventually_absoluteField_eq_oldField
    (D : ComplexCenteredHilbertCauchyContinuationData H k)
    (Ψ : (Fin (k + 1) → ℂ) → H)
    (hΨ :
      ∀ᶠ increment : Fin (k + 1) → ℂ in 𝓝 0,
        Ψ increment = D.oldField (D.center + increment)) :
    (fun z => D.absoluteField Ψ z) =ᶠ[𝓝 D.center] D.oldField := by
  have hshift :
      Tendsto
        (fun z : Fin (k + 1) → ℂ => z - D.center)
        (𝓝 D.center) (𝓝 0) := by
    have hcont :
        Continuous
          (fun z : Fin (k + 1) → ℂ => z - D.center) :=
      (continuous_id :
        Continuous (fun z : Fin (k + 1) → ℂ => z)).sub
          (continuous_const :
            Continuous (fun _ : Fin (k + 1) → ℂ => D.center))
    simpa using hcont.tendsto D.center
  filter_upwards [hshift.eventually hΨ] with z hz
  rw [absoluteField, hz]
  congr 1
  abel

end ComplexCenteredHilbertCauchyContinuationData

end OSIIChapterV
end OSReconstruction
