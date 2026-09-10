import Mathlib.Analysis.LocallyConvex.Barrelled
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeBoundary

/-!
# OS II Chapter VI: Mixed Time--Spatial Boundary

The fixed-spatial-test boundary theorem produces a tempered distribution in
the real time gaps.  This file proves the complementary continuity statement:
after fixing a time test, the same boundary value is a tempered distribution
in the spatial variables.

The proof first realizes every positive tube slice as a spatial distribution.
Pointwise convergence of those distributions then gives spatial continuity of
the boundary by Banach--Steinhaus.  Consequently the boundary pairing is a
separately continuous bilinear form on the time and spatial Schwartz spaces.

Extending that bilinear form to one functional on full spacetime Schwartz
space is kept as the next, distinct mixed Schwartz-kernel obligation.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

omit [NeZero d] in
private theorem exists_timeIntegratedSpatialDistribution
    (L : (Fin k -> Real) -> OSIISpatialDistribution d k)
    (hL_cont : forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun t => L t chi))
    (spatialSeminorms : Finset (Nat × Nat))
    (constant : Real) (degree : Nat) (hconstant : 0 < constant)
    (hL_bound : forall (t : Fin k -> Real)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
      norm (L t chi) <=
        constant * (1 + norm t) ^ degree *
          spatialSeminorms.sup
            (schwartzSeminormFamily Complex
              (Section43SpatialSpace d k) Complex) chi)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    exists T : OSIISpatialDistribution d k,
      (forall chi, T chi =
        ∫ t : Fin k -> Real, L t chi * phi t) ∧
      forall chi, Integrable (fun t : Fin k -> Real => L t chi * phi t) := by
  let decayDegree : Nat :=
    (volume : Measure (Fin k -> Real)).integrablePower
  let timeSeminorms : Finset (Nat × Nat) :=
    Finset.Iic (degree + decayDegree, 0)
  let timeSeminorm : Real :=
    timeSeminorms.sup
      (schwartzSeminormFamily Complex (Fin k -> Real) Complex) phi
  let spatialSeminorm :
      Seminorm Complex (SchwartzMap (Section43SpatialSpace d k) Complex) :=
    spatialSeminorms.sup
      (schwartzSeminormFamily Complex
        (Section43SpatialSpace d k) Complex)
  let decayIntegral : Real :=
    ∫ t : Fin k -> Real, (1 + norm t) ^ (-(decayDegree : Real))
  let boundConstant : Real :=
    constant * (2 ^ (degree + decayDegree) * timeSeminorm) * decayIntegral
  let value : SchwartzMap (Section43SpatialSpace d k) Complex -> Complex :=
    fun chi => ∫ t : Fin k -> Real, L t chi * phi t
  have htimeSeminorm_nonneg : 0 <= timeSeminorm := apply_nonneg _ _
  have hspatialSeminorm_nonneg :
      forall chi, 0 <= spatialSeminorm chi := fun chi => apply_nonneg _ chi
  have hdecay_integrable :
      Integrable (fun t : Fin k -> Real =>
        (1 + norm t) ^ (-(decayDegree : Real))) := by
    simpa [decayDegree] using
      (MeasureTheory.Measure.integrable_pow_neg_integrablePower
        (μ := (volume : Measure (Fin k -> Real))))
  have hpointwise : forall
      (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
      (t : Fin k -> Real),
      norm (L t chi * phi t) <=
        (1 + norm t) ^ (-(decayDegree : Real)) *
          (constant * (2 ^ (degree + decayDegree) * timeSeminorm) *
            spatialSeminorm chi) := by
    intro chi t
    have hschwartz :
        (1 + norm t) ^ (degree + decayDegree) * norm (phi t) <=
          2 ^ (degree + decayDegree) * timeSeminorm := by
      simpa [timeSeminorm, timeSeminorms] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (k := degree + decayDegree) (n := 0)
          (𝕜 := Complex)
          (m := (degree + decayDegree, 0)) le_rfl le_rfl phi t)
    have hdecay :
        (1 + norm t) ^ degree * norm (phi t) <=
          (1 + norm t) ^ (-(decayDegree : Real)) *
            (2 ^ (degree + decayDegree) * timeSeminorm) := by
      rw [Real.rpow_neg (by positivity), <- div_eq_inv_mul,
        le_div_iff₀' (by positivity), Real.rpow_natCast]
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hschwartz
    rw [norm_mul]
    calc
      norm (L t chi) * norm (phi t) <=
          (constant * (1 + norm t) ^ degree * spatialSeminorm chi) *
            norm (phi t) := by
        gcongr
        simpa [spatialSeminorm] using hL_bound t chi
      _ = constant * spatialSeminorm chi *
          ((1 + norm t) ^ degree * norm (phi t)) := by ring
      _ <= constant * spatialSeminorm chi *
          ((1 + norm t) ^ (-(decayDegree : Real)) *
            (2 ^ (degree + decayDegree) * timeSeminorm)) := by
        gcongr
      _ = (1 + norm t) ^ (-(decayDegree : Real)) *
          (constant * (2 ^ (degree + decayDegree) * timeSeminorm) *
            spatialSeminorm chi) := by ring
  have hintegrable : forall
      chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      Integrable (fun t : Fin k -> Real => L t chi * phi t) := by
    intro chi
    refine Integrable.mono'
      (hdecay_integrable.mul_const
        (constant * (2 ^ (degree + decayDegree) * timeSeminorm) *
          spatialSeminorm chi))
      ((hL_cont chi).aestronglyMeasurable.mul
        phi.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall (hpointwise chi))
  have hboundConstant_nonneg : 0 <= boundConstant := by
    dsimp [boundConstant, decayIntegral]
    positivity
  have hvalue_bound : forall
      chi : SchwartzMap (Section43SpatialSpace d k) Complex,
      norm (value chi) <= boundConstant * spatialSeminorm chi := by
    intro chi
    calc
      norm (value chi) = norm (∫ t : Fin k -> Real, L t chi * phi t) := rfl
      _ <= ∫ t : Fin k -> Real,
          (1 + norm t) ^ (-(decayDegree : Real)) *
            (constant * (2 ^ (degree + decayDegree) * timeSeminorm) *
              spatialSeminorm chi) := by
        exact MeasureTheory.norm_integral_le_of_norm_le
          (hdecay_integrable.mul_const
            (constant * (2 ^ (degree + decayDegree) * timeSeminorm) *
              spatialSeminorm chi))
          (Filter.Eventually.of_forall (hpointwise chi))
      _ = boundConstant * spatialSeminorm chi := by
        rw [integral_mul_const]
        simp only [boundConstant, decayIntegral]
        ring
  let T : OSIISpatialDistribution d k :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex) value
      (fun chi psi => by
        simp only [value]
        rw [<- integral_add (hintegrable chi) (hintegrable psi)]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [map_add, add_mul])
      (fun c chi => by
        simp only [value]
        change (∫ t : Fin k -> Real, L t (c • chi) * phi t) =
          c • ∫ t : Fin k -> Real, L t chi * phi t
        rw [<- integral_smul]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [map_smul]
        simp only [smul_eq_mul]
        ring)
      (by
        refine ⟨spatialSeminorms, boundConstant,
          hboundConstant_nonneg, ?_⟩
        intro chi
        simpa [spatialSeminorm] using hvalue_bound chi)
  exact ⟨T, fun chi => rfl, hintegrable⟩

namespace OSIIFullTimeStageVladimirovGrowthData

/-- At every positive distance from the imaginary-time boundary, integration
against a fixed time Schwartz test is a tempered spatial distribution, and
the defining time integral is absolutely integrable for every spatial test. -/
theorem exists_positiveSliceSpatialDistributionWithIntegrability
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    exists T : OSIISpatialDistribution d k,
      (forall chi,
        T chi = osiiFullTimeBoundaryPairing A eta epsilon phi chi) ∧
      forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        Integrable (fun t : Fin k -> Real =>
          A.distribution (osiiMinkowskiTimeApproach eta t epsilon) chi * phi t) := by
  let sliceConstant : Real :=
    G.constant * (1 + norm (epsilon • eta)) ^ G.polynomialDegree *
      (1 + (Metric.infDist (epsilon • eta)
        (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree
  have hsliceConstant : 0 < sliceConstant := by
    dsimp [sliceConstant]
    have hdist :
        0 <= (Metric.infDist (epsilon • eta)
          (osiiTimePositiveCone k)ᶜ)⁻¹ :=
      inv_nonneg.mpr Metric.infDist_nonneg
    exact mul_pos
      (mul_pos G.constant_pos (pow_pos (by positivity) _))
      (pow_pos (by linarith) _)
  let L : (Fin k -> Real) -> OSIISpatialDistribution d k :=
    fun t => A.distribution (osiiMinkowskiTimeApproach eta t epsilon)
  have hL_cont : forall chi :
      SchwartzMap (Section43SpatialSpace d k) Complex,
      Continuous (fun t => L t chi) := by
    intro chi
    have hpath : Continuous
        (fun t : Fin k -> Real => osiiMinkowskiTimeApproach eta t epsilon) := by
      change Continuous (fun t : Fin k -> Real =>
        fun i => (epsilon * eta i : Complex) - (t i : Complex) * I)
      fun_prop
    exact (A.weaklyHolomorphic chi).continuousOn.comp_continuous hpath <| by
      intro t
      rw [G.fullCarrier]
      exact osiiMinkowskiTimeApproach_mem heta hepsilon
  have hL_bound : forall (t : Fin k -> Real)
      (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
      norm (L t chi) <=
        sliceConstant * (1 + norm t) ^ G.polynomialDegree *
          G.spatialSeminorms.sup
            (schwartzSeminormFamily Complex
              (Section43SpatialSpace d k) Complex) chi := by
    intro t chi
    have hgrowth := G.bound
      (osiiMinkowskiTimeApproach eta t epsilon)
      (by exact osiiMinkowskiTimeApproach_mem heta hepsilon) chi
    have hreal_le :
        norm (fun i => ((epsilon • eta) i : Complex)) <=
          norm (epsilon • eta) := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg (epsilon • eta))]
      intro i
      simpa using norm_le_pi_norm (epsilon • eta) i
    have himag_le :
        norm (fun i => ((t i : Real) : Complex) * I) <= norm t := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
      intro i
      simpa [Complex.norm_mul, Complex.norm_I] using norm_le_pi_norm t i
    have hnorm_le :
        norm (osiiMinkowskiTimeApproach eta t epsilon) <=
          norm (epsilon • eta) + norm t := by
      calc
        norm (osiiMinkowskiTimeApproach eta t epsilon) <=
            norm (fun i => ((epsilon • eta) i : Complex)) +
              norm (fun i => ((t i : Real) : Complex) * I) := by
          simpa [osiiMinkowskiTimeApproach, Pi.smul_apply] using
            (norm_sub_le
              (fun i => ((epsilon • eta) i : Complex))
              (fun i => ((t i : Real) : Complex) * I))
        _ <= norm (epsilon • eta) + norm t := add_le_add hreal_le himag_le
    have hbase_le :
        1 + norm (osiiMinkowskiTimeApproach eta t epsilon) <=
          (1 + norm (epsilon • eta)) * (1 + norm t) := by
      nlinarith [hnorm_le, norm_nonneg t, norm_nonneg (epsilon • eta)]
    have hpow_le :
        (1 + norm (osiiMinkowskiTimeApproach eta t epsilon)) ^
            G.polynomialDegree <=
          ((1 + norm (epsilon • eta)) * (1 + norm t)) ^
            G.polynomialDegree :=
      pow_le_pow_left₀ (by positivity) hbase_le _
    calc
      norm (L t chi) <=
          G.constant *
              (1 + norm (osiiMinkowskiTimeApproach eta t epsilon)) ^
                G.polynomialDegree *
            (1 + (Metric.infDist (epsilon • eta)
              (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree *
              G.spatialSeminorms.sup
                (schwartzSeminormFamily Complex
                  (Section43SpatialSpace d k) Complex) chi := by
        simpa [L, osiiTimeBoundaryDistance, osiiMinkowskiTimeApproach,
          Pi.smul_apply] using hgrowth
      _ <= G.constant *
              (((1 + norm (epsilon • eta)) * (1 + norm t)) ^
                G.polynomialDegree) *
            (1 + (Metric.infDist (epsilon • eta)
              (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree *
              G.spatialSeminorms.sup
                (schwartzSeminormFamily Complex
                  (Section43SpatialSpace d k) Complex) chi := by
        gcongr
        · exact pow_nonneg
            (by
              have hdist :
                  0 <= (Metric.infDist (epsilon • eta)
                    (osiiTimePositiveCone k)ᶜ)⁻¹ :=
                inv_nonneg.mpr Metric.infDist_nonneg
              linarith) _
        · exact G.constant_pos.le
      _ = sliceConstant * (1 + norm t) ^ G.polynomialDegree *
          G.spatialSeminorms.sup
            (schwartzSeminormFamily Complex
              (Section43SpatialSpace d k) Complex) chi := by
        dsimp [sliceConstant]
        rw [mul_pow]
        ring
  simpa [L, osiiFullTimeBoundaryPairing] using
    exists_timeIntegratedSpatialDistribution L hL_cont
      G.spatialSeminorms sliceConstant G.polynomialDegree
      hsliceConstant hL_bound phi

/-- At every positive tube slice, integration against a fixed time Schwartz
test defines a tempered spatial distribution. -/
theorem exists_positiveSliceSpatialDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    exists T : OSIISpatialDistribution d k,
      forall chi,
        T chi = osiiFullTimeBoundaryPairing A eta epsilon phi chi := by
  obtain ⟨T, hT, _⟩ :=
    G.exists_positiveSliceSpatialDistributionWithIntegrability
      eta heta epsilon hepsilon phi
  exact ⟨T, hT⟩

/-- The positive-slice pairing is absolutely integrable. -/
theorem integrable_positiveSlicePairing
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Integrable (fun t : Fin k -> Real =>
      A.distribution (osiiMinkowskiTimeApproach eta t epsilon) chi * phi t) := by
  obtain ⟨_, _, hintegrable⟩ :=
    G.exists_positiveSliceSpatialDistributionWithIntegrability
      eta heta epsilon hepsilon phi
  exact hintegrable chi

/-- A selected spatial distribution for a positive tube slice.  Nonpositive
parameters are assigned the zero distribution so that this forms a family on
all real parameters and can be fed directly to Banach--Steinhaus. -/
noncomputable def positiveSliceSpatialDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) (epsilon : Real) :
    OSIISpatialDistribution d k := by
  by_cases hepsilon : 0 < epsilon
  · exact Classical.choose
      (G.exists_positiveSliceSpatialDistribution eta heta epsilon hepsilon phi)
  · exact 0

@[simp] theorem positiveSliceSpatialDistribution_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.positiveSliceSpatialDistribution eta heta phi epsilon chi =
      osiiFullTimeBoundaryPairing A eta epsilon phi chi := by
  rw [positiveSliceSpatialDistribution]
  split
  · exact Classical.choose_spec
      (G.exists_positiveSliceSpatialDistribution eta heta epsilon hepsilon phi) chi
  · contradiction

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed time test, the Chapter VI boundary value is a tempered
distribution in the spatial Schwartz variables. -/
theorem exists_spatialBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    exists S : OSIISpatialDistribution d k,
      forall chi, S chi = G.timeBoundary chi phi := by
  let eta : Fin k -> Real := fun _ => 1
  have heta : eta ∈ osiiTimePositiveCone k := by
    intro i
    exact zero_lt_one
  let T : Real -> OSIISpatialDistribution d k :=
    fun epsilon => G.positiveSliceSpatialDistribution eta heta phi epsilon
  let F : SchwartzMap (Section43SpatialSpace d k) Complex -> Complex :=
    fun chi => G.timeBoundary chi phi
  have hpointwise : forall chi,
      Tendsto (fun epsilon : Real => T epsilon chi)
        (nhdsWithin 0 (Ioi 0)) (nhds (F chi)) := by
    intro chi
    apply (G.timeBoundary_boundaryValue chi eta heta phi).congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact (G.positiveSliceSpatialDistribution_apply eta heta phi epsilon
      hepsilon chi).symm
  have hfun :
      Tendsto (fun epsilon chi => T epsilon chi)
        (nhdsWithin 0 (Ioi 0)) (nhds F) := by
    rw [tendsto_pi_nhds]
    exact hpointwise
  have hF_add : forall chi psi, F (chi + psi) = F chi + F psi := by
    intro chi psi
    apply tendsto_nhds_unique (hpointwise (chi + psi))
    simpa only [map_add] using (hpointwise chi).add (hpointwise psi)
  have hF_smul : forall c : Complex, forall chi, F (c • chi) = c • F chi := by
    intro c chi
    apply tendsto_nhds_unique (hpointwise (c • chi))
    simpa only [map_smul] using tendsto_const_nhds.smul (hpointwise chi)
  letI : ContinuousSMul Real
      (SchwartzMap (Section43SpatialSpace d k) Complex) :=
    SchwartzMap.instContinuousSMul
  let LR :
      SchwartzMap (Section43SpatialSpace d k) Complex →L[Real] Complex :=
    continuousLinearMapOfTendsto
      (fun epsilon => (T epsilon).restrictScalars Real) hfun
  have hF_cont : Continuous F := by
    simpa [LR, continuousLinearMapOfTendsto] using LR.continuous
  let S : OSIISpatialDistribution d k :=
    { toLinearMap :=
        { toFun := F
          map_add' := hF_add
          map_smul' := hF_smul }
      cont := hF_cont }
  exact ⟨S, fun chi => rfl⟩

/-- The canonical spatial distribution obtained from the time boundary. -/
noncomputable def spatialBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    OSIISpatialDistribution d k :=
  Classical.choose (G.exists_spatialBoundary phi)

@[simp] theorem spatialBoundary_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.spatialBoundary phi chi = G.timeBoundary chi phi :=
  Classical.choose_spec (G.exists_spatialBoundary phi) chi

/-- The time--spatial boundary pairing as an algebraic bilinear map.  Its two
partial maps are continuous by `timeBoundary` and `spatialBoundary`. -/
noncomputable def mixedBoundaryBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex where
  toFun phi := (G.spatialBoundary phi).toLinearMap
  map_add' phi psi := by
    ext chi
    simp
  map_smul' c phi := by
    ext chi
    simp

@[simp] theorem mixedBoundaryBilinearMap_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.mixedBoundaryBilinearMap phi chi = G.timeBoundary chi phi := by
  simp [mixedBoundaryBilinearMap]

theorem continuous_mixedBoundaryBilinearMap_left
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Continuous (fun phi : SchwartzMap (Fin k -> Real) Complex =>
      G.mixedBoundaryBilinearMap phi chi) := by
  simpa only [mixedBoundaryBilinearMap_apply] using
    (G.timeBoundary chi).continuous

theorem continuous_mixedBoundaryBilinearMap_right
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Continuous (fun chi : SchwartzMap (Section43SpatialSpace d k) Complex =>
      G.mixedBoundaryBilinearMap phi chi) := by
  simpa only [mixedBoundaryBilinearMap_apply, ← spatialBoundary_apply] using
    (G.spatialBoundary phi).continuous

set_option backward.isDefEq.respectTransparency false in
/-- The mixed boundary pairing is jointly continuous.  To reuse the proved
equal-space Banach--Steinhaus theorem, place the time and spatial Schwartz
spaces in their product and evaluate the first component in slot zero and the
second component in slot one. -/
theorem continuous_mixedBoundaryBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      G.mixedBoundaryBilinearMap p.1 p.2) := by
  let TimeTest := SchwartzMap (Fin k -> Real) Complex
  let SpatialTest := SchwartzMap (Section43SpatialSpace d k) Complex
  let X := TimeTest × SpatialTest
  let B := G.mixedBoundaryBilinearMap
  let Phi : MultilinearMap Complex (fun _ : Fin 2 => X) Complex :=
    { toFun := fun fs => B (fs 0).1 (fs 1).2
      map_update_add' := by
        intro hdec fs i x y
        rcases x with ⟨xt, xs⟩
        rcases y with ⟨yt, ys⟩
        have hdec_eq : hdec = instDecidableEqFin 2 := Subsingleton.elim _ _
        subst hdec_eq
        fin_cases i
        · simp [B, X, Function.update]
        · simp [B, X, Function.update, ← spatialBoundary_apply]
      map_update_smul' := by
        intro hdec fs i c x
        rcases x with ⟨xt, xs⟩
        have hdec_eq : hdec = instDecidableEqFin 2 := Subsingleton.elim _ _
        subst hdec_eq
        fin_cases i <;> simp [B, X, Function.update] }
  have hPhi : forall (i : Fin 2) (fs : Fin 2 -> X),
      Continuous (fun x => Phi (Function.update fs i x)) := by
    intro i fs
    fin_cases i
    · simpa [Phi, B, Function.update] using
        (G.continuous_mixedBoundaryBilinearMap_left (fs 1).2).comp
          continuous_fst
    · simpa [Phi, B, Function.update] using
        (G.continuous_mixedBoundaryBilinearMap_right (fs 0).1).comp
          continuous_snd
  letI : (uniformity X).IsCountablyGenerated := by
    exact IsUniformAddGroup.uniformity_countably_generated
  let hcomplete :
      TopologicalSpace.IsCompletelyPseudoMetrizableSpace X :=
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
  letI := hcomplete
  letI : BaireSpace X :=
    @BaireSpace.of_completelyPseudoMetrizable X inferInstance hcomplete
  obtain ⟨PhiCont, hPhiCont⟩ :=
    GaussianField.exists_continuousMultilinear_ofSeparatelyContinuous Phi hPhi
  let embed : TimeTest × SpatialTest -> (Fin 2 -> X) :=
    fun p i => Fin.cases (p.1, 0) (fun _ => (0, p.2)) i
  have hembed : Continuous embed := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.prodMk continuous_const
    · exact continuous_const.prodMk continuous_snd
  have hcont : Continuous (fun p => PhiCont (embed p)) :=
    PhiCont.cont.comp hembed
  simpa [TimeTest, SpatialTest, Phi, B, embed, hPhiCont] using hcont

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
