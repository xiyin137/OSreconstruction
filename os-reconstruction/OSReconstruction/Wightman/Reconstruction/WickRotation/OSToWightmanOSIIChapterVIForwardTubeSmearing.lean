/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIHolomorphicSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeTimeSliceIdentification










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

namespace OSIIChapterVI

theorem integrable_one_add_norm_pow_mul_schwartz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu : Measure E) [mu.HasTemperateGrowth]
    (f : SchwartzMap E Complex) (N : Nat) :
    Integrable (fun x => (1 + ‖x‖) ^ N * ‖f x‖) mu := by
  have h := (f.integrable.norm.add (f.integrable_pow_mul mu N)).const_mul
    ((2 : Real) ^ (N - 1))
  apply h.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    (1 + ‖x‖) ^ N * ‖f x‖ ≤
        (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (add_pow_le (by positivity) (norm_nonneg x) N)
        (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
      simp only [one_pow]
      ring

end OSIIChapterVI

variable {d k : Nat}

/-- Complex relative times with real spatial coordinates. -/
def osiiForwardTubeTimeSpatialPoint (z : Fin k -> Complex)
    (x : Section43SpatialSpace d k) : Fin k -> Fin (d + 1) -> Complex :=
  fun j => Fin.cons (z j) (fun a => (x (j, a) : Complex))

@[simp] theorem osiiForwardTubeTimeSpatialPoint_time
    (z : Fin k -> Complex) (x : Section43SpatialSpace d k) (j : Fin k) :
    osiiForwardTubeTimeSpatialPoint z x j 0 = z j := rfl

@[simp] theorem osiiForwardTubeTimeSpatialPoint_space
    (z : Fin k -> Complex) (x : Section43SpatialSpace d k)
    (j : Fin k) (a : Fin d) :
    osiiForwardTubeTimeSpatialPoint z x j a.succ = (x (j, a) : Complex) := rfl

theorem osiiForwardTubeTimeSpatialPoint_continuous :
    Continuous (fun p : (Fin k -> Complex) × Section43SpatialSpace d k =>
      osiiForwardTubeTimeSpatialPoint p.1 p.2) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro mu
  refine Fin.cases ?_ (fun a => ?_) mu
  · change Continuous (fun p : (Fin k -> Complex) ×
      Section43SpatialSpace d k => p.1 j)
    fun_prop
  · simp only [osiiForwardTubeTimeSpatialPoint_space]
    fun_prop

theorem osiiForwardTubeTimeSpatialPoint_differentiable
    (x : Section43SpatialSpace d k) :
    Differentiable Complex (fun z : Fin k -> Complex =>
      osiiForwardTubeTimeSpatialPoint z x) := by
  apply differentiable_pi.mpr
  intro j
  apply differentiable_pi.mpr
  intro mu
  refine Fin.cases ?_ (fun a => ?_) mu
  · simpa using (differentiable_apply j :
      Differentiable Complex (fun z : Fin k -> Complex => z j))
  · simp only [osiiForwardTubeTimeSpatialPoint_space]
    fun_prop

theorem osiiForwardTubeTimeSpatialPoint_mem
    (z : Fin k -> Complex) (hz : z ∈ SCV.TubeDomain (osiiTimePositiveCone k))
    (x : Section43SpatialSpace d k) :
    osiiForwardTubeTimeSpatialPoint z x ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
  have h := osiiPureTimeReducedDirection_mem_productForwardCone
    (d := d) (fun j => (z j).im) hz
  have heq : (fun j mu => (osiiForwardTubeTimeSpatialPoint z x j mu).im) =
      osiiPureTimeReducedDirection d k (fun j => (z j).im) := by
    ext j mu
    refine Fin.cases ?_ (fun a => ?_) mu <;> simp
  change (fun j mu => (osiiForwardTubeTimeSpatialPoint z x j mu).im) ∈
    BHW.ProductForwardConeReal d k
  rwa [heq]

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}

/-- The physical tube paired with a spatial Schwartz test. -/
def spatialSmearing (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (z : Fin k -> Complex) : Complex :=
  ∫ x, H.kernel (osiiForwardTubeTimeSpatialPoint z x) * chi x

theorem timeSpatialKernel_bound_on_compact_imaginary
    (H : OSIIReducedForwardTubeBoundaryData W)
    (K : Set (Fin k -> Real)) (hK : IsCompact K) (hKC : K ⊆ osiiTimePositiveCone k) :
    ∃ (C : Real) (N : Nat), 0 < C ∧
      ∀ z : Fin k -> Complex, (fun j => (z j).im) ∈ K ->
        ∀ x : Section43SpatialSpace d k,
          ‖H.kernel (osiiForwardTubeTimeSpatialPoint z x)‖ ≤
            C * (1 + ‖fun j => (z j).re‖) ^ N * (1 + ‖x‖) ^ N := by
  have hc : Continuous (osiiPureTimeReducedDirection d k) := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro mu
    by_cases hmu : mu = 0 <;> simp [osiiPureTimeReducedDirection, hmu] <;> fun_prop
  obtain ⟨C, N, hC, hb⟩ := H.compactSubsetGrowth
    (osiiPureTimeReducedDirection d k '' K) (hK.image hc) (by
      rintro _ ⟨eta, heta, rfl⟩
      exact osiiPureTimeReducedDirection_mem_productForwardCone eta (hKC heta))
  refine ⟨C, N, hC, ?_⟩
  intro z hz x
  let t : Fin k -> Real := fun j => (z j).re
  let q : NPointDomain d k := fun j => Fin.cons (t j) (fun a => x (j, a))
  let y := osiiPureTimeReducedDirection d k (fun j => (z j).im)
  have heq : osiiForwardTubeTimeSpatialPoint z x =
      fun j mu => (q j mu : Complex) + (y j mu : Complex) * I := by
    ext j mu
    refine Fin.cases ?_ (fun a => ?_) mu
    · simp [q, y, t]
    · simp [q, y]
  have hq : ‖q‖ ≤ ‖t‖ + ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro mu
    refine Fin.cases ?_ (fun a => ?_) mu
    · exact (norm_le_pi_norm t j).trans (le_add_of_nonneg_right (norm_nonneg x))
    · exact (PiLp.norm_apply_le x (j, a)).trans (le_add_of_nonneg_left (norm_nonneg t))
  have hprod : 1 + ‖q‖ ≤ (1 + ‖t‖) * (1 + ‖x‖) := by
    nlinarith [mul_nonneg (norm_nonneg t) (norm_nonneg x)]
  rw [heq]
  calc
    _ ≤ C * (1 + ‖q‖) ^ N := hb q y ⟨_, hz, rfl⟩
    _ ≤ C * ((1 + ‖t‖) * (1 + ‖x‖)) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod N) hC.le
    _ = C * (1 + ‖fun j => (z j).re‖) ^ N * (1 + ‖x‖) ^ N := by
      rw [mul_pow, ← mul_assoc]

theorem spatialSmearing_integrand_continuousOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ContinuousOn (fun p : (Fin k -> Complex) × Section43SpatialSpace d k =>
      H.kernel (osiiForwardTubeTimeSpatialPoint p.1 p.2) * chi p.2)
      (SCV.TubeDomain (osiiTimePositiveCone k) ×ˢ univ) := by
  exact (H.holomorphic.continuousOn.comp
    osiiForwardTubeTimeSpatialPoint_continuous.continuousOn
    (fun p hp => osiiForwardTubeTimeSpatialPoint_mem p.1 hp.1 p.2)).mul
      (chi.continuous.comp continuous_snd).continuousOn

theorem spatialSmearing_compact_domination
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (K : Set (Fin k -> Complex)) (hK : IsCompact K)
    (hKC : K ⊆ SCV.TubeDomain (osiiTimePositiveCone k)) :
    ∃ g : Section43SpatialSpace d k -> Real, Integrable g ∧
      ∀ z ∈ K, ∀ x, ‖H.kernel (osiiForwardTubeTimeSpatialPoint z x) * chi x‖ ≤ g x := by
  obtain ⟨C, N, hC, hb⟩ := H.timeSpatialKernel_bound_on_compact_imaginary
    ((fun z : Fin k -> Complex => fun j => (z j).im) '' K)
    (hK.image (by fun_prop)) (by rintro _ ⟨z, hz, rfl⟩; exact hKC hz)
  obtain ⟨R, hR, hRb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨fun x => C * (1 + R) ^ N * ((1 + ‖x‖) ^ N * ‖chi x‖),
    (OSIIChapterVI.integrable_one_add_norm_pow_mul_schwartz volume chi N).const_mul _, ?_⟩
  intro z hz x
  have hre : ‖fun j => (z j).re‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro j
    exact (Complex.abs_re_le_norm (z j)).trans ((norm_le_pi_norm z j).trans (hRb z hz))
  rw [norm_mul]
  have hp := mul_le_mul_of_nonneg_right (hb z ⟨z, hz, rfl⟩ x) (norm_nonneg (chi x))
  calc
    _ ≤ C * (1 + ‖fun j => (z j).re‖) ^ N * (1 + ‖x‖) ^ N * ‖chi x‖ := hp
    _ ≤ C * (1 + R) ^ N * (1 + ‖x‖) ^ N * ‖chi x‖ := by
      gcongr
    _ = _ := by ring

/-- Spatial smearing is jointly holomorphic in the entire positive time
tube. The integrable majorant is derived from the existing growth field. -/
theorem spatialSmearing_differentiableOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex (H.spatialSmearing chi)
      (SCV.TubeDomain (osiiTimePositiveCone k)) := by
  apply OSIIChapterVI.differentiableOn_integral_of_compact_domination volume
    (SCV.tubeDomain_isOpen (osiiTimePositiveCone_open k))
    (fun z x => H.kernel (osiiForwardTubeTimeSpatialPoint z x) * chi x)
    (H.spatialSmearing_integrand_continuousOn chi)
  · intro x
    exact (H.holomorphic.comp
      (osiiForwardTubeTimeSpatialPoint_differentiable x).differentiableOn
      (fun z hz => osiiForwardTubeTimeSpatialPoint_mem z hz x)).mul_const (chi x)
  · exact H.spatialSmearing_compact_domination chi

theorem spatialSmearing_slice_growth
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) :
    ∃ (C : Real) (N : Nat), 0 ≤ C ∧ ∀ t : Fin k -> Real,
      ‖H.spatialSmearing chi (fun j => (t j : Complex) + (y j : Complex) * I)‖ ≤
        C * (1 + ‖t‖) ^ N := by
  obtain ⟨C, N, hC, hb⟩ := H.timeSpatialKernel_bound_on_compact_imaginary {y}
    isCompact_singleton (singleton_subset_iff.mpr hy)
  let g := fun x : Section43SpatialSpace d k => (1 + ‖x‖) ^ N * ‖chi x‖
  have hg : Integrable g := OSIIChapterVI.integrable_one_add_norm_pow_mul_schwartz volume chi N
  refine ⟨C * ∫ x, g x, N, mul_nonneg hC.le (integral_nonneg (fun x => by positivity)), ?_⟩
  intro t
  have hb' (x : Section43SpatialSpace d k) :
      ‖H.kernel (osiiForwardTubeTimeSpatialPoint
        (fun j => (t j : Complex) + (y j : Complex) * I) x) * chi x‖ ≤
          C * (1 + ‖t‖) ^ N * g x := by
    rw [norm_mul]
    have h := hb (fun j => (t j : Complex) + (y j : Complex) * I) (by simp) x
    simpa [g, mul_assoc] using mul_le_mul_of_nonneg_right h (norm_nonneg (chi x))
  calc
    _ ≤ ∫ x, C * (1 + ‖t‖) ^ N * g x :=
      norm_integral_le_of_norm_le (hg.const_mul _) (Filter.Eventually.of_forall hb')
    _ = (C * ∫ x, g x) * (1 + ‖t‖) ^ N := by
      rw [integral_const_mul]
      ring

/-- Time-boundary pairings of the smeared kernel are genuine integrable
slices, as required by distributional tube uniqueness. -/
theorem spatialSmearing_slice_integrable
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Integrable (fun t => H.spatialSmearing chi
      (fun j => (t j : Complex) + (y j : Complex) * I) * phi t) := by
  obtain ⟨C, N, hC, hb⟩ := H.spatialSmearing_slice_growth chi y hy
  have hc : Continuous (fun t : Fin k -> Real => H.spatialSmearing chi
      (fun j => (t j : Complex) + (y j : Complex) * I)) := by
    exact (H.spatialSmearing_differentiableOn chi).continuousOn.comp_continuous
      (by fun_prop) (fun t => by simpa [SCV.TubeDomain] using hy)
  apply ((OSIIChapterVI.integrable_one_add_norm_pow_mul_schwartz volume phi N).const_mul C).mono'
    (hc.mul phi.continuous).aestronglyMeasurable
  filter_upwards with t
  simpa [norm_mul, mul_assoc] using mul_le_mul_of_nonneg_right (hb t) (norm_nonneg (phi t))

variable [NeZero d]

theorem spatialSmearing_eq_pureTimeSpatialPairing
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta t : Fin k -> Real) (epsilon : Real) :
    H.spatialSmearing chi
        (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) =
      osiiReducedForwardTubePureTimeSpatialPairing H eta epsilon t chi := by
  apply integral_congr_ae
  filter_upwards with x
  have hsplit : (section43NPointTimeSpatialMeasurableEquiv d k).symm (t, x) =
      (nPointTimeSpatialCLE (d := d) k).symm (t, x) := by
    apply (nPointTimeSpatialCLE (d := d) k).injective
    rw [(nPointTimeSpatialCLE (d := d) k).apply_symm_apply,
      ← section43NPointTimeSpatialMeasurableEquiv_apply]
    exact (section43NPointTimeSpatialMeasurableEquiv d k).apply_symm_apply (t, x)
  apply congrArg (fun z => H.kernel z * chi x)
  ext j mu
  rw [hsplit]
  refine Fin.cases ?_ (fun a => ?_) mu <;>
    simp [nPointTimeSpatialCLE]

theorem spatialSmearing_boundaryValue
    (H : OSIIReducedForwardTubeBoundaryData W)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto (fun epsilon : Real => ∫ t : Fin k -> Real,
      H.spatialSmearing chi
        (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t)
      (nhdsWithin 0 (Ioi 0)) (nhds (W (section43NPointTimeSpatialTensor d k phi chi))) := by
  have h := H.boundaryValue (osiiPureTimeReducedDirection d k eta)
    (osiiPureTimeReducedDirection_mem_productForwardCone eta heta)
    (section43NPointTimeSpatialTensor d k phi chi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  rw [H.boundaryPairing_eq_spatialPairing eta heta epsilon hepsilon phi chi]
  apply integral_congr_ae
  filter_upwards with t
  rw [H.spatialSmearing_eq_pureTimeSpatialPairing]

end OSIIReducedForwardTubeBoundaryData

end OSReconstruction
