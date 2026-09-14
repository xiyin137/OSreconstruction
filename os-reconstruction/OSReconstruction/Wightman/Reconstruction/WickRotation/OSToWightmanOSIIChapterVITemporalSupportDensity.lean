/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeSpectralSupport















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- Schwartz-space transport along the standard Section 4.3 time/spatial
flattening. -/
private noncomputable def section43TimeSpatialFlatSchwartzCLE (d k : Nat) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex ≃L[Complex]
      SchwartzMap (Fin (k + k * d) -> Real) Complex := by
  let e := section43TimeSpatialFlatCLE d k
  let toFlat :
      SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
        SchwartzMap (Fin (k + k * d) -> Real) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
  let fromFlat :
      SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex]
        SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
  exact
    { toLinearEquiv :=
        { toFun := toFlat
          map_add' := toFlat.map_add
          map_smul' := toFlat.map_smul
          invFun := fromFlat
          left_inv := by
            intro F
            ext p
            simp [toFlat, fromFlat,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro F
            ext x
            simp [toFlat, fromFlat,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFlat.continuous
      continuous_invFun := fromFlat.continuous }

/-- Standard radial compact truncation transported to the Section 4.3
time/spatial product block. -/
private noncomputable def section43TimeSpatialBumpTruncation
    (d k N : Nat)
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  (section43TimeSpatialFlatSchwartzCLE d k).symm
    (bumpTruncationRadius
      (section43TimeSpatialFlatSchwartzCLE d k F) N)

/-- Transported radial truncations converge in the Section 4.3 product
Schwartz topology. -/
private theorem section43TimeSpatialBumpTruncation_tendsto
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Tendsto
      (fun N : Nat => section43TimeSpatialBumpTruncation d k N F)
      atTop (nhds F) := by
  have hflat :=
    SchwartzMap.tendsto_bump_truncation_nhds
      (section43TimeSpatialFlatSchwartzCLE d k F)
  have htransport :=
    ((section43TimeSpatialFlatSchwartzCLE d k).symm.continuous.tendsto
      (section43TimeSpatialFlatSchwartzCLE d k F)).comp hflat
  simpa only [section43TimeSpatialBumpTruncation,
    (section43TimeSpatialFlatSchwartzCLE d k).symm_apply_apply] using
    htransport

/-- Each transported radial truncation has compact topological support. -/
private theorem section43TimeSpatialBumpTruncation_hasCompactSupport
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (N : Nat) :
    HasCompactSupport
      ((section43TimeSpatialBumpTruncation d k N F :
        SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
          Section43TimeSpatialSpace d k -> Complex) := by
  let e := section43TimeSpatialFlatCLE d k
  let f := bumpTruncationRadius
    (section43TimeSpatialFlatSchwartzCLE d k F) N
  have hf : HasCompactSupport
      (f : (Fin (k + k * d) -> Real) -> Complex) :=
    hasCompactSupport_cutoff_mul_radius
      (bumpTruncationRadiusValue N)
      (bumpTruncationRadiusValue_pos N)
      (section43TimeSpatialFlatSchwartzCLE d k F)
  have hcomp : HasCompactSupport
      (fun p : Section43TimeSpatialSpace d k => f (e p)) :=
    hf.comp_homeomorph e.toHomeomorph
  simpa [section43TimeSpatialBumpTruncation, f, e,
    section43TimeSpatialFlatSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hcomp

/-- Radial truncation does not enlarge topological support after transport to
the Section 4.3 product block. -/
private theorem section43TimeSpatialBumpTruncation_tsupport_subset
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (N : Nat) :
    tsupport
        ((section43TimeSpatialBumpTruncation d k N F :
          SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
            Section43TimeSpatialSpace d k -> Complex) ⊆
      tsupport (F : Section43TimeSpatialSpace d k -> Complex) := by
  let e := section43TimeSpatialFlatCLE d k
  let Fflat := section43TimeSpatialFlatSchwartzCLE d k F
  let Fcut := bumpTruncationRadius Fflat N
  have hflat :
      tsupport (Fcut : (Fin (k + k * d) -> Real) -> Complex) ⊆
        tsupport (Fflat : (Fin (k + k * d) -> Real) -> Complex) := by
    rw [show Fcut = bumpTruncationRadius Fflat N by rfl]
    unfold bumpTruncationRadius
    exact (SchwartzMap.tsupport_smulLeftCLM_subset
      (unitBallBumpSchwartzPiRadius
        (k + k * d) (bumpTruncationRadiusValue N)
        (bumpTruncationRadiusValue_pos N)) Fflat).trans inter_subset_left
  have hcut_tsupport :
      tsupport
          ((section43TimeSpatialBumpTruncation d k N F :
            SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
              Section43TimeSpatialSpace d k -> Complex) =
        e.toHomeomorph ⁻¹'
          tsupport (Fcut : (Fin (k + k * d) -> Real) -> Complex) := by
    simpa [section43TimeSpatialBumpTruncation, Fcut, e,
      section43TimeSpatialFlatSchwartzCLE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (Fcut : (Fin (k + k * d) -> Real) -> Complex))
        e.toHomeomorph)
  have hflat_tsupport :
      tsupport (Fflat : (Fin (k + k * d) -> Real) -> Complex) =
        e.symm.toHomeomorph ⁻¹'
          tsupport (F : Section43TimeSpatialSpace d k -> Complex) := by
    simpa [Fflat, e, section43TimeSpatialFlatSchwartzCLE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (F : Section43TimeSpatialSpace d k -> Complex))
        e.symm.toHomeomorph)
  intro p hp
  rw [hcut_tsupport] at hp
  have hp_cut : e p ∈ tsupport (Fcut : (Fin (k + k * d) -> Real) -> Complex) := hp
  have hp_flat := hflat hp_cut
  rw [hflat_tsupport] at hp_flat
  simpa using hp_flat

/-- Section 4.3 time/spatial tensors whose time factor has topological
support in the complement of `S`. -/
def section43TimeComplementTensorSet
    (d k : Nat) [NeZero d] (S : Set (Fin k -> Real)) :
    Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex) :=
  {F | ∃ phi : SchwartzMap (Fin k -> Real) Complex,
      tsupport (phi : (Fin k -> Real) -> Complex) ⊆ Sᶜ ∧
      ∃ chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        F = section43TimeSpatialTensor d k phi chi}

/-- Linear span of time/spatial tensors whose time factor is supported in the
complement of `S`. -/
def section43TimeComplementTensorSubmodule
    (d k : Nat) [NeZero d] (S : Set (Fin k -> Real)) :
    Submodule Complex
      (SchwartzMap (Section43TimeSpatialSpace d k) Complex) :=
  Submodule.span Complex (section43TimeComplementTensorSet d k S)

/-- A compactly supported time/spatial test missing a closed temporal set is
already in the closed span of tensors whose time factors miss that set. -/
private theorem section43TimeSpatial_mem_timeComplementTensorClosure_of_compactSupport
    (S : Set (Fin k -> Real)) (hS_closed : IsClosed S)
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (hF_compact : HasCompactSupport
      (F : Section43TimeSpatialSpace d k -> Complex))
    (hF_support : ∀ p ∈ tsupport
      (F : Section43TimeSpatialSpace d k -> Complex), p.1 ∉ S) :
    F ∈ (section43TimeComplementTensorSubmodule d k S).topologicalClosure := by
  let U : Set (Fin k -> Real) := Sᶜ
  let K : Set (Fin k -> Real) := Prod.fst ''
    tsupport (F : Section43TimeSpatialSpace d k -> Complex)
  have hK_compact : IsCompact K :=
    hF_compact.isCompact.image continuous_fst
  have hU_open : IsOpen U := by
    simpa [U] using hS_closed.isOpen_compl
  have hKU : K ⊆ U := by
    rintro t ⟨p, hp, rfl⟩
    exact hF_support p hp
  obtain ⟨theta, htheta_one, htheta_support⟩ :=
    SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
      hK_compact hU_open hKU
  let multiplier : Section43TimeSpatialSpace d k -> Complex :=
    fun p => theta p.1
  have hmult : multiplier.HasTemperateGrowth := by
    have hfst : (fun p : Section43TimeSpatialSpace d k => p.1).HasTemperateGrowth :=
      (ContinuousLinearMap.fst Real (Fin k -> Real)
        (Section43SpatialSpace d k)).hasTemperateGrowth
    exact theta.hasTemperateGrowth.comp hfst
  let L : SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
    SchwartzMap.smulLeftCLM Complex multiplier
  have hLF : L F = F := by
    ext p
    rw [show L F p = multiplier p * F p by
      simp [L, SchwartzMap.smulLeftCLM_apply_apply hmult]]
    by_cases hp : p ∈ tsupport
        (F : Section43TimeSpatialSpace d k -> Complex)
    · have hpK : p.1 ∈ K := ⟨p, hp, rfl⟩
      simp [multiplier, htheta_one p.1 hpK]
    · have hzero : F p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp [hzero]
  let P : Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex) :=
    {H | ∃ phi : SchwartzMap (Fin k -> Real) Complex,
      ∃ chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        H = section43TimeSpatialTensor d k phi chi}
  let A : Submodule Complex
      (SchwartzMap (Section43TimeSpatialSpace d k) Complex) :=
    Submodule.span Complex P
  let M := section43TimeComplementTensorSubmodule d k S
  have hgenerator : ∀ H ∈ P, L H ∈ M := by
    intro H hH
    rcases hH with ⟨phi, chi, rfl⟩
    let phi' : SchwartzMap (Fin k -> Real) Complex :=
      SchwartzMap.smulLeftCLM Complex (theta : (Fin k -> Real) -> Complex) phi
    have hphi'_support :
        tsupport (phi' : (Fin k -> Real) -> Complex) ⊆ Sᶜ := by
      have hsubset :
          tsupport (phi' : (Fin k -> Real) -> Complex) ⊆
            tsupport (theta : (Fin k -> Real) -> Complex) := by
        exact (SchwartzMap.tsupport_smulLeftCLM_subset
          (theta : (Fin k -> Real) -> Complex) phi).trans inter_subset_right
      exact hsubset.trans (by simpa [U] using htheta_support)
    have hL_tensor :
        L (section43TimeSpatialTensor d k phi chi) =
          section43TimeSpatialTensor d k phi' chi := by
      ext p
      rcases p with ⟨tau, eta⟩
      rw [show L (section43TimeSpatialTensor d k phi chi) (tau, eta) =
          multiplier (tau, eta) *
            section43TimeSpatialTensor d k phi chi (tau, eta) by
        simp [L, SchwartzMap.smulLeftCLM_apply_apply hmult]]
      simp [multiplier, phi', SchwartzMap.smulLeftCLM_apply_apply
        theta.hasTemperateGrowth, section43TimeSpatialTensor_apply, mul_assoc]
    apply Submodule.subset_span
    exact ⟨phi', hphi'_support, chi, hL_tensor⟩
  have hA_le : A ≤ M.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    intro H hH
    exact hgenerator H hH
  have hpre_closed :
      IsClosed {H : SchwartzMap (Section43TimeSpatialSpace d k) Complex |
        L H ∈ M.topologicalClosure} :=
    M.isClosed_topologicalClosure.preimage L.continuous
  have hclosure_le :
      closure (A : Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) ⊆
        {H : SchwartzMap (Section43TimeSpatialSpace d k) Complex |
          L H ∈ M.topologicalClosure} :=
    hpre_closed.closure_subset_iff.mpr fun H hH =>
      M.le_topologicalClosure (hA_le hH)
  have hF_dense : F ∈
      closure (A : Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) := by
    have hDense := dense_section43TimeSpatialTensor_span d k
    have hA_dense : Dense
        (A : Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) := by
      simpa [A, P] using hDense
    rw [hA_dense.closure_eq]
    exact Set.mem_univ F
  have hLF_mem := hclosure_le hF_dense
  change L F ∈ M.topologicalClosure at hLF_mem
  rw [hLF] at hLF_mem
  simpa [M] using hLF_mem

/-- Support-localized Section 4.3 tensor density.  A general Schwartz test
whose topological support misses a closed temporal set lies in the closed
span of tensors whose time factor already misses that set. -/
theorem section43TimeSpatial_mem_timeComplementTensorClosure
    (S : Set (Fin k -> Real)) (hS_closed : IsClosed S)
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (hF_support : ∀ p ∈ tsupport
      (F : Section43TimeSpatialSpace d k -> Complex), p.1 ∉ S) :
    F ∈ (section43TimeComplementTensorSubmodule d k S).topologicalClosure := by
  let M := section43TimeComplementTensorSubmodule d k S
  have hlimit := section43TimeSpatialBumpTruncation_tendsto (d := d) (k := k) F
  apply M.isClosed_topologicalClosure.mem_of_tendsto hlimit
  filter_upwards with N
  apply section43TimeSpatial_mem_timeComplementTensorClosure_of_compactSupport
    (d := d) (k := k) S hS_closed
      (section43TimeSpatialBumpTruncation d k N F)
  · exact section43TimeSpatialBumpTruncation_hasCompactSupport F N
  · intro p hp
    exact hF_support p
      (section43TimeSpatialBumpTruncation_tsupport_subset F N hp)

/-- A continuous functional that vanishes on all time-complement tensor
generators vanishes on their closed span. -/
theorem section43TimeComplementTensorClosure_annihilated
    (S : Set (Fin k -> Real))
    (W : SchwartzMap (Section43TimeSpatialSpace d k) Complex
      →L[Complex] Complex)
    (hW : forall (phi : SchwartzMap (Fin k -> Real) Complex),
      tsupport (phi : (Fin k -> Real) -> Complex) ⊆ Sᶜ ->
      forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        W (section43TimeSpatialTensor d k phi chi) = 0)
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (hF : F ∈
      (section43TimeComplementTensorSubmodule d k S).topologicalClosure) :
    W F = 0 := by
  let T := section43TimeComplementTensorSet d k S
  have hspan : ∀ H : SchwartzMap (Section43TimeSpatialSpace d k) Complex,
      H ∈ Submodule.span Complex T → W H = 0 := by
    intro H hH
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hH
    · intro V hV
      rcases hV with ⟨phi, hphi, chi, rfl⟩
      exact hW phi hphi chi
    · simp
    · intro V Z _ _ hV hZ
      simpa [map_add, hV, hZ] using
        congrArg₂ (fun a b : Complex => a + b) hV hZ
    · intro c V _ hV
      simpa [map_smul, hV] using
        congrArg (fun z : Complex => c * z) hV
  have hclosed :
      IsClosed {H : SchwartzMap (Section43TimeSpatialSpace d k) Complex |
        W H = 0} :=
    isClosed_eq W.continuous continuous_const
  have hclosure :
      closure ((Submodule.span Complex T : Submodule Complex
        (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) :
          Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) ⊆
        {H : SchwartzMap (Section43TimeSpatialSpace d k) Complex | W H = 0} :=
    hclosed.closure_subset_iff.mpr hspan
  exact hclosure (by
    simpa [section43TimeComplementTensorSubmodule, T] using hF)

namespace OSIIFullTimeStageVladimirovGrowthData

variable {A : OSIITimeContinuationStage d k}

/-- The Chapter VI mixed boundary pairing after inverse Fourier transform in
the time variables only.  Its first argument is a time-frequency test and its
second argument is an untouched spatial Schwartz test. -/
noncomputable def timeFrequencyMixedBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex where
  toFun phi :=
    G.mixedBoundaryBilinearMap (physicsFourierFlatInvCLM phi)
  map_add' phi psi := by
    ext chi
    simp
  map_smul' c phi := by
    ext chi
    simp

@[simp] theorem timeFrequencyMixedBilinearMap_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.timeFrequencyMixedBilinearMap phi chi =
      G.timeFrequencyDistribution chi phi := by
  simp [timeFrequencyMixedBilinearMap, timeFrequencyDistribution,
    ContinuousLinearMap.comp_apply]

/-- Joint continuity survives inverse Fourier transform in the time factor. -/
theorem continuous_timeFrequencyMixedBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      G.timeFrequencyMixedBilinearMap p.1 p.2) := by
  exact G.continuous_mixedBoundaryBilinearMap.comp
    (((physicsFourierFlatInvCLM (m := k)).continuous.comp continuous_fst).prodMk
      continuous_snd)

/-- The temporal positive-energy cylinder in mixed time-frequency/spatial
coordinates.  Spatial coordinates are unrestricted at this stage. -/
def osiiTimeFrequencyPositiveCylinder (d k : Nat) [NeZero d] :
    Set (Section43TimeSpatialSpace d k) :=
  {p | p.1 ∈ DualConeFlat (osiiTimePositiveCone k)}

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
