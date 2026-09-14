/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeSpatialCanonicalFrequency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIReducedForwardTubePaleyWiener












noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

/-- Split a particle coordinate into its time coordinate or its spatial
coordinate together with the particle label. -/
private def osiiFullToTimeSpatialSumIndexEquiv (d k : Nat) :
    (Fin k × Fin (d + 1)) ≃ (Fin k ⊕ (Fin k × Fin d)) where
  toFun p :=
    Fin.cases (Sum.inl p.1) (fun j => Sum.inr (p.1, j)) p.2
  invFun s :=
    Sum.elim (fun i => (i, 0)) (fun p => (p.1, Fin.succ p.2)) s
  left_inv := by
    rintro ⟨i, mu⟩
    refine Fin.cases ?_ (fun j => ?_) mu
    · rfl
    · rfl
  right_inv := by
    intro s
    cases s <;> rfl

/-- Flatten the time summand first and the spatial particle block second. -/
private def osiiTimeSpatialSumFlatIndexEquiv (d k : Nat) :
    (Fin k ⊕ (Fin k × Fin d)) ≃ Fin (k + k * d) :=
  (Equiv.sumCongr (Equiv.refl (Fin k))
      (finProdFinEquiv : (Fin k × Fin d) ≃ Fin (k * d))).trans
    (finSumFinEquiv : (Fin k ⊕ Fin (k * d)) ≃ Fin (k + k * d))

/-- Index permutation from particle-block flat order to time-first flat
order. -/
def osiiFullFlatTimeSpatialIndexEquiv (d k : Nat) :
    Fin (k * (d + 1)) ≃ Fin (k + k * d) :=
  (finProdFinEquiv :
      (Fin k × Fin (d + 1)) ≃ Fin (k * (d + 1))).symm.trans
    ((osiiFullToTimeSpatialSumIndexEquiv d k).trans
      (osiiTimeSpatialSumFlatIndexEquiv d k))

/-- The coordinate permutation corresponding to
`osiiFullFlatTimeSpatialIndexEquiv`. -/
def osiiFullFlatTimeSpatialReindexCLE (d k : Nat) :
    (Fin (k * (d + 1)) -> Real) ≃L[Real]
      (Fin (k + k * d) -> Real) :=
  ContinuousLinearEquiv.piCongrLeft Real
    (fun _ : Fin (k + k * d) => Real)
    (osiiFullFlatTimeSpatialIndexEquiv d k)

/-- Pull a time-first flat Schwartz test back to particle-block flat
coordinates. -/
def osiiFullFlatTimeSpatialPullbackCLM (d k : Nat) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex]
      SchwartzMap (Fin (k * (d + 1)) -> Real) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (osiiFullFlatTimeSpatialReindexCLE d k)

private theorem osiiPiCongrLeft_pair_eq
    {a b : Nat} (e : Fin a ≃ Fin b)
    (x xi : Fin a -> Real) :
    (∑ i : Fin a, (x i : Complex) * (xi i : Complex)) =
      ∑ j : Fin b,
        ((ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : Fin b => Real) e x) j : Complex) *
        ((ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : Fin b => Real) e xi) j : Complex) := by
  symm
  rw [← e.sum_comp]
  simp [ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply_apply]

/-- Physics Fourier transform commutes with finite coordinate permutations. -/
theorem physicsFourierFlatCLM_comp_piCongrLeft_apply
    {a b : Nat} (e : Fin a ≃ Fin b)
    (F : SchwartzMap (Fin b -> Real) Complex)
    (xi : Fin a -> Real) :
    physicsFourierFlatCLM
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (ContinuousLinearEquiv.piCongrLeft Real
            (fun _ : Fin b => Real) e) F) xi =
      physicsFourierFlatCLM F
        (ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : Fin b => Real) e xi) := by
  rw [← physicsFourierFlatCLM_integral,
    ← physicsFourierFlatCLM_integral]
  let L : (Fin a -> Real) ≃L[Real] (Fin b -> Real) :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin b => Real) e
  let em : (Fin a -> Real) ≃ᵐ (Fin b -> Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin b => Real) e
  have hem : MeasurePreserving em volume volume := by
    simpa [em] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin b => Real) e)
  let g : (Fin b -> Real) -> Complex := fun y =>
    Complex.exp (Complex.I * ∑ j,
      (y j : Complex) * (L xi j : Complex)) * F y
  calc
    (∫ x : Fin a -> Real,
      Complex.exp (Complex.I * ∑ i,
        (x i : Complex) * (xi i : Complex)) *
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex L F) x)
        = ∫ x : Fin a -> Real, g (L x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [g]
          rw [← osiiPiCongrLeft_pair_eq e x xi]
    _ = ∫ y : Fin b -> Real, g y := by
          simpa [L, em, MeasurableEquiv.piCongrLeft,
            ContinuousLinearEquiv.piCongrLeft] using
            (hem.integral_comp' (g := g))
    _ = ∫ y : Fin b -> Real,
        Complex.exp (Complex.I * ∑ j,
          (y j : Complex) *
            ((ContinuousLinearEquiv.piCongrLeft Real
              (fun _ : Fin b => Real) e xi) j : Complex)) *
          F y := by rfl

/-- The explicit inverse physics Fourier transform also commutes with finite
coordinate permutations. -/
theorem physicsFourierFlatInvCLM_comp_piCongrLeft
    {a b : Nat} (e : Fin a ≃ Fin b)
    (F : SchwartzMap (Fin b -> Real) Complex) :
    physicsFourierFlatInvCLM
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (ContinuousLinearEquiv.piCongrLeft Real
            (fun _ : Fin b => Real) e) F) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : Fin b => Real) e)
        (physicsFourierFlatInvCLM F) := by
  apply (Function.LeftInverse.injective
    (fun H : SchwartzMap (Fin a -> Real) Complex =>
      physicsFourierFlatInvCLM_left H))
  ext xi
  rw [physicsFourierFlatCLM_inv_right,
    physicsFourierFlatCLM_comp_piCongrLeft_apply,
    physicsFourierFlatCLM_inv_right]
  rfl

variable {d k : Nat} [NeZero d]

/-- Particle-block flattening written in the public coordinate API.  This is
the same vector used by \`unflattenSchwartzNPoint\`, but exposing it here keeps
the time-first transport independent of the private block-flattening helper. -/
def osiiParticleFlatCoordinates (d k : Nat) (q : NPointDomain d k) :
    Fin (k * (d + 1)) -> Real :=
  fun a =>
    q (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

@[simp] theorem osiiParticleFlatCoordinates_finProdFinEquiv
    (q : NPointDomain d k) (i : Fin k) (mu : Fin (d + 1)) :
    osiiParticleFlatCoordinates d k q (finProdFinEquiv (i, mu)) =
      q i mu := by
  simp [osiiParticleFlatCoordinates]

@[simp] theorem osiiFullFlatTimeSpatialIndexEquiv_time
    (i : Fin k) :
    osiiFullFlatTimeSpatialIndexEquiv d k
        (finProdFinEquiv (i, 0)) =
      Fin.castAdd (k * d) i := by
  simp [osiiFullFlatTimeSpatialIndexEquiv,
    osiiFullToTimeSpatialSumIndexEquiv,
    osiiTimeSpatialSumFlatIndexEquiv,
    finSumFinEquiv_apply_left]

@[simp] theorem osiiFullFlatTimeSpatialIndexEquiv_spatial
    (i : Fin k) (j : Fin d) :
    osiiFullFlatTimeSpatialIndexEquiv d k
        (finProdFinEquiv (i, Fin.succ j)) =
      Fin.natAdd k (finProdFinEquiv (i, j)) := by
  simp [osiiFullFlatTimeSpatialIndexEquiv,
    osiiFullToTimeSpatialSumIndexEquiv,
    osiiTimeSpatialSumFlatIndexEquiv,
    finSumFinEquiv_apply_right]

@[simp] theorem osiiFullFlatTimeSpatialReindexCLE_particleFlat_splitFirst
    (q : NPointDomain d k) :
    splitFirst k (k * d)
        (osiiFullFlatTimeSpatialReindexCLE d k
          (osiiParticleFlatCoordinates d k q)) =
      section43QTime (d := d) (n := k) q := by
  ext i
  change (osiiFullFlatTimeSpatialReindexCLE d k
      (osiiParticleFlatCoordinates d k q))
      (Fin.castAdd (k * d) i) = q i 0
  calc
    (osiiFullFlatTimeSpatialReindexCLE d k
        (osiiParticleFlatCoordinates d k q))
        (Fin.castAdd (k * d) i) =
      (osiiFullFlatTimeSpatialReindexCLE d k
        (osiiParticleFlatCoordinates d k q))
        (osiiFullFlatTimeSpatialIndexEquiv d k
          (finProdFinEquiv (i, 0))) := by
            rw [osiiFullFlatTimeSpatialIndexEquiv_time]
    _ = osiiParticleFlatCoordinates d k q (finProdFinEquiv (i, 0)) := by
          change (Equiv.piCongrLeft
              (fun _ : Fin (k + k * d) => Real)
              (osiiFullFlatTimeSpatialIndexEquiv d k)
              (osiiParticleFlatCoordinates d k q))
            (osiiFullFlatTimeSpatialIndexEquiv d k
              (finProdFinEquiv (i, 0))) =
              osiiParticleFlatCoordinates d k q (finProdFinEquiv (i, 0))
          exact Equiv.piCongrLeft_apply_apply
            (fun _ : Fin (k + k * d) => Real)
            (osiiFullFlatTimeSpatialIndexEquiv d k)
            (osiiParticleFlatCoordinates d k q)
            (finProdFinEquiv (i, 0))
    _ = q i 0 := osiiParticleFlatCoordinates_finProdFinEquiv q i 0

@[simp] theorem osiiFullFlatTimeSpatialReindexCLE_particleFlat_splitLast
    (q : NPointDomain d k) :
    splitLast k (k * d)
        (osiiFullFlatTimeSpatialReindexCLE d k
          (osiiParticleFlatCoordinates d k q)) =
      section43SpatialFlatCLE d k
        (section43QSpatial (d := d) (n := k) q) := by
  ext a
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
  rcases p with ⟨i, j⟩
  change (osiiFullFlatTimeSpatialReindexCLE d k
      (osiiParticleFlatCoordinates d k q))
      (Fin.natAdd k (finProdFinEquiv (i, j))) =
    section43SpatialFlatCLE d k
      (section43QSpatial (d := d) (n := k) q)
      (finProdFinEquiv (i, j))
  simp only [section43SpatialFlatCLE_apply, section43QSpatial_apply,
    Equiv.symm_apply_apply]
  calc
    (osiiFullFlatTimeSpatialReindexCLE d k
        (osiiParticleFlatCoordinates d k q))
        (Fin.natAdd k (finProdFinEquiv (i, j))) =
      (osiiFullFlatTimeSpatialReindexCLE d k
        (osiiParticleFlatCoordinates d k q))
        (osiiFullFlatTimeSpatialIndexEquiv d k
          (finProdFinEquiv (i, Fin.succ j))) := by
            rw [osiiFullFlatTimeSpatialIndexEquiv_spatial]
    _ = osiiParticleFlatCoordinates d k q
        (finProdFinEquiv (i, Fin.succ j)) := by
          change (Equiv.piCongrLeft
              (fun _ : Fin (k + k * d) => Real)
              (osiiFullFlatTimeSpatialIndexEquiv d k)
              (osiiParticleFlatCoordinates d k q))
            (osiiFullFlatTimeSpatialIndexEquiv d k
              (finProdFinEquiv (i, Fin.succ j))) =
              osiiParticleFlatCoordinates d k q
                (finProdFinEquiv (i, Fin.succ j))
          exact Equiv.piCongrLeft_apply_apply
            (fun _ : Fin (k + k * d) => Real)
            (osiiFullFlatTimeSpatialIndexEquiv d k)
            (osiiParticleFlatCoordinates d k q)
            (finProdFinEquiv (i, Fin.succ j))
    _ = q i j.succ :=
      osiiParticleFlatCoordinates_finProdFinEquiv q i j.succ

@[simp] theorem unflattenSchwartzNPoint_apply_osiiParticleFlatCoordinates
    (F : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (q : NPointDomain d k) :
    _root_.unflattenSchwartzNPoint (d := d) F q =
      F (osiiParticleFlatCoordinates d k q) := by
  rw [_root_.unflattenSchwartzNPoint_apply]
  congr 1

/-- Pulling a time-first flat tensor test back to particle-block coordinates
and then unflattening gives the existing Section 4.3 tensor test. -/
theorem unflatten_osiiFullFlatTimeSpatialPullbackCLM_tensorProduct
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Fin (k * d) -> Real) Complex) :
    _root_.unflattenSchwartzNPoint (d := d)
        (osiiFullFlatTimeSpatialPullbackCLM d k
          (SchwartzMap.tensorProduct phi chi)) =
      section43NPointTimeSpatialTensor d k phi
        ((section43SpatialFlatSchwartzCLE d k).symm chi) := by
  ext q
  rw [unflattenSchwartzNPoint_apply_osiiParticleFlatCoordinates]
  change
    SchwartzMap.tensorProduct phi chi
        (osiiFullFlatTimeSpatialReindexCLE d k
          (osiiParticleFlatCoordinates d k q)) = _
  rw [SchwartzMap.tensorProduct_apply,
    osiiFullFlatTimeSpatialReindexCLE_particleFlat_splitFirst,
    osiiFullFlatTimeSpatialReindexCLE_particleFlat_splitLast,
    section43NPointTimeSpatialTensor_apply,
    section43SpatialFlatSchwartzCLE_symm_apply]

/-- The existing particle-block canonical momentum distribution, viewed in
the time-first Section 4.3 frequency coordinates. -/
def osiiCanonicalFrequencyTimeSpatialBoundary
    (W : SchwartzNPoint d k →L[Complex] Complex) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  (osiiCanonicalFrequencyDistribution W).comp
    ((osiiFullFlatTimeSpatialPullbackCLM d k).comp
      (section43TimeSpatialFlatSchwartzCLM d k))

/-- The direct coordinate equivalence from particle-block flat coordinates to
the unflattened Section 4.3 time/spatial product. -/
def osiiFullFlatToTimeSpatialCLE (d k : Nat) [NeZero d] :
    (Fin (k * (d + 1)) -> Real) ≃L[Real]
      Section43TimeSpatialSpace d k :=
  (osiiFullFlatTimeSpatialReindexCLE d k).trans
    (section43TimeSpatialFlatCLE d k).symm

theorem osiiFullFlatTimeSpatialPullback_comp_flat_eq_direct
    (d k : Nat) [NeZero d] :
    (osiiFullFlatTimeSpatialPullbackCLM d k).comp
        (section43TimeSpatialFlatSchwartzCLM d k) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (osiiFullFlatToTimeSpatialCLE d k) := by
  ext F x
  rfl

/-- The temporal positive-energy cylinder expressed in the older
particle-block flat momentum coordinates. -/
def osiiCanonicalFrequencyTemporalCylinder (d k : Nat) [NeZero d] :
    Set (Fin (k * (d + 1)) -> Real) :=
  (osiiFullFlatToTimeSpatialCLE d k) ⁻¹'
    OSIIFullTimeStageVladimirovGrowthData.osiiTimeFrequencyPositiveCylinder d k

theorem osiiCanonicalFrequencyTimeSpatialBoundary_timeSpatialTensor
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCanonicalFrequencyTimeSpatialBoundary W
        (section43TimeSpatialTensor d k phi chi) =
      W (section43NPointTimeSpatialTensor d k
        (physicsFourierFlatInvCLM phi)
        (section43SpatialPhysicsFourierFlatInvCLM d k chi)) := by
  change W (_root_.unflattenSchwartzNPoint (d := d)
    (physicsFourierFlatInvCLM
      (osiiFullFlatTimeSpatialPullbackCLM d k
        (section43TimeSpatialFlatSchwartzCLM d k
          (section43TimeSpatialTensor d k phi chi))))) = _
  rw [section43TimeSpatialFlatSchwartzCLM_timeSpatialTensor]
  change W (_root_.unflattenSchwartzNPoint (d := d)
    (physicsFourierFlatInvCLM
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (ContinuousLinearEquiv.piCongrLeft Real
          (fun _ : Fin (k + k * d) => Real)
          (osiiFullFlatTimeSpatialIndexEquiv d k))
        (SchwartzMap.tensorProduct phi
          (section43SpatialFlatSchwartzCLE d k chi))))) = _
  rw [physicsFourierFlatInvCLM_comp_piCongrLeft,
    physicsFourierFlatInvCLM_tensorProduct]
  change W (_root_.unflattenSchwartzNPoint (d := d)
    (osiiFullFlatTimeSpatialPullbackCLM d k
      (SchwartzMap.tensorProduct
        (physicsFourierFlatInvCLM phi)
        (physicsFourierFlatInvCLM
          (section43SpatialFlatSchwartzCLE d k chi))))) = _
  rw [unflatten_osiiFullFlatTimeSpatialPullbackCLM_tensorProduct]
  rfl

/-- The time-first view of the older canonical frequency distribution is the
canonical Section 4.3 frequency boundary. -/
theorem osiiCanonicalFrequencyTimeSpatialBoundary_eq_section43Canonical
    (W : SchwartzNPoint d k →L[Complex] Complex) :
    osiiCanonicalFrequencyTimeSpatialBoundary W =
      section43CanonicalTimeSpatialFrequencyBoundary W := by
  apply OSIIFullTimeStageVladimirovGrowthData.section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
  intro phi chi
  rw [osiiCanonicalFrequencyTimeSpatialBoundary_timeSpatialTensor,
    section43CanonicalTimeSpatialFrequencyBoundary_timeSpatialTensor]

namespace OSIIFullTimeStageVladimirovGrowthData

variable {A : OSIITimeContinuationStage d k}

/-- The transported canonical frequency distribution vanishes on every
particle-block Schwartz test supported outside the temporal positive-energy
cylinder. -/
theorem osiiCanonicalFrequencyDistribution_isVanishingOn_compl_temporalCylinder
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ := by
  intro f hf
  let e := osiiFullFlatToTimeSpatialCLE d k
  let F : SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm f
  have hF :
      tsupport (F : Section43TimeSpatialSpace d k -> Complex) ⊆
        (osiiTimeFrequencyPositiveCylinder d k)ᶜ := by
    intro y hy
    have hy' :
        e.symm y ∈ tsupport
          (f : (Fin (k * (d + 1)) -> Real) -> Complex) := by
      have hpre :=
        tsupport_comp_subset_preimage
          (f : (Fin (k * (d + 1)) -> Real) -> Complex)
          e.symm.continuous
      simpa [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hpre hy
    have hnot : e.symm y ∈
        (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ := hf hy'
    simpa [osiiCanonicalFrequencyTemporalCylinder, e] using hnot
  have hvan :
      Distribution.IsVanishingOn
        (osiiCanonicalFrequencyTimeSpatialBoundary
          G.toTemperedBoundaryData.reducedBoundary)
        (osiiTimeFrequencyPositiveCylinder d k)ᶜ := by
    rw [osiiCanonicalFrequencyTimeSpatialBoundary_eq_section43Canonical,
      G.section43CanonicalTimeSpatialFrequencyBoundary_eq_fullFrequencyMixedBoundary]
    exact G.fullFrequencyMixedBoundary_isVanishingOn_compl_positiveCylinder
  have hzero := hvan F hF
  change
    osiiCanonicalFrequencyDistribution G.toTemperedBoundaryData.reducedBoundary
      (((osiiFullFlatTimeSpatialPullbackCLM d k).comp
        (section43TimeSpatialFlatSchwartzCLM d k)) F) = 0 at hzero
  rw [osiiFullFlatTimeSpatialPullback_comp_flat_eq_direct] at hzero
  have hroundtrip :
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex e F = f := by
    ext x
    simp [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [show osiiFullFlatToTimeSpatialCLE d k = e by rfl,
    hroundtrip] at hzero
  exact hzero

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
