/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform


























noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d m : Nat} [NeZero d]

/-- Flattened real coordinates for `m` reduced spacetime differences. -/
abbrev OSIIReducedForwardFlatRealSpace (d m : Nat) :=
  Fin (m * (d + 1)) -> Real

/-- Flattened complex coordinates for `m` reduced spacetime differences. -/
abbrev OSIIReducedForwardFlatSpace (d m : Nat) :=
  Fin (m * (d + 1)) -> Complex

/-- The flattened product forward cone for reduced difference variables. -/
def osiiReducedForwardFlatCone (d m : Nat) :
    Set (OSIIReducedForwardFlatRealSpace d m) :=
  BHW.FlatProductForwardConeReal d m

/-- The flattened reduced forward tube. -/
def osiiReducedForwardFlatDomain (d m : Nat) :
    Set (OSIIReducedForwardFlatSpace d m) :=
  SCV.TubeDomain (osiiReducedForwardFlatCone d m)

theorem isOpen_osiiReducedForwardFlatCone :
    IsOpen (osiiReducedForwardFlatCone d m) :=
  BHW.isOpen_flatProductForwardConeReal (n := m) (d := d)

omit [NeZero d] in
theorem osiiReducedForwardFlatCone_convex :
    Convex Real (osiiReducedForwardFlatCone d m) :=
  BHW.flatProductForwardConeReal_convex (n := m) (d := d)

omit [NeZero d] in
theorem osiiReducedForwardFlatCone_isCone :
    IsCone (osiiReducedForwardFlatCone d m) := by
  intro y hy t ht
  exact
    BHW.flatProductForwardConeReal_smul_pos
      (n := m) (d := d) t ht y hy

theorem osiiReducedForwardFlatCone_nonempty :
    (osiiReducedForwardFlatCone d m).Nonempty :=
  BHW.flatProductForwardConeReal_nonempty (n := m) (d := d)

/-- The real product forward cone is pointed.  This is proved directly in
difference coordinates so the active E-to-R route does not import the larger
spectral-equivalence development merely for this geometric fact. -/
theorem osiiProductForwardConeReal_salient (d m : Nat) :
    IsSalientCone (BHW.ProductForwardConeReal d m) := by
  intro y hy hny
  have htime : forall j : Fin m, y j 0 = 0 := by
    intro j
    let time : (Fin m -> Fin (d + 1) -> Real) -> Real :=
      fun w => w j 0
    have htime_cont : Continuous time :=
      (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply j)
    have hcone_time :
        BHW.ProductForwardConeReal d m ⊆
          {w : Fin m -> Fin (d + 1) -> Real | 0 < time w} := by
      intro w hw
      exact (hw j).1
    have hnonneg : 0 <= time y :=
      (closure_lt_subset_le continuous_const htime_cont)
        (closure_mono hcone_time hy)
    have hnonneg_neg : 0 <= time (-y) :=
      (closure_lt_subset_le continuous_const htime_cont)
        (closure_mono hcone_time hny)
    have hneg : time (-y) = -time y := by
      simp [time]
    linarith
  have hspatial :
      forall j : Fin m, forall i : Fin d, y j i.succ = 0 := by
    intro j i
    let spatialSq : (Fin m -> Fin (d + 1) -> Real) -> Real :=
      fun w => ∑ a : Fin d, (w j a.succ) ^ 2
    let timeSq : (Fin m -> Fin (d + 1) -> Real) -> Real :=
      fun w => (w j 0) ^ 2
    have hspatial_cont : Continuous spatialSq := by
      apply continuous_finset_sum
      intro a _
      exact
        ((continuous_apply a.succ).comp (continuous_apply j)).pow 2
    have htimeSq_cont : Continuous timeSq :=
      ((continuous_apply (0 : Fin (d + 1))).comp
        (continuous_apply j)).pow 2
    have hcone_quad :
        ∀ w, w ∈ BHW.ProductForwardConeReal d m ->
          spatialSq w <= timeSq w := by
      intro w hw
      have hquad := (hw j).2
      rw [BHW.minkowski_sum_decomp] at hquad
      change
        (∑ a : Fin d, (w j a.succ) ^ 2) <=
          (w j 0) ^ 2
      linarith
    have hquad_closed : spatialSq y <= timeSq y :=
      closure_minimal hcone_quad
        (isClosed_le hspatial_cont htimeSq_cont) hy
    have hspatial_nonpos : spatialSq y <= 0 := by
      simpa [timeSq, htime j] using hquad_closed
    have hone_le :
        (y j i.succ) ^ 2 <= spatialSq y := by
      exact
        Finset.single_le_sum
          (fun a _ => sq_nonneg (y j a.succ))
          (Finset.mem_univ i)
    have hsquare : (y j i.succ) ^ 2 = 0 := by
      apply le_antisymm
      · exact hone_le.trans hspatial_nonpos
      · exact sq_nonneg _
    exact (sq_eq_zero_iff).mp hsquare
  ext j mu
  by_cases hmu : mu = 0
  · subst hmu
    exact htime j
  · let i : Fin d := Fin.pred mu hmu
    have hmu_eq : mu = i.succ :=
      (Fin.succ_pred mu hmu).symm
    rw [hmu_eq]
    exact hspatial j i

private theorem continuous_osiiUnflattenCfgReal (d m : Nat) :
    Continuous
      (BHW.unflattenCfgReal m d :
        OSIIReducedForwardFlatRealSpace d m ->
          Fin m -> Fin (d + 1) -> Real) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro mu
  simpa [BHW.unflattenCfgReal] using
    (continuous_apply (finProdFinEquiv (j, mu)))

omit [NeZero d] in
/-- Salience transported to the flattened product cone. -/
theorem osiiReducedForwardFlatCone_salient :
    IsSalientCone (osiiReducedForwardFlatCone d m) := by
  intro u hu hnu
  let unflatten :
      OSIIReducedForwardFlatRealSpace d m ->
        Fin m -> Fin (d + 1) -> Real :=
    BHW.unflattenCfgReal m d
  have himage :
      unflatten '' osiiReducedForwardFlatCone d m ⊆
        BHW.ProductForwardConeReal d m := by
    rintro _ ⟨v, hv, rfl⟩
    exact hv
  have hu_image :
      unflatten u ∈
        unflatten '' closure (osiiReducedForwardFlatCone d m) :=
    ⟨u, hu, rfl⟩
  have hnu_image :
      unflatten (-u) ∈
        unflatten '' closure (osiiReducedForwardFlatCone d m) :=
    ⟨-u, hnu, rfl⟩
  have hu_closure :
      unflatten u ∈ closure (BHW.ProductForwardConeReal d m) :=
    closure_mono himage <|
      image_closure_subset_closure_image
        (continuous_osiiUnflattenCfgReal d m) hu_image
  have hnu_closure :
      -unflatten u ∈ closure (BHW.ProductForwardConeReal d m) := by
    have :
        unflatten (-u) ∈ closure (BHW.ProductForwardConeReal d m) :=
      closure_mono himage <|
        image_closure_subset_closure_image
          (continuous_osiiUnflattenCfgReal d m) hnu_image
    convert this using 1
    ext j mu
    simp [unflatten, BHW.unflattenCfgReal]
  have hunflatten_zero : unflatten u = 0 :=
    osiiProductForwardConeReal_salient d m
      (unflatten u) hu_closure hnu_closure
  calc
    u = BHW.flattenCfgReal m d (unflatten u) := by
      simpa [unflatten] using
        (BHW.flatten_unflatten_cfg_real m d u).symm
    _ = BHW.flattenCfgReal m d 0 :=
      congrArg (BHW.flattenCfgReal m d) hunflatten_zero
    _ = 0 := by
      ext i
      simp [BHW.flattenCfgReal]

theorem isOpen_osiiReducedForwardFlatDomain :
    IsOpen (osiiReducedForwardFlatDomain d m) :=
  SCV.tubeDomain_isOpen isOpen_osiiReducedForwardFlatCone

omit [NeZero d] in
/-- Reduced forward-tube membership is exactly flattened SCV tube-domain
membership. -/
theorem osiiReducedForwardTube_iff_flattenCfg_mem
    (z : Fin m -> Fin (d + 1) -> Complex) :
    z ∈ BHW.ProductForwardCone d m ↔
      BHW.flattenCfg m d z ∈ osiiReducedForwardFlatDomain d m := by
  change
    z ∈ BHW.ProductForwardCone d m ↔
      BHW.flattenCfg m d z ∈
        SCV.TubeDomain (BHW.FlatProductForwardConeReal d m)
  rw [BHW.mem_tubeDomain_flatProductForwardConeReal]
  exact BHW.mem_productForwardCone_iff_flat_im m d z

private theorem differentiable_osiiFlattenCfg (d m : Nat) :
    Differentiable Complex
      (BHW.flattenCfg m d :
        (Fin m -> Fin (d + 1) -> Complex) ->
          OSIIReducedForwardFlatSpace d m) := by
  rw [differentiable_pi]
  intro i
  simp only [BHW.flattenCfg]
  fun_prop

/-- The precise spectral input needed for a reduced forward-tube
Fourier-Laplace continuation. -/
structure OSIIReducedForwardTubeSpectralData (d m : Nat) where
  frequencyDistribution :
    SchwartzMap (OSIIReducedForwardFlatRealSpace d m) Complex →L[Complex]
      Complex
  support :
    HasFourierSupportInDualCone
      (osiiReducedForwardFlatCone d m) frequencyDistribution

/-- Flatten a reduced spacetime distribution without making any Fourier
choice. -/
def osiiFlatReducedBoundaryDistribution
    (W : SchwartzNPoint d m →L[Complex] Complex) :
    SchwartzMap (OSIIReducedForwardFlatRealSpace d m) Complex →L[Complex]
      Complex :=
  W.comp (unflattenSchwartzNPoint (d := d))

/-- The canonical momentum representative of a reduced spacetime
distribution, selected by the explicit inverse of the physics-convention
Fourier transform. -/
def osiiCanonicalFrequencyDistribution
    (W : SchwartzNPoint d m →L[Complex] Complex) :
    SchwartzMap (OSIIReducedForwardFlatRealSpace d m) Complex →L[Complex]
      Complex :=
  (osiiFlatReducedBoundaryDistribution W).comp physicsFourierFlatInvCLM

omit [NeZero d] in
@[simp]
theorem osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM
    (W : SchwartzNPoint d m →L[Complex] Complex)
    (f : SchwartzMap (OSIIReducedForwardFlatRealSpace d m) Complex) :
    osiiCanonicalFrequencyDistribution W (physicsFourierFlatCLM f) =
      osiiFlatReducedBoundaryDistribution W f := by
  change
    W (unflattenSchwartzNPoint
      (physicsFourierFlatInvCLM (physicsFourierFlatCLM f))) =
      W (unflattenSchwartzNPoint f)
  rw [physicsFourierFlatInvCLM_left]

/-- Boundary-side form of the reduced spectral input.  The frequency
distribution is no longer chosen: only support of the canonical Fourier
representative remains to be proved. -/
structure OSIIReducedForwardTubeBoundarySpectralData (d m : Nat) where
  boundaryDistribution : SchwartzNPoint d m →L[Complex] Complex
  support :
    HasFourierSupportInDualCone
      (osiiReducedForwardFlatCone d m)
      (osiiCanonicalFrequencyDistribution boundaryDistribution)

namespace OSIIReducedForwardTubeBoundarySpectralData

/-- Forget the reduced boundary presentation and retain the canonical
frequency-side Paley-Wiener input. -/
def toSpectralData
    (P : OSIIReducedForwardTubeBoundarySpectralData d m) :
    OSIIReducedForwardTubeSpectralData d m where
  frequencyDistribution :=
    osiiCanonicalFrequencyDistribution P.boundaryDistribution
  support := P.support

end OSIIReducedForwardTubeBoundarySpectralData

namespace OSIIReducedForwardTubeSpectralData

/-- The flattened Fourier-Laplace kernel. -/
def flatKernel (P : OSIIReducedForwardTubeSpectralData d m) :
    OSIIReducedForwardFlatSpace d m -> Complex :=
  fourierLaplaceExtMultiDim
    (osiiReducedForwardFlatCone d m)
    isOpen_osiiReducedForwardFlatCone
    osiiReducedForwardFlatCone_convex
    osiiReducedForwardFlatCone_isCone
    osiiReducedForwardFlatCone_salient
    P.frequencyDistribution

/-- The reduced difference-coordinate kernel. -/
def kernel (P : OSIIReducedForwardTubeSpectralData d m) :
    (Fin m -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => P.flatKernel (BHW.flattenCfg m d z)

/-- The boundary distribution selected by the physics Fourier convention. -/
def boundaryDistribution
    (P : OSIIReducedForwardTubeSpectralData d m) :
    SchwartzMap (OSIIReducedForwardFlatRealSpace d m) Complex →L[Complex]
      Complex :=
  P.frequencyDistribution.comp physicsFourierFlatCLM

/-- The boundary distribution transported back from flattened coordinates to
the reduced `m`-point Schwartz space. -/
def reducedBoundaryDistribution
    (P : OSIIReducedForwardTubeSpectralData d m) :
    SchwartzNPoint d m →L[Complex] Complex :=
  P.boundaryDistribution.comp (flattenSchwartzNPoint (d := d))

/-- Dual-cone support gives joint holomorphy on the flattened reduced forward
tube. -/
theorem flatKernel_holomorphic
    (P : OSIIReducedForwardTubeSpectralData d m) :
    DifferentiableOn Complex P.flatKernel
      (osiiReducedForwardFlatDomain d m) := by
  exact
    fourierLaplaceExtMultiDim_holomorphic
      (osiiReducedForwardFlatCone d m)
      isOpen_osiiReducedForwardFlatCone
      osiiReducedForwardFlatCone_convex
      osiiReducedForwardFlatCone_isCone
      osiiReducedForwardFlatCone_salient
      P.frequencyDistribution P.support

/-- The flattened kernel transports to a jointly holomorphic kernel on the
ordinary reduced difference-coordinate forward tube. -/
theorem kernel_holomorphic
    (P : OSIIReducedForwardTubeSpectralData d m) :
    DifferentiableOn Complex P.kernel
      (BHW.ProductForwardCone d m) := by
  intro z hz
  have hflat :
      BHW.flattenCfg m d z ∈ osiiReducedForwardFlatDomain d m :=
    (osiiReducedForwardTube_iff_flattenCfg_mem z).mp hz
  have hkernel_at :
      DifferentiableAt Complex P.flatKernel (BHW.flattenCfg m d z) :=
    (P.flatKernel_holomorphic _ hflat).differentiableAt
      (isOpen_osiiReducedForwardFlatDomain.mem_nhds hflat)
  exact
    (hkernel_at.comp z
      (differentiable_osiiFlattenCfg d m z)).differentiableWithinAt

/-- The Fourier-Laplace kernel has the global Vladimirov bound in flattened
reduced coordinates. -/
theorem flatKernel_vladimirov_growth
    (P : OSIIReducedForwardTubeSpectralData d m) :
    ∃ (C_bd : Real) (N M : Nat), C_bd > 0 ∧
      ∀ z : OSIIReducedForwardFlatSpace d m,
        z ∈ osiiReducedForwardFlatDomain d m ->
          ‖P.flatKernel z‖ <=
            C_bd * (1 + ‖z‖) ^ N *
              (1 +
                (Metric.infDist (fun i => (z i).im)
                  (osiiReducedForwardFlatCone d m)ᶜ)⁻¹) ^ M := by
  exact
    fourierLaplaceExtMultiDim_vladimirov_growth
      (osiiReducedForwardFlatCone d m)
      isOpen_osiiReducedForwardFlatCone
      osiiReducedForwardFlatCone_convex
      osiiReducedForwardFlatCone_isCone
      osiiReducedForwardFlatCone_salient
      P.frequencyDistribution P.support

/-- The Fourier-Laplace kernel converges distributionally to the selected
boundary distribution along every direction in the product forward cone. -/
theorem flatKernel_boundaryValue
    (P : OSIIReducedForwardTubeSpectralData d m) :
    ∀ eta : OSIIReducedForwardFlatRealSpace d m,
      eta ∈ osiiReducedForwardFlatCone d m ->
        ∀ f : SchwartzMap
            (OSIIReducedForwardFlatRealSpace d m) Complex,
          Tendsto
            (fun epsilon : Real =>
              ∫ x : OSIIReducedForwardFlatRealSpace d m,
                P.flatKernel
                    (fun i =>
                      (x i : Complex) +
                        (epsilon : Complex) * (eta i : Complex) * I) *
                  f x)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (P.boundaryDistribution f)) := by
  intro eta heta f
  simpa [flatKernel, boundaryDistribution] using
    fourierLaplaceExtMultiDim_boundaryValue
      (osiiReducedForwardFlatCone d m)
      isOpen_osiiReducedForwardFlatCone
      osiiReducedForwardFlatCone_convex
      osiiReducedForwardFlatCone_isCone
      osiiReducedForwardFlatCone_salient
      osiiReducedForwardFlatCone_nonempty
      P.frequencyDistribution P.support eta heta f

end OSIIReducedForwardTubeSpectralData

namespace OSIIReducedForwardTubeBoundarySpectralData

omit [NeZero d] in
@[simp]
theorem toSpectralData_boundaryDistribution
    (P : OSIIReducedForwardTubeBoundarySpectralData d m) :
    P.toSpectralData.boundaryDistribution =
      osiiFlatReducedBoundaryDistribution P.boundaryDistribution := by
  ext f
  exact
    osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM
      P.boundaryDistribution f

omit [NeZero d] in
@[simp]
theorem toSpectralData_reducedBoundaryDistribution
    (P : OSIIReducedForwardTubeBoundarySpectralData d m) :
    P.toSpectralData.reducedBoundaryDistribution =
      P.boundaryDistribution := by
  ext f
  calc
    P.toSpectralData.reducedBoundaryDistribution f =
        P.toSpectralData.boundaryDistribution
          (flattenSchwartzNPoint f) := rfl
    _ = osiiFlatReducedBoundaryDistribution P.boundaryDistribution
          (flattenSchwartzNPoint f) := by
        rw [toSpectralData_boundaryDistribution]
    _ = P.boundaryDistribution
          (unflattenSchwartzNPoint (flattenSchwartzNPoint f)) := rfl
    _ = P.boundaryDistribution f := by
        apply congrArg P.boundaryDistribution
        ext x
        simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]

end OSIIReducedForwardTubeBoundarySpectralData

end OSReconstruction
