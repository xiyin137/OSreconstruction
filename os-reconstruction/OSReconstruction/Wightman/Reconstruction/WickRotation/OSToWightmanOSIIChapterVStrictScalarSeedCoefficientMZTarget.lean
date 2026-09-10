import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientMZ

/-!
# Distribution-valued strict coefficient targets

For one finite strict-seed coefficient chart, compact-local stage bounds give
a common Malgrange-Zerner continuation for every spatial Schwartz pairing.
Connected-domain uniqueness removes all dependence on the selected scalar
continuation, proves linearity in the spatial test, and preserves the sharp
Schwartz seminorm bound at simultaneous coefficient targets.

The resulting target value is therefore a genuine spatial distribution. This
module deliberately stops before ambient logarithmic-chart gluing.
-/

noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

@[simp]
theorem osiiStrictScalarSeedCoefficientPairing_add
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (chi psi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (r : ι -> Complex) :
    osiiStrictScalarSeedCoefficientPairing A seed (chi + psi) r =
      osiiStrictScalarSeedCoefficientPairing A seed chi r +
        osiiStrictScalarSeedCoefficientPairing A seed psi r := by
  simp [osiiStrictScalarSeedCoefficientPairing]

@[simp]
theorem osiiStrictScalarSeedCoefficientPairing_smul
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (c : Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (r : ι -> Complex) :
    osiiStrictScalarSeedCoefficientPairing A seed (c • chi) r =
      c * osiiStrictScalarSeedCoefficientPairing A seed chi r := by
  simp [osiiStrictScalarSeedCoefficientPairing, smul_eq_mul]

/-- Uniform data needed to continue all spatial pairings in one fixed
strict-seed coefficient chart. -/
structure StrictScalarSeedCoefficientMZBoundData
    {d : Nat} [NeZero d]
    {n k : Nat}
    (A : OSIITimeContinuationStage d k)
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (seed : Fin n -> Fin k -> Real) where
  flatCoefficientTube_subset :
    SCV.horizontalTube
        (fintypeFlatImaginaryUnion (Fin n) 1) ⊆
      osiiStrictScalarSeedCoefficientCarrier A seed
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  seminormIndices : Finset (Nat × Nat)
  constant : Real
  constant_pos : 0 < constant
  bound :
    ∀ r ∈
        osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho,
      ∀ chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        ‖osiiStrictScalarSeedCoefficientPairing
            A seed chi r‖ <=
          constant *
            seminormIndices.sup
              (schwartzSeminormFamily Complex
                (Section43SpatialSpace d k) Complex) chi

namespace StrictScalarSeedCoefficientMZBoundData

set_option maxHeartbeats 800000

variable
  {d : Nat} [NeZero d]
  {n k : Nat} [NeZero n]
  {A : OSIITimeContinuationStage d k}
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {seed : Fin n -> Fin k -> Real}

omit [NeZero n] in
/-- Compact-local bounds from the predecessor stage supply one uniform MZ
bound package for the complete coefficient chart. -/
theorem nonempty
    (hflat :
      SCV.horizontalTube
          (fintypeFlatImaginaryUnion (Fin n) 1) ⊆
        osiiStrictScalarSeedCoefficientCarrier A seed)
    (hrho : 0 < rho)
    (hrho_lt_one : rho < 1) :
    Nonempty
      (StrictScalarSeedCoefficientMZBoundData A P seed) := by
  obtain ⟨delta, _hdelta, _hdelta_subset,
      s, C, hC, hbound⟩ :=
    exists_strictScalarSeedCoefficientFlatWindow_neighborhood_bound_of_flat
      A seed hflat (P.radius + rho) rho hrho_lt_one
  refine ⟨{
    flatCoefficientTube_subset := hflat
    rho_pos := hrho
    rho_lt_one := hrho_lt_one
    seminormIndices := s
    constant := C
    constant_pos := hC
    bound := ?_ }⟩
  intro r hr chi
  have hr' :
      r ∈
        Metric.cthickening delta
          (osiiStrictScalarSeedCoefficientFlatWindow
            (Fin n) (P.radius + rho) rho) :=
    Metric.self_subset_cthickening _ hr
  exact hbound r hr' chi

/-- Common real edge of the compactified coefficient continuation. -/
def realEdge
    (_B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : osiiAxisPairIndex n -> Real) :
    Complex :=
  osiiStrictScalarSeedCoefficientPairing
    A seed chi
    (fun j =>
      SCV.stripCompactification P.radius P.slope
        (x (j, false) : Complex))

/-- Every spatial pairing in the fixed chart has a holomorphic
compactified MZ continuation with the explicit common real edge. -/
theorem exists_extension
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ∃ Gamma : (osiiAxisPairIndex n -> Complex) -> Complex,
      DifferentiableOn Complex Gamma
        (osiiAxisPairLogDomain (d := n)) ∧
      forall x : osiiAxisPairIndex n -> Real,
        Gamma (osiiAxisPairLogRealEmbed x) =
          B.realEdge chi x := by
  let F : (Fin n -> Complex) -> Complex :=
    osiiStrictScalarSeedCoefficientPairing
      A seed chi
  let U : Set (Fin n -> Complex) :=
    osiiStrictScalarSeedCoefficientCarrier
      A seed
  have hF :
      DifferentiableOn Complex F U := by
    exact
      differentiableOn_osiiStrictScalarSeedCoefficientPairing
        A seed chi
  have hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U := by
    exact
      strictScalarSeedCoefficientFlatWindow_subset_carrier_of_flat
        A seed B.flatCoefficientTube_subset
        (P.radius + rho) rho B.rho_lt_one
  let q : Real :=
    B.seminormIndices.sup
      (schwartzSeminormFamily Complex
        (Section43SpatialSpace d k) Complex) chi
  let Cchi : Real := 1 + B.constant * q
  have hq : 0 <= q := by
    exact apply_nonneg _ _
  have hCchi : 0 < Cchi := by
    dsimp [Cchi]
    nlinarith [B.constant_pos.le]
  have hbound :
      ∀ r,
        r ∈
            osiiStrictScalarSeedCoefficientFlatWindow
              (Fin n) (P.radius + rho) rho →
          ‖F r‖ <= Cchi := by
    intro r hr
    calc
      ‖F r‖ <= B.constant * q := by
        exact B.bound r hr chi
      _ <= Cchi := by
        dsimp [Cchi]
        linarith
  obtain ⟨Gamma, hGamma, hreal, _hflat, _hGamma_bound⟩ :=
    exists_osiiStrictCoefficientCompactifiedMZExtension
      P B.rho_pos F U hF hwindow Cchi hCchi hbound
  refine ⟨Gamma, hGamma, ?_⟩
  intro x
  simpa [realEdge, F, U,
    osiiStrictCoefficientCompactifiedFlatCrossData,
    osiiStrictCoefficientCompactifiedDirectionalFamily] using
    hreal x

/-- A canonical selected continuation for later algebraic packaging. -/
def extension
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    (osiiAxisPairIndex n -> Complex) -> Complex :=
  Classical.choose (B.exists_extension chi)

theorem extension_differentiableOn
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex (B.extension chi)
      (osiiAxisPairLogDomain (d := n)) :=
  (Classical.choose_spec (B.exists_extension chi)).1

theorem extension_realEdge
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : osiiAxisPairIndex n -> Real) :
    B.extension chi (osiiAxisPairLogRealEmbed x) =
      B.realEdge chi x :=
  (Classical.choose_spec (B.exists_extension chi)).2 x

omit [NeZero n] in
/-- Holomorphic functions on the connected MZ carrier are determined by
their complete real edge. -/
theorem eqOn_logDomain_of_eq_realEdge
    {Gamma₁ Gamma₂ :
      (osiiAxisPairIndex n -> Complex) -> Complex}
    (hGamma₁ :
      DifferentiableOn Complex Gamma₁
        (osiiAxisPairLogDomain (d := n)))
    (hGamma₂ :
      DifferentiableOn Complex Gamma₂
        (osiiAxisPairLogDomain (d := n)))
    (hreal :
      forall x : osiiAxisPairIndex n -> Real,
        Gamma₁ (osiiAxisPairLogRealEmbed x) =
          Gamma₂ (osiiAxisPairLogRealEmbed x)) :
    Set.EqOn Gamma₁ Gamma₂
      (osiiAxisPairLogDomain (d := n)) := by
  intro z hz
  apply
    SCV.holomorphic_eq_of_eq_on_real_of_connected_finite
      isOpen_osiiAxisPairLogDomain
      isConnected_osiiAxisPairLogDomain
      hGamma₁ hGamma₂
      (x₀ := (0 : osiiAxisPairIndex n -> Real))
  · simpa [osiiAxisPairLogRealEmbed] using
      (osiiAxisPairLogRealEmbed_mem
        (0 : osiiAxisPairIndex n -> Real))
  · intro x _hx
    simpa [osiiAxisPairLogRealEmbed] using hreal x
  · exact hz

omit [NeZero n] in
@[simp]
theorem realEdge_add
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi psi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : osiiAxisPairIndex n -> Real) :
    B.realEdge (chi + psi) x =
      B.realEdge chi x + B.realEdge psi x := by
  simp [realEdge]

omit [NeZero n] in
@[simp]
theorem realEdge_smul
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (c : Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : osiiAxisPairIndex n -> Real) :
    B.realEdge (c • chi) x =
      c * B.realEdge chi x := by
  simp [realEdge]

/-- The selected continuation is additive, by uniqueness from its real
edge. -/
theorem extension_add
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi psi : SchwartzMap (Section43SpatialSpace d k) Complex)
    {z : osiiAxisPairIndex n -> Complex}
    (hz : z ∈ osiiAxisPairLogDomain (d := n)) :
    B.extension (chi + psi) z =
      B.extension chi z + B.extension psi z := by
  apply
    eqOn_logDomain_of_eq_realEdge
      (B.extension_differentiableOn (chi + psi))
      ((B.extension_differentiableOn chi).add
        (B.extension_differentiableOn psi))
      (fun x => by
        rw [B.extension_realEdge]
        change
          B.realEdge (chi + psi) x =
            B.extension chi (osiiAxisPairLogRealEmbed x) +
              B.extension psi (osiiAxisPairLogRealEmbed x)
        rw [B.extension_realEdge, B.extension_realEdge]
        exact B.realEdge_add chi psi x)
      hz

/-- The selected continuation is complex homogeneous, by uniqueness from
its real edge. -/
theorem extension_smul
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (c : Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    {z : osiiAxisPairIndex n -> Complex}
    (hz : z ∈ osiiAxisPairLogDomain (d := n)) :
    B.extension (c • chi) z =
      c * B.extension chi z := by
  apply
    eqOn_logDomain_of_eq_realEdge
      (B.extension_differentiableOn (c • chi))
      ((differentiableOn_const c).mul
        (B.extension_differentiableOn chi))
      (fun x => by
        rw [B.extension_realEdge]
        change
          B.realEdge (c • chi) x =
            c * B.extension chi (osiiAxisPairLogRealEmbed x)
        rw [B.extension_realEdge]
        exact B.realEdge_smul c chi x)
      hz

/-- Value of the compactified coefficient continuation at one simultaneous
nonnegative coefficient target. -/
def targetValue
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Complex :=
  B.extension chi
    (osiiStrictCoefficientCompactifiedMZTarget P w)

theorem targetValue_add
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S)
    (chi psi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.targetValue w (chi + psi) =
      B.targetValue w chi + B.targetValue w psi := by
  exact
    B.extension_add chi psi
      (osiiStrictCoefficientCompactifiedMZTarget_mem_logDomain
        P w hw hsum)

theorem targetValue_smul
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S)
    (c : Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.targetValue w (c • chi) =
      c * B.targetValue w chi := by
  exact
    B.extension_smul c chi
      (osiiStrictCoefficientCompactifiedMZTarget_mem_logDomain
        P w hw hsum)

/-- The common real edge obeys the original sharp compact-window seminorm
bound. -/
theorem norm_realEdge_le
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (x : osiiAxisPairIndex n -> Real) :
    ‖B.realEdge chi x‖ <=
      B.constant *
        B.seminormIndices.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi := by
  let a0 : osiiAxisPairIndex n :=
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, false)
  have hstrip :
      osiiAxisPairLogRealEmbed x ∈
        osiiAxisPairCoordinateLogStrip a0 := by
    simp [osiiAxisPairCoordinateLogStrip,
      osiiAxisPairLogRealEmbed]
    positivity
  have hmem :=
    osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
      P B.rho_pos x a0 hstrip
  have hbound := B.bound _ hmem chi
  simpa [realEdge,
    osiiStrictCoefficientCompactifiedDirectionalInput_real] using
    hbound

/-- The selected continuation inherits the same sharp Schwartz seminorm
bound at every point of the complete logarithmic MZ domain. -/
theorem norm_extension_le
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (z : osiiAxisPairIndex n -> Complex)
    (hz : z ∈ osiiAxisPairLogDomain (d := n)) :
    ‖B.extension chi z‖ <=
      B.constant *
        B.seminormIndices.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi := by
  let F : (Fin n -> Complex) -> Complex :=
    osiiStrictScalarSeedCoefficientPairing
      A seed chi
  let U : Set (Fin n -> Complex) :=
    osiiStrictScalarSeedCoefficientCarrier
      A seed
  have hF :
      DifferentiableOn Complex F U := by
    exact
      differentiableOn_osiiStrictScalarSeedCoefficientPairing
        A seed chi
  have hwindow :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆ U := by
    exact
      strictScalarSeedCoefficientFlatWindow_subset_carrier_of_flat
        A seed B.flatCoefficientTube_subset
        (P.radius + rho) rho B.rho_lt_one
  let X :=
    osiiStrictCoefficientCompactifiedFlatCrossData
      P B.rho_pos F U hF hwindow
  let q : Real :=
    B.seminormIndices.sup
      (schwartzSeminormFamily Complex
        (Section43SpatialSpace d k) Complex) chi
  have hq : 0 <= q := by
    exact apply_nonneg _ _
  have hreal :
      forall x : osiiAxisPairIndex n -> Real,
        B.extension chi (osiiAxisPairLogRealEmbed x) =
          X.family.realEdge x := by
    intro x
    simpa [X, F, U, realEdge,
      osiiStrictCoefficientCompactifiedFlatCrossData,
      osiiStrictCoefficientCompactifiedDirectionalFamily] using
      B.extension_realEdge chi x
  have hreal_bound :
      forall x : osiiAxisPairIndex n -> Real,
        ‖X.family.realEdge x‖ <= B.constant * q := by
    intro x
    simpa [X, F, U, realEdge, q,
      osiiStrictCoefficientCompactifiedFlatCrossData,
      osiiStrictCoefficientCompactifiedDirectionalFamily] using
      B.norm_realEdge_le chi x
  have hchart_bound :
      forall a : osiiAxisPairIndex n,
        forall (x : osiiAxisPairIndex n -> Real) (z : Complex),
          |z.im| < Real.pi / 2 ->
          ‖X.family.flatTubeBranch
            (Function.update
              (osiiAxisPairLogRealEmbed x) a z)‖ <=
            B.constant * q := by
    intro a x z hz
    rw [X.family.flatTubeBranch_coordinate_line_eq_branch
      x a hz]
    apply B.bound
    apply
      osiiStrictCoefficientCompactifiedDirectionalInput_mem_flatWindow
        P B.rho_pos x a
    simpa [osiiAxisPairCoordinateLogStrip] using hz
  by_cases hqzero : q = 0
  · have hzero_real :
        forall x : osiiAxisPairIndex n -> Real,
          B.extension chi (osiiAxisPairLogRealEmbed x) =
            (0 : Complex) := by
      intro x
      rw [B.extension_realEdge]
      apply norm_eq_zero.mp
      apply le_antisymm
      · simpa [q, hqzero] using B.norm_realEdge_le chi x
      · exact norm_nonneg _
    have hzero :
        B.extension chi z = 0 := by
      exact
        eqOn_logDomain_of_eq_realEdge
          (B.extension_differentiableOn chi)
          (differentiableOn_const (0 : Complex))
          hzero_real
          hz
    rw [hzero, norm_zero]
    simp [q, hqzero]
  · have hqpos : 0 < q :=
      lt_of_le_of_ne hq (Ne.symm hqzero)
    have hCq : 0 < B.constant * q :=
      mul_pos B.constant_pos hqpos
    exact
      X.norm_holomorphic_realEdge_extension_le
        (B.constant * q) hreal_bound
        (B.constant * q) hCq hchart_bound
        (B.extension chi)
        (B.extension_differentiableOn chi)
        hreal
        z hz

/-- The selected target value inherits the same sharp Schwartz seminorm
bound as the original compact coefficient cross. -/
theorem norm_targetValue_le
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖B.targetValue w chi‖ <=
      B.constant *
        B.seminormIndices.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi :=
  B.norm_extension_le chi
    (osiiStrictCoefficientCompactifiedMZTarget P w)
    (osiiStrictCoefficientCompactifiedMZTarget_mem_logDomain
      P w hw hsum)

/-- The target continuation packaged as a genuine spatial Schwartz
distribution. -/
def targetDistribution
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    OSIISpatialDistribution d k :=
  SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex)
    (B.targetValue w)
    (B.targetValue_add w hw hsum)
    (fun c chi => by
      simpa [smul_eq_mul] using
        B.targetValue_smul w hw hsum c chi)
    ⟨B.seminormIndices, B.constant, B.constant_pos.le,
      B.norm_targetValue_le w hw hsum⟩

@[simp]
theorem targetDistribution_apply
    (B : StrictScalarSeedCoefficientMZBoundData A P seed)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.targetDistribution w hw hsum chi =
      B.targetValue w chi :=
  rfl

end StrictScalarSeedCoefficientMZBoundData
end OSIIChapterV
end OSReconstruction
