/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldScales
import OSReconstruction.SCV.TotallyRealIdentity



















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A scale-indexed open-domain block together with its honest positive-time
source realization on one scale-independent real neighborhood. -/
structure GeneratorOpenHilbertFieldScaleBlockRealEdgeData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (n m : ℕ)
    extends GeneratorOpenHilbertFieldScaleBlockData OS m where
  source :
    ℕ → ℕ → (Fin m → ℝ) →
      euclideanPositiveTimeSubmodule (d := d) n
  realRegion : Set (Fin m → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_mem_nhds : realRegion ∈ 𝓝 0
  realToComplex_mem_domain :
    ∀ x, x ∈ realRegion →
      (fun a => (x a : ℂ)) ∈ domain
  field_realEdge :
    ∀ scale mode,
      HasPositiveTimeSourceRealEdge OS
        (field scale mode) (source scale mode) realRegion

/-- All left and right open-domain generator fields, retaining their
scale-indexed positive-time sources and real edges. -/
structure GeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (k : ℕ)
    extends GeneratorOpenHilbertFieldScaleFamilyData OS k where
  leftSource :
    (i : GeneratorIndex k) → ℕ → ℕ →
      (Fin (i.n - 1) → ℝ) →
        euclideanPositiveTimeSubmodule (d := d) i.n
  rightSource :
    (i : GeneratorIndex k) → ℕ → ℕ →
      (Fin (i.m - 1) → ℝ) →
        euclideanPositiveTimeSubmodule (d := d) i.m
  leftRealRegion :
    (i : GeneratorIndex k) → Set (Fin (i.n - 1) → ℝ)
  rightRealRegion :
    (i : GeneratorIndex k) → Set (Fin (i.m - 1) → ℝ)
  leftRealRegion_open :
    ∀ i, IsOpen (leftRealRegion i)
  rightRealRegion_open :
    ∀ i, IsOpen (rightRealRegion i)
  leftRealRegion_mem_nhds :
    ∀ i, leftRealRegion i ∈ 𝓝 0
  rightRealRegion_mem_nhds :
    ∀ i, rightRealRegion i ∈ 𝓝 0
  leftRealToComplex_mem_domain :
    ∀ i x, x ∈ leftRealRegion i →
      (fun a => (x a : ℂ)) ∈ leftDomain i
  rightRealToComplex_mem_domain :
    ∀ i x, x ∈ rightRealRegion i →
      (fun a => (x a : ℂ)) ∈ rightDomain i
  leftField_realEdge :
    ∀ i scale mode,
      HasPositiveTimeSourceRealEdge OS
        (leftField i scale mode)
        (leftSource i scale mode)
        (leftRealRegion i)
  rightField_realEdge :
    ∀ i scale mode,
      HasPositiveTimeSourceRealEdge OS
        (rightField i scale mode)
        (rightSource i scale mode)
        (rightRealRegion i)

namespace GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Assemble the all-split source-realized family from source-realized block
packages. -/
def ofBlocks
    (left :
      (i : GeneratorIndex k) →
        GeneratorOpenHilbertFieldScaleBlockRealEdgeData
          OS i.n (i.n - 1))
    (right :
      (i : GeneratorIndex k) →
        GeneratorOpenHilbertFieldScaleBlockRealEdgeData
          OS i.m (i.m - 1)) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k where
  toGeneratorOpenHilbertFieldScaleFamilyData :=
    GeneratorOpenHilbertFieldScaleFamilyData.ofBlocks
      (fun i =>
        (left i).toGeneratorOpenHilbertFieldScaleBlockData)
      (fun i =>
        (right i).toGeneratorOpenHilbertFieldScaleBlockData)
  leftSource i := (left i).source
  rightSource i := (right i).source
  leftRealRegion i := (left i).realRegion
  rightRealRegion i := (right i).realRegion
  leftRealRegion_open i := (left i).realRegion_open
  rightRealRegion_open i := (right i).realRegion_open
  leftRealRegion_mem_nhds i := (left i).realRegion_mem_nhds
  rightRealRegion_mem_nhds i := (right i).realRegion_mem_nhds
  leftRealToComplex_mem_domain i := (left i).realToComplex_mem_domain
  rightRealToComplex_mem_domain i := (right i).realToComplex_mem_domain
  leftField_realEdge i := (left i).field_realEdge
  rightField_realEdge i := (right i).field_realEdge

private theorem tendsto_leftRealCoordinates_zero
    (i : GeneratorIndex k) :
    Tendsto i.leftRealCoordinates (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous i.leftRealCoordinates := by
    unfold GeneratorIndex.leftRealCoordinates
    fun_prop
  have hzero :
      i.leftRealCoordinates (0 : Fin k → ℝ) = 0 := by
    ext a
    simp [GeneratorIndex.leftRealCoordinates]
  rw [← hzero]
  exact hcontinuous.continuousAt

private theorem tendsto_rightRealCoordinates_zero
    (i : GeneratorIndex k) :
    Tendsto i.rightRealCoordinates (𝓝 0) (𝓝 0) := by
  have hcontinuous : Continuous i.rightRealCoordinates := by
    unfold GeneratorIndex.rightRealCoordinates
    fun_prop
  have hzero :
      i.rightRealCoordinates (0 : Fin k → ℝ) = 0 := by
    ext b
    simp [GeneratorIndex.rightRealCoordinates]
  rw [← hzero]
  exact hcontinuous.continuousAt

/-- The source-realized left and right field conditions for every split. -/
def simultaneousRealAutomaticSet
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k) :
    Set (Fin k → ℝ) :=
  {τ | ∀ i : GeneratorIndex k,
    i.leftRealCoordinates τ ∈ E.leftRealRegion i ∧
      i.rightRealCoordinates τ ∈ E.rightRealRegion i}

/-- Finiteness of the generator splits makes all block real-edge conditions
hold on one neighborhood of the global real origin. -/
theorem simultaneousRealAutomaticSet_mem_nhds
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k) :
    E.simultaneousRealAutomaticSet ∈ 𝓝 0 := by
  letI : Fintype (GeneratorIndex k) :=
    Fintype.ofEquiv (Fin k) (GeneratorIndex.equivGap k).symm
  change
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      ∀ i : GeneratorIndex k,
        i.leftRealCoordinates τ ∈ E.leftRealRegion i ∧
          i.rightRealCoordinates τ ∈ E.rightRealRegion i
  rw [Filter.eventually_all]
  intro i
  filter_upwards
    [(tendsto_leftRealCoordinates_zero i).eventually
      (E.leftRealRegion_mem_nhds i),
    (tendsto_rightRealCoordinates_zero i).eventually
      (E.rightRealRegion_mem_nhds i)] with τ hleft hright
  exact ⟨hleft, hright⟩

private theorem open_inter_strictPositive_nonempty
    (V : Set (Fin k → ℝ))
    (hVopen : IsOpen V)
    (h0V : (0 : Fin k → ℝ) ∈ V) :
    (V ∩ section43TimeStrictPositiveRegion k).Nonempty := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (hVopen.mem_nhds h0V)
  let τ : Fin k → ℝ := fun _ => ε / 2
  refine ⟨τ, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖τ‖ ≤ ‖ε / 2‖ := by
        simpa [τ] using
          (pi_norm_const_le (ι := Fin k) (ε / 2 : ℝ))
      _ = ε / 2 := by
        rw [Real.norm_of_nonneg]
        linarith
      _ < ε := by linarith
  · intro j
    exact half_pos hε

/-- Two source-realized open-field families carry the same positive-time
sources at every split, packet scale, Hermite mode, and real block
parameter. -/
structure SourceAgreementData
    (E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k) where
  leftSource_eq :
    ∀ i scale mode x,
      E.leftSource i scale mode x =
        F.leftSource i scale mode x
  rightSource_eq :
    ∀ i scale mode x,
      E.rightSource i scale mode x =
        F.rightSource i scale mode x

namespace SourceAgreementData

variable
  {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}

/-- The real points where both source-realized families are simultaneously
admissible for every generator split. -/
def commonRealAutomaticSet
    (_P : SourceAgreementData E F) :
    Set (Fin k → ℝ) :=
  E.simultaneousRealAutomaticSet ∩
    F.simultaneousRealAutomaticSet

theorem commonRealAutomaticSet_mem_nhds
    (P : SourceAgreementData E F) :
    P.commonRealAutomaticSet ∈ 𝓝 0 :=
  Filter.inter_mem
    E.simultaneousRealAutomaticSet_mem_nhds
    F.simultaneousRealAutomaticSet_mem_nhds

/-- Equal realized sources identify the original-OS scalar generators on
their common positive-real source edge. -/
theorem modeOfOS_eq_on_commonReal
    (P : SourceAgreementData E F)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hE : τ ∈ E.simultaneousRealAutomaticSet)
    (hF : τ ∈ F.simultaneousRealAutomaticSet) :
    E.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) =
      F.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) := by
  calc
    E.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) =
        OS.S (i.n + i.m)
          (ZeroDiagonalSchwartz.ofClassical
            (((E.leftSource i scale mode
                (i.leftRealCoordinates τ)).1).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (τ i.bridgeGlobalIndex)
                (E.rightSource i scale mode
                  (i.rightRealCoordinates τ)).1))) := by
      exact
        generatorSemigroupPairing_positiveReal_eq_schwinger
          OS i
          (E.leftField i scale mode)
          (E.rightField i scale mode)
          (E.leftSource i scale mode)
          (E.rightSource i scale mode)
          (E.leftField_realEdge i scale mode)
          (E.rightField_realEdge i scale mode)
          τ hbridge (hE i).1 (hE i).2
    _ =
        OS.S (i.n + i.m)
          (ZeroDiagonalSchwartz.ofClassical
            (((F.leftSource i scale mode
                (i.leftRealCoordinates τ)).1).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (τ i.bridgeGlobalIndex)
                (F.rightSource i scale mode
                  (i.rightRealCoordinates τ)).1))) := by
      rw [P.leftSource_eq, P.rightSource_eq]
    _ =
        F.modeOfOS scale i mode
          (osiiPositiveRealTimeEmbed τ) := by
      symm
      exact
        generatorSemigroupPairing_positiveReal_eq_schwinger
          OS i
          (F.leftField i scale mode)
          (F.rightField i scale mode)
          (F.leftSource i scale mode)
          (F.rightSource i scale mode)
          (F.leftField_realEdge i scale mode)
          (F.rightField_realEdge i scale mode)
          τ hbridge (hF i).1 (hF i).2

/-- A common positive-real germ on which all genuine original-OS scalar
generators of two source-agreeing families coincide. -/
structure CommonPositiveRealModeAgreementDataOfOS
    (P : SourceAgreementData E F) where
  realRegion : Set (Fin k -> ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  first_real_mem :
    ∀ i τ, τ ∈ realRegion ->
      osiiPositiveRealTimeEmbed τ ∈ E.domain i
  second_real_mem :
    ∀ i τ, τ ∈ realRegion ->
      osiiPositiveRealTimeEmbed τ ∈ F.domain i
  mode_eq :
    ∀ i scale mode τ, τ ∈ realRegion ->
      E.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ) =
        F.modeOfOS scale i mode (osiiPositiveRealTimeEmbed τ)

/-- Equal original-OS positive-time sources determine one common positive
real generator germ before any quantitative arity-growth assumption. -/
noncomputable def toCommonPositiveRealModeAgreementDataOfOS
    (P : SourceAgreementData E F) :
    P.CommonPositiveRealModeAgreementDataOfOS := by
  let hV := mem_nhds_iff.mp P.commonRealAutomaticSet_mem_nhds
  let V : Set (Fin k -> ℝ) := Classical.choose hV
  have hVspec := Classical.choose_spec hV
  have hVsub : V ⊆ P.commonRealAutomaticSet :=
    hVspec.1
  have hVopen : IsOpen V := hVspec.2.1
  have h0V : (0 : Fin k -> ℝ) ∈ V := hVspec.2.2
  refine
    { realRegion :=
        V ∩ section43TimeStrictPositiveRegion k
      realRegion_open :=
        hVopen.inter (isOpen_section43TimeStrictPositiveRegion k)
      realRegion_nonempty :=
        open_inter_strictPositive_nonempty V hVopen h0V
      first_real_mem := ?_
      second_real_mem := ?_
      mode_eq := ?_ }
  · intro i τ hτ
    have hE := (hVsub hτ.1).1
    exact
      positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i τ
        (hτ.2 i.bridgeGlobalIndex)
        (E.leftRealToComplex_mem_domain
          i (i.leftRealCoordinates τ) (hE i).1)
        (E.rightRealToComplex_mem_domain
          i (i.rightRealCoordinates τ) (hE i).2)
  · intro i τ hτ
    have hF := (hVsub hτ.1).2
    exact
      positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i τ
        (hτ.2 i.bridgeGlobalIndex)
        (F.leftRealToComplex_mem_domain
          i (i.leftRealCoordinates τ) (hF i).1)
        (F.rightRealToComplex_mem_domain
          i (i.rightRealCoordinates τ) (hF i).2)
  · intro i scale mode τ hτ
    exact
      P.modeOfOS_eq_on_commonReal i scale mode τ
        (hτ.2 i.bridgeGlobalIndex)
        (hVsub hτ.1).1
        (hVsub hτ.1).2

/-- Compatibility presentation of the genuine original-OS common real
generator germ. -/
structure CommonPositiveRealModeAgreementData
    (P : SourceAgreementData E F)
    (lgc : OSLinearGrowthCondition d OS) where
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  first_real_mem :
    ∀ i τ, τ ∈ realRegion →
      osiiPositiveRealTimeEmbed τ ∈ E.domain i
  second_real_mem :
    ∀ i τ, τ ∈ realRegion →
      osiiPositiveRealTimeEmbed τ ∈ F.domain i
  mode_eq :
    ∀ i scale mode τ, τ ∈ realRegion →
      E.mode lgc scale i mode (osiiPositiveRealTimeEmbed τ) =
        F.mode lgc scale i mode (osiiPositiveRealTimeEmbed τ)

/-- Intersect the two finite real-edge systems and enter the strict-positive
orthant.  Source equality then gives a scale-uniform scalar mode germ. -/
noncomputable def toCommonPositiveRealModeAgreementData
    (P : SourceAgreementData E F)
    (lgc : OSLinearGrowthCondition d OS) :
    P.CommonPositiveRealModeAgreementData lgc :=
  { P.toCommonPositiveRealModeAgreementDataOfOS with }

namespace CommonPositiveRealModeAgreementDataOfOS

variable {P : SourceAgreementData E F}

end CommonPositiveRealModeAgreementDataOfOS

namespace CommonPositiveRealModeAgreementData

variable
  {P : SourceAgreementData E F}
  {lgc : OSLinearGrowthCondition d OS}

end CommonPositiveRealModeAgreementData

variable {P : SourceAgreementData E F}

/-- A genuine original-OS common positive-real source germ extends to a
connected complex neighborhood for every split and packet scale. -/
structure CommonComplexModeGermDataOfOS
    (G : P.CommonPositiveRealModeAgreementDataOfOS) where
  center : Fin k -> ℝ
  center_mem : center ∈ G.realRegion
  radius : GeneratorIndex k -> ℝ
  radius_pos : ∀ i, 0 < radius i
  ball_subset_first :
    ∀ i,
      Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
        E.domain i
  ball_subset_second :
    ∀ i,
      Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
        F.domain i
  mode_eq :
    ∀ i scale mode z,
      z ∈ Metric.ball
          (osiiPositiveRealTimeEmbed center) (radius i) ->
        E.modeOfOS scale i mode z =
          F.modeOfOS scale i mode z

/-- Totally-real uniqueness propagates exact original-OS source agreement
from its positive-real region to the genuine complex generator germs. -/
noncomputable def
    CommonPositiveRealModeAgreementDataOfOS.toCommonComplexModeGermDataOfOS
    (G : P.CommonPositiveRealModeAgreementDataOfOS) :
    CommonComplexModeGermDataOfOS G := by
  let center : Fin k -> ℝ :=
    Classical.choose G.realRegion_nonempty
  have hcenter : center ∈ G.realRegion :=
    Classical.choose_spec G.realRegion_nonempty
  let commonDomain : GeneratorIndex k ->
      Set (OSIITimeGapSpace k) :=
    fun i => E.domain i ∩ F.domain i
  have hcenter_domain :
      ∀ i, osiiPositiveRealTimeEmbed center ∈ commonDomain i := by
    intro i
    exact
      ⟨G.first_real_mem i center hcenter,
        G.second_real_mem i center hcenter⟩
  have hexists :
      ∀ i, ∃ r > 0,
        Metric.ball (osiiPositiveRealTimeEmbed center) r ⊆
          commonDomain i := by
    intro i
    exact
      Metric.isOpen_iff.mp
        ((E.domain_open i).inter (F.domain_open i))
        (osiiPositiveRealTimeEmbed center)
        (hcenter_domain i)
  let radius : GeneratorIndex k -> ℝ :=
    fun i => Classical.choose (hexists i)
  have hradius :
      ∀ i, 0 < radius i ∧
        Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
          commonDomain i := by
    intro i
    exact Classical.choose_spec (hexists i)
  refine
    { center := center
      center_mem := hcenter
      radius := radius
      radius_pos := fun i => (hradius i).1
      ball_subset_first := fun i z hz => (hradius i).2 hz |>.1
      ball_subset_second := fun i z hz => (hradius i).2 hz |>.2
      mode_eq := ?_ }
  intro i scale mode z hz
  let D : Set (OSIITimeGapSpace k) :=
    Metric.ball (osiiPositiveRealTimeEmbed center) (radius i)
  let H : OSIITimeGapSpace k -> ℂ :=
    fun w => E.modeOfOS scale i mode w -
      F.modeOfOS scale i mode w
  have hD_open : IsOpen D :=
    Metric.isOpen_ball
  have hD_connected : IsConnected D :=
    (convex_ball
      (osiiPositiveRealTimeEmbed center) (radius i)).isConnected
        ⟨osiiPositiveRealTimeEmbed center,
          Metric.mem_ball_self (hradius i).1⟩
  have hH : DifferentiableOn ℂ H D :=
    (E.modeOfOS_holomorphic scale i mode).mono
        (fun w hw => (hradius i).2 hw |>.1) |>.sub
      ((F.modeOfOS_holomorphic scale i mode).mono
        (fun w hw => (hradius i).2 hw |>.2))
  let V : Set (Fin k -> ℝ) :=
    G.realRegion ∩
      SCV.realToComplex ⁻¹' D
  have hrealToComplex :
      Continuous (SCV.realToComplex (m := k)) :=
    continuous_pi fun j =>
      Complex.continuous_ofReal.comp (continuous_apply j)
  have hV_open : IsOpen V :=
    G.realRegion_open.inter
      (hrealToComplex.isOpen_preimage D hD_open)
  have hV_nonempty : V.Nonempty := by
    refine ⟨center, hcenter, ?_⟩
    change SCV.realToComplex center ∈ D
    rw [show SCV.realToComplex center =
        osiiPositiveRealTimeEmbed center by rfl]
    exact Metric.mem_ball_self (hradius i).1
  have hV_sub :
      ∀ x ∈ V, SCV.realToComplex x ∈ D :=
    fun x hx => hx.2
  have hH_zero :
      ∀ x ∈ V, H (SCV.realToComplex x) = 0 := by
    intro x hx
    simp only [H]
    rw [show SCV.realToComplex x =
        osiiPositiveRealTimeEmbed x by rfl,
      G.mode_eq i scale mode x hx.1,
      sub_self]
  exact
    sub_eq_zero.mp
      (SCV.identity_theorem_totally_real
        hD_open hD_connected hH
        hV_open hV_nonempty hV_sub hH_zero z hz)

namespace CommonComplexModeGermDataOfOS

variable {G : P.CommonPositiveRealModeAgreementDataOfOS}

/-- The open original-OS common complex source germ at one split. -/
def domain
    (C : CommonComplexModeGermDataOfOS G)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  Metric.ball (osiiPositiveRealTimeEmbed C.center) (C.radius i)

theorem domain_open
    (C : CommonComplexModeGermDataOfOS G)
    (i : GeneratorIndex k) :
    IsOpen (C.domain i) :=
  Metric.isOpen_ball

theorem domain_convex
    (C : CommonComplexModeGermDataOfOS G)
    (i : GeneratorIndex k) :
    Convex ℝ (C.domain i) :=
  convex_ball _ _

theorem center_mem_domain
    (C : CommonComplexModeGermDataOfOS G)
    (i : GeneratorIndex k) :
    osiiPositiveRealTimeEmbed C.center ∈ C.domain i :=
  Metric.mem_ball_self (C.radius_pos i)

end CommonComplexModeGermDataOfOS

variable
  {P : SourceAgreementData E F}
  {lgc : OSLinearGrowthCondition d OS}

/-- A connected complex neighborhood around one common positive-real point
on which the two open-field families agree mode by mode. -/
structure CommonComplexModeGermData
    (G : P.CommonPositiveRealModeAgreementData lgc) where
  center : Fin k → ℝ
  center_mem : center ∈ G.realRegion
  radius : GeneratorIndex k → ℝ
  radius_pos : ∀ i, 0 < radius i
  ball_subset_first :
    ∀ i,
      Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
        E.domain i
  ball_subset_second :
    ∀ i,
      Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
        F.domain i
  mode_eq :
    ∀ i scale mode z,
      z ∈ Metric.ball
          (osiiPositiveRealTimeEmbed center) (radius i) →
        E.mode lgc scale i mode z =
          F.mode lgc scale i mode z

/-- Every common positive-real mode germ extends to a splitwise connected
complex germ by the totally-real identity theorem. -/
noncomputable def CommonPositiveRealModeAgreementData.toCommonComplexModeGermData
    (G : P.CommonPositiveRealModeAgreementData lgc) :
    CommonComplexModeGermData G := by
  let center : Fin k → ℝ :=
    Classical.choose G.realRegion_nonempty
  have hcenter : center ∈ G.realRegion :=
    Classical.choose_spec G.realRegion_nonempty
  let commonDomain : GeneratorIndex k →
      Set (OSIITimeGapSpace k) :=
    fun i => E.domain i ∩ F.domain i
  have hcenter_domain :
      ∀ i, osiiPositiveRealTimeEmbed center ∈ commonDomain i := by
    intro i
    exact
      ⟨G.first_real_mem i center hcenter,
        G.second_real_mem i center hcenter⟩
  have hexists :
      ∀ i, ∃ r > 0,
        Metric.ball (osiiPositiveRealTimeEmbed center) r ⊆
          commonDomain i := by
    intro i
    exact
      Metric.isOpen_iff.mp
        ((E.domain_open i).inter (F.domain_open i))
        (osiiPositiveRealTimeEmbed center)
        (hcenter_domain i)
  let radius : GeneratorIndex k → ℝ :=
    fun i => Classical.choose (hexists i)
  have hradius :
      ∀ i, 0 < radius i ∧
        Metric.ball (osiiPositiveRealTimeEmbed center) (radius i) ⊆
          commonDomain i := by
    intro i
    exact Classical.choose_spec (hexists i)
  refine
    { center := center
      center_mem := hcenter
      radius := radius
      radius_pos := fun i => (hradius i).1
      ball_subset_first := fun i z hz => (hradius i).2 hz |>.1
      ball_subset_second := fun i z hz => (hradius i).2 hz |>.2
      mode_eq := ?_ }
  intro i scale mode z hz
  let D : Set (OSIITimeGapSpace k) :=
    Metric.ball (osiiPositiveRealTimeEmbed center) (radius i)
  let H : OSIITimeGapSpace k → ℂ :=
    fun w => E.mode lgc scale i mode w -
      F.mode lgc scale i mode w
  have hD_open : IsOpen D :=
    Metric.isOpen_ball
  have hD_connected : IsConnected D :=
    (convex_ball
      (osiiPositiveRealTimeEmbed center) (radius i)).isConnected
        ⟨osiiPositiveRealTimeEmbed center,
          Metric.mem_ball_self (hradius i).1⟩
  have hH : DifferentiableOn ℂ H D :=
    (E.mode_holomorphic lgc scale i mode).mono
        (fun w hw => (hradius i).2 hw |>.1) |>.sub
      ((F.mode_holomorphic lgc scale i mode).mono
        (fun w hw => (hradius i).2 hw |>.2))
  let V : Set (Fin k → ℝ) :=
    G.realRegion ∩
      SCV.realToComplex ⁻¹' D
  have hrealToComplex :
      Continuous (SCV.realToComplex (m := k)) :=
    continuous_pi fun j =>
      Complex.continuous_ofReal.comp (continuous_apply j)
  have hV_open : IsOpen V :=
    G.realRegion_open.inter
      (hrealToComplex.isOpen_preimage D hD_open)
  have hV_nonempty : V.Nonempty := by
    refine ⟨center, hcenter, ?_⟩
    change SCV.realToComplex center ∈ D
    rw [show SCV.realToComplex center =
        osiiPositiveRealTimeEmbed center by rfl]
    exact Metric.mem_ball_self (hradius i).1
  have hV_sub :
      ∀ x ∈ V, SCV.realToComplex x ∈ D :=
    fun x hx => hx.2
  have hH_zero :
      ∀ x ∈ V, H (SCV.realToComplex x) = 0 := by
    intro x hx
    simp only [H]
    rw [show SCV.realToComplex x =
        osiiPositiveRealTimeEmbed x by rfl,
      G.mode_eq i scale mode x hx.1,
      sub_self]
  exact
    sub_eq_zero.mp
      (SCV.identity_theorem_totally_real
        hD_open hD_connected hH
        hV_open hV_nonempty hV_sub hH_zero z hz)

namespace CommonComplexModeGermData

variable
  {G : P.CommonPositiveRealModeAgreementData lgc}

/-- The splitwise common complex germ. -/
def domain
    (C : CommonComplexModeGermData G)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  Metric.ball (osiiPositiveRealTimeEmbed C.center) (C.radius i)

theorem domain_open
    (C : CommonComplexModeGermData G)
    (i : GeneratorIndex k) :
    IsOpen (C.domain i) :=
  Metric.isOpen_ball

theorem domain_convex
    (C : CommonComplexModeGermData G)
    (i : GeneratorIndex k) :
    Convex ℝ (C.domain i) :=
  convex_ball _ _

theorem center_mem_domain
    (C : CommonComplexModeGermData G)
    (i : GeneratorIndex k) :
    osiiPositiveRealTimeEmbed C.center ∈ C.domain i :=
  Metric.mem_ball_self (C.radius_pos i)

end CommonComplexModeGermData

end SourceAgreementData

end GeneratorOpenHilbertFieldScaleFamilyRealEdgeData
end OSIIChapterV
end OSReconstruction
