/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicArgumentDomains










noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

theorem JoinedIn.target_mem_connectedComponentIn
    {X : Type*}
    [TopologicalSpace X]
    {D : Set X}
    {x y : X}
    (h : JoinedIn D x y) :
    y ∈ connectedComponentIn D x := by
  have hrange :
      Set.range h.somePath ⊆ connectedComponentIn D x := by
    apply
      (isPreconnected_range h.somePath.continuous
        ).subset_connectedComponentIn
    · exact ⟨0, h.somePath.source⟩
    · rintro z ⟨t, rfl⟩
      exact h.somePath_mem t
  apply hrange
  exact ⟨1, h.somePath.target⟩

namespace GeneratorIndex

/-- The split-native point with only the semigroup bridge coordinate
nonzero. -/
def nativeBridgePoint
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    OSIITimeGapSpace r :=
  Pi.single i.bridgeGlobalIndex bridge

@[simp]
theorem nativeBridgePoint_apply_bridge
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    i.nativeBridgePoint bridge i.bridgeGlobalIndex = bridge := by
  simp [nativeBridgePoint]

@[simp]
theorem nativeBridgePoint_apply_toGap
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    i.nativeBridgePoint bridge i.toGap = bridge := by
  simpa using i.nativeBridgePoint_apply_bridge bridge

@[simp]
theorem splitCoordinatesCLM_nativeBridgePoint_fst
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    (i.splitCoordinatesCLM (i.nativeBridgePoint bridge)).1 = bridge := by
  simp [nativeBridgePoint, GeneratorIndex.splitCoordinatesCLM_fst,
    Pi.single_apply]

@[simp]
theorem splitCoordinatesCLM_nativeBridgePoint_left
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    (i.splitCoordinatesCLM (i.nativeBridgePoint bridge)).2.1 = 0 := by
  funext a
  have hne :
      i.leftGlobalIndex a ≠ i.toGap := by
    intro h
    have hval := congrArg Fin.val h
    exact (i.leftGlobalIndex_lt_bridgeGlobalIndex a).ne hval
  simp [nativeBridgePoint, GeneratorIndex.splitCoordinatesCLM_left,
    hne]

@[simp]
theorem splitCoordinatesCLM_nativeBridgePoint_right
    {r : ℕ}
    (i : GeneratorIndex r)
    (bridge : ℂ) :
    (i.splitCoordinatesCLM (i.nativeBridgePoint bridge)).2.2 = 0 := by
  funext b
  have hne :
      i.rightGlobalIndex b ≠ i.toGap := by
    intro h
    have hval := congrArg Fin.val h
    simp [GeneratorIndex.rightGlobalIndex] at hval
    omega
  simp [nativeBridgePoint, GeneratorIndex.splitCoordinatesCLM_right,
    hne]

theorem continuous_nativeBridgePoint
    {r : ℕ}
    (i : GeneratorIndex r) :
    Continuous i.nativeBridgePoint := by
  simpa [nativeBridgePoint] using
    (ContinuousLinearMap.single
      ℂ (fun _ : Fin r => ℂ) i.bridgeGlobalIndex).continuous

end GeneratorIndex

namespace GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

theorem left_zero_mem_domain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    (0 : Fin (i.n - 1) → ℂ) ∈ E.leftDomain i := by
  simpa [SCV.realToComplex] using
    E.leftRealToComplex_mem_domain i 0
      (mem_of_mem_nhds (E.leftRealRegion_mem_nhds i))

theorem right_zero_mem_domain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :
    (0 : Fin (i.m - 1) → ℂ) ∈ E.rightDomain i := by
  simpa [SCV.realToComplex] using
    E.rightRealToComplex_mem_domain i 0
      (mem_of_mem_nhds (E.rightRealRegion_mem_nhds i))

theorem nativeBridgePoint_mem_domain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (bridge : ℂ)
    (hbridge : 0 < bridge.re) :
    i.nativeBridgePoint bridge ∈ E.domain i := by
  change
    0 <
        ((i.splitCoordinatesCLM
          (i.nativeBridgePoint bridge)).1).re ∧
      (i.splitCoordinatesCLM
          (i.nativeBridgePoint bridge)).2.1 ∈
        conjugateFieldDomain (E.leftDomain i) ∧
      (i.splitCoordinatesCLM
          (i.nativeBridgePoint bridge)).2.2 ∈
        E.rightDomain i
  refine ⟨?_, ?_, ?_⟩
  · rw [GeneratorIndex.splitCoordinatesCLM_nativeBridgePoint_fst]
    exact hbridge
  · simpa [conjugateFieldDomain] using E.left_zero_mem_domain i
  · simpa using E.right_zero_mem_domain i

/-- Bridge-only points in the right half-plane are joined inside every
source-realized open generator domain. -/
theorem nativeBridgePoints_joinedIn_domain
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (bridge₀ bridge₁ : ℂ)
    (hbridge₀ : 0 < bridge₀.re)
    (hbridge₁ : 0 < bridge₁.re) :
    JoinedIn (E.domain i)
      (i.nativeBridgePoint bridge₀)
      (i.nativeBridgePoint bridge₁) := by
  let f : ℝ → OSIITimeGapSpace k :=
    fun t =>
      i.nativeBridgePoint
        (((1 - t : ℝ) : ℂ) * bridge₀ + (t : ℂ) * bridge₁)
  apply JoinedIn.ofLine (f := f)
  · exact
      (i.continuous_nativeBridgePoint.comp
        (((Complex.continuous_ofReal.comp
            (continuous_const.sub continuous_id)).mul continuous_const).add
          ((Complex.continuous_ofReal.comp continuous_id).mul
            continuous_const))).continuousOn
  · simp [f, GeneratorIndex.nativeBridgePoint]
  · simp [f, GeneratorIndex.nativeBridgePoint]
  · rintro _ ⟨t, ht, rfl⟩
    apply E.nativeBridgePoint_mem_domain
    have h :
        0 < (1 - t) * bridge₀.re + t * bridge₁.re := by
      by_cases ht1 : t = 1
      · subst t
        simpa using hbridge₁
      · have hlt1 : t < 1 := lt_of_le_of_ne ht.2 ht1
        have hfirst :
            0 < (1 - t) * bridge₀.re :=
          mul_pos (sub_pos.mpr hlt1) hbridge₀
        have hsecond :
            0 ≤ t * bridge₁.re :=
          mul_nonneg ht.1 hbridge₁.le
        linarith
    simpa [Complex.mul_re] using h

/-- A positive-real point is joined to its bridge-only projection whenever
both block parameters contract radially inside their field domains. -/
theorem nativeBridgePoint_joinedIn_positiveReal
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hleft :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • SCV.realToComplex (i.leftRealCoordinates τ) ∈
          E.leftDomain i)
    (hright :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • SCV.realToComplex (i.rightRealCoordinates τ) ∈
          E.rightDomain i) :
    JoinedIn (E.domain i)
      (i.nativeBridgePoint (τ i.bridgeGlobalIndex))
      (osiiPositiveRealTimeEmbed τ) := by
  let f : ℝ → OSIITimeGapSpace k :=
    fun t =>
      (1 - t) •
          i.nativeBridgePoint (τ i.bridgeGlobalIndex) +
        t • osiiPositiveRealTimeEmbed τ
  apply JoinedIn.ofLine (f := f)
  · fun_prop
  · simp [f]
  · simp [f]
  · rintro _ ⟨t, ht, rfl⟩
    change
      0 < ((i.splitCoordinatesCLM (f t)).1).re ∧
        (i.splitCoordinatesCLM (f t)).2.1 ∈
          conjugateFieldDomain (E.leftDomain i) ∧
        (i.splitCoordinatesCLM (f t)).2.2 ∈
          E.rightDomain i
    refine ⟨?_, ?_, ?_⟩
    · have hfst :
          (i.splitCoordinatesCLM (f t)).1 =
            (τ i.bridgeGlobalIndex : ℂ) := by
        simp [f, osiiPositiveRealTimeEmbed]
        ring
      rw [hfst]
      simpa using hbridge
    · change star (i.splitCoordinatesCLM (f t)).2.1 ∈
        E.leftDomain i
      have heq :
          star (i.splitCoordinatesCLM (f t)).2.1 =
            t • SCV.realToComplex (i.leftRealCoordinates τ) := by
        funext a
        simp [f, SCV.realToComplex, osiiPositiveRealTimeEmbed,
          GeneratorIndex.leftRealCoordinates]
      rw [heq]
      exact hleft t ht
    · have heq :
          (i.splitCoordinatesCLM (f t)).2.2 =
            t • SCV.realToComplex (i.rightRealCoordinates τ) := by
        funext b
        simp [f, SCV.realToComplex, osiiPositiveRealTimeEmbed,
          GeneratorIndex.rightRealCoordinates]
      rw [heq]
      exact hright t ht

/-- A split-native point is joined to its bridge-only projection whenever
its two block coordinates contract radially inside their field domains. -/
theorem nativeBridgePoint_joinedIn_of_radial
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hbridge : 0 < (z i.bridgeGlobalIndex).re)
    (hleft :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        star (t • (i.splitCoordinatesCLM z).2.1) ∈
          E.leftDomain i)
    (hright :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • (i.splitCoordinatesCLM z).2.2 ∈
          E.rightDomain i) :
    JoinedIn (E.domain i)
      (i.nativeBridgePoint (z i.bridgeGlobalIndex))
      z := by
  let f : ℝ → OSIITimeGapSpace k :=
    fun t =>
      (1 - t) •
          i.nativeBridgePoint (z i.bridgeGlobalIndex) +
        t • z
  apply JoinedIn.ofLine (f := f)
  · fun_prop
  · simp [f]
  · simp [f]
  · rintro _ ⟨t, ht, rfl⟩
    change
      0 < ((i.splitCoordinatesCLM (f t)).1).re ∧
        (i.splitCoordinatesCLM (f t)).2.1 ∈
          conjugateFieldDomain (E.leftDomain i) ∧
        (i.splitCoordinatesCLM (f t)).2.2 ∈
          E.rightDomain i
    refine ⟨?_, ?_, ?_⟩
    · have hfst :
          (i.splitCoordinatesCLM (f t)).1 =
            z i.bridgeGlobalIndex := by
        simp [f]
        ring
      rw [hfst]
      exact hbridge
    · change star (i.splitCoordinatesCLM (f t)).2.1 ∈
        E.leftDomain i
      have heq :
          star (i.splitCoordinatesCLM (f t)).2.1 =
            star (t • (i.splitCoordinatesCLM z).2.1) := by
        funext a
        simp [f]
      rw [heq]
      exact hleft t ht
    · have heq :
          (i.splitCoordinatesCLM (f t)).2.2 =
            t • (i.splitCoordinatesCLM z).2.2 := by
        funext b
        simp [f]
      rw [heq]
      exact hright t ht

namespace SourceAgreementData

variable
  {E F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}

/-- The genuine original-OS common real source germ retains the first
family's left real-edge membership. -/
theorem first_leftReal_mem_of_mem_commonPositiveRealOfOS
    (P : SourceAgreementData E F)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ P.toCommonPositiveRealModeAgreementDataOfOS.realRegion) :
    i.leftRealCoordinates τ ∈ E.leftRealRegion i := by
  unfold toCommonPositiveRealModeAgreementDataOfOS at hτ
  exact
    (((Classical.choose_spec
      (mem_nhds_iff.mp P.commonRealAutomaticSet_mem_nhds)).1 hτ.1).1 i).1

/-- The genuine original-OS common real source germ retains the first
family's right real-edge membership. -/
theorem first_rightReal_mem_of_mem_commonPositiveRealOfOS
    (P : SourceAgreementData E F)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ P.toCommonPositiveRealModeAgreementDataOfOS.realRegion) :
    i.rightRealCoordinates τ ∈ E.rightRealRegion i := by
  unfold toCommonPositiveRealModeAgreementDataOfOS at hτ
  exact
    (((Classical.choose_spec
      (mem_nhds_iff.mp P.commonRealAutomaticSet_mem_nhds)).1 hτ.1).1 i).2

/-- The actual original-OS common source germ lies in the strict positive
orthant without a quantitative arity-growth assumption. -/
theorem strictPositive_of_mem_commonPositiveRealOfOS
    (P : SourceAgreementData E F)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ P.toCommonPositiveRealModeAgreementDataOfOS.realRegion) :
    τ ∈ section43TimeStrictPositiveRegion k := by
  unfold toCommonPositiveRealModeAgreementDataOfOS at hτ
  exact hτ.2

/-- The concrete common-germ constructor retains the first family's left
real-edge membership. -/
theorem first_leftReal_mem_of_mem_commonPositiveReal
    (P : SourceAgreementData E F)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ (P.toCommonPositiveRealModeAgreementData lgc).realRegion) :
    i.leftRealCoordinates τ ∈ E.leftRealRegion i :=
  P.first_leftReal_mem_of_mem_commonPositiveRealOfOS i τ hτ

/-- The concrete common-germ constructor retains the first family's right
real-edge membership. -/
theorem first_rightReal_mem_of_mem_commonPositiveReal
    (P : SourceAgreementData E F)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ (P.toCommonPositiveRealModeAgreementData lgc).realRegion) :
    i.rightRealCoordinates τ ∈ E.rightRealRegion i :=
  P.first_rightReal_mem_of_mem_commonPositiveRealOfOS i τ hτ

/-- The common real germ selected by the constructor lies in the strict
positive orthant. -/
theorem strictPositive_of_mem_commonPositiveReal
    (P : SourceAgreementData E F)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ (P.toCommonPositiveRealModeAgreementData lgc).realRegion) :
    τ ∈ section43TimeStrictPositiveRegion k :=
  P.strictPositive_of_mem_commonPositiveRealOfOS τ hτ

end SourceAgreementData
end GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

end OSIIChapterV
end OSReconstruction
