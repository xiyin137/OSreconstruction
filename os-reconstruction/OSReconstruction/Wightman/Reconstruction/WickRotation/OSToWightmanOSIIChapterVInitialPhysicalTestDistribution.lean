/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Distribution.TestFunction
import OSReconstruction.Mathlib429Compat
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalFixedCarrier





















noncomputable section

open Complex Set TopologicalSpace Topology
open scoped Classical Distributions

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- A compactly supported smooth reduced test, viewed as a reduced Schwartz
source. -/
def initialPhysicalCompactSmoothToSchwartzLinearMap
    (K : Compacts (NPointDomain d k)) :
    ContDiffMapSupportedIn (NPointDomain d k) ℂ ⊤ K →ₗ[ℂ]
      SchwartzNPoint d k where
  toFun := fun φ =>
    φ.compact_supp.toSchwartzMap φ.contDiff
  map_add' := by
    intro φ ψ
    ext x
    rfl
  map_smul' := by
    intro c φ
    ext x
    rfl

omit [NeZero d] [NeZero k] in
/-- On a fixed compact carrier, the smooth-test-to-Schwartz inclusion is
continuous.  Polynomial Schwartz weights are bounded on the compact carrier,
while each derivative is one of the defining fixed-support seminorms. -/
theorem continuous_initialPhysicalCompactSmoothToSchwartzLinearMap
    (K : Compacts (NPointDomain d k)) :
    Continuous
      (initialPhysicalCompactSmoothToSchwartzLinearMap
        (d := d) (k := k) K) := by
  apply
    WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms
        ℂ (NPointDomain d k) ℂ ⊤ K)
      (schwartz_withSeminorms ℂ (NPointDomain d k) ℂ)
      (initialPhysicalCompactSmoothToSchwartzLinearMap
        (d := d) (k := k) K)
  apply Seminorm.IsBounded.of_real
  rintro ⟨p, n⟩
  obtain ⟨R, hKR⟩ :=
    K.isCompact.isBounded.subset_closedBall
      (0 : NPointDomain d k)
  let C : ℝ := (max 1 R) ^ p
  refine ⟨{n}, C, ?_⟩
  intro φ
  change
    SchwartzMap.seminorm ℂ p n
        (initialPhysicalCompactSmoothToSchwartzLinearMap
          (d := d) (k := k) K φ) ≤
      C *
        (({n} : Finset ℕ).sup
          (ContDiffMapSupportedIn.seminorm
            ℂ (NPointDomain d k) ℂ ⊤ K)) φ
  apply SchwartzMap.seminorm_le_bound ℂ p n
  · positivity
  · intro x
    by_cases hx : x ∈ K
    · have hxR : ‖x‖ ≤ R := by
        exact mem_closedBall_zero_iff.mp (hKR hx)
      have hxC : ‖x‖ ≤ max 1 R :=
        hxR.trans (le_max_right 1 R)
      calc
        ‖x‖ ^ p *
            ‖iteratedFDeriv ℝ n
              (initialPhysicalCompactSmoothToSchwartzLinearMap
                (d := d) (k := k) K φ) x‖ =
            ‖x‖ ^ p * ‖iteratedFDeriv ℝ n φ x‖ := rfl
        _ ≤
            (max 1 R) ^ p *
              ContDiffMapSupportedIn.seminorm
                ℂ (NPointDomain d k) ℂ ⊤ K n φ := by
          gcongr
          exact
            ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
              ℂ
        _ =
            C *
              (({n} : Finset ℕ).sup
                (ContDiffMapSupportedIn.seminorm
                  ℂ (NPointDomain d k) ℂ ⊤ K)) φ := by
          simp [C]
    · have hzero :
          iteratedFDeriv ℝ n
              (initialPhysicalCompactSmoothToSchwartzLinearMap
                (d := d) (k := k) K φ) x = 0 := by
        simpa [initialPhysicalCompactSmoothToSchwartzLinearMap] using
          (φ.iteratedFDeriv_zero_on_compl (i := n) hx)
      rw [hzero, norm_zero, mul_zero]
      positivity

/-- The preceding continuous linear map, bundled for later composition. -/
def initialPhysicalCompactSmoothToSchwartzCLM
    (K : Compacts (NPointDomain d k)) :
    ContDiffMapSupportedIn (NPointDomain d k) ℂ ⊤ K →L[ℂ]
      SchwartzNPoint d k where
  toLinearMap :=
    initialPhysicalCompactSmoothToSchwartzLinearMap
      (d := d) (k := k) K
  cont :=
    continuous_initialPhysicalCompactSmoothToSchwartzLinearMap
      (d := d) (k := k) K

omit [NeZero d] [NeZero k] in
@[simp]
theorem initialPhysicalCompactSmoothToSchwartzCLM_apply
    (K : Compacts (NPointDomain d k))
    (φ : ContDiffMapSupportedIn (NPointDomain d k) ℂ ⊤ K) :
    initialPhysicalCompactSmoothToSchwartzCLM
        (d := d) (k := k) K φ =
      φ.compact_supp.toSchwartzMap φ.contDiff :=
  rfl

/-- Smooth compactly supported tests on an open reduced window, continuously
embedded into reduced Schwartz space by the LF universal property. -/
def initialPhysicalTestToSchwartzCLM
    (U : Opens (NPointDomain d k)) :
    TestFunction U ℂ ⊤ →L[ℂ] SchwartzNPoint d k :=
  TestFunction.limitCLM ℂ
    (fun φ => φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    (fun K _hKU =>
      initialPhysicalCompactSmoothToSchwartzCLM
        (d := d) (k := k) K)
    (fun _K _hKU φ => by
      ext x
      rfl)

omit [NeZero d] [NeZero k] in
@[simp]
theorem initialPhysicalTestToSchwartzCLM_apply
    (U : Opens (NPointDomain d k))
    (φ : TestFunction U ℂ ⊤) :
    initialPhysicalTestToSchwartzCLM (d := d) (k := k) U φ =
      φ.hasCompactSupport.toSchwartzMap φ.contDiff :=
  by
    simp [initialPhysicalTestToSchwartzCLM, TestFunction.limitCLM,
      TestFunction.mkCLM]

omit [NeZero d] [NeZero k] in
/-- The LF smooth-test inclusion preserves support in its declared open
window. -/
theorem initialPhysicalTestToSchwartzCLM_tsupport_subset
    (U : Opens (NPointDomain d k))
    (φ : TestFunction U ℂ ⊤) :
    tsupport
        ((initialPhysicalTestToSchwartzCLM
            (d := d) (k := k) U φ :
          SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      U := by
  rw [initialPhysicalTestToSchwartzCLM_apply]
  simpa using φ.tsupport_subset

/-- The full open chamber of strictly positive consecutive Euclidean times. -/
def initialReducedStrictPositiveGapOpen (d k : ℕ) [NeZero d] :
    Opens (NPointDomain d k) :=
  ⟨initialReducedStrictPositiveGapRegion d k,
    isOpen_initialReducedStrictPositiveGapRegion⟩

omit [NeZero k] in
/-- A reduced source supported in the positive chamber lifts to the original
zero-diagonal Schwinger domain, regardless of its basepoint factor. -/
theorem reducedTestLift_vanishes_of_tsupport_initialReducedStrictPositiveGapRegion
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d k)
    (hφ :
      tsupport (φ : NPointDomain d k → ℂ) ⊆
        initialReducedStrictPositiveGapRegion d k) :
    VanishesToInfiniteOrderOnCoincidence
      (BHW.reducedTestLift k d χ φ) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hdiff :
      BHW.reducedDiffMapRealCLM (k + 1) d x ∈
        tsupport (φ : NPointDomain d k → ℂ) :=
    reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      χ φ hx
  have hpositive :
      section43QTimeCLM d k
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        section43TimeStrictPositiveRegion k :=
    hφ hdiff
  have hgap : ∀ i : Fin k, 0 < x i.succ 0 - x i.castSucc 0 := by
    intro i
    have hi := hpositive i
    have hi' :
        0 <
          BHW.reducedDiffMapReal (k + 1) d x
            ⟨i.val, by omega⟩ 0 := by
      simpa [section43QTimeCLM_apply,
        BHW.reducedDiffMapRealCLM] using hi
    change 0 < x i.succ 0 - x i.castSucc 0 at hi'
    exact hi'
  have htime : StrictMono (fun i : Fin (k + 1) => x i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  rcases hcoin with ⟨i, j, hij, hxeq⟩
  exact hij
    (htime.injective
      (congrArg (fun y : SpacetimeDim d => y 0) hxeq))

/-- Direct continuous lifting from the positive-chamber LF test space to the
original zero-diagonal full-point Schwinger source space. -/
def initialPhysicalPositiveSourceLiftCLM
    (χ : BHW.NormalizedBasepointCutoff d) :
    TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤ →L[ℂ]
      ZeroDiagonalSchwartz d (k + 1) :=
  ((BHW.reducedTestLift k d χ.toSchwartz).comp
    (initialPhysicalTestToSchwartzCLM
      (d := d) (k := k)
      (initialReducedStrictPositiveGapOpen d k))).codRestrict
    (zeroDiagonalSubmodule d (k + 1))
    (fun φ =>
      reducedTestLift_vanishes_of_tsupport_initialReducedStrictPositiveGapRegion
        χ.toSchwartz
        (initialPhysicalTestToSchwartzCLM
          (d := d) (k := k)
          (initialReducedStrictPositiveGapOpen d k) φ)
        (initialPhysicalTestToSchwartzCLM_tsupport_subset
          (initialReducedStrictPositiveGapOpen d k) φ))

omit [NeZero k] in
@[simp]
theorem initialPhysicalPositiveSourceLiftCLM_coe
    (χ : BHW.NormalizedBasepointCutoff d)
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤) :
    (initialPhysicalPositiveSourceLiftCLM (k := k) χ φ).1 =
      BHW.reducedTestLift k d χ.toSchwartz
        (initialPhysicalTestToSchwartzCLM
          (d := d) (k := k)
          (initialReducedStrictPositiveGapOpen d k) φ) :=
  rfl

/-- The genuine positive-chamber LF current, constructed directly from E0 on
the original zero-diagonal Schwinger source space. -/
def initialPhysicalPositiveChamberCurrent
    (OS : OsterwalderSchraderAxioms d)
    (χ : BHW.NormalizedBasepointCutoff d) :
    TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤ →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (k + 1)).comp
    (initialPhysicalPositiveSourceLiftCLM (k := k) χ)

omit [NeZero k] in
@[simp]
theorem initialPhysicalPositiveChamberCurrent_apply
    (OS : OsterwalderSchraderAxioms d)
    (χ : BHW.NormalizedBasepointCutoff d)
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤) :
    initialPhysicalPositiveChamberCurrent (k := k) OS χ φ =
      OS.S (k + 1) (initialPhysicalPositiveSourceLiftCLM χ φ) :=
  rfl

omit [NeZero k] in
/-- Any positive-time plateau covering a chamber test computes the same
direct LF current through the canonical reduced Schwinger distribution. -/
theorem initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff
    (OS : OsterwalderSchraderAxioms d)
    (χ : BHW.NormalizedBasepointCutoff d)
    {compactCarrier : Set (Fin k → ℝ)}
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤)
    (hcarrier :
      ∀ ξ ∈ tsupport
          ((initialPhysicalTestToSchwartzCLM
              (d := d) (k := k)
              (initialReducedStrictPositiveGapOpen d k) φ :
            SchwartzNPoint d k) :
            NPointDomain d k → ℂ),
        section43QTimeCLM d k ξ ∈ compactCarrier) :
    initialPhysicalPositiveChamberCurrent (k := k) OS χ φ =
      canonicalReducedTimeCutoffSchwingerCLM
        OS C.cutoff C.cutoff_support
        (initialPhysicalTestToSchwartzCLM
          (d := d) (k := k)
          (initialReducedStrictPositiveGapOpen d k) φ) := by
  let F : ZeroDiagonalSchwartz d (k + 1) :=
    initialPhysicalPositiveSourceLiftCLM χ φ
  have hfullcarrier :
      ∀ x ∈ tsupport
          ((F.1 : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ),
        reducedTimeProjectionCLM d k x ∈ compactCarrier := by
    intro x hx
    have hdiff :
        BHW.reducedDiffMapRealCLM (k + 1) d x ∈
          tsupport
            ((initialPhysicalTestToSchwartzCLM
                (d := d) (k := k)
                (initialReducedStrictPositiveGapOpen d k) φ :
              SchwartzNPoint d k) :
              NPointDomain d k → ℂ) := by
      apply
        reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
          χ.toSchwartz
          (initialPhysicalTestToSchwartzCLM
            (d := d) (k := k)
            (initialReducedStrictPositiveGapOpen d k) φ)
      exact hx
    change
      section43QTimeCLM d k
          (BHW.reducedDiffMapRealCLM (k + 1) d x) ∈
        compactCarrier
    exact hcarrier _ hdiff
  have hfactor :=
    C.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport
      (OS := OS) F.1 F.property hfullcarrier
  change OS.S (k + 1) F = _
  calc
    OS.S (k + 1) F =
        canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support
          (diffVarReduction d k F.1) := hfactor.symm
    _ =
        canonicalReducedTimeCutoffSchwingerCLM
          OS C.cutoff C.cutoff_support
          (initialPhysicalTestToSchwartzCLM
            (d := d) (k := k)
            (initialReducedStrictPositiveGapOpen d k) φ) := by
      congr 1
      exact diffVarReduction_reducedTestLift χ _

/-- The time projection of the compact support of a positive-chamber LF
test. -/
def initialPhysicalPositiveTestTimeCarrier
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤) :
    Set (Fin k → ℝ) :=
  section43QTimeCLM d k ''
    tsupport
      ((initialPhysicalTestToSchwartzCLM
          (d := d) (k := k)
          (initialReducedStrictPositiveGapOpen d k) φ :
        SchwartzNPoint d k) :
        NPointDomain d k → ℂ)

omit [NeZero k] in
theorem initialPhysicalPositiveTestTimeCarrier_compact
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤) :
    IsCompact (initialPhysicalPositiveTestTimeCarrier φ) := by
  have hcompact :
      HasCompactSupport
        ((initialPhysicalTestToSchwartzCLM
            (d := d) (k := k)
            (initialReducedStrictPositiveGapOpen d k) φ :
          SchwartzNPoint d k) :
          NPointDomain d k → ℂ) := by
    rw [initialPhysicalTestToSchwartzCLM_apply]
    exact φ.hasCompactSupport
  exact hcompact.isCompact.image (section43QTimeCLM d k).continuous

omit [NeZero k] in
theorem initialPhysicalPositiveTestTimeCarrier_subset_strictPositive
    (φ : TestFunction (initialReducedStrictPositiveGapOpen d k) ℂ ⊤) :
    initialPhysicalPositiveTestTimeCarrier φ ⊆
      section43TimeStrictPositiveRegion k := by
  rintro τ ⟨ξ, hξ, rfl⟩
  exact
    initialPhysicalTestToSchwartzCLM_tsupport_subset
      (initialReducedStrictPositiveGapOpen d k) φ hξ

/-- The direct LF current does not depend on the normalized common-basepoint
Schwartz cutoff used to construct its zero-diagonal lift. -/
theorem initialPhysicalPositiveChamberCurrent_basepoint_independent
    (OS : OsterwalderSchraderAxioms d)
    (χ₁ χ₂ : BHW.NormalizedBasepointCutoff d) :
    initialPhysicalPositiveChamberCurrent (k := k) OS χ₁ =
      initialPhysicalPositiveChamberCurrent (k := k) OS χ₂ := by
  ext φ
  obtain ⟨C⟩ := CanonicalReducedCompactCutoffData.nonempty
    (initialPhysicalPositiveTestTimeCarrier φ)
    (initialPhysicalPositiveTestTimeCarrier_compact φ)
    (initialPhysicalPositiveTestTimeCarrier_subset_strictPositive φ)
  have hcarrier :
      ∀ ξ ∈ tsupport
          ((initialPhysicalTestToSchwartzCLM
              (d := d) (k := k)
              (initialReducedStrictPositiveGapOpen d k) φ :
            SchwartzNPoint d k) :
            NPointDomain d k → ℂ),
        section43QTimeCLM d k ξ ∈
          initialPhysicalPositiveTestTimeCarrier φ :=
    fun ξ hξ => ⟨ξ, hξ, rfl⟩
  rw [initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff
    OS χ₁ C φ hcarrier,
    initialPhysicalPositiveChamberCurrent_eq_canonical_of_cutoff
      OS χ₂ C φ hcarrier]

/-- Tests supported in an open window contained in a fixed carrier embed
continuously into that carrier's Schwartz source submodule. -/
def initialPhysicalTestToFixedCarrierCLM
    (U : Opens (NPointDomain d k))
    (K : Set (NPointDomain d k))
    (hUK : (U : Set (NPointDomain d k)) ⊆ K) :
    TestFunction U ℂ ⊤ →L[ℂ]
      initialPhysicalFixedCarrierSourceSubmodule (d := d) K :=
  (initialPhysicalTestToSchwartzCLM
    (d := d) (k := k) U).codRestrict
      (initialPhysicalFixedCarrierSourceSubmodule (d := d) K)
      (fun φ =>
        (initialPhysicalTestToSchwartzCLM_tsupport_subset
          (d := d) (k := k) U φ).trans hUK)

omit [NeZero d] [NeZero k] in
@[simp]
theorem initialPhysicalTestToFixedCarrierCLM_coe
    (U : Opens (NPointDomain d k))
    (K : Set (NPointDomain d k))
    (hUK : (U : Set (NPointDomain d k)) ⊆ K)
    (φ : TestFunction U ℂ ⊤) :
    (initialPhysicalTestToFixedCarrierCLM
        (d := d) (k := k) U K hUK φ).1 =
      initialPhysicalTestToSchwartzCLM
        (d := d) (k := k) U φ :=
  rfl

/-- LF-continuous source transport from tests on one open real window into
a fixed carrier containing the inverse-translated window.  This is the
test-function-level form of the physical-chart source transition. -/
def initialPhysicalTransportedTestToFixedCarrierCLM
    (U : Opens (NPointDomain d k))
    (K : Set (NPointDomain d k))
    (a : NPointDomain d k)
    (hUaK :
      (Homeomorph.addRight a) ⁻¹'
          (U : Set (NPointDomain d k)) ⊆ K) :
    TestFunction U ℂ ⊤ →L[ℂ]
      initialPhysicalFixedCarrierSourceSubmodule (d := d) K :=
  ((translateSchwartzConfigurationCLM a).comp
      (initialPhysicalTestToSchwartzCLM
        (d := d) (k := k) U)).codRestrict
    (initialPhysicalFixedCarrierSourceSubmodule (d := d) K)
    (fun φ => by
      rw [ContinuousLinearMap.comp_apply,
        translateSchwartzConfigurationCLM_apply]
      change
        tsupport
            ((translateSchwartzConfiguration a
                (initialPhysicalTestToSchwartzCLM
                  (d := d) (k := k) U φ) :
              SchwartzNPoint d k) :
              NPointDomain d k → ℂ) ⊆ K
      rw [tsupport_translateSchwartzConfiguration_eq_preimage]
      exact
        (Set.preimage_mono
          (initialPhysicalTestToSchwartzCLM_tsupport_subset
            (d := d) (k := k) U φ)).trans hUaK)

omit [NeZero d] [NeZero k] in
@[simp]
theorem initialPhysicalTransportedTestToFixedCarrierCLM_coe
    (U : Opens (NPointDomain d k))
    (K : Set (NPointDomain d k))
    (a : NPointDomain d k)
    (hUaK :
      (Homeomorph.addRight a) ⁻¹'
          (U : Set (NPointDomain d k)) ⊆ K)
    (φ : TestFunction U ℂ ⊤) :
    (initialPhysicalTransportedTestToFixedCarrierCLM
        (d := d) (k := k) U K a hUaK φ).1 =
      translateSchwartzConfiguration a
        (initialPhysicalTestToSchwartzCLM
          (d := d) (k := k) U φ) :=
  rfl

namespace InitialPhysicalFixedCarrierChartData

variable
  {K : Set (NPointDomain d k)}
  {base : OSIIAxisPairMultiGapPhysicalBlockPatch d k}

/-- One fixed-carrier physical chart, now valued in continuous functionals on
smooth compactly supported tests from an open real window inside the carrier.
-/
def testDistribution
    (A : InitialPhysicalFixedCarrierChartData (d := d) K base)
    (U : Opens (NPointDomain d k))
    (hUK : (U : Set (NPointDomain d k)) ⊆ K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (k * (d + 1)) → ℂ) :
    TestFunction U ℂ ⊤ →L[ℂ] ℂ :=
  (A.distribution OS lgc z).comp
    (initialPhysicalTestToFixedCarrierCLM
      (d := d) (k := k) U K hUK)

@[simp]
theorem testDistribution_apply
    (A : InitialPhysicalFixedCarrierChartData (d := d) K base)
    (U : Opens (NPointDomain d k))
    (hUK : (U : Set (NPointDomain d k)) ⊆ K)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (k * (d + 1)) → ℂ)
    (φ : TestFunction U ℂ ⊤) :
    A.testDistribution U hUK OS lgc z φ =
      A.distribution OS lgc z
        (initialPhysicalTestToFixedCarrierCLM
          (d := d) (k := k) U K hUK φ) :=
  rfl

end InitialPhysicalFixedCarrierChartData

end OSIIChapterV
end OSReconstruction
