import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIRegularizedSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional

/-!
# OS-II Step 4 Regularized BVT Source Currents

This downstream companion instantiates the abstract regularized source-current
split with the concrete descended BVT time-shell CLM.  It sits after both the
source-current regularizer package and the Section 4.3 product-functional
package, avoiding an import cycle in the core source-current module.
-/

open Complex Topology MeasureTheory
open Set
open scoped Classical NNReal BigOperators

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Step-4 regularized source-current split evaluated by the descended BVT
time-shell CLM.

Monograph Vol IV Ch 2 Step 4 (lines 1078-1099): once the local time cutoff and
A0 cutoff are normalized on the positive product window, compact product-source
equality supplies the hypothesis of the translated `g_rho` density bridge, so
the whole `k_rho` regularized scalar is transported to the BVT time-shell
pairing. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_bvtTimeCLM_integral
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χA0 : SchwartzNPoint d (n + m))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (κ : Section43SpatialCompactSource d m)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf κ.1 η hη))
        S_real U)
    (hUK : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    {Window : Set (Fin m → ℝ)}
    (χs : Fin m → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin m, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin m, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_Window :
      ∀ τ : Fin m → ℝ,
        (∀ i : Fin m, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ Window)
    (hχ_one :
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
        ∀ y ∈ tsupport
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
              (Fin m → ℝ) → ℂ),
          section43TimeProductTensor χs y = 1)
    (hBVT_A0 :
      bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n m u κ.1 =
        osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ)
    (hη_one_Window : ∀ τ ∈ Window, η τ = 1)
    (hχA0_one_product :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ Window →
        ∀ x ∈ tsupport
            ((f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
                (section43TimeProductSource gs).f)) :
                NPointDomain d (n + m) → ℂ),
          χA0 x = 1) :
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ) =
      ∫ x : Fin m → ℝ,
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n m u κ.1
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n m u κ.1
  refine
    section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_timeCLM_integral
      (d := d) OS f hf κ.1 η hη hrho hRep hUK
      T χs hχ_pos hχ_compact hχ_Window hχ_one ?_
  intro gs hgsWindow
  have hη_one_source :
      ∀ τ ∈ tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ), η τ = 1 := by
    intro τ hτ
    exact hη_one_Window τ (hgsWindow hτ)
  have hcut :=
    osiiA0LocalCutoffTimeShellCLM_eq_fixedLeftOrderedPullbackCutoffZeroCLM_of_cutoffs_on_source
      (d := d) OS χA0 hχA0_disj f hf κ η hη
      (section43TimeProductSource gs) hη_one_source
      (hχA0_one_product gs hgsWindow)
  calc
    T (section43TimeProductSource gs).f =
      osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ
        (section43TimeProductSource gs).f := by
        simpa [T] using
          congrArg
            (fun L : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ =>
              L (section43TimeProductSource gs).f)
            hBVT_A0
    _ =
      OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf κ.1 η hη (section43TimeProductSource gs).f) := hcut

/-- BVT regularized source-current split with the full BVT/A0 CLM equality
discharged from the OS-II V.2 compact one-sided Laplace product equality. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_bvtTimeCLM_integral_of_products
    {n m : ℕ} [Nonempty (Fin m)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χA0 : SchwartzNPoint d (n + m))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (hχA0_time :
      tsupport (χA0 : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimeStrictPositiveRegion m })
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (κ : Section43SpatialCompactSource d m)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf κ.1 η hη))
        S_real U)
    (hUK : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    {Window : Set (Fin m → ℝ)}
    (χs : Fin m → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin m, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin m, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_Window :
      ∀ τ : Fin m → ℝ,
        (∀ i : Fin m, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ Window)
    (hχ_one :
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
        ∀ y ∈ tsupport
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
              (Fin m → ℝ) → ℂ),
          section43TimeProductTensor χs y = 1)
    (hBVT_A0_products :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n m u κ.1
            (section43TimeProductTensor
              (fun i : Fin m =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          osiiA0LocalCutoffTimeShellCLM
            (d := d) OS χA0 hχA0_disj f κ
            (section43TimeProductTensor
              (fun i : Fin m =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
    (hη_one_Window : ∀ τ ∈ Window, η τ = 1)
    (hχA0_one_product :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ Window →
        ∀ x ∈ tsupport
            ((f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
                (section43TimeProductSource gs).f)) :
                NPointDomain d (n + m) → ℂ),
          χA0 x = 1) :
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ) =
      ∫ x : Fin m → ℝ,
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n m u κ.1
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
  have hBVT_A0 :
      bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n m u κ.1 =
        osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ :=
    bvt_W_pairing_descended_timeSpatialRightCLM_eq_osiiA0LocalCutoffTimeShellCLM
      (d := d) OS lgc u κ χA0 hχA0_disj hχA0_time f hBVT_A0_products
  exact
    section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_bvtTimeCLM_integral
      (d := d) OS lgc u χA0 hχA0_disj f hf κ η hη hrho
      hRep hUK χs hχ_pos hχ_compact hχ_Window hχ_one
      hBVT_A0 hη_one_Window hχA0_one_product

/-- Monograph Vol IV Ch 2 Step 4 (lines 1099-1135): once the regularized
source current has been transported to the BVT time-shell pairing, a
supportwise OS scalar-product bound on the `g_rho` support bounds the whole
regularized `k_rho` scalar.

This is the production handoff to the remaining OS-specific estimate:
`hbound` is exactly the Cauchy-Schwarz / positive-energy semigroup bound for
the BVT time-shell pairing evaluated on translated `g_rho` tests. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_bvtTimeCLM_norm_le_of_products
    {n m : ℕ} [Nonempty (Fin m)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χA0 : SchwartzNPoint d (n + m))
    (hχA0_disj :
      Disjoint (tsupport (χA0 : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (hχA0_time :
      tsupport (χA0 : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimeStrictPositiveRegion m })
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (κ : Section43SpatialCompactSource d m)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf κ.1 η hη))
        S_real U)
    (hUK : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    {Window : Set (Fin m → ℝ)}
    (χs : Fin m → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin m, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin m, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_Window :
      ∀ τ : Fin m → ℝ,
        (∀ i : Fin m, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ Window)
    (hχ_one :
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
        ∀ y ∈ tsupport
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
              (Fin m → ℝ) → ℂ),
          section43TimeProductTensor χs y = 1)
    (hBVT_A0_products :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n m u κ.1
            (section43TimeProductTensor
              (fun i : Fin m =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          osiiA0LocalCutoffTimeShellCLM
            (d := d) OS χA0 hχA0_disj f κ
            (section43TimeProductTensor
              (fun i : Fin m =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
    (hη_one_Window : ∀ τ ∈ Window, η τ = 1)
    (hχA0_one_product :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ Window →
        ∀ x ∈ tsupport
            ((f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
                (section43TimeProductSource gs).f)) :
                NPointDomain d (n + m) → ℂ),
          χA0 x = 1)
    {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ x ∈ Function.support
          (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
        ‖bvt_W_pairing_descended_timeSpatialRightCLM
            (d := d) OS lgc n m u κ.1
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x)‖ ≤ B) :
    ‖∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ‖ ≤ B := by
  have hsplit :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_bvtTimeCLM_integral_of_products
      (d := d) OS lgc u χA0 hχA0_disj hχA0_time f hf κ η hη hrho
      hRep hUK χs hχ_pos hχ_compact hχ_Window hχ_one
      hBVT_A0_products hη_one_Window hχA0_one_product
  rw [hsplit]
  exact
    osiiStep4_GSchwartz_weighted_integral_norm_le_of_support_bound
      m hrho
      (fun x : Fin m → ℝ =>
        bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n m u κ.1
          (osiiStep4RegularizerGReflectedTranslate m rho hrho x))
      (integrable_osiiStep4RegularizerGSchwartz_weighted_CLM
        m hrho
        (bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n m u κ.1))
      hB_nonneg hbound

end OSReconstruction
