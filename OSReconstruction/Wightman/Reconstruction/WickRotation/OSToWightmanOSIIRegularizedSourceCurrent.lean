/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIRegularizedPairing
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# OS II Step 4 Regularized Source Currents

This file instantiates the Step-4 regularized pairing bridge with the actual
OS source-current CLMs.  It is the pre-quotient source-current identity needed
before the regularized vectors are passed to the OS Hilbert scalar-product
bound.
-/

open Complex Topology MeasureTheory
open Set
open scoped Classical NNReal BigOperators

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Cutoff normalization between the local A0 time-shell CLM and the fixed-left
cutoff source current.

Monograph Vol IV Ch 2 Step 4 (lines 1078-1091): the regularized
scalar-product representation is an identity of test functions before
quotienting.  This lemma records the precise local normalization needed in
Lean: on a compact positive time source, if the time cutoff is one on the time
support and the A0 cutoff is one on the resulting full spacetime support, then
the local A0 time-shell CLM and the fixed-left cutoff source current give the
same Schwinger value. -/
theorem osiiA0LocalCutoffTimeShellCLM_eq_fixedLeftOrderedPullbackCutoffZeroCLM_of_cutoffs_on_source
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
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
    (g : Section43CompactStrictPositiveTimeSource m)
    (hη_one :
      ∀ τ ∈ tsupport (g.f : (Fin m → ℝ) → ℂ), η τ = 1)
    (hχA0_one :
      ∀ x ∈ tsupport
          ((f.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 g.f)) :
              NPointDomain d (n + m) → ℂ),
        χA0 x = 1) :
    osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ g.f =
      OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf κ.1 η hη g.f) := by
  let right : SchwartzNPoint d m :=
    section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 g.f
  let F : SchwartzNPoint d (n + m) := f.osConjTensorProduct right
  have hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m := by
    simpa [right] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d m κ.1 g.f g.positive
  have hvanish : VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F] using
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) f right hf hright
  have hηg :
      SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ) g.f = g.f :=
    section43StrictPositiveCutoff_smulLeftCLM_eq_of_eq_one_on_tsupport
      η g hη_one
  have hfixed :
      section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf κ.1 η hη g.f =
        (⟨F, hvanish⟩ : ZeroDiagonalSchwartz d (n + m)) := by
    apply Subtype.ext
    calc
      (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf κ.1 η hη g.f).1 =
        f.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
            (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ) g.f)) := rfl
      _ =
        f.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 g.f) := by
          rw [hηg]
      _ = F := by
          simp [F, right]
  have hA0 :
      osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ g.f =
        OS.S (n + m) (⟨F, hvanish⟩ : ZeroDiagonalSchwartz d (n + m)) := by
    simpa [osiiA0LocalCutoffTimeShellCLM, F, right] using
      osiiA0LocalCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        (d := d) OS χA0 hχA0_disj F hvanish hχA0_one
  calc
    osiiA0LocalCutoffTimeShellCLM OS χA0 hχA0_disj f κ g.f
        = OS.S (n + m)
            (⟨F, hvanish⟩ : ZeroDiagonalSchwartz d (n + m)) := hA0
    _ = OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf κ.1 η hη g.f) := by
        rw [hfixed]

/-- Fixed-left source-current form of the Step-4 regularized kernel split.

The left side is the selected source current tested against `k_rho`; the right
side is the same source-current CLM tested against translated `g_rho` kernels
and integrated against the second `g_rho` factor. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_integral
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho) :
    OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (osiiStep4RegularizerKSchwartz m rho hrho)) =
      ∫ x : Fin m → ℝ,
        OS.S (n + m)
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
  let Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + m) :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM
      (d := d) f hf χ η hη
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp Z
  have hpair := osiiStep4_regularizedDistribution_pairing_GG_eq_K_flat
    m hrho T
  simpa [T, Z] using hpair.symm

/-- Local `(A0)` representative evaluated on the Step-4 regularized source
current.

This is the first consumption of the actual local representative by the
regularizer: if the `rho / 4` support of `k_rho` lies in the local A0 carrier,
the fixed-left OS source current paired with `k_rho` is the A0 scalar average
against `k_rho`. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_representedRegularizedKernel_eq_A0_average
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη))
        S_real U)
    (hU : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U) :
    OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (osiiStep4RegularizerKSchwartz m rho hrho)) =
      ∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ := by
  simpa using
    hRep (osiiStep4RegularizerKSchwartz m rho hrho)
      (osiiStep4RegularizerKSchwartz_supportsInOpen_of_closedBall_subset
        m hrho hU)

/-- Local `(A0)` representative evaluated on one translated `g_rho` source
current.

This is the pointwise ingredient needed after splitting `k_rho = g_rho *
g_rho`: each translated left/right smearing is still inside the same local A0
carrier once its `rho / 8` support ball is contained there. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_representedGReflectedTranslate_eq_A0_average
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη))
        S_real U)
    (x : Fin m → ℝ)
    (hU : Metric.closedBall x (rho / 8) ⊆ U) :
    OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) =
      ∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerGReflectedTranslate m rho hrho x τ := by
  simpa using
    hRep (osiiStep4RegularizerGReflectedTranslate m rho hrho x)
      (osiiStep4RegularizerGReflectedTranslate_supportsInOpen_of_closedBall_subset
        m hrho x hU)

/-- Local product-density transport from compact positive product sources to a
translated `g_rho` test.

This is the bridge needed before the BVT/semigroup CLM can be used on the
Step-4 split kernels: the translated regularizer is not asserted to be a
product source.  Instead, if a product cutoff is one on its support and the
cutoff product support lies in the local window where the two CLMs agree on
compact positive product sources, the local product-source closure theorem
extends that equality to the translated `g_rho` test. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_timeCLM_eq_on_GReflectedTranslate_of_productCutoff
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    {Window : Set (Fin m → ℝ)}
    (χs : Fin m → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin m, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin m, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_Window :
      ∀ τ : Fin m → ℝ,
        (∀ i : Fin m, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ Window)
    (x : Fin m → ℝ)
    (hχ_one :
      ∀ y ∈ tsupport
          (osiiStep4RegularizerGReflectedTranslate m rho hrho x :
            (Fin m → ℝ) → ℂ),
        section43TimeProductTensor χs y = 1)
    (h_on_products :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ Window →
        T (section43TimeProductSource gs).f =
          OS.S (n + m)
            (section43FixedLeftOrderedPullbackCutoffZeroCLM
              (d := d) f hf χ η hη
              (section43TimeProductSource gs).f)) :
    T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) =
      OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) := by
  let Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + m) :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM
      (d := d) f hf χ η hη
  let Uclm : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp Z
  have hEq :=
    section43_timeCLM_eq_of_productCutoff_supportedProductSources
      T Uclm χs hχ_pos hχ_compact hχ_Window
      (osiiStep4RegularizerGReflectedTranslate m rho hrho x)
      hχ_one ?_
  · simpa [Uclm, Z] using hEq
  · intro gs hgs
    simpa [Uclm, Z] using h_on_products gs hgs

/-- Step-4 local A0 split for the fixed-left source current.

After the convolution split of `k_rho`, every source-current factor is replaced
by the same local A0 representative on the precise supports where the
regularizer lives.  This is the local representative version of the book's
regularized pairing identity, before passing to OS Hilbert scalar products. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_representedRegularizedKernel_A0_split
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη))
        S_real U)
    (hUK : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    (hUG : ∀ x ∈ Function.support
        (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
      Metric.closedBall x (rho / 8) ⊆ U) :
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ) =
      ∫ x : Fin m → ℝ,
        (∫ τ : Fin m → ℝ,
          S_real τ *
            osiiStep4RegularizerGReflectedTranslate m rho hrho x τ) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
  have hK :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM_representedRegularizedKernel_eq_A0_average
      (d := d) OS f hf χ η hη hrho hRep hUK
  have hsplit :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_integral
      (d := d) OS f hf χ η hη hrho
  calc
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ)
        =
      OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (osiiStep4RegularizerKSchwartz m rho hrho)) := hK.symm
    _ =
      ∫ x : Fin m → ℝ,
        OS.S (n + m)
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη
            (osiiStep4RegularizerGReflectedTranslate m rho hrho x)) *
          osiiStep4RegularizerGSchwartz m rho hrho x := hsplit
    _ =
      ∫ x : Fin m → ℝ,
        (∫ τ : Fin m → ℝ,
          S_real τ *
            osiiStep4RegularizerGReflectedTranslate m rho hrho x τ) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
        refine integral_congr_ae ?_
        filter_upwards with x
        by_cases hx :
            osiiStep4RegularizerGSchwartz m rho hrho x = 0
        · simp [hx]
        · have hxsupp :
              x ∈ Function.support
                (osiiStep4RegularizerGSchwartz m rho hrho :
                  (Fin m → ℝ) → ℂ) := by
            simpa [Function.mem_support] using hx
          rw [
            section43FixedLeftOrderedPullbackCutoffZeroCLM_representedGReflectedTranslate_eq_A0_average
              (d := d) OS f hf χ η hη hrho hRep x (hUG x hxsupp)]

/-- Step-4 local A0 split with the translated `g_rho` factors evaluated by a
candidate time CLM.

Monograph Vol IV Ch 2 Step 4 (lines 1078-1099): after the
`k_rho = g_rho * g_rho` split, the translated kernels are the exact test
functions used to build the OS left/right vectors.  If a candidate time CLM
agrees with the fixed-left source current on compact positive product sources
inside the chosen window, the product-density theorem transports that agreement
to every translated `g_rho` factor and hence to the whole regularized average. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_regularizedKernel_eq_timeCLM_integral
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    {rho : ℝ} (hrho : 0 < rho)
    {S_real : (Fin m → ℝ) → ℂ} {U : Set (Fin m → ℝ)}
    (hRep :
      SCV.RepresentsDistributionOn
        ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
          (section43FixedLeftOrderedPullbackCutoffZeroCLM
            (d := d) f hf χ η hη))
        S_real U)
    (hUK : Metric.closedBall (0 : Fin m → ℝ) (rho / 4) ⊆ U)
    (hUG : ∀ x ∈ Function.support
        (osiiStep4RegularizerGSchwartz m rho hrho : (Fin m → ℝ) → ℂ),
      Metric.closedBall x (rho / 8) ⊆ U)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
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
    (h_on_products :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin m → ℝ) → ℂ) ⊆ Window →
        T (section43TimeProductSource gs).f =
          OS.S (n + m)
            (section43FixedLeftOrderedPullbackCutoffZeroCLM
              (d := d) f hf χ η hη
              (section43TimeProductSource gs).f)) :
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ) =
      ∫ x : Fin m → ℝ,
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
  have hsplit :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM_representedRegularizedKernel_A0_split
      (d := d) OS f hf χ η hη hrho hRep hUK hUG
  calc
    (∫ τ : Fin m → ℝ,
        S_real τ * osiiStep4RegularizerKSchwartz m rho hrho τ)
        =
      ∫ x : Fin m → ℝ,
        (∫ τ : Fin m → ℝ,
          S_real τ *
            osiiStep4RegularizerGReflectedTranslate m rho hrho x τ) *
          osiiStep4RegularizerGSchwartz m rho hrho x := hsplit
    _ =
      ∫ x : Fin m → ℝ,
        T (osiiStep4RegularizerGReflectedTranslate m rho hrho x) *
          osiiStep4RegularizerGSchwartz m rho hrho x := by
        refine integral_congr_ae ?_
        filter_upwards with x
        by_cases hx :
            osiiStep4RegularizerGSchwartz m rho hrho x = 0
        · simp [hx]
        · have hxsupp :
              x ∈ Function.support
                (osiiStep4RegularizerGSchwartz m rho hrho :
                  (Fin m → ℝ) → ℂ) := by
            simpa [Function.mem_support] using hx
          have hA0 :=
            section43FixedLeftOrderedPullbackCutoffZeroCLM_representedGReflectedTranslate_eq_A0_average
              (d := d) OS f hf χ η hη hrho hRep x (hUG x hxsupp)
          have hT :=
            section43FixedLeftOrderedPullbackCutoffZeroCLM_timeCLM_eq_on_GReflectedTranslate_of_productCutoff
              (d := d) OS f hf χ η hη hrho T χs hχ_pos hχ_compact
              hχ_Window x (hχ_one x hxsupp) h_on_products
          rw [← hA0, ← hT]

end OSReconstruction
