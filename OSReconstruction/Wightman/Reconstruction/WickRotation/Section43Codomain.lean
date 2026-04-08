import OSReconstruction.Wightman.Reconstruction.WickRotation.EuclideanPositiveTime
import OSReconstruction.SCV.PaleyWiener
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open scoped Topology
open Set

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The Section 4.3 positive-energy region on the Minkowski test-function side:
every time component `q_i^0` is nonnegative. -/
def section43PositiveEnergyRegion (d n : ℕ) : Set (NPointDomain d n) :=
  {q | ∀ i : Fin n, 0 ≤ q i 0}

/-- Ordered positive-time support is stronger than the Section 4.3 positive-energy
condition: strict time ordering in particular forces every time coordinate to be
nonnegative. -/
theorem orderedPositiveTimeRegion_subset_section43PositiveEnergyRegion
    (d n : ℕ) :
    OrderedPositiveTimeRegion d n ⊆ section43PositiveEnergyRegion d n := by
  intro x hx i
  exact (hx i).1.le

/-- Ambient Schwartz `n`-point tests that vanish on the positive-energy region.

The quotient by this submodule is the concrete Lean model for the paper's
half-space codomain `L(R_+^{4n})`. Two ambient Schwartz functions represent the
same class exactly when they agree on the positive-energy region. -/
def section43PositiveEnergyVanishingSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    Set.EqOn (f : NPointDomain d n → ℂ) 0 (section43PositiveEnergyRegion d n)}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf hx, hg hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf hx]

/-- The multivariate Section 4.3 positive-energy codomain. -/
abbrev Section43PositiveEnergyComponent (d n : ℕ) [NeZero d] :=
  (SchwartzNPoint d n) ⧸ section43PositiveEnergyVanishingSubmodule (d := d) n

/-- The canonical quotient map into the Section 4.3 positive-energy codomain. -/
noncomputable def section43PositiveEnergyQuotientMap (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent (d := d) n :=
  ContinuousLinearMap.mk
    (Submodule.mkQ (section43PositiveEnergyVanishingSubmodule (d := d) n))
    ((section43PositiveEnergyVanishingSubmodule (d := d) n).isOpenQuotientMap_mkQ.continuous)

/-- The ambient-Schwartz quotient map is the honest dense-range map onto the
Section 4.3 half-space carrier. This is the correct quotient-side density
statement, in contrast to the false dense-range target on the support-restricted
subtype. -/
theorem surjective_section43PositiveEnergyQuotientMap (d n : ℕ) [NeZero d] :
    Function.Surjective (section43PositiveEnergyQuotientMap (d := d) n) :=
  Submodule.mkQ_surjective (section43PositiveEnergyVanishingSubmodule (d := d) n)

/-- The ambient-Schwartz quotient map is the honest dense-range map onto the
Section 4.3 half-space carrier. This is the correct quotient-side density
statement, in contrast to the false dense-range target on the support-restricted
subtype. -/
theorem denseRange_section43PositiveEnergyQuotientMap (d n : ℕ) [NeZero d] :
    DenseRange (section43PositiveEnergyQuotientMap (d := d) n) :=
  (surjective_section43PositiveEnergyQuotientMap (d := d) n).denseRange

/-- Equality on the positive-energy region is exactly equality in the quotient
codomain. -/
theorem section43PositiveEnergyQuotientMap_eq_of_eqOn_region
    {n : ℕ} {f g : SchwartzNPoint d n}
    (hfg :
      Set.EqOn (f : NPointDomain d n → ℂ) (g : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n)) :
    section43PositiveEnergyQuotientMap (d := d) n f =
      section43PositiveEnergyQuotientMap (d := d) n g := by
  change (Submodule.Quotient.mk f :
      Section43PositiveEnergyComponent (d := d) n) =
    Submodule.Quotient.mk g
  rw [Submodule.Quotient.eq]
  change Set.EqOn ((f - g : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0
    (section43PositiveEnergyRegion d n)
  intro x hx
  have hEq : f x = g x := hfg hx
  simp [hEq]

/-- Quotient equality is exactly equality on the positive-energy region. -/
theorem eqOn_region_of_section43PositiveEnergyQuotientMap_eq
    {n : ℕ} {f g : SchwartzNPoint d n}
    (hfg :
      section43PositiveEnergyQuotientMap (d := d) n f =
        section43PositiveEnergyQuotientMap (d := d) n g) :
    Set.EqOn (f : NPointDomain d n → ℂ) (g : NPointDomain d n → ℂ)
      (section43PositiveEnergyRegion d n) := by
  change (Submodule.Quotient.mk f : Section43PositiveEnergyComponent (d := d) n) =
    Submodule.Quotient.mk g at hfg
  rw [Submodule.Quotient.eq] at hfg
  intro x hx
  have hx0 : ((f - g : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := hfg hx
  exact sub_eq_zero.mp <| by simpa using hx0

/-- Quotient-zero form of the same region-restriction principle. -/
theorem section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region
    {n : ℕ} {f g : SchwartzNPoint d n}
    (hfg :
      Set.EqOn (f : NPointDomain d n → ℂ) (g : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n)) :
    section43PositiveEnergyQuotientMap (d := d) n (f - g) = 0 := by
  change (Submodule.Quotient.mk (f - g) :
      Section43PositiveEnergyComponent (d := d) n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change Set.EqOn ((f - g : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0
    (section43PositiveEnergyRegion d n)
  intro x hx
  have hEq : f x = g x := hfg hx
  simp [hEq]

/-- The multivariate Section 4.3 transport map on the Euclidean positive-time
submodule. This is the quotient-side analog of `os1TransportOneVar`. -/
noncomputable def os1TransportComponent (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
      Section43PositiveEnergyComponent (d := d) n :=
  (section43PositiveEnergyQuotientMap (d := d) n).comp
    (euclideanPositiveTimeSubmodule (d := d) n).subtypeL

@[simp] theorem os1TransportComponent_apply
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    os1TransportComponent d n f =
      section43PositiveEnergyQuotientMap (d := d) n f.1 := rfl

/-- The multivariate Section 4.3 transport map is injective on the current
Euclidean positive-time source domain: quotient equality gives equality on the
positive-energy region, and outside that region both inputs vanish by ordered
positive-time support. -/
theorem os1TransportComponent_injective (d n : ℕ) [NeZero d] :
    Function.Injective (os1TransportComponent d n) := by
  intro f g hfg
  apply Subtype.ext
  have hEqOn :
      Set.EqOn ((f.1 : NPointDomain d n → ℂ)) ((g.1 : NPointDomain d n → ℂ))
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n f.1 =
          section43PositiveEnergyQuotientMap (d := d) n g.1 := hfg
    change (Submodule.Quotient.mk (f.1 : SchwartzNPoint d n) :
        Section43PositiveEnergyComponent (d := d) n) =
      Submodule.Quotient.mk g.1 at hq
    rw [Submodule.Quotient.eq] at hq
    intro x hx
    have hx0 : ((f.1 - g.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := hq hx
    exact sub_eq_zero.mp <| by simpa using hx0
  ext x
  by_cases hx : x ∈ section43PositiveEnergyRegion d n
  · exact hEqOn hx
  · have hf_zero : ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hx (orderedPositiveTimeRegion_subset_section43PositiveEnergyRegion d n (f.2 hxt))
    have hg_zero : ((g.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hx (orderedPositiveTimeRegion_subset_section43PositiveEnergyRegion d n (g.2 hxt))
    simp [hf_zero, hg_zero]

/-- Kernel-zero form of multivariate injectivity. -/
theorem os1TransportComponent_eq_zero_iff
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    os1TransportComponent d n f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hzero : os1TransportComponent d n (0 : euclideanPositiveTimeSubmodule (d := d) n) = 0 := by
    simp
  exact os1TransportComponent_injective d n (h.trans hzero.symm)

/-- Evaluation at the boundary point `0` descends to the positive-degree
Section 4.3 quotient, because the quotient relation is equality on the whole
positive-energy region and `0` belongs to that region. -/
noncomputable def evalAtZeroDescendsToSection43PositiveEnergyComponent
    (n : ℕ) [NeZero d] :
    Section43PositiveEnergyComponent (d := d) (n + 1) →L[ℂ] ℂ := by
  let raw : SchwartzNPoint d (n + 1) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (0 : NPointDomain d (n + 1))).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (NPointDomain d (n + 1)) ℂ)
  have hker :
      section43PositiveEnergyVanishingSubmodule (d := d) (n + 1) ≤
        LinearMap.ker raw.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker]
    have hf0 : ((f : SchwartzNPoint d (n + 1)) : NPointDomain d (n + 1) → ℂ) 0 = 0 := by
      exact hf (by simp [section43PositiveEnergyRegion])
    simpa [raw, SchwartzMap.toBoundedContinuousFunctionCLM_apply] using hf0
  let descended : Section43PositiveEnergyComponent (d := d) (n + 1) →ₗ[ℂ] ℂ :=
    (section43PositiveEnergyVanishingSubmodule (d := d) (n + 1)).liftQ raw.toLinearMap hker
  refine ContinuousLinearMap.mk descended ?_
  let hopen :=
    (section43PositiveEnergyVanishingSubmodule (d := d) (n + 1)).isOpenQuotientMap_mkQ
  exact hopen.isQuotientMap.continuous_iff.2 <| by
    simpa [descended, raw, Function.comp] using raw.continuous

@[simp] theorem evalAtZeroDescendsToSection43PositiveEnergyComponent_apply
    (n : ℕ) [NeZero d]
    (f : SchwartzNPoint d (n + 1)) :
    evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) n
        (section43PositiveEnergyQuotientMap (d := d) (n + 1) f) =
      f 0 := by
  change
    ((section43PositiveEnergyVanishingSubmodule (d := d) (n + 1)).liftQ
      (((BoundedContinuousFunction.evalCLM ℂ (0 : NPointDomain d (n + 1))).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (NPointDomain d (n + 1)) ℂ)).toLinearMap)
      ?_ (Submodule.Quotient.mk f)) =
      f 0
  simp [SchwartzMap.toBoundedContinuousFunctionCLM_apply]

@[simp] theorem evalAtZeroDescendsToSection43PositiveEnergyComponent_os1TransportComponent
    (n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1)) :
    evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) n
        (os1TransportComponent d (n + 1) f) = 0 := by
  rw [os1TransportComponent_apply,
    evalAtZeroDescendsToSection43PositiveEnergyComponent_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro h0
  have hord : (0 : NPointDomain d (n + 1)) ∈ OrderedPositiveTimeRegion d (n + 1) := f.2 h0
  have hlt : (0 : ℝ) < 0 := by
    simpa using (hord 0).1
  exact (lt_irrefl (0 : ℝ)) hlt

/-- For positive degree, the support-restricted Section 4.3 source is not dense
in the quotient codomain: every image class vanishes at the boundary point
`0`, but the quotient contains classes with nonzero boundary value there. -/
theorem not_denseRange_os1TransportComponent_succ
    (n : ℕ) [NeZero d] :
    ¬ DenseRange (os1TransportComponent d (n + 1)) := by
  intro hdense
  let z : Section43PositiveEnergyComponent (d := d) (n + 1) →L[ℂ] ℂ :=
    evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) n
  have hz_zero_on_range :
      ∀ f : euclideanPositiveTimeSubmodule (d := d) (n + 1),
        z (os1TransportComponent d (n + 1) f) = 0 := by
    intro f
    simpa [z] using
      evalAtZeroDescendsToSection43PositiveEnergyComponent_os1TransportComponent
        (d := d) n f
  have hcomp :
      (z : Section43PositiveEnergyComponent (d := d) (n + 1) → ℂ) ∘
          os1TransportComponent d (n + 1) =
        (fun _ : euclideanPositiveTimeSubmodule (d := d) (n + 1) => (0 : ℂ)) := by
    funext f
    exact hz_zero_on_range f
  have hz_eq_zero :
      (z : Section43PositiveEnergyComponent (d := d) (n + 1) → ℂ) =
        fun _ : Section43PositiveEnergyComponent (d := d) (n + 1) => (0 : ℂ) :=
    DenseRange.equalizer (f := os1TransportComponent d (n + 1))
      hdense z.continuous continuous_const hcomp
  let b : ContDiffBump (0 : NPointDomain d (n + 1)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let ψfun : NPointDomain d (n + 1) → ℂ := fun x => (b x : ℂ)
  have hψ_smooth : ContDiff ℝ (⊤ : ENat) ψfun := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hψ_compact : HasCompactSupport ψfun :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let ψ : SchwartzNPoint d (n + 1) := hψ_compact.toSchwartzMap hψ_smooth
  have hψ0 : ψ 0 = 1 := by
    have happly :
        ψ 0 = ψfun 0 := by
      simpa [ψ, ψfun] using
        (HasCompactSupport.toSchwartzMap_toFun hψ_compact hψ_smooth
          (0 : NPointDomain d (n + 1)))
    rw [happly]
    have hball :
        (0 : NPointDomain d (n + 1)) ∈
          Metric.closedBall (0 : NPointDomain d (n + 1)) (1 : ℝ) := by
      simp [Metric.mem_closedBall]
    exact congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall hball)
  have hz_nonzero :
      z (section43PositiveEnergyQuotientMap (d := d) (n + 1) ψ) ≠ 0 := by
    simpa [z] using
      show evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) n
          (section43PositiveEnergyQuotientMap (d := d) (n + 1) ψ) ≠ 0 by
        rw [evalAtZeroDescendsToSection43PositiveEnergyComponent_apply, hψ0]
        norm_num
  have hz_zero :
      z (section43PositiveEnergyQuotientMap (d := d) (n + 1) ψ) = 0 := by
    simpa using congrFun hz_eq_zero
      (section43PositiveEnergyQuotientMap (d := d) (n + 1) ψ)
  exact hz_nonzero hz_zero

/-- The one-variable positive-time Euclidean test domain used by Section 4.3. -/
def euclideanPositiveTimeTest1D : Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {f | tsupport (f : ℝ → ℂ) ⊆ Set.Ici (0 : ℝ)}
  zero_mem' := by
    intro x hx
    simp at hx
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add (f : ℝ → ℂ) (g : ℝ → ℂ) hx
    exact hx'.elim (fun hx_f => hf hx_f) (fun hx_g => hg hx_g)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right (fun _ : ℝ => c) (f : ℝ → ℂ)).trans hf

/-- The 1D vanishing submodule for the half-line codomain `L(R_+)`. -/
def section43PositiveEnergyVanishingSubmodule1D :
    Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {f | Set.EqOn (f : ℝ → ℂ) 0 (Set.Ici (0 : ℝ))}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf hx, hg hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf hx]

/-- The one-variable Section 4.3 positive-energy quotient codomain. -/
abbrev Section43PositiveEnergy1D :=
  (SchwartzMap ℝ ℂ) ⧸ section43PositiveEnergyVanishingSubmodule1D

/-- The canonical quotient map into the one-variable half-line codomain. -/
noncomputable def section43PositiveEnergyQuotientMap1D :
    SchwartzMap ℝ ℂ →L[ℂ] Section43PositiveEnergy1D :=
  ContinuousLinearMap.mk
    (Submodule.mkQ section43PositiveEnergyVanishingSubmodule1D)
    (section43PositiveEnergyVanishingSubmodule1D.isOpenQuotientMap_mkQ.continuous)

/-- The ambient-Schwartz quotient map is the honest dense-range map onto the
one-variable Section 4.3 half-line carrier. The negative theorem
`not_denseRange_os1TransportOneVar` shows that this must not be confused with
density of the support-restricted subtype. -/
theorem surjective_section43PositiveEnergyQuotientMap1D :
    Function.Surjective section43PositiveEnergyQuotientMap1D :=
  Submodule.mkQ_surjective section43PositiveEnergyVanishingSubmodule1D

/-- The ambient-Schwartz quotient map is the honest dense-range map onto the
one-variable Section 4.3 half-line carrier. The negative theorem
`not_denseRange_os1TransportOneVar` shows that this must not be confused with
density of the support-restricted subtype. -/
theorem denseRange_section43PositiveEnergyQuotientMap1D :
    DenseRange section43PositiveEnergyQuotientMap1D :=
  surjective_section43PositiveEnergyQuotientMap1D.denseRange

/-- The one-variable Section 4.3 transport map.

On the quotient codomain model, the honest production surface is: take the
positive-time Euclidean Schwartz test itself and pass to its class modulo
functions vanishing on `[0, ∞)`. The Fourier transform is then supplied by the
descended pairing `fourierPairingDescendsToSection43PositiveEnergy1D`, so the
transport does not introduce a second Fourier transform by hand. -/
noncomputable def os1TransportOneVar :
    euclideanPositiveTimeTest1D →L[ℂ] Section43PositiveEnergy1D :=
  section43PositiveEnergyQuotientMap1D.comp euclideanPositiveTimeTest1D.subtypeL

@[simp] theorem os1TransportOneVar_apply
    (f : euclideanPositiveTimeTest1D) :
    os1TransportOneVar f =
      section43PositiveEnergyQuotientMap1D f.1 := rfl

/-- Equality on `[0,∞)` is exactly equality in the one-variable quotient
codomain. -/
theorem section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
    {f g : SchwartzMap ℝ ℂ}
    (hfg : Set.EqOn (f : ℝ → ℂ) (g : ℝ → ℂ) (Set.Ici (0 : ℝ))) :
    section43PositiveEnergyQuotientMap1D f =
      section43PositiveEnergyQuotientMap1D g := by
  change (Submodule.Quotient.mk f : Section43PositiveEnergy1D) =
    Submodule.Quotient.mk g
  rw [Submodule.Quotient.eq]
  change Set.EqOn ((f - g : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0 (Set.Ici (0 : ℝ))
  intro x hx
  have hEq : f x = g x := hfg hx
  simp [hEq]

/-- Quotient-zero form of the same one-variable EqOn principle. -/
theorem section43PositiveEnergyQuotientMap1D_sub_eq_zero_of_eqOn_nonneg
    {f g : SchwartzMap ℝ ℂ}
    (hfg : Set.EqOn (f : ℝ → ℂ) (g : ℝ → ℂ) (Set.Ici (0 : ℝ))) :
    section43PositiveEnergyQuotientMap1D (f - g) = 0 := by
  change (Submodule.Quotient.mk (f - g) : Section43PositiveEnergy1D) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change Set.EqOn ((f - g : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0 (Set.Ici (0 : ℝ))
  intro x hx
  have hEq : f x = g x := hfg hx
  simp [hEq]

/-- Any one-sided Fourier-support pairing factors through the one-variable
half-line quotient. This is the quotient-side reformulation of
`SCV.fourier_pairing_eq_of_eqOn_nonneg`. -/
noncomputable def fourierPairingDescendsToSection43PositiveEnergy1D
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T) :
    Section43PositiveEnergy1D →L[ℂ] ℂ := by
  let raw : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.fourierTransformCLM ℂ)
  have hker :
      section43PositiveEnergyVanishingSubmodule1D ≤
        LinearMap.ker raw.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker]
    have hEq : Set.EqOn (f : ℝ → ℂ) (0 : ℝ → ℂ) (Set.Ici (0 : ℝ)) := hf
    simpa [raw] using
      (SCV.fourier_pairing_eq_of_eqOn_nonneg T hT_supp
        (φ := f) (ψ := 0) hEq)
  let descended : Section43PositiveEnergy1D →ₗ[ℂ] ℂ :=
    section43PositiveEnergyVanishingSubmodule1D.liftQ raw.toLinearMap hker
  refine ContinuousLinearMap.mk descended ?_
  refine section43PositiveEnergyVanishingSubmodule1D.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.2 ?_
  simpa [descended, raw, Function.comp] using raw.continuous

@[simp] theorem fourierPairingDescendsToSection43PositiveEnergy1D_apply
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (f : SchwartzMap ℝ ℂ) :
    fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (section43PositiveEnergyQuotientMap1D f) =
      T ((SchwartzMap.fourierTransformCLM ℂ) f) := by
  change
    (section43PositiveEnergyVanishingSubmodule1D.liftQ
      ((T.comp (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap) ?_
      (Submodule.Quotient.mk f)) =
      T ((SchwartzMap.fourierTransformCLM ℂ) f)
  simp

@[simp] theorem fourierPairingDescendsToSection43PositiveEnergy1D_os1TransportOneVar
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (f : euclideanPositiveTimeTest1D) :
    fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (os1TransportOneVar f) =
      T ((SchwartzMap.fourierTransformCLM ℂ) f.1) := by
  simp [os1TransportOneVar]

/-- The one-variable transport map is injective: two positive-time Euclidean
tests with the same quotient class agree on `[0,∞)`, and outside that half-line
they both vanish by support. -/
theorem os1TransportOneVar_injective :
    Function.Injective os1TransportOneVar := by
  intro f g hfg
  apply Subtype.ext
  change (f : SchwartzMap ℝ ℂ) = g
  have hEqOn :
      Set.EqOn (f : ℝ → ℂ) (g : ℝ → ℂ) (Set.Ici (0 : ℝ)) := by
    have hq :
        section43PositiveEnergyQuotientMap1D (f : SchwartzMap ℝ ℂ) =
          section43PositiveEnergyQuotientMap1D (g : SchwartzMap ℝ ℂ) := hfg
    change (Submodule.Quotient.mk (f : SchwartzMap ℝ ℂ) : Section43PositiveEnergy1D) =
      Submodule.Quotient.mk (g : SchwartzMap ℝ ℂ) at hq
    rw [Submodule.Quotient.eq] at hq
    intro x hx
    have hx0 : ((f - g : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := hq hx
    exact sub_eq_zero.mp hx0
  ext x
  by_cases hx : 0 ≤ x
  · exact hEqOn hx
  · have hf_zero : (f : ℝ → ℂ) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hx (f.2 hxt)
    have hg_zero : (g : ℝ → ℂ) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hx (g.2 hxt)
    simp [hf_zero, hg_zero]

/-- A positive-time Schwartz test vanishes at the boundary point `0`. Indeed it
vanishes on a whole left neighborhood, so continuity forces the boundary value
to be `0` as well. -/
theorem euclideanPositiveTimeTest1D_apply_zero
    (f : euclideanPositiveTimeTest1D) :
    (f : SchwartzMap ℝ ℂ) 0 = 0 := by
  by_contra hf0
  have hzero_mem : (0 : ℝ) ∈ Function.support ((f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    simpa [Function.mem_support] using hf0
  have hnhds : Function.support ((f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ∈ 𝓝 (0 : ℝ) := by
    have hmem : ((f : SchwartzMap ℝ ℂ) 0) ∈ ({0} : Set ℂ)ᶜ := by
      simpa [Set.mem_compl_iff] using hf0
    have hset : ({0} : Set ℂ)ᶜ ∈ 𝓝 ((f : SchwartzMap ℝ ℂ) 0) :=
      isClosed_singleton.isOpen_compl.mem_nhds hmem
    simpa [Function.support] using ((f : SchwartzMap ℝ ℂ).continuous.continuousAt hset)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε_pos, hball⟩
  have hneg : (-(ε / 2) : ℝ) < 0 := by linarith
  have hdist : dist (-(ε / 2)) (0 : ℝ) < ε := by
    have hdist_eq : dist (-(ε / 2)) (0 : ℝ) = ε / 2 := by
      rw [Real.dist_eq, sub_zero, abs_of_neg hneg]
      ring
    rw [hdist_eq]
    have hhalf_lt : ε / 2 < ε := by linarith
    exact hhalf_lt
  have hneg_mem :
      (-(ε / 2) : ℝ) ∈ Function.support ((f : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    hball hdist
  have hneg_tsupport :
      (-(ε / 2) : ℝ) ∈ tsupport ((f : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    subset_tsupport _ hneg_mem
  have hnonneg : 0 ≤ (-(ε / 2) : ℝ) := f.2 hneg_tsupport
  linarith

/-- Evaluation at `0` descends to the Section 4.3 half-line quotient, because
the quotient relation is exactly equality on `[0,∞)`. -/
noncomputable def evalAtZeroDescendsToSection43PositiveEnergy1D :
    Section43PositiveEnergy1D →L[ℂ] ℂ := by
  let raw : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
  have hker :
      section43PositiveEnergyVanishingSubmodule1D ≤
        LinearMap.ker raw.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker]
    have hf0 : (f : ℝ → ℂ) 0 = 0 := hf (by simp)
    simpa [raw, SchwartzMap.toBoundedContinuousFunctionCLM_apply] using hf0
  let descended : Section43PositiveEnergy1D →ₗ[ℂ] ℂ :=
    section43PositiveEnergyVanishingSubmodule1D.liftQ raw.toLinearMap hker
  refine ContinuousLinearMap.mk descended ?_
  refine section43PositiveEnergyVanishingSubmodule1D.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.2 ?_
  simpa [descended, raw, Function.comp] using raw.continuous

@[simp] theorem evalAtZeroDescendsToSection43PositiveEnergy1D_apply
    (f : SchwartzMap ℝ ℂ) :
    evalAtZeroDescendsToSection43PositiveEnergy1D
        (section43PositiveEnergyQuotientMap1D f) =
      f 0 := by
  change
    (section43PositiveEnergyVanishingSubmodule1D.liftQ
      (((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).toLinearMap) ?_
      (Submodule.Quotient.mk f)) =
      f 0
  simp [SchwartzMap.toBoundedContinuousFunctionCLM_apply]

@[simp] theorem evalAtZeroDescendsToSection43PositiveEnergy1D_os1TransportOneVar
    (f : euclideanPositiveTimeTest1D) :
    evalAtZeroDescendsToSection43PositiveEnergy1D (os1TransportOneVar f) = 0 := by
  rw [os1TransportOneVar_apply, evalAtZeroDescendsToSection43PositiveEnergy1D_apply]
  exact euclideanPositiveTimeTest1D_apply_zero f

/-- The literal current `DenseRange os1TransportOneVar` target is false on the
support-restricted source domain: all image classes vanish at the boundary
point `0`, but the quotient contains classes with nonzero boundary value. -/
theorem not_denseRange_os1TransportOneVar :
    ¬ DenseRange os1TransportOneVar := by
  intro hdense
  let z : Section43PositiveEnergy1D →L[ℂ] ℂ := evalAtZeroDescendsToSection43PositiveEnergy1D
  have hz_zero_on_range :
      ∀ f : euclideanPositiveTimeTest1D, z (os1TransportOneVar f) = 0 := by
    intro f
    simpa [z] using evalAtZeroDescendsToSection43PositiveEnergy1D_os1TransportOneVar f
  have hcomp :
      (z : Section43PositiveEnergy1D → ℂ) ∘ os1TransportOneVar =
        (fun _ : Section43PositiveEnergy1D => (0 : ℂ)) ∘ os1TransportOneVar := by
    funext f
    exact hz_zero_on_range f
  have hz_eq_zero :
      (z : Section43PositiveEnergy1D → ℂ) = fun _ : Section43PositiveEnergy1D => (0 : ℂ) :=
    DenseRange.equalizer (f := os1TransportOneVar) hdense z.continuous continuous_const hcomp
  let ψ : SchwartzMap ℝ ℂ := SCV.schwartzPsiZ Complex.I (by norm_num)
  have hψ0 : ψ 0 = 1 := by
    simp [ψ, SCV.schwartzPsiZ_apply, SCV.psiZ_eq]
  have hz_nonzero :
      z (section43PositiveEnergyQuotientMap1D ψ) ≠ 0 := by
    simpa [z] using
      show evalAtZeroDescendsToSection43PositiveEnergy1D
          (section43PositiveEnergyQuotientMap1D ψ) ≠ 0 by
        rw [evalAtZeroDescendsToSection43PositiveEnergy1D_apply, hψ0]
        norm_num
  have hz_zero :
      z (section43PositiveEnergyQuotientMap1D ψ) = 0 := by
    simpa using congrFun hz_eq_zero (section43PositiveEnergyQuotientMap1D ψ)
  exact hz_nonzero hz_zero

end OSReconstruction
