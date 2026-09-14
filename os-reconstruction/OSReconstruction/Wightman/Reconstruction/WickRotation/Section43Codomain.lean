/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
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

end OSReconstruction
