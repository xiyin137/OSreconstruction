/- 
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslationCore
import OSReconstruction.ComplexLieGroups.Connectedness.ReducedPermutedTube
import OSReconstruction.Bridge.AxiomBridge
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Reduced BHW Extension Shell

This file sets up the Route 1 reduced analytic-continuation interface.

The key point is that the reduced `(n - 1)`-difference-variable problem does not
use the standard coordinate-permutation action on `Fin (n - 1)`. Physical
permutations act through the induced linear action `permOnReducedDiff`, so the
reduced BHW theorem must be stated natively against that action rather than by
reusing the absolute-coordinate BHW theorem unchanged.

Just as importantly, permutation symmetry is not a property of the raw reduced
forward-tube holomorphic input. It belongs to the extension/local-commutativity
step on reduced PET, so the bundled reduced forward-tube input below does not
include a `perm_invariant` field.

For now this file provides:

* the reduced extension witness structure,
* reduced Lorentz/permutation invariance predicates,
* an axiomatic reduced BHW theorem surface,
* a chosen reduced BHW extension,
* a safe section from reduced forward-tube coordinates into the absolute forward
  tube,
* descent of absolute forward-tube holomorphic data along that safe section,
* algebraic pullback from reduced coordinates back to absolute coordinates,
* the one-line absolute translation invariance lemma for any reduced pullback.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace BHW

open scoped SchwartzMap

variable {d n : ℕ}

/-- Reduced complex configuration space with `n - 1` successive differences. -/
abbrev ReducedConfig (d n : ℕ) := Fin (n - 1) → Fin (d + 1) → ℂ

/-- Reduced configuration space indexed by the number of difference variables.

`ReducedNPointConfig d m` is the internal Route 1 reduced complex domain for an
`m`-variable object descended from the public literal `(m + 1)`-point family. -/
abbrev ReducedNPointConfig (d m : ℕ) := ReducedConfig d (m + 1)

/-- Reduced PET at reduced arity `m`, i.e. the image of absolute PET for
`m + 1` spacetime points under `reducedDiffMap`. -/
abbrev ReducedPermutedExtendedTubeN (d m : ℕ) : Set (ReducedNPointConfig d m) :=
  reducedPermutedExtendedTube d (m + 1)

/-- Reduced forward tube at reduced arity `m`. -/
abbrev ReducedForwardTubeN (d m : ℕ) : Set (ReducedNPointConfig d m) :=
  ReducedForwardTube d (m + 1)

/-- Reduced complex Lorentz invariance on the reduced PET image. -/
def IsReducedLorentzInvariant (F : ReducedConfig d n → ℂ) : Prop :=
  ∀ (Λ : ComplexLorentzGroup d) (η : ReducedConfig d n),
    η ∈ reducedPermutedExtendedTube d n →
    complexLorentzAction Λ η ∈ reducedPermutedExtendedTube d n →
    F (complexLorentzAction Λ η) = F η

/-- Reduced permutation invariance on the reduced PET image, using the induced
action `permOnReducedDiff` of `S_n` on successive differences. -/
def IsReducedPermutationInvariant (F : ReducedConfig d n → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (η : ReducedConfig d n),
    η ∈ reducedPermutedExtendedTube d n →
    permOnReducedDiff (d := d) (n := n) π η ∈ reducedPermutedExtendedTube d n →
    F (permOnReducedDiff (d := d) (n := n) π η) = F η

/-- Route 1 reduced BHW extension package.

This mirrors the absolute `W_analytic_BHW` interface, but lives natively on
reduced `(n - 1)`-difference coordinates and uses the induced `S_n` action on
differences. It is internal reduced infrastructure below the public literal
`n`-point API. -/
structure ReducedBHWExtensionData (d n : ℕ)
    (F : ReducedConfig d n → ℂ) where
  toFun : ReducedConfig d n → ℂ
  holomorphic :
    DifferentiableOn ℂ toFun (reducedPermutedExtendedTube d n)
  agrees_on_reducedForwardTube :
    ∀ η ∈ ReducedForwardTube d n, toFun η = F η
  lorentz_invariant :
    IsReducedLorentzInvariant (d := d) (n := n) toFun
  perm_invariant :
    IsReducedPermutationInvariant (d := d) (n := n) toFun

/-! #### Reduced BHW extension infrastructure

The raw `reduced_bargmann_hall_wightman` axiom (taking generic `F` with `hF_perm`
on the reduced forward tube) was **removed** because its `hF_perm` hypothesis is
vacuously true: non-trivial permutations send `V₊` to `−V₊`, so the premise
`permOnReducedDiff π η ∈ ReducedForwardTube` is always false.

The correct axiom is `reduced_bargmann_hall_wightman_of_input`, which takes the
full Wightman bundle `Wfn` and a cutoff `χ`. Permutation symmetry is derived
from local commutativity of the Wightman functions, not from a forward-tube
hypothesis. -/

/-- Pull a reduced analytic function back to absolute coordinates along the
reduced difference map. This is one direction of the internal reduced/absolute
Route 1 bridge. -/
def pullbackReducedExtension (F : ReducedConfig d n → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  pullbackReducedComplex n d F

@[simp] theorem pullbackReducedExtension_apply
    (F : ReducedConfig d n → ℂ) (z : Fin n → Fin (d + 1) → ℂ) :
    pullbackReducedExtension (d := d) (n := n) F z = F (reducedDiffMap n d z) := by
  rfl

/-- Any absolute function defined as a pullback from reduced difference
coordinates is automatically invariant under uniform complex translations. -/
theorem pullbackReducedExtension_translate_uniform
    (F : ReducedConfig d n → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    pullbackReducedExtension (d := d) (n := n) F (fun k μ => z k μ + c μ) =
      pullbackReducedExtension (d := d) (n := n) F z := by
  exact pullbackReducedComplex_translate_uniform n d F z c

/-- Route 1's algebraic translation-invariance tautology: once the absolute
extension is defined as a pullback from reduced coordinates, uniform
translations disappear immediately. -/
theorem reduced_pullback_translation_invariant
    (F : ReducedConfig d n → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    pullbackReducedExtension (d := d) (n := n) F (fun k μ => z k μ + c μ) =
      pullbackReducedExtension (d := d) (n := n) F z := by
  exact pullbackReducedExtension_translate_uniform (d := d) (n := n) F z c

/-- The canonical reduced real-side family used by Route 1, exposed here so the
reduced extension file can talk directly in reduced variables. -/
def route1ReducedWightmanFamily
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ :=
  reducedWightmanFamily Wfn χ

@[simp] theorem route1ReducedWightmanFamily_apply
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (m : ℕ) (φ : SchwartzNPoint d m) :
    route1ReducedWightmanFamily Wfn χ m φ = reducedWightman Wfn m χ φ := by
  rfl

theorem route1ReducedWightmanFamily_eq_of_cutoff_canonical
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    route1ReducedWightmanFamily Wfn χ₁ = route1ReducedWightmanFamily Wfn χ₂ := by
  exact reducedWightmanFamily_eq_of_cutoff_canonical (Wfn := Wfn) χ₁ χ₂

/-- Canonical future-timelike real vector used to place the absolute basepoint
safely inside the forward cone when descending to reduced coordinates. -/
def safeBasepointVec (d : ℕ) : Fin (d + 1) → ℝ :=
  Pi.single 0 1

theorem safeBasepointVec_mem_forwardCone [NeZero d] :
    InOpenForwardCone d (safeBasepointVec d) := by
  rw [InOpenForwardCone, minkowski_sum_decomp]
  constructor
  · simp [safeBasepointVec]
  · simp [safeBasepointVec]

/-- Shift every spacetime point by the same imaginary future-timelike vector. -/
def safeUniformShift (d m : ℕ) : Fin (m + 1) → Fin (d + 1) → ℂ :=
  fun _ μ => Complex.I * safeBasepointVec d μ

/-- `reducedDiffSection` normalized at the zero basepoint. -/
@[simp] theorem reducedDiffSection_zero (n d : ℕ) [NeZero n]
    (η : Fin (n - 1) → Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    reducedDiffSection n d η ⟨0, Nat.pos_of_neZero n⟩ μ = 0 := by
  simp [reducedDiffSection, diffCoordEquiv_symm_apply, prependZeroDiff]

/-- The safe absolute representative of a reduced configuration, obtained by
placing the basepoint at `i e₀` instead of `0`. -/
def safeSection (d m : ℕ) :
    ReducedNPointConfig d m → (Fin (m + 1) → Fin (d + 1) → ℂ) :=
  fun η k μ => reducedDiffSection (m + 1) d η k μ + safeUniformShift d m k μ

@[simp] theorem safeSection_apply (d m : ℕ)
    (η : ReducedNPointConfig d m) (k : Fin (m + 1)) (μ : Fin (d + 1)) :
    safeSection d m η k μ =
      reducedDiffSection (m + 1) d η k μ + Complex.I * safeBasepointVec d μ := by
  rfl

@[simp] theorem safeSection_zero (d m : ℕ)
    (η : ReducedNPointConfig d m) (μ : Fin (d + 1)) :
    safeSection d m η 0 μ = Complex.I * safeBasepointVec d μ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hzero :
      reducedDiffSection (m + 1) d η ⟨0, Nat.succ_pos _⟩ μ = 0 :=
    reducedDiffSection_zero (n := m + 1) (d := d) η μ
  change reducedDiffSection (m + 1) d η ⟨0, Nat.succ_pos _⟩ μ +
      safeUniformShift d m ⟨0, Nat.succ_pos _⟩ μ =
    Complex.I * safeBasepointVec d μ
  rw [hzero]
  simp [safeUniformShift]

/-- The safe section preserves reduced differences because the added basepoint
shift is uniform in the configuration index. -/
@[simp] theorem reducedDiffMap_safeSection (d m : ℕ)
    (η : ReducedNPointConfig d m) :
    reducedDiffMap (m + 1) d (safeSection d m η) = η := by
  calc
    reducedDiffMap (m + 1) d (safeSection d m η)
        = reducedDiffMap (m + 1) d
            (fun k μ => reducedDiffSection (m + 1) d η k μ +
              (Complex.I * safeBasepointVec d μ)) := by
              rfl
    _ = reducedDiffMap (m + 1) d (reducedDiffSection (m + 1) d η) := by
          simpa using reducedDiffMap_translate_uniform_eq (m + 1) d
            (reducedDiffSection (m + 1) d η) (fun μ => Complex.I * safeBasepointVec d μ)
    _ = η := reducedDiffMap_section (m + 1) d η

/-- The safe section lands in the absolute forward tube whenever the reduced
differences are in the reduced forward tube. -/
theorem safeSection_mem_forwardTube [NeZero d] (m : ℕ)
    (η : ReducedNPointConfig d m) (hη : η ∈ ReducedForwardTubeN d m) :
    safeSection d m η ∈ ForwardTube d (m + 1) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  rw [mem_forwardTube_iff_basepoint_and_reducedDiff]
  constructor
  · have hbase :
        (fun μ => (safeSection d m η 0 μ).im) = safeBasepointVec d := by
      ext μ
      rw [safeSection_zero]
      simp [Complex.mul_im, Complex.I_re, Complex.I_im, safeBasepointVec]
    rw [hbase]
    exact safeBasepointVec_mem_forwardCone (d := d)
  · rw [reducedDiffMap_safeSection]
    simpa [ReducedForwardTubeN, ReducedForwardTube] using hη

/-- Descend an absolute forward-tube function to reduced coordinates using the
safe section. -/
def descendAlongSafeSection (d m : ℕ)
    (F : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ) :
    ReducedNPointConfig d m → ℂ :=
  fun η => F (safeSection d m η)

@[simp] theorem descendAlongSafeSection_apply (d m : ℕ)
    (F : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ) (η : ReducedNPointConfig d m) :
    descendAlongSafeSection d m F η = F (safeSection d m η) := by
  rfl

/-- Abstract translation-invariance hypothesis for an absolute forward-tube
witness. This is the temporary analytic axiom Route 1 needs in order to descend
the absolute witness through the safe section. -/
def IsForwardTubeTranslationInvariant (d m : ℕ)
    (F : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ) : Prop :=
  ∀ (z : Fin (m + 1) → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
    z ∈ ForwardTube d (m + 1) →
    (fun k μ => z k μ + c μ) ∈ ForwardTube d (m + 1) →
    F (fun k μ => z k μ + c μ) = F z

/-- For a point already in the absolute forward tube, the safe section of its
reduced differences differs from the original point by a uniform complex shift.
Hence any translation-invariant absolute witness factors through the reduced
difference map on the forward tube. -/
theorem descendAlongSafeSection_eq_of_translation_invariant
    [NeZero d] (m : ℕ)
    (F : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hF_trans : IsForwardTubeTranslationInvariant d m F)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (m + 1)) :
    descendAlongSafeSection d m F (reducedDiffMap (m + 1) d z) = F z := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hz_split := (mem_forwardTube_iff_basepoint_and_reducedDiff (n := m + 1) (d := d) z).1 hz
  have hred : reducedDiffMap (m + 1) d z ∈ ReducedForwardTubeN d m := by
    simpa [ReducedForwardTubeN] using hz_split.2
  have hsafe : safeSection d m (reducedDiffMap (m + 1) d z) ∈ ForwardTube d (m + 1) :=
    safeSection_mem_forwardTube (d := d) m _ hred
  let c : Fin (d + 1) → ℂ := fun μ => z 0 μ - Complex.I * safeBasepointVec d μ
  have hshift :
      (fun k μ => safeSection d m (reducedDiffMap (m + 1) d z) k μ + c μ) = z := by
    ext k μ
    rw [safeSection]
    rw [reducedDiffSection_reducedDiffMap_eq_sub_basepoint (n := m + 1) (d := d) z]
    simp [safeUniformShift, c]
  have hshift_mem :
      (fun k μ => safeSection d m (reducedDiffMap (m + 1) d z) k μ + c μ) ∈
        ForwardTube d (m + 1) := by
    rw [hshift]
    exact hz
  have hEq := hF_trans (safeSection d m (reducedDiffMap (m + 1) d z)) c hsafe hshift_mem
  rw [hshift] at hEq
  simpa [descendAlongSafeSection] using hEq.symm

/-- Two absolute configurations with the same reduced difference coordinates
differ by a uniform translation. -/
theorem exists_uniformShift_eq_of_reducedDiffMap_eq
    {n : ℕ} [NeZero n]
    (z w : Fin n → Fin (d + 1) → ℂ)
    (hzw : reducedDiffMap n d z = reducedDiffMap n d w) :
    ∃ c : Fin (d + 1) → ℂ, w = fun k μ => z k μ + c μ := by
  let c : Fin (d + 1) → ℂ := fun μ => w 0 μ - z 0 μ
  refine ⟨c, ?_⟩
  ext k μ
  have hz :
      reducedDiffSection n d (reducedDiffMap n d z) k μ =
        z k μ - z 0 μ := by
    simpa using congrFun (congrFun
      (reducedDiffSection_reducedDiffMap_eq_sub_basepoint (n := n) (d := d) z) k) μ
  have hw :
      reducedDiffSection n d (reducedDiffMap n d w) k μ =
        w k μ - w 0 μ := by
    simpa using congrFun (congrFun
      (reducedDiffSection_reducedDiffMap_eq_sub_basepoint (n := n) (d := d) w) k) μ
  have hdiff : z k μ - z 0 μ = w k μ - w 0 μ := by
    calc
      z k μ - z 0 μ = reducedDiffSection n d (reducedDiffMap n d z) k μ := by simpa using hz.symm
      _ = reducedDiffSection n d (reducedDiffMap n d w) k μ := by rw [hzw]
      _ = w k μ - w 0 μ := hw
  calc
    w k μ = (w k μ - w 0 μ) + w 0 μ := by ring
    _ = (z k μ - z 0 μ) + w 0 μ := by rw [← hdiff]
    _ = z k μ + c μ := by
          dsimp [c]
          ring

/-- Distributional boundary values for an absolute `(m + 1)`-point holomorphic
function on the forward tube. -/
def HasAbsoluteBoundaryValues
    [NeZero d] (m : ℕ) (Wabs : SchwartzNPoint d (m + 1) → ℂ)
    (F : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ) : Prop :=
  ∀ (f : SchwartzNPoint d (m + 1)) (η : Fin (m + 1) → Fin (d + 1) → ℝ),
    InForwardCone d (m + 1) η →
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d (m + 1),
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wabs f))

/-- Absolute forward-tube witness data at public arity `m + 1` that Route 1
later descends to reduced arity `m`.

This is the concrete theorem surface exposed by `Wfn.spectrum_condition
(m + 1)` before any reduced-coordinate quotient step is taken. -/
structure AbsoluteForwardTubeInput
    [NeZero d] (m : ℕ) (Wabs : SchwartzNPoint d (m + 1) → ℂ) where
  toFun : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ
  holomorphic :
    DifferentiableOn ℂ toFun (ForwardTube d (m + 1))
  real_lorentz_invariant :
    ∀ (Λ : LorentzGroup d)
      (z : Fin (m + 1) → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d (m + 1) →
      toFun (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) = toFun z
  translation_invariant :
    IsForwardTubeTranslationInvariant d m toFun
  boundary_values :
    HasAbsoluteBoundaryValues (d := d) m Wabs toFun

private theorem bhwForwardTube_eq_rootForwardTube {d n : ℕ} [NeZero d] :
    ForwardTube d n = _root_.ForwardTube d n := by
  ext z
  simp only [ForwardTube]
  exact forall_congr' fun _ => inOpenForwardCone_iff _

/-- Canonical absolute forward-tube input at public arity `m + 1` extracted
from `Wfn.spectrum_condition (m + 1)`.

This remains on the public absolute-coordinate side. The reduced arity `m`
objects are obtained only later by descent. -/
noncomputable def spectrumConditionAbsoluteInput
    [NeZero d] (Wfn : WightmanFunctions d) (m : ℕ) :
    AbsoluteForwardTubeInput (d := d) m (Wfn.W (m + 1)) where
  toFun := (Wfn.spectrum_condition (m + 1)).choose
  holomorphic := by
    have hft_eq : ForwardTube d (m + 1) = _root_.ForwardTube d (m + 1) :=
      bhwForwardTube_eq_rootForwardTube (d := d) (n := m + 1)
    simpa [hft_eq] using (Wfn.spectrum_condition (m + 1)).choose_spec.1
  real_lorentz_invariant := by
    have hft_eq : ForwardTube d (m + 1) = _root_.ForwardTube d (m + 1) :=
      bhwForwardTube_eq_rootForwardTube (d := d) (n := m + 1)
    intro Λ z hz
    exact W_analytic_lorentz_on_tube (d := d) Wfn (m + 1) Λ z (hft_eq ▸ hz)
  translation_invariant := by
    have hft_eq : ForwardTube d (m + 1) = _root_.ForwardTube d (m + 1) :=
      bhwForwardTube_eq_rootForwardTube (d := d) (n := m + 1)
    intro z c hz hzc
    exact W_analytic_translation_on_forwardTube (d := d) (n := m + 1) Wfn c z
      (hft_eq ▸ hz) (hft_eq ▸ hzc)
  boundary_values := (Wfn.spectrum_condition (m + 1)).choose_spec.2

/-- Reduced real-Lorentz invariance on the reduced forward tube. This is the
part of the reduced symmetry that can already be descended directly from the
absolute forward-tube witness. -/
def IsReducedRealLorentzInvariantOnTube [NeZero d]
    (F : ReducedNPointConfig d m → ℂ) : Prop :=
  ∀ (Λ : LorentzGroup d) (η : ReducedNPointConfig d m),
    η ∈ ReducedForwardTubeN d m →
    complexLorentzAction
        (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup Λ)) η ∈
      ReducedForwardTubeN d m →
    F
        (complexLorentzAction
          (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup Λ)) η) =
      F η

/-- The part of the reduced forward-tube input that can be obtained immediately
from the absolute witness by safe-section descent, before solving the reduced
boundary-value and permutation-flow bridge. -/
structure ReducedForwardTubePreInput (d m : ℕ) [NeZero d] where
  toFun : ReducedNPointConfig d m → ℂ
  holomorphic :
    DifferentiableOn ℂ toFun (ReducedForwardTubeN d m)
  real_lorentz_invariant :
    IsReducedRealLorentzInvariantOnTube (d := d) (m := m) toFun

private theorem safeSection_differentiable (d m : ℕ) :
    Differentiable ℂ (fun η : ReducedNPointConfig d m => safeSection d m η) := by
  change Differentiable ℂ
    (fun η : ReducedNPointConfig d m =>
      (reducedDiffSection (m + 1) d) η + safeUniformShift d m)
  have hconst : Differentiable ℂ
      (fun _ : ReducedNPointConfig d m => safeUniformShift d m) := by
    simpa using
      (differentiable_const : Differentiable ℂ
        (fun _ : ReducedNPointConfig d m => safeUniformShift d m))
  exact (reducedDiffSection (m + 1) d).differentiable.add hconst

/-- Descend an absolute forward-tube witness to reduced coordinates via the
safe section. This packages the reduced holomorphic function together with the
real Lorentz covariance that follows from absolute covariance plus translation
absorption. -/
noncomputable def descendAbsoluteForwardTubeInput
    [NeZero d] {Wabs : SchwartzNPoint d (m + 1) → ℂ}
    (hAbs : AbsoluteForwardTubeInput (d := d) m Wabs) :
    ReducedForwardTubePreInput d m where
  toFun := descendAlongSafeSection d m hAbs.toFun
  holomorphic := by
    have hsec :
        DifferentiableOn ℂ (safeSection d m) (ReducedForwardTubeN d m) :=
      (safeSection_differentiable d m).differentiableOn
    refine DifferentiableOn.comp hAbs.holomorphic hsec ?_
    intro η hη
    exact safeSection_mem_forwardTube (d := d) m η hη
  real_lorentz_invariant := by
    show IsReducedRealLorentzInvariantOnTube (d := d) (m := m)
      (descendAlongSafeSection d m hAbs.toFun)
    intro Λ η hη hΛη
    let Λc : ComplexLorentzGroup d :=
      ComplexLorentzGroup.ofReal (wightmanToLorentzGroup Λ)
    let z₁ : Fin (m + 1) → Fin (d + 1) → ℂ :=
      safeSection d m (complexLorentzAction Λc η)
    let z₂ : Fin (m + 1) → Fin (d + 1) → ℂ :=
      complexLorentzAction Λc (safeSection d m η)
    have hz₁ : z₁ ∈ ForwardTube d (m + 1) := by
      exact safeSection_mem_forwardTube (d := d) m _ hΛη
    have hz₂ : z₂ ∈ ForwardTube d (m + 1) := by
      haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      rw [mem_forwardTube_iff_basepoint_and_reducedDiff]
      constructor
      · have hbase :
            (fun μ => (z₂ 0 μ).im) =
              fun μ => ∑ ν, Λ.val μ ν * safeBasepointVec d ν := by
          ext μ
          calc
            (z₂ 0 μ).im
                = ∑ ν, Λ.val μ ν * (safeSection d m η 0 ν).im := by
                    simpa [z₂, complexLorentzAction] using
                      ofReal_im_action (wightmanToLorentzGroup Λ)
                        (fun ν => safeSection d m η 0 ν) μ
            _ = ∑ ν, Λ.val μ ν * safeBasepointVec d ν := by
                  have hzero : ∀ ν : Fin (d + 1),
                      ((reducedDiffSection (m + 1) d η 0 ν).im) = 0 := by
                    intro ν
                    have hz0 : reducedDiffSection (m + 1) d η 0 ν = 0 := by
                      simpa using reducedDiffSection_zero (n := m + 1) (d := d) η ν
                    rw [hz0]
                    simp
                  calc
                    ∑ x, Λ.val μ x * (safeSection d m η 0 x).im
                        = ∑ x, Λ.val μ x * (((reducedDiffSection (m + 1) d η 0 x).im) +
                            safeBasepointVec d x) := by
                              simp [safeSection, safeUniformShift]
                    _ = ∑ x, Λ.val μ x * (0 + safeBasepointVec d x) := by
                          congr with x
                          rw [hzero x]
                    _ = ∑ ν, Λ.val μ ν * safeBasepointVec d ν := by
                          simp
        rw [hbase]
        exact (inOpenForwardCone_iff _).2 <|
          orthochronous_preserves_forward_cone Λ (LorentzGroup.zero_zero_ge_one Λ)
            (safeBasepointVec d)
            ((inOpenForwardCone_iff _).1 (safeBasepointVec_mem_forwardCone (d := d)))
      · have hz₂red :
            reducedDiffMap (m + 1) d z₂ =
              complexLorentzAction Λc η := by
          have hact := reducedDiffMap_action (n := m + 1) (d := d)
              Λc (safeSection d m η)
          rw [reducedDiffMap_safeSection] at hact
          simpa [z₂] using hact
        rw [hz₂red]
        exact hΛη
    have hred_eq :
        reducedDiffMap (m + 1) d z₂ = reducedDiffMap (m + 1) d z₁ := by
      calc
        reducedDiffMap (m + 1) d z₂
            = complexLorentzAction Λc η := by
                have hact := reducedDiffMap_action (n := m + 1) (d := d)
                    Λc (safeSection d m η)
                rw [reducedDiffMap_safeSection] at hact
                simpa [z₂] using hact
        _ = reducedDiffMap (m + 1) d z₁ := by
              simpa [z₁] using (reducedDiffMap_safeSection (d := d) (m := m)
                (complexLorentzAction Λc η)).symm
    obtain ⟨c, hc⟩ := exists_uniformShift_eq_of_reducedDiffMap_eq
      (d := d) (n := m + 1) z₂ z₁ hred_eq
    have hzsafe : safeSection d m η ∈ ForwardTube d (m + 1) :=
      safeSection_mem_forwardTube (d := d) m η hη
    calc
      descendAlongSafeSection d m hAbs.toFun
          (complexLorentzAction Λc η)
          = hAbs.toFun z₁ := rfl
      _ = hAbs.toFun z₂ := by
            rw [hc]
            exact hAbs.translation_invariant z₂ c hz₂ (hc ▸ hz₁)
      _ = hAbs.toFun (safeSection d m η) := by
            simpa [z₂, Λc, complexLorentzAction] using
              hAbs.real_lorentz_invariant Λ (safeSection d m η) hzsafe
      _ = descendAlongSafeSection d m hAbs.toFun η := rfl

/-- The descended reduced preinput agrees with the absolute witness on the
forward tube after passing through `reducedDiffMap`. -/
theorem descendAbsoluteForwardTubeInput_factorization
    [NeZero d] {Wabs : SchwartzNPoint d (m + 1) → ℂ}
    (hAbs : AbsoluteForwardTubeInput (d := d) m Wabs)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (m + 1)) :
    (descendAbsoluteForwardTubeInput (d := d) (m := m) hAbs).toFun
        (reducedDiffMap (m + 1) d z) = hAbs.toFun z := by
  exact descendAlongSafeSection_eq_of_translation_invariant
    (d := d) m hAbs.toFun hAbs.translation_invariant z hz

/-- Concrete Route 1 reduced preinput obtained by descending the spectrum
condition witness at absolute arity `m + 1`. -/
noncomputable def route1ReducedPreInputFromSpectrumCondition
    [NeZero d] (Wfn : WightmanFunctions d) (m : ℕ) :
    ReducedForwardTubePreInput d m :=
  descendAbsoluteForwardTubeInput (d := d) (m := m)
    (spectrumConditionAbsoluteInput (d := d) Wfn m)

/-- The concrete spectrum-condition witness factors through reduced difference
coordinates on the absolute forward tube. -/
theorem route1ReducedPreInputFromSpectrumCondition_factorization
    [NeZero d] (Wfn : WightmanFunctions d) (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (m + 1)) :
    (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
        (reducedDiffMap (m + 1) d z) =
      (Wfn.spectrum_condition (m + 1)).choose z := by
  exact descendAbsoluteForwardTubeInput_factorization
    (d := d) (m := m) (spectrumConditionAbsoluteInput (d := d) Wfn m) z hz

/-- Promote a reduced product-cone direction to a full `(m + 1)`-tuple of
difference coordinates by inserting a future-timelike basepoint direction in
the zeroth slot. -/
def liftReducedDirection (d m : ℕ) :
    (Fin m → Fin (d + 1) → ℝ) → Fin (m + 1) → Fin (d + 1) → ℝ :=
  fun η k =>
    if hk : k.val = 0 then safeBasepointVec d
    else η ⟨k.val - 1, by omega⟩

@[simp] theorem liftReducedDirection_zero (d m : ℕ)
    (η : Fin m → Fin (d + 1) → ℝ) :
    liftReducedDirection d m η 0 = safeBasepointVec d := by
  ext μ
  simp [liftReducedDirection]

@[simp] theorem liftReducedDirection_succ (d m : ℕ)
    (η : Fin m → Fin (d + 1) → ℝ) (j : Fin m) :
    liftReducedDirection d m η j.succ = η j := by
  ext μ
  simp [liftReducedDirection]

/-- The lifted reduced direction is a full product-cone direction. -/
theorem liftReducedDirection_mem_productForwardConeReal
    [NeZero d] (m : ℕ) (η : Fin m → Fin (d + 1) → ℝ)
    (hη : η ∈ ProductForwardConeReal d m) :
    liftReducedDirection d m η ∈ ProductForwardConeReal d (m + 1) := by
  intro k
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    simpa using safeBasepointVec_mem_forwardCone (d := d)
  · let j : Fin m := ⟨k.val - 1, by omega⟩
    have hk_eq : k = j.succ := by
      ext
      simp [j]
      omega
    rw [hk_eq]
    simpa using hη j

/-- Purely imaginary configurations detect the absolute forward-cone condition
exactly. This is a bookkeeping bridge between the difference-coordinate and
Wightman forward-tube conventions. -/
theorem pureImag_mem_forwardTube_iff
    [NeZero d] {n : ℕ} (η : Fin n → Fin (d + 1) → ℝ) :
    (fun k μ => (η k μ : ℂ) * Complex.I) ∈ ForwardTube d n ↔
      InForwardCone d n η := by
  rw [bhwForwardTube_eq_rootForwardTube, forwardTube_eq_imPreimage,
    Set.mem_setOf_eq, inForwardCone_iff_mem_forwardConeAbs]
  simp

/-- On purely imaginary real data, the complex difference-coordinate chart is
the real chart tensored with `i`. -/
theorem diffCoordEquiv_pureImag
    {n : ℕ} (d : ℕ) (x : Fin n → Fin (d + 1) → ℝ) :
    diffCoordEquiv n d (fun k μ => (x k μ : ℂ) * Complex.I) =
      fun k μ => (realDiffCoordCLE n d x k μ : ℂ) * Complex.I := by
  ext k μ
  by_cases hk : k.val = 0
  · simp [diffCoordEquiv_apply, realDiffCoordCLE_apply, hk]
  · simp [diffCoordEquiv_apply, realDiffCoordCLE_apply, hk]
    ring

/-- The absolute approach direction obtained by partial summing a lifted reduced
product-cone direction satisfies the ordinary absolute forward-cone condition. -/
def absoluteDirectionOfReduced
    (d m : ℕ) (η : Fin m → Fin (d + 1) → ℝ) :
    Fin (m + 1) → Fin (d + 1) → ℝ :=
  (realDiffCoordCLE (m + 1) d).symm (liftReducedDirection d m η)

theorem absoluteDirectionOfReduced_mem_forwardCone
    [NeZero d] (m : ℕ) (η : Fin m → Fin (d + 1) → ℝ)
    (hη : η ∈ ProductForwardConeReal d m) :
    InForwardCone d (m + 1) (absoluteDirectionOfReduced d m η) := by
  have hlift : liftReducedDirection d m η ∈ ProductForwardConeReal d (m + 1) :=
    liftReducedDirection_mem_productForwardConeReal (d := d) m η hη
  have hprod :
      (fun k μ => (((liftReducedDirection d m η) k μ : ℂ) * Complex.I)) ∈
        ProductForwardCone d (m + 1) := by
    intro k
    simpa using hlift k
  have hpure :
      (fun k μ => ((absoluteDirectionOfReduced d m η) k μ : ℂ) * Complex.I) ∈
        ForwardTube d (m + 1) := by
    rw [forwardTube_eq_diffCoord_preimage (n := m + 1) (d := d)]
    change diffCoordEquiv (m + 1) d
        (fun k μ => ((absoluteDirectionOfReduced d m η) k μ : ℂ) * Complex.I) ∈
      ProductForwardCone d (m + 1)
    rw [diffCoordEquiv_pureImag (d := d)]
    have hcoord :
        realDiffCoordCLE (m + 1) d (absoluteDirectionOfReduced d m η) =
          liftReducedDirection d m η := by
      simpa [absoluteDirectionOfReduced] using
        (realDiffCoordCLE (m + 1) d).apply_symm_apply (liftReducedDirection d m η)
    rw [hcoord]
    exact hprod
  exact (pureImag_mem_forwardTube_iff
    (η := absoluteDirectionOfReduced d m η)).1 hpure

/-- Full real difference coordinates with a chosen real basepoint in slot `0`
and reduced variables in the remaining slots. -/
def prependBasepointReal (d m : ℕ) :
    SpacetimeDim d → (Fin m → Fin (d + 1) → ℝ) →
      Fin (m + 1) → Fin (d + 1) → ℝ :=
  fun x₀ ξ k =>
    if hk : k.val = 0 then x₀
    else ξ ⟨k.val - 1, by omega⟩

@[simp] theorem prependBasepointReal_zero (d m : ℕ)
    (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) :
    prependBasepointReal d m x₀ ξ 0 = x₀ := by
  ext μ
  simp [prependBasepointReal]

@[simp] theorem prependBasepointReal_succ (d m : ℕ)
    (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) (j : Fin m) :
    prependBasepointReal d m x₀ ξ j.succ = ξ j := by
  ext μ
  simp [prependBasepointReal]

@[simp] theorem realDiffCoordCLE_symm_prependBasepointReal_zero (d m : ℕ)
    (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) :
    (realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ) 0 = x₀ := by
  ext μ
  have h :=
    congrFun
      (congrFun
        ((realDiffCoordCLE (m + 1) d).apply_symm_apply
          (prependBasepointReal d m x₀ ξ)) 0) μ
  simpa [realDiffCoordCLE_apply, prependBasepointReal] using h

@[simp] theorem reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
    (d m : ℕ) (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) :
    reducedDiffMapReal (m + 1) d
      ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)) = ξ := by
  ext j μ
  change
    (realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
        ⟨j.val + 1, by omega⟩ μ -
      (realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
        ⟨j.val, by omega⟩ μ = ξ j μ
  have h :=
    congrFun
      (congrFun
        ((realDiffCoordCLE (m + 1) d).apply_symm_apply
          (prependBasepointReal d m x₀ ξ)) j.succ) μ
  simpa [realDiffCoordCLE_apply, prependBasepointReal] using h

@[simp] theorem absoluteDirectionOfReduced_zero (d m : ℕ)
    (η : Fin m → Fin (d + 1) → ℝ) :
    absoluteDirectionOfReduced d m η 0 = safeBasepointVec d := by
  ext μ
  have h :=
    congrFun
      (congrFun
        ((realDiffCoordCLE (m + 1) d).apply_symm_apply
          (liftReducedDirection d m η)) 0) μ
  simpa [absoluteDirectionOfReduced, realDiffCoordCLE_apply, liftReducedDirection] using h

@[simp] theorem reducedDiffMapReal_absoluteDirectionOfReduced (d m : ℕ)
    (η : Fin m → Fin (d + 1) → ℝ) :
    reducedDiffMapReal (m + 1) d (absoluteDirectionOfReduced d m η) = η := by
  ext j μ
  change
    absoluteDirectionOfReduced d m η ⟨j.val + 1, by omega⟩ μ -
      absoluteDirectionOfReduced d m η ⟨j.val, by omega⟩ μ = η j μ
  have h :=
    congrFun
      (congrFun
        ((realDiffCoordCLE (m + 1) d).apply_symm_apply
          (liftReducedDirection d m η)) j.succ) μ
  simpa [absoluteDirectionOfReduced, realDiffCoordCLE_apply, liftReducedDirection] using h

/-- The absolute complex approach point corresponding to a real basepoint
parameter `x₀`, reduced real coordinate `ξ`, reduced cone direction `η`, and
imaginary scale `ε > 0`. -/
def absoluteApproachOfReduced (d m : ℕ)
    (x₀ : SpacetimeDim d) (ξ η : Fin m → Fin (d + 1) → ℝ) (ε : ℝ) :
    Fin (m + 1) → Fin (d + 1) → ℂ :=
  fun k μ =>
    (((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ) k μ : ℂ) +
      ε * (absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I)

@[simp] theorem reducedDiffMap_absoluteApproachOfReduced
    (d m : ℕ) (x₀ : SpacetimeDim d)
    (ξ η : Fin m → Fin (d + 1) → ℝ) (ε : ℝ) :
    reducedDiffMap (m + 1) d (absoluteApproachOfReduced d m x₀ ξ η ε) =
      (fun j μ => (ξ j μ : ℂ) + ε * (η j μ : ℂ) * Complex.I) := by
  ext j μ
  change
    absoluteApproachOfReduced d m x₀ ξ η ε ⟨j.val + 1, by omega⟩ μ -
      absoluteApproachOfReduced d m x₀ ξ η ε ⟨j.val, by omega⟩ μ =
    (ξ j μ : ℂ) + ε * (η j μ : ℂ) * Complex.I
  have hξ :
      (realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
          ⟨j.val + 1, by omega⟩ μ -
        (realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
          ⟨j.val, by omega⟩ μ =
      ξ j μ := by
    simpa [reducedDiffMapReal_apply] using
      congrFun
        (congrFun
          (reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
            (d := d) (m := m) x₀ ξ) j) μ
  have hη :
      absoluteDirectionOfReduced d m η ⟨j.val + 1, by omega⟩ μ -
        absoluteDirectionOfReduced d m η ⟨j.val, by omega⟩ μ =
      η j μ := by
    simpa [reducedDiffMapReal_apply] using
      congrFun
        (congrFun
          (reducedDiffMapReal_absoluteDirectionOfReduced (d := d) (m := m) η) j) μ
  have hξ' :
      (((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
        ⟨j.val + 1, by omega⟩ μ : ℂ) -
      ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
        ⟨j.val, by omega⟩ μ : ℂ)) = ξ j μ := by
    exact_mod_cast hξ
  have hη' :
      ((absoluteDirectionOfReduced d m η ⟨j.val + 1, by omega⟩ μ : ℂ) -
        (absoluteDirectionOfReduced d m η ⟨j.val, by omega⟩ μ : ℂ)) = η j μ := by
    exact_mod_cast hη
  calc
    absoluteApproachOfReduced d m x₀ ξ η ε ⟨j.val + 1, by omega⟩ μ -
        absoluteApproachOfReduced d m x₀ ξ η ε ⟨j.val, by omega⟩ μ
      = (((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
            ⟨j.val + 1, by omega⟩ μ : ℂ) -
          ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)
            ⟨j.val, by omega⟩ μ : ℂ)) +
        ε * (((absoluteDirectionOfReduced d m η ⟨j.val + 1, by omega⟩ μ : ℂ) -
          (absoluteDirectionOfReduced d m η ⟨j.val, by omega⟩ μ : ℂ)) * Complex.I) := by
            simp [absoluteApproachOfReduced]
            ring
    _ = (ξ j μ : ℂ) + ε * ((η j μ : ℂ) * Complex.I) := by
          rw [hξ', hη']
    _ = (ξ j μ : ℂ) + ε * (η j μ : ℂ) * Complex.I := by
          ring

theorem absoluteApproachOfReduced_mem_forwardTube
    [NeZero d] (m : ℕ) (x₀ : SpacetimeDim d)
    (ξ η : Fin m → Fin (d + 1) → ℝ)
    (hη : η ∈ ProductForwardConeReal d m) {ε : ℝ} (hε : 0 < ε) :
    absoluteApproachOfReduced d m x₀ ξ η ε ∈ ForwardTube d (m + 1) := by
  rw [mem_forwardTube_iff_basepoint_and_reducedDiff]
  constructor
  · have hbase :
        (fun μ => (absoluteApproachOfReduced d m x₀ ξ η ε 0 μ).im) =
          ε • safeBasepointVec d := by
      ext μ
      simp [absoluteApproachOfReduced, absoluteDirectionOfReduced_zero, Pi.smul_apply]
    rw [hbase]
    exact inOpenForwardCone_smul_pos (safeBasepointVec_mem_forwardCone (d := d)) hε
  · rw [reducedDiffMap_absoluteApproachOfReduced]
    intro j
    have hj : InOpenForwardCone d (ε • η j) :=
      inOpenForwardCone_smul_pos (hη j) hε
    simpa [ReducedForwardTube, ReducedForwardCone, ProductForwardCone, Pi.smul_apply,
      Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] using hj

theorem route1ReducedPreInputFromSpectrumCondition_factorization_absoluteApproach
    [NeZero d] (Wfn : WightmanFunctions d) (m : ℕ)
    (x₀ : SpacetimeDim d) (ξ η : Fin m → Fin (d + 1) → ℝ)
    (hη : η ∈ ProductForwardConeReal d m) {ε : ℝ} (hε : 0 < ε) :
    (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
        (fun j μ => (ξ j μ : ℂ) + ε * (η j μ : ℂ) * Complex.I) =
      (Wfn.spectrum_condition (m + 1)).choose
        (absoluteApproachOfReduced d m x₀ ξ η ε) := by
  have hz :
      absoluteApproachOfReduced d m x₀ ξ η ε ∈ ForwardTube d (m + 1) :=
    absoluteApproachOfReduced_mem_forwardTube (d := d) m x₀ ξ η hη hε
  have hred := reducedDiffMap_absoluteApproachOfReduced (d := d) (m := m) x₀ ξ η ε
  have hfact := route1ReducedPreInputFromSpectrumCondition_factorization
    (d := d) Wfn m (absoluteApproachOfReduced d m x₀ ξ η ε) hz
  rw [hred] at hfact
  exact hfact

theorem reducedTestLift_apply_realDiffCoordCLE_symm_prependBasepointReal
    (m d : ℕ) (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m) (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) :
    reducedTestLift m d χ φ
        ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)) =
      χ x₀ * φ ξ := by
  rw [reducedTestLift_apply]
  rw [realDiffCoordCLE_symm_prependBasepointReal_zero]
  rw [reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal]

/-- Distributional boundary values for a reduced `m`-variable holomorphic
function on the reduced forward tube. This is the reduced analogue of the
`spectrum_condition` boundary-value clause in `WightmanFunctions`, but now the
test functions and approach directions already live in the quotient space.

Unlike absolute coordinates, the reduced forward tube is a product tube:
each reduced difference variable independently approaches through `V₊`.
Therefore the reduced boundary directions are indexed by
`ProductForwardConeReal d m`, not by the successive-difference predicate
`InForwardCone d m`. -/
def HasReducedBoundaryValues
    [NeZero d] (Wred : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (m : ℕ) (F : ReducedNPointConfig d m → ℂ) : Prop :=
  ∀ (f : SchwartzNPoint d m) (η : Fin m → Fin (d + 1) → ℝ),
    η ∈ ProductForwardConeReal d m →
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d m,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wred m f))

/-- Reduced analytic input datum at reduced arity `m`: a holomorphic function
on the reduced forward tube together with reduced Lorentz symmetry and the
reduced distributional boundary-value theorem it must satisfy. Local
commutativity / permutation-flow data belongs to the reduced BHW step and is
therefore not stored here. This is the natural Route 1 replacement for the
absolute `spectrum_condition` witness. -/
structure ReducedForwardTubeInput
    [NeZero d] (Wred : (m : ℕ) → SchwartzNPoint d m → ℂ) (m : ℕ) where
  toFun : ReducedNPointConfig d m → ℂ
  holomorphic :
    DifferentiableOn ℂ toFun (ReducedForwardTubeN d m)
  real_lorentz_invariant :
    IsReducedRealLorentzInvariantOnTube (d := d) (m := m) toFun
  boundary_values :
    HasReducedBoundaryValues (d := d) Wred m toFun

/-- Specialized Route 1 reduced analytic datum built against the canonical
reduced Wightman family descended from the public literal `(m + 1)`-point
data of `Wfn` using a normalized cutoff. -/
abbrev Route1ReducedAnalyticInput
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :=
  ReducedForwardTubeInput (route1ReducedWightmanFamily Wfn χ) m

/-- If the descended reduced preinput satisfies the reduced boundary-value
theorem, it upgrades immediately to the bundled reduced forward-tube input that
Route 1 needs. -/
def route1ReducedInputOfBoundary
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (hBv : HasReducedBoundaryValues (d := d)
      (route1ReducedWightmanFamily Wfn χ) m
      (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun) :
    Route1ReducedAnalyticInput Wfn χ m where
  toFun := (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
  holomorphic := (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).holomorphic
  real_lorentz_invariant :=
    (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).real_lorentz_invariant
  boundary_values := hBv

/-- Reduced-coordinate Bargmann-Hall-Wightman bridge.

This is the quotient-space form of the ordinary BHW theorem: starting from a
holomorphic reduced forward-tube input with reduced real Lorentz covariance and
the correct reduced boundary values, produce a unique holomorphic extension on
the reduced permuted extended tube, together with reduced Lorentz and
permutation invariance.

The intended future discharge is to derive this from the absolute BHW theorem
plus translation descent:
1. apply absolute BHW on absolute configurations,
2. prove the absolute extension is constant on fibers of `reducedDiffMap`,
3. descend through the translation quotient,
4. identify the descended domain with `ReducedPermutedExtendedTubeN`,
5. transport Lorentz invariance, permutation invariance, and uniqueness.

Part of that bridge already exists in production:
- `AbsoluteForwardTubeInput`,
- `descendAbsoluteForwardTubeInput`,
- `route1ReducedBoundaryValuesFromSpectrumCondition`.

What is still missing is the generic PET-level quotient descent, or an inverse
bridge lifting generic reduced input back to an absolute BHW input while
preserving the boundary-value theorem.

Numerical diagnostics were run as sanity checks for the reduced geometry behind
this axiom. In randomized low-dimensional samples they confirmed:
- uniform translations are invisible to `reducedDiffMap`,
- `reducedDiffSection` is a right inverse,
- `safeSection` lands in the absolute forward tube,
- reduced permutation actions agree with absolute permutation followed by
  quotienting,
- adjacent transpositions match the expected `A_(n-1)` formulas.

The most informative negative test also behaved as expected: naive evaluation on
an arbitrary absolute representative is not well-defined unless the absolute
function is already translation-invariant.

These diagnostics support the quotient/permutation scaffolding but do not prove
holomorphic extension, edge-of-the-wedge continuation, permutation invariance
from locality, or uniqueness. We therefore keep the bridge axiomatic for now. -/
axiom reduced_bargmann_hall_wightman_of_input
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ∃ (F_ext : ReducedNPointConfig d m → ℂ),
      DifferentiableOn ℂ F_ext (ReducedPermutedExtendedTubeN d m) ∧
      (∀ η ∈ ReducedForwardTubeN d m, F_ext η = hInput.toFun η) ∧
      IsReducedLorentzInvariant (d := d) (n := m + 1) F_ext ∧
      IsReducedPermutationInvariant (d := d) (n := m + 1) F_ext ∧
      (∀ (G : ReducedNPointConfig d m → ℂ),
        DifferentiableOn ℂ G (ReducedPermutedExtendedTubeN d m) →
        (∀ η ∈ ReducedForwardTubeN d m, G η = hInput.toFun η) →
        ∀ η ∈ ReducedPermutedExtendedTubeN d m, G η = F_ext η)

/-- Chosen reduced BHW extension associated to a bundled reduced forward-tube
datum. -/
noncomputable def W_analytic_BHW_reduced_of_input
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ReducedBHWExtensionData (d := d) (n := m + 1) hInput.toFun := by
  let h := reduced_bargmann_hall_wightman_of_input (d := d) Wfn χ m hInput
  exact
    { toFun := h.choose
      holomorphic := by
        simpa [ReducedPermutedExtendedTubeN] using h.choose_spec.1
      agrees_on_reducedForwardTube := by
        simpa [ReducedForwardTubeN] using h.choose_spec.2.1
      lorentz_invariant := h.choose_spec.2.2.1
      perm_invariant := h.choose_spec.2.2.2.1 }

/-- Uniqueness of the chosen reduced BHW extension associated to a bundled
reduced forward-tube datum. -/
theorem W_analytic_BHW_reduced_of_input_unique
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m)
    (G : ReducedNPointConfig d m → ℂ)
    (hG_holo : DifferentiableOn ℂ G (ReducedPermutedExtendedTubeN d m))
    (hG_eq : ∀ η ∈ ReducedForwardTubeN d m, G η = hInput.toFun η) :
    ∀ η ∈ ReducedPermutedExtendedTubeN d m,
      G η = (W_analytic_BHW_reduced_of_input (d := d) Wfn χ hInput).toFun η := by
  let h := reduced_bargmann_hall_wightman_of_input (d := d) Wfn χ m hInput
  have hchosen :
      (W_analytic_BHW_reduced_of_input (d := d) Wfn χ hInput).toFun = h.choose := by
    rfl
  intro η hη
  rw [hchosen]
  exact h.choose_spec.2.2.2.2 G hG_holo hG_eq η hη

/-- Chosen reduced BHW extension in the Route 1 setting, built from a reduced
analytic datum for the canonical reduced Wightman family. -/
noncomputable def route1ReducedBHWExtension
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ReducedBHWExtensionData (d := d) (n := m + 1) hInput.toFun :=
  W_analytic_BHW_reduced_of_input (d := d) Wfn χ hInput

/-- The Route 1 absolute extension obtained by pulling a bundled reduced
analytic datum back along `reducedDiffMap`. This is the form that should later
replace the old absolute translation proof backend. -/
noncomputable def route1AbsoluteBHWExtension
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  pullbackReducedExtension (d := d) (n := m + 1)
    (route1ReducedBHWExtension (d := d) Wfn χ hInput).toFun

@[simp] theorem route1AbsoluteBHWExtension_apply
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    route1AbsoluteBHWExtension (d := d) Wfn χ hInput z =
      (route1ReducedBHWExtension (d := d) Wfn χ hInput).toFun
        (reducedDiffMap (m + 1) d z) := by
  rfl

/-- Final Route 1 translation invariance wrapper for a bundled reduced analytic
input. This is the theorem shape the old overlap-connectedness proof should be
replaced by once the reduced analytic input is instantiated. -/
theorem route1AbsoluteBHWExtension_translate
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    route1AbsoluteBHWExtension (d := d) Wfn χ hInput
        (fun k μ => z k μ + c μ) =
      route1AbsoluteBHWExtension (d := d) Wfn χ hInput z := by
  exact reduced_pullback_translation_invariant (d := d) (n := m + 1)
    (route1ReducedBHWExtension (d := d) Wfn χ hInput).toFun z c

/-- Backward shift on `Fin n`-indexed tuples: sends index `k` to the value at
    index `k - 1`, with index `0` mapping to `0`. -/
private def backwardShiftLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin n → Fin (d + 1) → ℝ) where
  toFun x k μ := if k.val = 0 then 0 else x ⟨k.val - 1, by omega⟩ μ
  map_add' x y := by ext k μ; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r x := by
    ext k μ; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

private theorem realDiffCoord_eq_id_sub_backwardShift (n d : ℕ) :
    (realDiffCoordLinearEquiv n d).toLinearMap = LinearMap.id - backwardShiftLM n d := by
  apply LinearMap.ext; intro x; funext k μ
  simp only [LinearEquiv.coe_toLinearMap, LinearMap.sub_apply, LinearMap.id_apply,
    backwardShiftLM, LinearMap.coe_mk, AddHom.coe_mk]
  show realDiffCoordFun n d x k μ = x k μ - (if k.val = 0 then 0 else x ⟨k.val - 1, _⟩ μ)
  simp only [realDiffCoordFun]
  by_cases hk : k.val = 0 <;> simp [hk]

private theorem backwardShiftLM_pow_apply (n d : ℕ) :
    ∀ (m : ℕ) (x : Fin n → Fin (d + 1) → ℝ) (k : Fin n) (μ : Fin (d + 1)),
    (backwardShiftLM n d ^ m) x k μ =
      if k.val < m then 0 else x ⟨k.val - m, by omega⟩ μ := by
  intro m
  induction m with
  | zero => intro x k μ; simp
  | succ m ih =>
    intro x k μ
    -- f^(m+1) = f^m * f definitionally, so (f^(m+1)) x = f^m (f x)
    show (backwardShiftLM n d ^ m) (backwardShiftLM n d x) k μ = _
    rw [ih]
    simp only [backwardShiftLM, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hkm : k.val < m
    · simp [hkm, show k.val < m + 1 from by omega]
    · push_neg at hkm
      simp only [show ¬(k.val < m) from by omega, ↓reduceIte]
      by_cases hkm1 : k.val - m = 0
      · simp [hkm1, show k.val < m + 1 from by omega]
      · simp only [hkm1, ↓reduceIte, show ¬(k.val < m + 1) from by omega,
          show k.val - m - 1 = k.val - (m + 1) from by omega]

private theorem backwardShiftLM_isNilpotent (n d : ℕ) :
    IsNilpotent (backwardShiftLM n d) := by
  refine ⟨n, ?_⟩
  apply LinearMap.ext; intro x; funext k μ
  simp only [LinearMap.zero_apply, Pi.zero_apply]
  rw [backwardShiftLM_pow_apply, if_pos k.isLt]

private theorem realDiffCoord_det_eq_one (n d : ℕ) :
    LinearMap.det (realDiffCoordLinearEquiv n d).toLinearMap = 1 := by
  rw [realDiffCoord_eq_id_sub_backwardShift]
  have h_alg : LinearMap.id - backwardShiftLM n d =
      algebraMap ℝ (Module.End ℝ _) 1 - backwardShiftLM n d := by
    congr 1; ext; simp [Algebra.algebraMap_eq_smul_one]
  rw [h_alg, ← LinearMap.eval_charpoly (backwardShiftLM n d) 1,
    (backwardShiftLM_isNilpotent n d).charpoly_eq_X_pow_finrank]
  simp

/-- The partial-sum operator `(realDiffCoordCLE n d).symm` preserves Lebesgue
volume. Its matrix (in any standard basis ordering) is lower-triangular with
all-ones diagonal, so `|det| = 1` and the measure-theoretic Jacobian is `1`. -/
theorem realDiffCoordCLE_symm_measurePreserving (n d : ℕ) :
    MeasureTheory.MeasurePreserving
      (⇑(realDiffCoordCLE n d).symm)
      MeasureTheory.volume MeasureTheory.volume := by
  constructor
  · exact (realDiffCoordCLE n d).symm.continuous.measurable
  · have h_det := realDiffCoord_det_eq_one n d
    ext s hs
    rw [MeasureTheory.Measure.map_apply
      ((realDiffCoordCLE n d).symm.continuous.measurable) hs]
    change MeasureTheory.volume ((realDiffCoordLinearEquiv n d).symm ⁻¹' s) =
      MeasureTheory.volume s
    rw [MeasureTheory.Measure.addHaar_preimage_linearEquiv MeasureTheory.volume
      (realDiffCoordLinearEquiv n d).symm s, LinearEquiv.symm_symm]
    simp [h_det]

/-- `prependBasepointReal` agrees with Mathlib's `Fin.cons`. -/
theorem prependBasepointReal_eq_finCons (d m : ℕ)
    (x₀ : SpacetimeDim d) (ξ : Fin m → Fin (d + 1) → ℝ) :
    prependBasepointReal d m x₀ ξ = Fin.cons x₀ ξ := by
  ext ⟨k, hk⟩ μ
  simp only [prependBasepointReal]
  rcases k with _ | k
  · simp [Fin.cons]
  · simp [Fin.cons]

/-- Integrating over absolute real coordinates is equivalent to changing
variables to the real full-difference chart, whose Jacobian is `1`, and then
splitting the integral into basepoint and reduced-difference variables. -/
theorem integral_realDiffCoord_change_variables
    [NeZero d] (m : ℕ) (G : NPointDomain d (m + 1) → ℂ)
    (hG : MeasureTheory.Integrable G) :
    ∫ x, G x =
      ∫ ξ : NPointDomain d m, ∫ x₀ : SpacetimeDim d,
        G ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)) := by
  -- Step 1: Change variables by CLE.symm (volume-preserving, det = 1)
  let eCLE := (realDiffCoordCLE (m + 1) d).symm.toHomeomorph.toMeasurableEquiv
  have h_mp_cle : MeasureTheory.MeasurePreserving eCLE
      MeasureTheory.volume MeasureTheory.volume := by
    have := realDiffCoordCLE_symm_measurePreserving (m + 1) d
    convert this using 1
  set H := fun y => G (eCLE y) with hH_def
  have h1 : ∫ x, G x = ∫ y, H y :=
    (h_mp_cle.integral_comp' (g := G)).symm
  -- Step 2: Split Fin (m+1) → V into V × (Fin m → V) via piFinSuccAbove
  let eSplit := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (m + 1) => Fin (d + 1) → ℝ) 0
  have h_mp_split : MeasureTheory.MeasurePreserving eSplit
      MeasureTheory.volume
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    simpa [eSplit] using MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => Fin (d + 1) → ℝ) 0
  -- Step 3: Integrability on the product space
  have hH_int : MeasureTheory.Integrable H := by
    exact (h_mp_cle.integrable_comp_emb eCLE.measurableEmbedding (g := G)).mpr hG
  have hH_pair_int : MeasureTheory.Integrable
      (fun p : SpacetimeDim d × NPointDomain d m => H (Fin.cons p.1 p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hiff := h_mp_split.symm.integrable_comp_emb
      eSplit.symm.measurableEmbedding (g := H)
    simpa [eSplit, MeasurableEquiv.piFinSuccAbove_symm_apply] using hiff.2 hH_int
  -- Step 4: Fubini + algebraic identity
  rw [h1]
  calc ∫ y, H y
      = ∫ p : SpacetimeDim d × NPointDomain d m, H (Fin.cons p.1 p.2) := by
        symm
        simpa [eSplit, MeasurableEquiv.piFinSuccAbove_symm_apply] using
          h_mp_split.symm.integral_comp' (g := H)
    _ = ∫ ξ : NPointDomain d m, ∫ x₀ : SpacetimeDim d, H (Fin.cons x₀ ξ) :=
        MeasureTheory.integral_prod_symm _ hH_pair_int
    _ = ∫ ξ, ∫ x₀, G ((realDiffCoordCLE (m + 1) d).symm
          (prependBasepointReal d m x₀ ξ)) := by
        simp_rw [hH_def, prependBasepointReal_eq_finCons]
        rfl

/-- At fixed positive imaginary height, the reduced smeared boundary integral
agrees with the absolute spectrum witness after changing variables to full
difference coordinates and integrating out the normalized basepoint cutoff. -/
theorem route1ReducedBoundaryIntegral_eq_absoluteBoundaryIntegral
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    ∀ (f : SchwartzNPoint d m) (η : Fin m → Fin (d + 1) → ℝ)
      (hη : η ∈ ProductForwardConeReal d m) {ε : ℝ}, 0 < ε →
      ∫ x : NPointDomain d m,
        (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
          (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x
        =
      ∫ x : NPointDomain d (m + 1),
        (Wfn.spectrum_condition (m + 1)).choose
          (fun k μ => (x k μ : ℂ) +
            ε * (absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I) *
          reducedTestLift m d χ f x := by
  intro f η hη ε hε
  let G : NPointDomain d (m + 1) → ℂ := fun x =>
    (Wfn.spectrum_condition (m + 1)).choose
      (fun k μ => (x k μ : ℂ) + ε * (absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I) *
      reducedTestLift m d χ f x
  have hG_int : MeasureTheory.Integrable G := by
    exact forward_tube_bv_integrable
      (Wfn.spectrum_condition (m + 1)).choose
      (Wfn.spectrum_condition (m + 1)).choose_spec.1
      ⟨{ toLinearMap := ⟨⟨Wfn.W (m + 1), (Wfn.linear (m + 1)).map_add⟩,
           (Wfn.linear (m + 1)).map_smul⟩,
         cont := Wfn.tempered (m + 1) },
        (Wfn.spectrum_condition (m + 1)).choose_spec.2⟩
      (reducedTestLift m d χ f)
      (absoluteDirectionOfReduced d m η)
      (absoluteDirectionOfReduced_mem_forwardCone (d := d) m η hη)
      ε hε
  rw [integral_realDiffCoord_change_variables (d := d) m G hG_int]
  simp_rw [G]
  have hfactor :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        (Wfn.spectrum_condition (m + 1)).choose
            (fun k μ =>
              (((realDiffCoordCLE (m + 1) d).symm
                (prependBasepointReal d m x₀ ξ) k μ : ℂ) +
                ε * (absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I)) =
          (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
            (fun k μ => (ξ k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) := by
    intro ξ x₀
    exact (route1ReducedPreInputFromSpectrumCondition_factorization_absoluteApproach
      (d := d) (Wfn := Wfn) (m := m) x₀ ξ η hη hε).symm
  simp_rw [hfactor]
  have htest :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        reducedTestLift m d χ f
          ((realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)) =
            χ.toSchwartz x₀ * f ξ := by
    intro ξ x₀
    simpa [reducedTestLift] using
      reducedTestLift_apply_realDiffCoordCLE_symm_prependBasepointReal
        (m := m) (d := d) (χ := χ.toSchwartz) (φ := f) x₀ ξ
  simp_rw [htest]
  simp_rw [mul_assoc]
  simp_rw [show ∀ (a b c : ℂ), a * (b * c) = (a * c) * b by
    intro a b c; ring]
  simp_rw [← smul_eq_mul (a := _ * _), MeasureTheory.integral_smul, smul_eq_mul]
  simp [χ.integral_eq_one]

/-- The reduced boundary-value theorem is now derived from a fixed-`ε`
change-of-variables identity together with the absolute `spectrum_condition`
boundary values. -/
theorem route1ReducedBoundaryValuesFromSpectrumCondition
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    HasReducedBoundaryValues (d := d)
      (route1ReducedWightmanFamily Wfn χ) m
      (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun := by
  intro f η hη
  let ηAbs := absoluteDirectionOfReduced d m η
  have hηAbs : InForwardCone d (m + 1) ηAbs :=
    absoluteDirectionOfReduced_mem_forwardCone (d := d) m η hη
  have habs :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : NPointDomain d (m + 1),
            (Wfn.spectrum_condition (m + 1)).choose
              (fun k μ => (x k μ : ℂ) + ε * (ηAbs k μ : ℂ) * Complex.I) *
            reducedTestLift m d χ f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (route1ReducedWightmanFamily Wfn χ m f)) := by
    simpa [ηAbs, route1ReducedWightmanFamily_apply, reducedWightman_apply] using
      (spectrumConditionAbsoluteInput (d := d) Wfn m).boundary_values
        (reducedTestLift m d χ f) ηAbs hηAbs
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d m,
          (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
            (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (m + 1),
          (Wfn.spectrum_condition (m + 1)).choose
            (fun k μ => (x k μ : ℂ) + ε * (ηAbs k μ : ℂ) * Complex.I) *
          reducedTestLift m d χ f x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact route1ReducedBoundaryIntegral_eq_absoluteBoundaryIntegral
      (d := d) Wfn χ m f η hη (Set.mem_Ioi.mp hε)
  exact Filter.Tendsto.congr' hEq.symm habs

/-- Temporary Route 1 reduced analytic datum, now isolated to the single
remaining bridge: proving reduced distributional boundary values for the
descended spectrum-condition witness. -/
noncomputable def route1ReducedAnalyticInputExists
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    Route1ReducedAnalyticInput Wfn χ m :=
  route1ReducedInputOfBoundary (d := d) Wfn χ m
    (route1ReducedBoundaryValuesFromSpectrumCondition (d := d) Wfn χ m)

/-- Fully packaged Route 1 absolute extension built from `Wfn` and a normalized
basepoint cutoff, using the temporary reduced-input existence axiom. -/
noncomputable def route1AbsoluteBHWExtensionCanonical
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  route1AbsoluteBHWExtension (d := d) Wfn χ
    (route1ReducedAnalyticInputExists (d := d) Wfn χ m)

/-- Canonical Route 1 translation invariance statement. This is the final proof
shape intended to replace the old overlap-connectedness argument once the
reduced analytic input is proved instead of axiomatized. -/
theorem route1AbsoluteBHWExtensionCanonical_translate
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    route1AbsoluteBHWExtensionCanonical (d := d) Wfn χ m
        (fun k μ => z k μ + c μ) =
      route1AbsoluteBHWExtensionCanonical (d := d) Wfn χ m z := by
  exact route1AbsoluteBHWExtension_translate (d := d) Wfn χ
    (route1ReducedAnalyticInputExists (d := d) Wfn χ m) z c

end BHW
